import Problem455FullSingleton
import Problem455RectangleRank

/- These two conditional implications use the very same tester product.
   The geometric data required to apply them are exhibited in the types. -/
namespace P455ReductionBoundary
open P455Witness P455FirstRewrite P455CrossedSupport P455SourceFamilies P455SlotSaturation
open P455ActualGuards P455Uncrossed P455FullSingleton P455Schedule Problem455.Slots
abbrev W := List Nat

theorem sym_step {G : W → W → Prop} {u v} (st : Step G u v) : Step G v u := by
  obtain ⟨a,b,l,k,h,rule,an,bn,hn,lo,hi⟩ := st
  exact ⟨b,a,l,k,h,rule.symm,bn,an,hn,hi,lo⟩

/-- Data on a scheduled local change. Independent intermediate words need
    no assumed algebraic validity. The changed pair and path refer back
    to the original endpoint identity U,V. -/
structure Layout (r : Nat) (allow : Tag → Prop) (ts : Tiles) (U V A B : W) where
  x : Nat
  y : Nat
  f : P455Closure.Frame Nat
  l : W
  k : W
  bit : Bool
  hp : f.p = [x]
  hq : f.q = [y]
  frame : f.Valid r allow noMark
  cap : P455Closure.Cap r (side f l k false)
  anchor : ClosedFlip r allow U x y
  changed : select [x,y] U ≠ select [x,y] V
  path : P455Quotient.Walk (P455Closure.Move r allow noMark) U (side f l k bit)
  compressed : Compressed r (side f l k bit)
  legal : ∀ b, ¬ EdgeViolation r allow ts (side f l k b) x y
  fromWord : A = side f l k bit
  toWord : B = side f l k (!bit)

theorem Layout.step {r allow ts U V A B} (g : Layout r allow ts U V A B)
    (capU : P455Closure.Cap r U) (idUV : (model r allow ts).Valid U V) :
    Step (fun a b => (model r allow ts).Valid a b ∧ rank a b ≤ P455MarkedRank.bound r) A B := by
  have mv : P455Closure.Move r allow noMark (side g.f g.l g.k false) (side g.f g.l g.k true) :=
    ⟨g.f,false,g.l,g.k,g.frame,rfl,rfl,g.cap⟩
  have path0 : P455Quotient.Walk (P455Closure.Move r allow noMark) U (side g.f g.l g.k false) := by
    cases h : g.bit
    · simpa [h] using g.path
    · exact .snoc (by simpa [h] using g.path) mv.symm
  have cmp0 : Compressed r (side g.f g.l g.k false) := by
    cases h : g.bit
    · simpa [h] using g.compressed
    · have cmp := g.compressed; rw [h] at cmp
      exact fun a b link => cmp a b ((Problem455BlockBridge.move_link mv a b).mp link)
  have st := bounded_step g.f g.l g.k g.x g.y g.hp g.hq g.frame g.cap U V capU idUV g.anchor
    g.changed path0 cmp0 g.legal
  have transport {a b c d : W} {G : W → W → Prop} (h : a=c) (j : b=d) (s : Step G c d) :
      Step G a b := by subst c; subst d; exact s
  apply transport g.fromWord g.toWord
  cases g.bit
  · exact st
  · exact sym_step st

theorem scheduled_deduction {r allow ts C E} (acy : Acyclic C E) (A B : Bits)
    (start : Good C E A) (finish : Good C E B) (fixed : ∀ a, A a ≠ B a → a ∈ C)
    (word : Bits → W) (cap : P455Closure.Cap r (word A))
    (valid : (model r allow ts).Valid (word A) (word B))
    (geometry : ∀ s t, Toward C E B s t → Nonempty (Layout r allow ts (word A) (word B) (word s) (word t))) :
    Derives (fun a b => (model r allow ts).Valid a b ∧ rank a b ≤ P455MarkedRank.bound r) (word A) (word B) :=
  derivation acy A B start finish fixed word _ (fun s t move => (geometry s t move).elim
    (fun g => g.step cap valid))

/-- The size parameter is inside the quantifier for one fixed monoid.
    The profile-geometry and semantic inputs are explicit, especially
    the constant identity and the complete class of the all-zero word. -/
theorem rectangle_family_no_basis {r allow ts} (hr : 0 < r)
    (padding : ∀ k : Nat, ∃ (t : Nat) (middle tail : W), k < 2*t ∧
      (∀ x ∈ middle ++ tail, x < 2*t) ∧ P455Quotient.Cap r (P455RectangleRank.word t middle tail
        (P455RectangleRank.constant false)) ∧
      (model r allow ts).Valid (P455RectangleRank.word t middle tail (P455RectangleRank.constant false))
        (P455RectangleRank.word t middle tail (P455RectangleRank.constant true)) ∧
      (∀ w, (model r allow ts).Valid (P455RectangleRank.word t middle tail (P455RectangleRank.constant false)) w →
        ∃ b, w = P455RectangleRank.word t middle tail b) ∧
      (∀ b, (model r allow ts).Valid (P455RectangleRank.word t middle tail (P455RectangleRank.constant false))
        (P455RectangleRank.word t middle tail b) →
        (∀ i, i+1 < t → b i = true → b (i+1) = true) ∧ (0 < t → b (t-1) = true → b 0 = true)))
    (basis : List (W × W)) (sound : ∀ u v, (u,v) ∈ basis → (model r allow ts).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (model r allow ts).Valid U V ∧ ¬ Derives (fun u v => (u,v) ∈ basis) U V := by
  apply no_basis_of_witnesses hr _ basis sound
  intro k
  obtain ⟨t,m,z,big,letters,cap,eq,all,edges⟩ := padding k
  exact ⟨_,_,_,P455RectangleRank.witness hr (by omega) m z letters cap eq all edges,by simpa using big⟩

end P455ReductionBoundary
