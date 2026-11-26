import Problem455CellClassFrames
import Problem455CellClassRank
import Problem455GridRows



namespace P455CellClassSnake
open P455RectangleRank P455CellClassFrames P455CellClass P455Witness P455CrossedSupport
open P455Closure P455SlotSaturation P455Uncrossed P455MarkedRank P455GridRows
open P455PortReflection P455ActualGuards P455ConstantLayout Problem455.Slots
abbrev W := List Nat

theorem closedAt {r allow t m z} (p : Phases r allow t m z) (bits : Nat → Bool) {i} (ix : i<t) :
    ClosedFlip r allow (word t m z bits) (owner i) (mate i) := by
  obtain ⟨f,l,k,hp,hq,ok,both⟩ := frameAt p bits ix
  have base : word t m z bits = word t m z (revise bits i (bits i)) :=
    same_word m z (fun j _ => by by_cases same : j=i <;> simp [revise,same])
  exact ⟨f,bits i,l,k,hp,hq,ok,base.trans (both _)⟩

theorem chain_walk {r allow used u v} (cp : Cap r u) (p : Chain r allow used u v) :
    P455Quotient.Walk (P455Closure.Move r allow noMark) u v := by
  induction p with
  | refl => exact .refl _
  | snoc _ flip ih =>
    obtain ⟨x,y,f,b,l,k,_,_,_,yes,rfl,rfl⟩ := flip
    have cv : Cap r (side f l k b) := fun a =>
      (P455Quotient.count_walk (rules r allow noMark) ih a) ▸ cp a
    exact .snoc ih ⟨f,b,l,k,yes,rfl,rfl,cv⟩

def At (r : Nat) (allow : Tag → Prop) (ts : Tiles) (w : W) (i j : Nat) :=
  ∃ e : EdgeCertificate, e.a.owner=owner i ∧ e.a.mate=mate i ∧
    e.b.owner=owner j ∧ e.b.mate=mate j ∧ Arrow r allow noMark w ts e

private theorem free_local (ts : Tiles) (e : EdgeCertificate) : markFree (localCert ts e)=true := by
  have hor (a b : Node) : markFree (rightward ts a b)=true := rfl
  have vert (a b : Node) : markFree (downward ts a b)=true := rfl
  cases rr : ts.right e.a.tag <;> cases ll : ts.left e.a.tag <;>
    cases dd : ts.bottom e.a.tag <;> cases uu : ts.top e.a.tag <;>
      simp [localCert,rr,ll,dd,uu,flagQ,allQ,markFree,hor,vert]

private theorem free_succ (ts : Tiles) (e : EdgeCertificate) : markFree (chosenSuccessor ts e)=true := by
  cases wrap : endOfRow ts e.a && ts.bottom e.a.tag <;> simp only [chosenSuccessor,wrap,Bool.false_eq_true,if_false,if_true] <;> rfl

/-- Changing the mutable cells preserves all bit-free arrows along the
    actual path. If a given snake edge now reads 1,0, the very same raw
    finite certificate succeeds with its two designated endpoint marks. -/
theorem descent {r allow ts t m z} (p : Phases r allow t m z) (bits : Nat → Bool)
    (finalPair : ∀ i<t, select [owner i,mate i] z=[owner i,mate i])
    {i j : Nat} (ix : i<t) (jx : j<t) (yes : bits i=true) (no : bits j=false)
    (arrow : At r allow ts (word t m z (constant false)) i j) :
    EdgeViolation r allow ts (word t m z bits) (owner i) (mate i) := by
  obtain ⟨e,ao,am,bo,bm,sa,sb,localQ,next⟩ := arrow
  let mark := P455SourceTheorem.sourceMarks id (.edge e)
  let w := word t m z bits
  have walk := chain_walk p.capped (chain p bits)
  have pass (q : Query) (h : Holds r allow noMark (word t m z (constant false)) q) :
      Holds r allow noMark w q := walk.transport h (fun mv old => (query_invariant mv _).mp old)
  have message (n : Node) (k : Nat) (lt : k<t) (o : n.owner=owner k) (a : n.mate=mate k)
      (record : Holds r allow noMark (word t m z (constant false)) (typedNode n))
      (marked : mark n.owner n.mate) : Holds r allow mark w (markedNode n (bits k)) := by
    obtain ⟨ne,len,admitted,tr⟩ := pass _ record
    refine ⟨ne,len,admitted,.inl marked,?_⟩
    rw [o,a] at tr ⊢
    exact read_bit lt m z bits (finalPair k lt) n.tag tr
  have anchor := message e.a i ix ao am sa (Or.inl ⟨rfl,rfl⟩)
  have successor := message e.b j jx bo bm sb (Or.inr ⟨rfl,rfl⟩)
  rw [yes] at anchor; rw [no] at successor
  exact ⟨e,false,.inl ⟨ao,am⟩,anchor,successor,remark (free_local ..) (pass _ localQ),
    remark (free_succ ..) (pass _ next),True.intro⟩

/-- These hypotheses are raw letter, tile and witness statements. The two
    constant endpoints are assumed geometrically clean at their cell pairs. -/
structure Geometry (r : Nat) (allow : Tag → Prop) (ts : Tiles) (t : Nat) (m z : W) where
  phases : Phases r allow t m z
  names : ∀ x ∈ m ++ z, x < 2*t
  finalPair : ∀ i<t, select [owner i,mate i] z=[owner i,mate i]
  clean : ∀ b i, i<t → ¬ P455SingletonEvaluation.Violation r allow ts (word t m z (constant b)) (owner i) (mate i)
  next : ∀ i, i+1<t → At r allow ts (word t m z (constant false)) i (i+1)
  wrap : 0<t → At r allow ts (word t m z (constant false)) (t-1) 0

def layout {r allow ts t m z} (hr : 0<r) (g : Geometry r allow ts t m z) :
    P455ConstantLayout.Layout r allow ts (fun b => word t m z (constant b)) := by
  have cap (b : Bool) := cap_word g.phases.capped (constant b)
  refine ⟨Used t,chain g.phases (constant true),?_,?_,?_,?_⟩
  · intro b a ha
    have small := word_names _ g.names a ha
    have lt : a/2<t := by omega
    obtain ⟨_,co,cm,_⟩ := flip_counts (cap b) (closedAt g.phases (constant b) lt)
    have which : a=owner (a/2) ∨ a=mate (a/2) := by unfold owner mate; omega
    rcases which with eq|eq <;> first | exact eq ▸ co | exact eq ▸ cm
  · intro b; exact no_links hr (constant b) g.names (cap b)
  · rintro b _ _ ⟨i,ix,rfl,rfl⟩; exact closedAt g.phases (constant b) ix
  · rintro b _ _ ⟨i,ix,rfl,rfl⟩; exact g.clean b i ix

theorem no_basis {r allow ts} (hr : 0<r)
    (padding : ∀ k : Nat, ∃ (t : Nat) (m z : W), k<2*t ∧ Nonempty (Geometry r allow ts t m z))
    (basis : List (W × W)) (sound : ∀ u v, (u,v) ∈ basis → (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (P455FullSingleton.model r allow ts).Valid U V ∧
      ¬ P455FirstRewrite.Derives (fun u v => (u,v) ∈ basis) U V := by
  apply P455CellClassRank.no_basis hr _ basis sound
  intro k; obtain ⟨t,m,z,big,⟨g⟩⟩ := padding k
  exact ⟨t,m,z,big,g.names,g.finalPair,⟨layout hr g⟩,
    fun bit i h yes no => descent g.phases bit g.finalPair (by omega) h yes no (g.next i h),
    fun bit h yes no => descent g.phases bit g.finalPair (by omega) h yes no (g.wrap h)⟩

end P455CellClassSnake
