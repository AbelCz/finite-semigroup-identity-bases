import Problem455WriterObservations
namespace P455WriterBlocks
open Problem455Swap P455WriterTiles P455WriterProfiles P455WriterObservations

def stable (r : Nat) (w s : W) :=
  (choices s w).all fun p => decide ((bigram p.1 p.2 w=r ∨ bigram p.2 p.1 w=r) → p.2∈s)

theorem stable_ok (r : Nat) (w s : W) : stable r w s=true ↔ P455Enum.stable r w s := by
  simp only [stable,P455Enum.stable,choices,List.all_eq_true,List.mem_flatMap,List.mem_map,decide_eq_true_eq,Link]
  constructor
  · intro h a i b j
    exact h (a,b) ⟨a,i,b,j,rfl⟩
  · rintro h _ ⟨a,i,b,j,rfl⟩
    exact h a i b j

def joined (r : Nat) (w : W) (x y : Nat) :=
  let v := x::w
  (Problem455Finite.wordsUpTo v v.length).all fun s => decide (x∈s → stable r w s=true → y∈s)

theorem joined_ok {r : Nat} (hr : 0<r) (w : W) (x y : Nat) :
    joined r w x y=true ↔ Joined (Link r w) x y := by
  simp only [joined,List.all_eq_true,decide_eq_true_eq,stable_ok]
  constructor
  · intro closed
    classical
    let v := x::w
    let s := v.filter (fun a => decide (Joined (Link r w) x a))
    have mem {a} : a∈s ↔ a∈v ∧ Joined (Link r w) x a := by simp [s]
    have ins : s∈Problem455Finite.wordsUpTo v v.length :=
      Problem455Finite.covered _ _ _ (List.length_filter_le ..) (fun _ m => (mem.mp m).1)
    have st : P455Enum.stable r w s := fun _ ma _ mb ed =>
      mem.mpr ⟨List.mem_cons_of_mem _ mb,.extend (mem.mp ma).2 ed⟩
    exact (mem.mp (closed s ins (mem.mpr ⟨List.mem_cons_self,.refl _⟩) st)).2
  · intro path s _ start st
    induction path with
    | refl => exact start
    | extend p ed ih =>
      exact st _ ih _ (ed.elim (fun h => (P455Enum.linkNames hr h).2) (fun h => (P455Enum.linkNames hr h).1)) ed

def same (r : Nat) (w : W) (x y : Nat) := decide (w.count x=r ∧ w.count y=r) && joined r w x y

theorem same_ok {r : Nat} (hr : 0<r) (w : W) (x y : Nat) : same r w x y=true ↔ SameBlock r w x y := by
  simp only [same,SameBlock,Problem455BlockBridge.occ_count,Bool.and_eq_true,decide_eq_true_eq,joined_ok hr,and_assoc]

variable {A : Type} [Primcodable A]

theorem stableRec {r : A → Nat} {w s : A → W} (hr : Primrec r) (hw : Primrec w) (hs : Primrec s) :
    Primrec fun a => stable (r a) (w a) (s a) := by
  apply P455FramePrim.allB (choicesRec hs hw)
  apply Primrec₂.mk
  have p := Primrec.snd (α := A) (β := Nat × Nat)
  have a := Primrec.fst.comp p
  have b := Primrec.snd.comp p
  have xy := Primrec.eq.comp (bigramRec (hw.comp Primrec.fst) a b) (hr.comp Primrec.fst)
  have yx := Primrec.eq.comp (bigramRec (hw.comp Primrec.fst) b a) (hr.comp Primrec.fst)
  exact impliesRec (PrimrecPred.or xy yx) (P455CataloguePrim.mem'.comp b (hs.comp Primrec.fst))

theorem joinedRec {r x y : A → Nat} {w : A → W} (hr : Primrec r) (hw : Primrec w) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun a => joined (r a) (w a) (x a) (y a) := by
  have v := Primrec.list_cons.comp hx hw
  unfold joined
  apply P455FramePrim.allB (p := fun a s => decide (x a∈s → stable (r a) (w a) s=true → y a∈s)) (P455GraphPrim.wordsUpTo.comp v (Primrec.list_length.comp v))
  apply Primrec₂.mk
  have s := Primrec.snd (α := A) (β := W)
  exact impliesRec (P455CataloguePrim.mem'.comp (hx.comp Primrec.fst) s)
    (impliesRec (Primrec.eq.comp (stableRec (hr.comp Primrec.fst) (hw.comp Primrec.fst) s) (.const true))
      (P455CataloguePrim.mem'.comp (hy.comp Primrec.fst) s))

theorem sameRec {r x y : A → Nat} {w : A → W} (hr : Primrec r) (hw : Primrec w) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun a => same (r a) (w a) (x a) (y a) :=
  Primrec.and.comp (PrimrecPred.and (Primrec.eq.comp (P455CataloguePrim.count'.comp hw hx) hr)
    (Primrec.eq.comp (P455CataloguePrim.count'.comp hw hy) hr)) (joinedRec hr hw hx hy)

end P455WriterBlocks
