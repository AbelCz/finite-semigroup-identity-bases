import Problem455Closure
import Problem455Swap



namespace Problem455BlockBridge
open P455Closure
open Problem455Swap

theorem occ_count (a : Nat) (w : List Nat) : occ a w = w.count a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases h : a = b
    · subst b; simp [occ, ih, List.count_cons, Nat.add_comm]
    · simp [occ, ih, List.count_cons, h, Ne.symm h]

private def leftPart (f : Frame Nat) (l : List Nat) :=
  l ++ f.early ++ f.mid ++ f.beforeMutable
private def rightPart (f : Frame Nat) (t : List Nat) :=
  f.beforeFinalP ++ f.p ++ f.beforeFinalQ ++ f.q ++ t

private theorem frame_false (f : Frame Nat) (l t : List Nat) :
    l ++ f.core false ++ t = leftPart f l ++ f.p ++ f.q ++ rightPart f t := by
  simp [leftPart, rightPart, Frame.core, Frame.pair, List.append_assoc]

private theorem frame_true (f : Frame Nat) (l t : List Nat) :
    l ++ f.core true ++ t = leftPart f l ++ f.q ++ f.p ++ rightPart f t := by
  simp [leftPart, rightPart, Frame.core, Frame.pair, List.append_assoc]

private theorem early_factor (f : Frame Nat) (l t : List Nat) (b : Bool) :
    Factor (privatePhase f.p f.q) (l ++ f.core b ++ t) := by
  refine ⟨l, f.mid ++ f.beforeMutable ++ f.pair b ++ f.beforeFinalP ++ f.p ++
      f.beforeFinalQ ++ f.q ++ t, ?_⟩
  simp [Frame.core, Frame.early, privatePhase, List.append_assoc]

private theorem frameLink {r : Nat} {allow : List Bool → Prop} {mark : Nat → Nat → Prop}
    (f : Frame Nat) (l t : List Nat) (wf : f.Valid r allow mark)
    (hc : Cap r (l ++ f.core false ++ t)) (x y : Nat) :
    Link r (l ++ f.core false ++ t) x y ↔ Link r (l ++ f.core true ++ t) x y := by
  have pn : f.p ≠ [] := by simp [Frame.p]
  have qn : f.q ≠ [] := by simp [Frame.q]
  let i := f.pHead
  let j := f.q.head qn
  let s := f.p.getLast pn
  let z := f.qLast
  have hp : f.p.head? = some i := rfl
  have hq : f.q.head? = some j := List.head?_eq_head qn
  have ep : f.p.getLast? = some s := List.getLast?_eq_getLast pn
  have eq : f.q.getLast? = some z := by simp [Frame.q,z]
  have disj := wf.2.2.2.2.2.1
  have hpMem : i ∈ f.p := by simp [i, Frame.p]
  have hqMem : j ∈ f.q := List.head_mem _
  have epMem : s ∈ f.p := List.getLast_mem _
  have eqMem : z ∈ f.q := by simp [z,Frame.q]
  have hij : i ≠ j := fun h => disj i hpMem (h ▸ hqMem)
  have hsz : s ≠ z := fun h => disj s epMem (h ▸ eqMem)
  have cf : cap r (l ++ f.core false ++ t) := by
    intro a
    rw [occ_count]
    exact hc a
  have ef := early_factor f l t false
  have et := early_factor f l t true
  rw [frame_false] at cf ef ⊢
  rw [frame_true] at et ⊢
  exact repeatedLink_swap _ _ hp hq ep eq hij hsz cf ef et x y

/-- Invariance of each repeated adjacent pair under the actual frame move. -/
theorem move_link {r : Nat} {allow : List Bool → Prop} {mark : Nat → Nat → Prop}
    {u v : List Nat} (h : Move r allow mark u v) (x y : Nat) :
    Link r u x y ↔ Link r v x y := by
  have hd := h.cap_right
  obtain ⟨f,b,l,t,hf,rfl,rfl,hc⟩ := h
  cases b
  · exact frameLink f l t hf hc x y
  · exact (frameLink f l t hf hd x y).symm

/-- The repeated-block relation consists of saturated endpoints and paths
    in the fixed graph of repeated links. -/
theorem move_sameBlock {r : Nat} {allow : List Bool → Prop} {mark : Nat → Nat → Prop}
    {u v : List Nat} (h : Move r allow mark u v) (x y : Nat) :
    SameBlock r u x y ↔ SameBlock r v x y := by
  have rel : Link r u = Link r v := funext fun a => funext fun b => propext (move_link h a b)
  simp only [SameBlock,rel,occ_count,h.count_eq]

end Problem455BlockBridge
