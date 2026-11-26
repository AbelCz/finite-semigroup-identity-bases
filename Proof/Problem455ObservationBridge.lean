import Problem455Slots
import Problem455Closure
/- Literal profile-frame move and the observations of marked testers.
   Names are natural numbers. All occurrence indices in this file are zero-based. -/

namespace P455Closure.Move
open Problem455
variable {r : Nat} {Allowed : List Bool → Prop} {Mark : Nat → Nat → Prop}
  {u v : List Nat}

/-- Extract adjacent, commonly indexed block occurrences from a literal frame.
    No position, marked projection, or protected-slot preservation is a premise. -/
theorem asSlotMove (h : P455Closure.Move r Allowed Mark u v) :
    ∃ s : Slots.Move (r-2), u = Slots.before s ∧ v = Slots.after s ∧
      (∀ a ∈ s.p, ∀ b ∈ s.q, ¬ Mark a b ∧ ¬ Mark b a) ∧ 16 ≤ r := by
  obtain ⟨f,bit,l,t,hf,hu,hv,hc⟩ := h
  have hr := hf.1
  have hx : ∀ x, x ∈ f.p ∨ x ∈ f.q →
      (l ++ f.early ++ f.mid ++ f.beforeMutable).count x = r-2 := by
    intro x hx
    have hh := f.mutable_index hf bit l t (hu ▸ hc) x hx
    omega
  obtain ⟨_,_,_,np,nq,dis,marks,_⟩ := hf
  let s : Slots.Move (r-2) :=
    { pre := l ++ f.early ++ f.mid ++ f.beforeMutable
      p := f.p
      q := f.q
      post := f.beforeFinalP ++ f.p ++ f.beforeFinalQ ++ f.q ++ t
      dp := np
      dq := nq
      disjoint := dis
      indexP := fun x m => hx x (.inl m)
      indexQ := fun x m => hx x (.inr m) }
  cases bit with
  | false =>
    refine ⟨s,?_,?_,marks,by omega⟩ <;>
      simp [s, hu, hv, Slots.before, Slots.after, Frame.core, Frame.pair, List.append_assoc]
  | true =>
    let t' : Slots.Move (r-2) :=
      { pre := s.pre
        p := s.q
        q := s.p
        post := s.post
        dp := s.dq
        dq := s.dp
        disjoint := fun x hx hx' => s.disjoint x hx' hx
        indexP := s.indexQ
        indexQ := s.indexP }
    refine ⟨t',?_,?_,(fun x hx y hy => (marks y hy x hx).symm),by omega⟩ <;>
      simp [s, t', hu, hv, Slots.before, Slots.after, Frame.core, Frame.pair, List.append_assoc]

theorem order_iff (h : P455Closure.Move r Allowed Mark u v) (pat : List Slots.Event)
    (idx : ∀ e ∈ pat, e.2 ≠ r-2) : Slots.sees u pat ↔ Slots.sees v pat := by
  obtain ⟨s,rfl,rfl,_⟩ := asSlotMove h
  exact Slots.immutable_pattern s pat idx

theorem slot_iff (h : P455Closure.Move r Allowed Mark u v) (owner i a : Nat)
    (hi : Slots.slotStart i) : Slots.occupies u owner i a ↔ Slots.occupies v owner i a := by
  obtain ⟨s,rfl,rfl,_,hr⟩ := asSlotMove h
  have h1 : i ≠ r-2 := by unfold Slots.slotStart at hi; omega
  have h2 : i+1 ≠ r-2 := by unfold Slots.slotStart at hi; omega
  exact exists_congr (fun j => Slots.open_slot_event s owner i (i+1) (a,j) h1 h2)

theorem marked_proj (h : P455Closure.Move r Allowed Mark u v) (a b : Nat)
    (hm : Mark a b) : Slots.select [a,b] u = Slots.select [a,b] v := by
  obtain ⟨s,rfl,rfl,marks,_⟩ := asSlotMove h
  apply Slots.protected_projection
  by_cases hap : a ∈ s.p
  · right
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun eq => s.disjoint a hap (eq ▸ hx),
           fun eq => (marks a hap b (eq ▸ hx)).1 hm⟩
  · by_cases hbp : b ∈ s.p
    · right
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun eq => (marks b hbp a (eq ▸ hx)).2 hm,
             fun eq => s.disjoint b hbp (eq ▸ hx)⟩
    · left
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun eq => hap (eq ▸ hx),fun eq => hbp (eq ▸ hx)⟩

theorem typed_iff (h : P455Closure.Move r Allowed Mark u v) (a b : Nat)
    (tag : List Bool) (hne : a ≠ b) (hlen : tag.length+16 = r) :
    Slots.typed u a b tag ↔ Slots.typed v a b tag := by
  constructor
  · obtain ⟨s,rfl,rfl,_⟩ := asSlotMove h
    exact Slots.type_forward s a b tag hne (by omega)
  · obtain ⟨s,hu,hv,_⟩ := asSlotMove h.symm
    rw [hu,hv]
    exact Slots.type_forward s a b tag hne (by omega)

end P455Closure.Move
