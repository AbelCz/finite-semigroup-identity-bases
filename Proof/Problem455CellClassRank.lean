import Problem455CellClass



namespace P455CellClassRank
open P455FirstRewrite P455RectangleRank P455Witness P455ActualGuards P455MarkedRank
open P455CellClass Problem455.Slots
abbrev W := List Nat

theorem no_incident_descent {r allow ts t middle tail bit i} (ix : i<t) (yes : bit i=true)
    (cap : P455Quotient.Cap r (word t middle tail (constant false)))
    (tailPair : select [owner i,mate i] tail = [owner i,mate i])
    (ident : (P455FullSingleton.model r allow ts).Valid (word t middle tail (constant false))
      (word t middle tail bit)) :
    ¬ EdgeViolation r allow ts (word t middle tail bit) (owner i) (mate i) := by
  have cv : P455Quotient.Cap r (word t middle tail bit) :=
    fun a => (P455CellClassBinary.exact_counts cap ident a) ▸ cap a
  have reverse : (P455FullSingleton.model r allow ts).Valid (word t middle tail bit)
    (word t middle tail (constant false)) := fun f => (ident f).symm
  exact endpoint_feasible cv (((valid_pair ..).mp ((valid_pair ..).mp reverse).2).1)
    (bit_change ix middle tail bit yes tailPair)

/-- The witnesses are local word observations at given cell labels. No
    assumption about the semantic identity classes enters the padding
    data. The model and its entire signature are fixed before k. -/
theorem no_basis {r allow ts} (hr : 0 < r)
    (padding : ∀ k : Nat, ∃ (t : Nat) (middle tail : W), k < 2*t ∧
      (∀ x ∈ middle ++ tail, x < 2*t) ∧
      (∀ i<t, select [owner i,mate i] tail = [owner i,mate i]) ∧
      Nonempty (P455ConstantLayout.Layout r allow ts (fun b => word t middle tail (constant b))) ∧
      (∀ (bit : Nat → Bool) (i : Nat), i+1<t → bit i=true → bit (i+1)=false →
        EdgeViolation r allow ts (word t middle tail bit) (owner i) (mate i)) ∧
      (∀ (bit : Nat → Bool), 0<t → bit (t-1)=true → bit 0=false →
        EdgeViolation r allow ts (word t middle tail bit) (owner (t-1)) (mate (t-1))))
    (basis : List (W × W)) (sound : ∀ u v, (u,v) ∈ basis → (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (P455FullSingleton.model r allow ts).Valid U V ∧
      ¬ Derives (fun u v => (u,v) ∈ basis) U V := by
  apply P455ConstantProduct.rectangle_no_basis hr _ basis sound
  intro k
  obtain ⟨t,m,z,big,small,tailPair,⟨layout⟩,next,wrap⟩ := padding k
  have cap : P455Quotient.Cap r (word t m z (constant false)) := by
    intro a; by_cases mem : a ∈ word t m z (constant false)
    · exact Nat.le_of_eq (layout.uniform false a mem)
    · simp [List.count_eq_zero.mpr mem]
  refine ⟨t,m,z,big,small,⟨layout⟩,(fun w idw => represent small cap tailPair idw),?_⟩
  intro bit valid
  constructor
  · intro i lt yes
    have ix : i<t := by omega
    cases hb : bit (i+1)
    · exact False.elim (no_incident_descent ix yes cap (tailPair i ix) valid (next bit i lt yes hb))
    · rfl
  · intro positive yes
    have ix : t-1<t := by omega
    cases hb : bit 0
    · exact False.elim (no_incident_descent ix yes cap (tailPair _ ix) valid (wrap bit positive yes hb))
    · rfl

end P455CellClassRank
