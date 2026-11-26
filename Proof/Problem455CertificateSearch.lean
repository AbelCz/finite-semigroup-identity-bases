import Mathlib.Computability.Partrec



namespace P455CertificateSearch
variable {α β : Type} [Primcodable α] [Primcodable β]

/-- A computable total checker scans certificates numbered by naturals.
    A certificate exists on every input. All accepted certificates recover
    the designated value, possibly with differing proof data or indices. -/
theorem computable_of_search (f : α → β) (check : α → Nat → Option β)
    (effective : Computable₂ check)
    (complete : ∀ x, ∃ n y, check x n=some y)
    (sound : ∀ x n y, check x n=some y → y=f x) : Computable f := by
  apply (Partrec.rfindOpt effective).of_eq_tot
  intro x
  have dom : (Nat.rfindOpt (check x)).Dom := Nat.rfindOpt_dom.mpr (complete x)
  have hit := Part.get_mem dom
  obtain ⟨n,accept⟩ := Nat.rfindOpt_spec hit
  rwa [sound x n _ accept] at hit

/-- If different certificates give different equally valid outputs, the
    very same search realizes a total partial-recursive selector. Its
    graph entails the required relation; no canonical numbering is needed. -/
theorem relational_search (rel : α → β → Prop) (check : α → Nat → Option β)
    (effective : Computable₂ check)
    (complete : ∀ x, ∃ n y, check x n=some y)
    (sound : ∀ x n y, check x n=some y → rel x y) :
    ∃ f : α → β, Computable f ∧ ∀ x, rel x (f x) := by
  have dom (x : α) : (Nat.rfindOpt (check x)).Dom := Nat.rfindOpt_dom.mpr (complete x)
  let f (x : α) := (Nat.rfindOpt (check x)).get (dom x)
  refine ⟨f,(Partrec.rfindOpt effective).of_eq_tot (fun x => Part.get_mem (dom x)),?_⟩
  intro x
  obtain ⟨n,accept⟩ := Nat.rfindOpt_spec (Part.get_mem (dom x))
  exact sound x n _ accept

end P455CertificateSearch
