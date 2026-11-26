import Problem455Undecidability

open P455Table P455TableSemantics P455BinaryTerms
open P455StatementAudit P455SemanticConsequence

-- No free implicit parameters occur in this statement.
example :
    ¬ ∃ algorithm : List (List Nat) →. Bool, Partrec algorithm ∧
      ∀ (T : List (List Nat)) (good : SemigroupTable T),
        ∃ b ∈ algorithm T, (b = true ↔
          ∃ laws : List (Term × Term), ∀ left right,
            (∀ assignment : Nat → Fin T.length,
              val good assignment left = val good assignment right) ↔
            ∀ (A : Type) (mul : A → A → A),
              (∀ l r, (l,r) ∈ laws → ∀ f : Nat → A, ev mul f l = ev mul f r) →
              ∀ f : Nat → A, ev mul f left = ev mul f right) :=
  P455Undecidability.finite_semigroup_finite_basis_undecidable

#print axioms P455Undecidability.presentation_writer_exists
#print axioms P455Undecidability.table_primitive_recursive
#print axioms P455Undecidability.presents_exact_model
#print axioms P455Undecidability.blank_tape_reduction
#print axioms P455Undecidability.finite_semigroup_finite_basis_undecidable
