import Problem455CertifiedReduction
import Problem455WriterCatalogue
import Problem455StandardDecision
import Problem455SemanticConsequence



namespace P455Undecidability
open P455Table P455TableSemantics P455EffectiveMachine P455MachineCleanup
open P455PureSemigroup P455BinaryTerms P455CertifiedReduction

theorem catalogue_ok : Correct P455WriterCatalogue.build := by
  intro n M d h
  rw [P455WriterCatalogue.build_correct h,P455SerializePrim.as_of]

/-- Total numerical array function on all binary inputs, with a proof in
    mathlib's standard primitive recursive model. -/
def multiplicationTable := codeTable P455WriterCatalogue.build

theorem table_primitive_recursive : Primrec multiplicationTable :=
  codeRec P455WriterCatalogue.buildRec

theorem table_is_finite_monoid (s : List Bool) :
    SemigroupTable (multiplicationTable s) ∧ HasUnit (multiplicationTable s) :=
  finite_monoid P455WriterCatalogue.build (P455WriterProgram.fromCodeBits s)

theorem presents_exact_model (C : Code ng nq) (safe : C.Safe) :
    P455NumericProduct.Represents (multiplicationTable C.bits) (P455MachineReduction.model (C.machine safe)) :=
  code_presents catalogue_ok C safe

theorem blank_tape_reduction (C : Code ng nq) (safe : C.Safe) :
    Basis (multiplicationTable C.bits) ↔ ¬ ∃ t, stopped (C.machine safe) t :=
  code_basis catalogue_ok C safe

theorem presentation_writer_exists : P455TableDecision.PresentationWriterExists :=
  presentation catalogue_ok P455WriterCatalogue.buildRec

theorem no_table_decider : ¬P455TableDecision.PureDeciderExists :=
  P455TableDecision.no_table_algorithm_of_presentation_writer presentation_writer_exists

theorem no_bit_promise_decider : ¬P455BooleanReader.PromiseDecider :=
  P455StandardDecision.promise_of_tables (selfTable P455WriterCatalogue.build)
    (selfRec P455WriterCatalogue.buildRec).to_comp (fun x => (finite_monoid P455WriterCatalogue.build (P455WriterProgram.fromBits x)).1)
    (self_basis catalogue_ok)

theorem no_matrix_promise_decider : ¬P455StandardDecision.PromiseOn (id : Matrix→Matrix) :=
  P455StandardDecision.numeric_promise (selfTable P455WriterCatalogue.build)
    (selfRec P455WriterCatalogue.buildRec).to_comp (fun x => (finite_monoid P455WriterCatalogue.build (P455WriterProgram.fromBits x)).1)
    (self_basis catalogue_ok)

/-- On every finite associative nonempty multiplication array, the
    alleged algorithm must terminate and correctly test equality of
    its identity theory with the semantic consequences of a finite list
    of equations in the language having only variables and multiplication. -/
theorem finite_semigroup_finite_basis_undecidable :
    ¬ ∃ p : Matrix →. Bool, Partrec p ∧ ∀ T (valid : SemigroupTable T),
      ∃ b ∈ p T, (b=true ↔ ∃ R : List (Term×Term), ∀ s t,
        (∀ a : Nat→Fin T.length, P455StatementAudit.val valid a s=P455StatementAudit.val valid a t) ↔
        P455SemanticConsequence.entails (fun u v => (u,v)∈R) s t) := by
  rintro ⟨p,hp,answers⟩
  apply no_matrix_promise_decider
  refine ⟨p,hp,?_⟩
  intro T valid
  obtain ⟨b,halt,spec⟩ := answers T valid
  exact ⟨b,halt,spec.trans (P455SemanticConsequence.public_basis valid).symm⟩

end P455Undecidability
