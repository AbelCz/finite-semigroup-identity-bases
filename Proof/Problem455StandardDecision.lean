import Problem455BooleanReader
import Problem455ComputableReduction

namespace P455StandardDecision
open P455MachineCleanup P455EffectiveMachine P455EffectiveChain P455RelabeledChain
open P455TableBits P455BooleanReader

theorem bit_decider {f : List Bool → Bool} (hf : Computable f) :
    ∃ (g q : Nat) (M : Ordinary g q) (A : Alphabet M) (ans : Fin q → Bool),
      ∀ x, Answers M A ans x (f x) := by
  have single : Computable (fun x => [f x]) :=
    Primrec.list_cons.to_comp.comp hf (Computable.const [])
  obtain ⟨g,r,W,A,writer⟩ := P455ComputableWriter.realizes single
  refine ⟨_,_,combined W A reader bits,inputs W A A reader bits,out r ans,?_⟩
  intro x
  exact answers_combined W A A reader bits ans (writer _) (reads_bit _)

theorem ordinary_of_standard : StandardDecider → P455TableDecision.PureDeciderExists := by
  rintro ⟨f,hf,correct⟩
  obtain ⟨g,q,M,A,ans,run⟩ := bit_decider hf
  exact ⟨g,q,M,A,ans,fun T valid => ⟨_,run (encode T),correct T valid⟩⟩

theorem standard_reduction (code : Computable P455PayloadBridge.selfPayload) : ¬StandardDecider :=
  fun alleged => P455ComputableReduction.reduction code (ordinary_of_standard alleged)

theorem table_valid (x : List Bool) : P455TableSemantics.SemigroupTable (P455PackedOutput.selfTable x) := by
  unfold P455PackedOutput.selfTable
  cases P455MachineParse.blankSource x with
  | none => exact (P455TableSemantics.output_laws P455RawReduction.singletonPresents).1
  | some src =>
    obtain ⟨_,_,M⟩ := src
    obtain ⟨_,h,⟨pres⟩⟩ := P455PackedOutput.alternative_represents M
    change P455TableSemantics.SemigroupTable (P455PackedOutput.alternative M)
    rw [h]
    exact (P455TableSemantics.output_laws pres).1

def PromiseOn {α : Type} [Primcodable α] (representation : P455Table.Matrix → α) :=
  ∃ p : α →. Bool, Partrec p ∧ ∀ T, P455TableSemantics.SemigroupTable T →
    ∃ b ∈ p (representation T), (b=true ↔ P455PureSemigroup.Basis T)

/-- Only the composite on machine codes is totalized. The alleged table
    decider is not required to return any answer on invalid encodings. -/
theorem promise_of_encoding {α : Type} [Primcodable α] (representation : P455Table.Matrix → α)
    (tables : List Bool → P455Table.Matrix)
    (computes : Computable (fun x => representation (tables x)))
    (valid : ∀ x, P455TableSemantics.SemigroupTable (tables x))
    (correct : ∀ {g q} (M : Ordinary g q) (A : Alphabet M),
      P455PureSemigroup.Basis (tables (selfBits M A)) ↔ ¬SelfHalt M A) :
    ¬PromiseOn representation := by
  rintro ⟨p,hp,good⟩
  let bits x := representation (tables x)
  have total (x : List Bool) : (p (bits x)).Dom := by
    obtain ⟨b,hb,_⟩ := good _ (valid x)
    exact Part.dom_iff_mem.mpr ⟨_,hb⟩
  let f (x : List Bool) := (p (bits x)).get (total x)
  have hf : Computable f := (hp.comp computes).of_eq_tot
    (fun x => Part.get_mem (total x))
  have exact_result (x : List Bool) : f x=true ↔ P455PureSemigroup.Basis (tables x) := by
    obtain ⟨b,hb,claim⟩ := good _ (valid x)
    have same : f x=b := Part.mem_unique (Part.get_mem (total x)) hb
    rw [same]; exact claim
  obtain ⟨_,_,D,A,ans,run⟩ := bit_decider hf
  apply no_self_decider D A (fun q => !(ans q))
  intro g q M B
  let x := selfBits M B
  obtain ⟨t,stop,verdict⟩ := run x
  refine ⟨t,stop,?_⟩
  have hs := (exact_result x).trans (correct M B)
  change (!(ans (follow D (inputConfig D A x) t).state))=true ↔ SelfHalt M B
  rw [verdict]
  classical
  cases eq : f x <;> simp_all

/-- A partial decider on canonically serialized rows. -/
theorem promise_of_bits (tables : List Bool → P455Table.Matrix)
    (computes : Computable (fun x => P455TableBits.encode (tables x)))
    (valid : ∀ x, P455TableSemantics.SemigroupTable (tables x))
    (correct : ∀ {g q} (M : Ordinary g q) (A : Alphabet M),
      P455PureSemigroup.Basis (tables (selfBits M A)) ↔ ¬SelfHalt M A) :
    ¬PromiseDecider :=
  promise_of_encoding P455TableBits.encode tables computes valid correct

/-- The natural matrix itself is the input. A decider may diverge on every
    malformed or nonassociative matrix. -/
theorem numeric_promise (tables : List Bool → P455Table.Matrix)
    (computes : Computable tables) (valid : ∀ x, P455TableSemantics.SemigroupTable (tables x))
    (correct : ∀ {g q} (M : Ordinary g q) (A : Alphabet M),
      P455PureSemigroup.Basis (tables (selfBits M A)) ↔ ¬SelfHalt M A) :
    ¬PromiseOn (id : P455Table.Matrix → P455Table.Matrix) :=
  promise_of_encoding id tables computes valid correct

theorem promise_of_tables (tables : List Bool → P455Table.Matrix)
    (computes : Computable tables) (valid : ∀ x, P455TableSemantics.SemigroupTable (tables x))
    (correct : ∀ {g q} (M : Ordinary g q) (A : Alphabet M),
      P455PureSemigroup.Basis (tables (selfBits M A)) ↔ ¬SelfHalt M A) :
    ¬PromiseDecider :=
  promise_of_bits tables (P455NumericProductPrim.encode.to_comp.comp computes) valid correct

theorem promise_reduction (code : Computable P455PayloadBridge.selfPayload) : ¬PromiseDecider :=
  promise_of_bits P455PackedOutput.selfTable (P455PayloadBridge.selfOutput_computable code)
    table_valid P455PackedOutput.pure_basis_on_self

end P455StandardDecision
