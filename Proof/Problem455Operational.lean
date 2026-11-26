import Problem455RawReduction
import Problem455EffectiveMachineRelabelChain




namespace P455Operational
open P455EffectiveMachine P455MachineCleanup P455EffectiveChain P455RelabeledChain
open P455RawReduction P455TableBits P455TableSemantics

def DecidesTable (D : Ordinary g r) (B : Alphabet D) (ans : Fin r → Bool) :=
  Separates (Answers D B ans)

/-- A single transducer, independent of all readers, including their
    alphabet sizes and state names. Only its behavior on self codes is needed. -/
def WritesSelf (W : Ordinary g q) (A O : Alphabet W) :=
  ∀ {h r} (P : Ordinary h r) (B : Alphabet P),
    Delivers W A (selfBits P B) W O (diagonalBits (selfBits P B))

private theorem negate_answer {b : Bool} {H : Prop} (spec : b=true ↔ ¬H) :
    (!b)=true ↔ H := by
  classical
  cases b <;> simp_all

/-- No ordinary binary-input machine decides the coded inverse image.
    This statement by itself concerns machine strings, not the table
    language on arbitrary multiplication arrays. -/
theorem no_diagonal_reader (D : Ordinary g r) (B : Alphabet D) (ans : Fin r → Bool) :
    ¬ (∀ x : List Bool, ∃ b, Answers D B ans x b ∧ (b=true ↔ HasBasis (diagonalTable x))) := by
  intro all
  apply no_self_decider D B (fun z => !(ans z))
  intro h s P A
  obtain ⟨b,⟨t,stop,outcome⟩,spec⟩ := all (selfBits P A)
  refine ⟨t,stop,?_⟩
  change (!(ans (follow D (inputConfig D B (selfBits P A)) t).state))=true ↔ SelfHalt P A
  rw [outcome]
  exact negate_answer (spec.trans (exact_self P A))

theorem no_table_decider_of_writer (W : Ordinary g q) (A O : Alphabet W) (writes : WritesSelf W A O)
    (D : Ordinary h r) (B : Alphabet D) (ans : Fin r → Bool) : ¬ DecidesTable D B ans := by
  intro reads
  let C := combined W O D B
  let I := inputs W A O D B
  apply no_self_decider C I (fun z => !(P455EffectiveChain.out q ans z))
  intro h' r' P X
  let x := selfBits P X
  obtain ⟨b,reading,spec⟩ := reads (diagonalTable x) (makeTable_laws _).1
  have run := answers_combined W A O D B ans (writes P X) reading
  obtain ⟨t,stop,outcome⟩ := run
  refine ⟨t,stop,?_⟩
  change (!(P455EffectiveChain.out q ans (follow (combined W O D B)
    (inputConfig (combined W O D B) (inputs W A O D B) (selfBits P X)) t).state))=true ↔ SelfHalt P X
  rw [outcome]
  exact negate_answer (spec.trans (exact_self P X))

/-- All that remains for the operational undecidability conclusion is
    existence of one finite writer for the indicated fixed transformation. -/
def WriterExists := ∃ (g q : Nat) (W : Ordinary g q) (A O : Alphabet W), WritesSelf W A O

def TableDeciderExists := ∃ (g q : Nat) (D : Ordinary g q) (B : Alphabet D) (ans : Fin q → Bool),
    DecidesTable D B ans

theorem operational_implication : WriterExists → ¬TableDeciderExists := by
  rintro ⟨_,_,W,A,O,writes⟩ ⟨_,_,D,B,ans,reads⟩
  exact no_table_decider_of_writer W A O writes D B ans reads

end P455Operational
