import Problem455PackedOutput





namespace P455TableDecision
open P455Table P455TableBits P455TableSemantics P455MachineCleanup P455EffectiveMachine
open P455EffectiveChain P455AnyPresentation P455Operational

def PureDecides (D : Ordinary g q) (B : Alphabet D) (ans : Fin q → Bool) :=
  ∀ T : Matrix, SemigroupTable T → ∃ b, Answers D B ans (encode T) b ∧
    (b=true ↔ P455PureSemigroup.Basis T)

def PureDeciderExists := ∃ (g q : Nat) (D : Ordinary g q) (B : Alphabet D) (ans : Fin q → Bool),
    PureDecides D B ans

def PresentationWriterExists := ∃ (g q : Nat) (W : Ordinary g q) (A O : Alphabet W),
    WritesPresentation W A O

theorem decider_iff (D : Ordinary g q) (B : Alphabet D) (ans : Fin q → Bool) :
    PureDecides D B ans ↔ DecidesTable D B ans := by
  constructor <;> intro h T valid <;> obtain ⟨b,read,ok⟩ := h T valid
  · exact ⟨b,read,ok.trans (P455PureSemigroup.basis_iff valid)⟩
  · exact ⟨b,read,ok.trans (P455PureSemigroup.basis_iff valid).symm⟩

/-- Conditional only on the existence of one finite physical writer, with
    any correct numbering of its output monoid. -/
theorem no_table_algorithm_of_presentation_writer : PresentationWriterExists → ¬PureDeciderExists := by
  rintro ⟨_,_,W,A,O,writes⟩ ⟨_,_,D,B,ans,pure⟩
  exact no_table_decider W A O writes D B ans ((decider_iff D B ans).mp pure)

/-- The unconditional bit-string reduction including validity of the finite
    output and its ordinary binary basis predicate, for every raw input. -/
theorem encoded_reduction (s : List Bool) :
    parse (P455RawReduction.blankBits s)=some (P455RawReduction.blankTable s) ∧
    SemigroupTable (P455RawReduction.blankTable s) ∧ HasUnit (P455RawReduction.blankTable s) ∧
    (P455PureSemigroup.Basis (P455RawReduction.blankTable s) ↔
      ¬P455RawReduction.realizesHalt (P455RawReduction.parseBlank s)) := by
  obtain ⟨parse,sem,unit,_⟩ := P455RawReduction.exact_blank s
  exact ⟨parse,sem,unit,P455PureSemigroup.raw_basis s⟩

end P455TableDecision
