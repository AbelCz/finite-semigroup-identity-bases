import Problem455Packed
import Problem455AnyPresentation
import Problem455PureSemigroup

/- Connect the numeric product and raw class tables to the relaxed writer
   premise: this output may have an entirely different element numbering. -/
namespace P455PackedOutput
open P455Table P455TableBits P455NumericProduct P455TableSemantics P455EffectiveMachine
open P455MachineCleanup P455MachineTable P455EffectiveWriter P455MachineParse
open P455EffectiveChain P455AnyPresentation

def alternative (M : Ordinary g q) := P455Packed.serialize (P455Packed.prepared (compile (normalized M)))

theorem alternative_represents (M : Ordinary g q) :
    Represents (alternative M) (P455MachineReduction.model M) :=
  P455Packed.serialize_represents (compile (normalized M))

def selfTable (input : List Bool) : Matrix :=
  match blankSource input with
  | none => [[0]]
  | some ⟨_,_,M⟩ => alternative M

def selfOutput (input : List Bool) := encode (selfTable input)

theorem on_self (M : Ordinary g q) (B : Alphabet M) :
    selfTable (selfBits M B)=alternative (diagonalInput M B).2 := by
  simp [selfTable,blankSource_self]

theorem pure_basis_on_self (M : Ordinary g q) (B : Alphabet M) :
    P455PureSemigroup.Basis (selfTable (selfBits M B)) ↔ ¬SelfHalt M B := by
  rw [on_self]
  obtain ⟨X,table,⟨p⟩⟩ := alternative_represents (diagonalInput M B).2
  rw [table]
  exact (P455PureSemigroup.basis_iff (output_laws p).1).trans
    ((P455TableSemantics.basis_iff p).trans (diagonal_basis M B))

theorem delivers_presentation (W : Ordinary g q) (A O : Alphabet W)
    (realizes : ∀ x, Delivers W A x W O (selfOutput x)) : WritesPresentation W A O := by
  intro k s P B
  obtain ⟨X,table,yes⟩ := alternative_represents (diagonalInput P B).2
  refine ⟨X,yes,?_⟩
  simpa only [selfOutput,on_self,table] using realizes (selfBits P B)

theorem no_decider_if_realized (W : Ordinary g q) (A O : Alphabet W)
    (realizes : ∀ x, Delivers W A x W O (selfOutput x)) :
    ¬ P455Operational.TableDeciderExists := by
  rintro ⟨_,_,D,B,ans,reads⟩
  exact no_table_decider W A O (delivers_presentation W A O realizes) D B ans reads

end P455PackedOutput
