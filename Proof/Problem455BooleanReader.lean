import Problem455TableDecision
import Mathlib.Computability.Partrec

namespace P455BooleanReader
open P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine
open P455EffectiveChain P455RelabeledChain P455Table P455TableBits P455TableSemantics

def delta (q a : Fin 4) : Option (Ins (Fin 4) (Fin 4)) :=
  if q=0 then some ⟨1,a,.right⟩
  else if q=1 then some ⟨if a=3 then 3 else 2,a,.stay⟩ else none

def reader : Ordinary 4 4 where
  marker := 0
  blank := 1
  blank_ne := by decide
  start := 0
  delta := delta
  keeps := by
    intro s a i h
    unfold delta at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · contradiction
  leftSafe := by
    intro s i h
    unfold delta at h
    split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · contradiction

def bits : Alphabet reader where
  bit b := if b then 3 else 2
  ink b := by cases b <;> decide
  away b := by cases b <;> decide
  distinct := by decide

def ans (q : Fin 4) := decide (q=3)

theorem reads_bit (b : Bool) : Answers reader bits ans [b] b := by
  cases b <;> exact ⟨2,rfl,rfl⟩

/-- This bit-string decider is total, but only its answers on serialized
    finite semigroups are constrained. -/
def StandardDecider := ∃ f : List Bool → Bool, Computable f ∧
  ∀ T : Matrix, SemigroupTable T → (f (encode T)=true ↔ P455PureSemigroup.Basis T)

/-- A partial algorithm may be undefined or wrong off the promise. -/
def PromiseDecider := ∃ f : List Bool →. Bool, Partrec f ∧
  ∀ T : Matrix, SemigroupTable T → ∃ b ∈ f (encode T), (b=true ↔ P455PureSemigroup.Basis T)

end P455BooleanReader
