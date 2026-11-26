import Problem455MathlibFinite
import Problem455FoldDelivery



namespace P455ComputableWriter
open Turing P455MachineCleanup P455EffectiveMachine P455EffectiveChain
open P455MathlibTM P455MathlibCode P455FoldInput

def wire : Wire Track where
  first := cell true .cons
  second := cell false .bit1
  letter b := cell false (P455MathlibCode.letter b)
  ink b eq := by
    have h := congrArg (fun (a : Track) => a.2 Turing.PartrecToTM2.K'.main) eq
    simp [cell,TM2to1.Γ'.inhabited] at h
  distinct eq := by
    have h := congrArg (fun (a : Track) => a.2 Turing.PartrecToTM2.K'.main) eq
    simp [cell,P455MathlibCode.letter] at h
  flag := Prod.fst
  flags := ⟨rfl,rfl,rfl,fun _ => rfl⟩

theorem realizes {f : List Bool → List Bool} (hf : Computable f) :
    ∃ (g r : Nat) (W : Ordinary g r) (A : Alphabet W), ∀ x, Delivers W A x W A (f x) := by
  obtain ⟨Q,fs,ih,M,guard,run⟩ := P455MathlibFinite.finite_machine hf
  exact P455FoldDelivery.exact_delivery M wire guard f run

end P455ComputableWriter
