import Problem455MachineCleanup
import Problem455CellClassHalting
import Problem455PaddedAssembly



namespace P455MachineReduction
open P455MachineCleanup P455MachineTable P455PaddedTiles

def model (M : Ordinary g q) :=
  P455FullSingleton.model (widthCode (g*(q+2+1))+16) (allowed (compile (normalized M))) (system (g*(q+2+1)))

theorem no_basis_of_halt (M : Ordinary g q) (halt : ∃ t,stopped M t)
    (basis : List (List Nat × List Nat))
    (sound : ∀ u v,(u,v)∈basis → (model M).Valid u v) :
    ∃ U V,U ≠ [] ∧ V ≠ [] ∧ (model M).Valid U V ∧
      ¬ P455FirstRewrite.Derives (fun u v=>(u,v)∈basis) U V := by
  obtain ⟨w,s,⟨T⟩⟩ := (halts_iff_trace M).mp halt
  let R : Run (compile (normalized M)) w s :=
    ⟨T.positive,T.rows,T.start,T.marks,T.steps,T.accept,trace_stutters (normalized M) T⟩
  exact P455CellClassHalting.no_basis_of_run R basis sound

theorem no_assembly_of_nonhalt (M : Ordinary g q) (nonhalt : ¬∃ t,stopped M t) :
    ¬Nonempty (P455GridAssembly.Rectangle (allowed (compile (normalized M))) (system (g*(q+2+1)))) := by
  rintro ⟨R⟩
  exact nonhalt ((halts_iff_trace M).mpr ⟨R.width+1,R.height,⟨assembly_trace R⟩⟩)

end P455MachineReduction
