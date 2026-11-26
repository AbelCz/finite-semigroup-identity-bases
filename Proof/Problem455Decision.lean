import Problem455Global
import Problem455MachineReduction




namespace P455Decision
open P455MachineCleanup P455MachineTable

theorem ordinary_equivalence {g q} (M : Ordinary g q) :
    P455Global.HasBasis (P455MachineReduction.model M) ↔ ¬ ∃ t, stopped M t := by
  have table := P455Global.table_equivalence (compile (normalized M))
    (fun T => trace_stutters (normalized M) T)
  exact table.trans (not_congr (halts_iff_trace M).symm)

end P455Decision
