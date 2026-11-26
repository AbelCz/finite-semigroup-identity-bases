import Problem455FiniteBasis
import Problem455PrefixChart
import Problem455CellClassHalting
import Problem455PaddedAssembly




namespace P455Global
open P455PaddedTiles P455FiniteBasis P455FirstRewrite

abbrev monoid {n} (M : MachineTable n) := P455FullSingleton.model (widthCode n+16) (allowed M) (system n)
def Accepts {n} (M : MachineTable n) := ∃ w s, Nonempty (AcceptingTrace M w s)
def HasBasis {S : Type} (M : Model S) := ∃ rules, Basis M rules
def Stationary {n} (M : MachineTable n) := ∀ {w s}, (T : AcceptingTrace M w s) → ∀ x, x<w →
    M.next (leftAt (T.rows s) x) (T.rows s x) (rightAt (T.rows s) w x)=some (T.rows s x)

theorem finite_of_no_trace {n} (M : MachineTable n) (negative : ¬Accepts M) :
    HasBasis (monoid M) := by
  apply finite_of_uniform _ (P455FiniteModel.fixed_product ..)
    (max (P455MarkedRank.bound (widthCode n+16)) (2*(widthCode n+16+2)+1))
  intro u v _ _ valid
  have alt := P455ChartBuild.arbitrary_schedule_or_rectangle (by omega : 0<widthCode n+16) (system_laws n) valid
  apply alt.resolve_right
  rintro ⟨R⟩
  exact negative ⟨R.width+1,R.height,⟨assembly_trace R⟩⟩

theorem no_basis_of_trace {n} (M : MachineTable n) (stationary : Stationary M)
    (pos : Accepts M) : ¬HasBasis (monoid M) := by
  obtain ⟨w,s,⟨t⟩⟩ := pos
  let run : Run M w s := ⟨t.positive,t.rows,t.start,t.marks,t.steps,t.accept,stationary t⟩
  rintro ⟨rules,ok,complete⟩
  obtain ⟨u,v,un,vn,idn,fail⟩ := P455CellClassHalting.no_basis_of_run run rules
    (fun a b m => (ok a b m).2.2)
  exact fail (complete u v un vn idn)

/-- The complete basis equivalence for a finite local transition table.
    The only machine normal-form property is stuttering of a reachable
    accepting configuration. The two rank implications are proved above. -/
theorem table_equivalence {n} (M : MachineTable n) (stationary : Stationary M) :
    HasBasis (monoid M) ↔ ¬Accepts M :=
  ⟨fun base accept => no_basis_of_trace M stationary accept base,finite_of_no_trace M⟩

end P455Global
