import Problem455OriginalWalk
import Problem455TerminalTransfer

/- Endpoint obstruction in the actual original source word after all gap
   variables of the smaller rule have been expanded. -/
namespace P455OriginalTerminal
open Problem455.Slots P455Witness P455Retained P455TerminalTransfer

/-- Keep the identical five selected output names and the identical five
    donor variables when an overflow obstruction is taken back to the
    original word. Deficiency already gives a contradiction. -/
theorem expand {r : Nat} {v : Word} {e h : Nat → Word} {kept : Nat → Prop} {x i : Nat}
    (exp : Expansion v e kept) (hr : 1 < r) (kx : kept x)
    (d : SlotDefect) (small : Lift v h x i r d) :
    Lift (v.flatMap e) h x i r d := by
  cases d with
  | deficient a => exact small
  | overflow xs =>
    obtain ⟨assign,len,nd,valid⟩ := small
    refine ⟨assign,len,nd,?_⟩
    intro a ha
    obtain ⟨obs,ha',cnt⟩ := valid a ha
    have used : assign a ∈ v := List.count_pos_iff.mp (by omega)
    have keep : kept (assign a) := by
      apply Classical.byContradiction
      intro gap
      have := (exp.gaps (assign a) used gap).1
      omega
    have hx : assign a ∈ e (assign a) := by rw [exp.literal _ used keep]; simp
    exact ⟨exp.in_original_slot x i _ kx obs _ hx,ha',(exp.count_eq _ (fun _ h => h) _ keep).trans cnt⟩

end P455OriginalTerminal
