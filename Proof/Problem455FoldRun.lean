import Problem455FoldMachine

namespace P455FoldRun
open Turing P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine
open P455WriterSweep P455FoldWorld P455FoldMachine

def Marked (flag : Γ → Bool) (w : World Γ Q) := ∀ p, flag (w.store p)=true ↔ p=0

theorem survives (flag : Γ→Bool) (M : Table Γ Q) (w : World Γ Q)
    (guard : ∀ q a z b, M q a=some (z,.write b) → flag b=flag a)
    {z i} (step : M w.state (w.store (pos w))=some (z,i)) (h : Marked flag w) :
    Marked flag (act w z i) := by
  cases i with
  | move d => exact h
  | write b =>
    intro p
    change flag (Function.update w.store (pos w) b p)=true ↔ p=0
    by_cases eq : p=pos w
    · subst p; simpa [guard _ _ _ _ step] using h (pos w)
    · simpa [Function.update_of_ne eq] using h p

variable [Inhabited Γ] [Inhabited Q]
variable (aCode : Sym Γ ≃ Fin g) (sCode : Ctrl Γ Q ≃ Fin r)

theorem lift_reaches (M : TM0.Machine Γ Q) (header : Γ×Γ) (flag : Γ→Bool)
    (guard : ∀ q a z b, M q a=some (z,.write b) → flag b=flag a)
    {u v : TM0.Cfg Γ Q} (path : Turing.Reaches (TM0.step M) u v)
    (w₀ : World Γ Q) (d₀ : Describes w₀ u) (m₀ : Marked flag w₀) :
    ∃ w, Describes w v ∧ Marked flag w ∧
      reach (machine aCode sCode M default header)
        (physical aCode sCode w₀) (physical aCode sCode w) := by
  induction path with
  | refl => exact ⟨_,d₀,m₀,0,rfl⟩
  | @tail a b _ step ih =>
    obtain ⟨w,d,m,h⟩ := ih
    obtain ⟨q,T⟩ := a
    rcases Option.map_eq_some_iff.mp step with ⟨⟨z,i⟩,e,rfl⟩
    change M q T.head=some (z,i) at e
    have scan : T.head=w.store (pos w) := by simpa using d.2 0
    have exec : M w.state (w.store (pos w))=some (z,i) := by rw [d.1,←scan]; exact e
    exact ⟨_,act_describes d z i,survives flag M w guard exec m,
      P455WriterSweep.trans h (single (act_step aCode sCode M default header w z i exec))⟩

end P455FoldRun
