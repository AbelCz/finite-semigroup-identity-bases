import Problem455FoldRun
import Problem455FoldInput

namespace P455FoldDelivery
open Turing P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine P455EffectiveChain
open P455FoldWorld P455FoldMachine P455FoldRun P455FoldInput

/-- A finite supported bilateral writer whose bottom flag is preserved becomes
    an ordinary finite one-sided writer with the exact physical bit-list convention. -/
theorem exact_delivery {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [Fintype Γ] [Fintype Q]
    (M : TM0.Machine Γ Q) (C : Wire Γ)
    (guard : ∀ q a z b, M q a=some (z,.write b) → C.flag b=C.flag a)
    (f : List Bool → List Bool) (run : ∀ x, ∃ q, (⟨q,Tape.mk₁ (stream C (f x))⟩ : TM0.Cfg Γ Q) ∈
      Turing.eval (TM0.step M) (TM0.init (stream C x))) :
    ∃ (g r : Nat) (W : Ordinary g r) (A : Alphabet W), ∀ x, Delivers W A x W A (f x) := by
  classical
  let ac := Fintype.equivFin (Sym Γ)
  let sc := Fintype.equivFin (Ctrl Γ Q)
  let W := machine ac sc M default (C.first,C.second)
  let A := inputAlpha ac sc M C
  refine ⟨_,_,W,A,?_⟩
  intro x
  obtain ⟨q,last⟩ := run x
  obtain ⟨steps,halt⟩ := Turing.mem_eval.mp last
  obtain ⟨w,descr,mark,t,arrive⟩ := lift_reaches ac sc M (C.first,C.second) C.flag guard steps
    (initWorld C x) (describes_init C x) (marked C x)
  rw [initial ac sc M C] at arrive
  have eq (i : Int) : layout C (f x) i=w.store (pos w+i) :=
    (nth_stream C (f x) i).symm.trans (descr.2 i)
  have head : pos w=0 := by
    apply (mark (pos w)).mp
    have he : C.first=w.store (pos w) := by simpa [layout] using eq 0
    rw [←he]; exact C.flags.1
  have rad : w.radius=0 := by
    unfold pos at head
    cases e : w.side <;> simp [e,coord] at head <;> omega
  have storeEq : w.store=layout C (f x) := by
    funext i; simpa [head] using (eq i).symm
  have hM : M q (Tape.mk₁ (stream C (f x))).head=none := by
    change (M q _).map _=none at halt
    exact Option.map_eq_none'.mp halt
  have scan := descr.2 0
  simp only [Tape.nth_zero,Int.add_zero] at scan
  have ended : M w.state (w.store (pos w))=none := by rw [descr.1,←scan]; exact hM
  refine ⟨t,?_⟩
  change follow W (inputConfig W A x) t=physical ac sc w at arrive
  dsimp only
  rw [arrive]
  refine ⟨?_,rad,?_⟩
  · change instruction (machine ac sc M default (C.first,C.second)) (physical ac sc w)=none
    rw [translated,ended]; rfl
  · change (fun j => ac (cell w.store j))=inputTape _ _ _
    rw [storeEq]; exact cell_layout ac sc M C (f x)

end P455FoldDelivery
