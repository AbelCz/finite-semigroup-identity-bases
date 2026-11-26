import Problem455FoldWorld
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace P455FoldMachine
open Turing P455MachineLocal P455MachineTable P455MachineCleanup P455FoldWorld

abbrev Sym (Γ : Type) := Option (Γ×Γ)
abbrev Ctrl (Γ Q : Type) := Q×Bool×(Γ×Γ)
abbrev Table (Γ Q : Type) := Q → Γ → Option (Q×TM0.Stmt Γ)

def emit (s : Ctrl Γ Q) (a : Sym Γ) (z : Q) (i : TM0.Stmt Γ) : Ins (Sym Γ) (Ctrl Γ Q) :=
  match i with
  | .move d =>
    let m := motion s.2.1 a.isNone d
    ⟨(z,m.1,s.2.2),a,m.2⟩
  | .write b =>
    let h := if a.isNone then put s.2.1 s.2.2 b else s.2.2
    ⟨(z,s.2.1,h),a.map (fun v => put s.2.1 v b),.stay⟩

def table (M : Table Γ Q) (s : Ctrl Γ Q) (a : Sym Γ) :=
  (M s.1 (choose s.2.1 (a.getD s.2.2))).map (fun (z,i) => emit s a z i)

theorem mark (s : Ctrl Γ Q) (a : Sym Γ) (z i) :
    (emit s a z i).symbol=none ↔ a=none := by
  cases i <;> cases a <;> simp [emit]

theorem safe (s : Ctrl Γ Q) (z i) : (emit s none z i).dir≠.left := by
  cases s with | mk q p =>
    obtain ⟨b,h⟩ := p
    cases i with
    | write => exact Direction.noConfusion
    | move d => cases d <;> cases b <;> exact Direction.noConfusion

variable [Inhabited Γ]
variable (aCode : Sym Γ ≃ Fin g) (sCode : Ctrl Γ Q ≃ Fin r)

def number (i : Ins (Sym Γ) (Ctrl Γ Q)) : Ins (Fin g) (Fin r) :=
  ⟨sCode i.state,aCode i.symbol,i.dir⟩

def machine (M : Table Γ Q) (start : Q) (header : Γ×Γ) : Ordinary g r where
  marker := aCode none
  blank := aCode (some (default,default))
  blank_ne := fun h => Option.noConfusion (aCode.injective h)
  start := sCode (start,false,header)
  delta z a := (table M (sCode.symm z) (aCode.symm a)).map (number aCode sCode)
  keeps := by
    intro z a i e
    rcases Option.map_eq_some_iff.mp e with ⟨j,h,rfl⟩
    rcases Option.map_eq_some_iff.mp h with ⟨⟨u,cmd⟩,_,rfl⟩
    change aCode _=aCode none ↔ a=aCode none
    rw [aCode.injective.eq_iff,mark,Equiv.symm_apply_eq]
  leftSafe := by
    intro z i e
    simp only [Equiv.symm_apply_apply] at e
    rcases Option.map_eq_some_iff.mp e with ⟨j,h,rfl⟩
    rcases Option.map_eq_some_iff.mp h with ⟨⟨u,cmd⟩,_,rfl⟩
    exact safe (sCode.symm z) u cmd

def cell (f : Int→Γ) (p : Nat) : Sym Γ := if p=0 then none else some (packed f p)
def control (w : World Γ Q) : Ctrl Γ Q := (w.state,w.side,packed w.store 0)
def physical (w : World Γ Q) : Config g r :=
  ⟨fun j => aCode (cell w.store j),w.radius,sCode (control w)⟩

omit [Inhabited Γ] in
theorem scanned (w : World Γ Q) :
    choose w.side ((cell w.store w.radius).getD (packed w.store 0))=w.store (pos w) := by
  cases h : w.radius with
  | zero => simp [cell,choose_packed,pos,h]
  | succ p => simp [cell,choose_packed,pos,h]

theorem translated (M : Table Γ Q) (start : Q) (hdr : Γ×Γ) (w : World Γ Q) :
    instruction (machine aCode sCode M start hdr) (physical aCode sCode w)=
      (M w.state (w.store (pos w))).map (fun (z,i) =>
        number aCode sCode (emit (control w) (cell w.store w.radius) z i)) := by
  simp only [instruction,machine,physical,Equiv.symm_apply_apply,table,control,scanned,Option.map_map]
  rfl

theorem act_step (M : Table Γ Q) (start : Q) (hdr : Γ×Γ) (w : World Γ Q) (z i)
    (e : M w.state (w.store (pos w))=some (z,i)) :
    once (machine aCode sCode M start hdr) (physical aCode sCode w)=
      physical aCode sCode (act w z i) := by
  rw [once,translated,e]
  have noneEq : (cell w.store w.radius).isNone=decide (w.radius=0) := by
    cases w.radius <;> simp [cell]
  cases i with
  | move d =>
    simp [emit,number,physical,control,act,P455EffectiveMachine.write_same,noneEq]
  | write b =>
    have pp : pos w=coord w.side w.radius := rfl
    have head : packed (Function.update w.store (pos w) b) 0=
        (if (cell w.store w.radius).isNone then put w.side (packed w.store 0) b else packed w.store 0) := by
      rw [pp,put_packed,noneEq]
      by_cases h : w.radius=0 <;> simp [h,eq_comm]
    have tp : writeAt (fun j=>aCode (cell w.store j)) w.radius
          (aCode ((cell w.store w.radius).map (fun v => put w.side v b))) =
        fun j => aCode (cell (Function.update w.store (pos w) b) j) := by
      funext j
      by_cases e : j=w.radius
      · subst j; by_cases h : w.radius=0 <;> simp [writeAt,cell,h,pp,put_packed]
      · by_cases h : j=0 <;> simp [writeAt,e,cell,h,pp,put_packed]
        omega
    change (⟨_,_,_⟩ : Config g r) = ⟨_,_,_⟩
    simp only [emit,number,physical,control,act,dest,head] at *
    congr 1

end P455FoldMachine
