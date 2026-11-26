import Mathlib.Computability.PostTuringMachine
import Problem455WriterPhysical

/- The left physical marker stores no data. The two virtual cells above
   it stay in finite control. At position p>0 the left and right tracks
   carry virtual positions -p and p+1, respectively. -/
namespace P455FoldWorld
open Turing P455MachineLocal P455MachineTable

def coord : Bool → Nat → Int
  | false,p => -(p : Int)
  | true,p => (p : Int)+1

def motion (s : Bool) (atMark : Bool) (dir : Turing.Dir) : Bool × Direction :=
  match s,dir with
  | false,.left => (false,.right)
  | false,.right => if atMark then (true,.stay) else (false,.left)
  | true,.right => (true,.right)
  | true,.left => if atMark then (false,.stay) else (true,.left)

theorem moves (s p d) :
    let m := motion s (decide (p=0)) d
    coord m.1 (dest m.2 p)=coord s p + (if d=.right then 1 else -1) := by
  cases s <;> cases d <;> cases p <;> simp [coord,motion,dest]
  omega

structure World (Γ Q : Type) where
  store : Int→Γ
  side : Bool
  radius : Nat
  state : Q

def pos (w : World Γ Q) := coord w.side w.radius

def act (w : World Γ Q) (z : Q) (i : TM0.Stmt Γ) : World Γ Q :=
  match i with
  | .move d =>
    let m := motion w.side (decide (w.radius=0)) d
    ⟨w.store,m.1,dest m.2 w.radius,z⟩
  | .write b => ⟨Function.update w.store (pos w) b,w.side,w.radius,z⟩

def packed (f : Int→Γ) (p : Nat) := (f (coord false p),f (coord true p))
def choose (side : Bool) (pair : Γ×Γ) := if side then pair.2 else pair.1
def put (side : Bool) (pair : Γ×Γ) (a : Γ) := if side then (pair.1,a) else (a,pair.2)

theorem choose_packed (s : Bool) (f : Int→Γ) (p) : choose s (packed f p)=f (coord s p) := by
  cases s <;> rfl

theorem put_packed (s : Bool) (f : Int→Γ) (p : Nat) (a) (j : Nat) :
    packed (Function.update f (coord s p) a) j=
      if j=p then put s (packed f p) a else packed f j := by
  by_cases e : j=p
  · subst j; cases s <;> simp [coord,put,packed,Function.update_apply] <;> intro h <;> omega
  · have same1 : - (j : Int) ≠ -(p : Int) := by omega
    have same2 : (j : Int)+1 ≠ (p : Int)+1 := by omega
    have cross1 : -(j : Int) ≠ (p : Int)+1 := by omega
    have cross2 : (j : Int)+1 ≠ -(p : Int) := by omega
    cases s <;> simp [coord,put,packed,e,Function.update_apply,same1,same2,cross1,cross2]

/-- The absolute tape retains the origin, which a bare bilateral configuration forgets. -/
def Describes [Inhabited Γ] (w : World Γ Q) (c : TM0.Cfg Γ Q) :=
  w.state=c.q ∧ ∀ i : Int, c.Tape.nth i=w.store (pos w+i)

theorem act_describes [Inhabited Γ] {w : World Γ Q} {c : TM0.Cfg Γ Q} (h : Describes w c) (z : Q) (i : TM0.Stmt Γ) :
    Describes (act w z i) ⟨z,match i with | .move d => c.Tape.move d | .write b => c.Tape.write b⟩ := by
  cases i with
  | write b =>
    refine ⟨rfl,fun j => ?_⟩
    simp only [Tape.write_nth,act,pos,Function.update_apply]
    by_cases e : j=0
    · simp [e]
    · have ne : coord w.side w.radius+j≠coord w.side w.radius := by omega
      simpa only [if_neg e,if_neg ne,pos] using h.2 j
  | move d =>
    refine ⟨rfl,fun j => ?_⟩
    have mv := moves w.side w.radius d
    cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth,act,pos] at *
    · rw [h.2]; congr 1; dsimp [pos] at *; omega
    · rw [h.2]; congr 1; dsimp [pos] at *; omega

end P455FoldWorld
