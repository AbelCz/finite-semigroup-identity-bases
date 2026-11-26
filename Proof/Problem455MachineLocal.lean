import Std




namespace P455MachineLocal

inductive Direction | left | stay | right
  deriving DecidableEq

structure Ins (A Q : Type) where
  state : Q
  symbol : A
  dir : Direction
  deriving DecidableEq

structure Cell (A Q : Type) where
  sym : A
  head : Option Q
  deriving DecidableEq

def action (d : Q→A→Ins A Q) (c : Cell A Q) := c.head.map fun q=>d q c.sym

def sends (i : Ins A Q) (toward : Direction) : Option Q := if i.dir=toward then some i.state else none

def update (d : Q→A→Ins A Q) (l : Option (Cell A Q)) (c : Cell A Q) (r : Option (Cell A Q)) :
    Option (Cell A Q) :=
  match l.bind (action d), action d c, r.bind (action d) with
  | none,none,none => some ⟨c.sym,none⟩
  | some a,none,none => some ⟨c.sym,sends a .right⟩
  | none,none,some a => some ⟨c.sym,sends a .left⟩
  | none,some a,none =>
    if (a.dir=.left ∧ l.isNone=true) ∨ (a.dir=.right ∧ r.isNone=true) then none
    else some ⟨a.symbol,sends a .stay⟩
  | _,_,_ => none

def atCell (tape : Nat→A) (p : Nat) (q : Q) (x : Nat) : Cell A Q :=
  ⟨tape x,if x=p then some q else none⟩

def leftOf (row : Nat→α) (x : Nat) := if x=0 then none else some (row (x-1))
def rightOf (row : Nat→α) (w x : Nat) := if x+1=w then none else some (row (x+1))

def exits (dir : Direction) (w p : Nat) : Prop :=
  (dir=.left ∧ p=0) ∨ (dir=.right ∧ p+1=w)

instance (dir : Direction) (w p : Nat) : Decidable (exits dir w p) := by unfold exits; infer_instance

def dest (dir : Direction) (p : Nat) : Nat :=
  match dir with | .left => p-1 | .stay => p | .right => p+1

def writeAt (tape : Nat→A) (p : Nat) (a : A) (x : Nat) := if x=p then a else tape x

private theorem center_action (d : Q→A→Ins A Q) (tape : Nat→A) (p : Nat) (q : Q) (x : Nat) :
    action d (atCell tape p q x) = if x=p then some (d q (tape p)) else none := by
  by_cases e : x=p <;> simp [action,atCell,e]

private theorem left_action (d : Q→A→Ins A Q) (tape : Nat→A) (p : Nat) (q : Q) (x : Nat) :
    (leftOf (atCell tape p q) x).bind (action d) =
      if x=p+1 then some (d q (tape p)) else none := by
  by_cases e : x=0
  · subst x; simp [leftOf]
  · have eq : (x-1=p) ↔ x=p+1 := by omega
    simp [leftOf,e,center_action,eq]

private theorem right_action (d : Q→A→Ins A Q) (tape : Nat→A) (p w : Nat) (hp : p<w) (q : Q) (x : Nat) :
    (rightOf (atCell tape p q) w x).bind (action d) =
      if x+1=p then some (d q (tape p)) else none := by
  by_cases e : x+1=w
  · simp [rightOf,e,show w≠p by omega]
  · simp [rightOf,e,center_action]

private theorem left_boundary (row : Nat→α) (x : Nat) : (leftOf row x).isNone=true ↔ x=0 := by
  by_cases e : x=0 <;> simp [leftOf,e]

private theorem right_boundary (row : Nat→α) (w x : Nat) : (rightOf row w x).isNone=true ↔ x+1=w := by
  by_cases e : x+1=w <;> simp [rightOf,e]

/-- When an entire bounded row has one head, the local rule at that head
is defined precisely when the physical move remains in the interval. -/
theorem defined_at_head (d : Q→A→Ins A Q) (tape : Nat→A) (w p : Nat) (q : Q) (hp : p<w) :
    update d (leftOf (atCell tape p q) p) (atCell tape p q p) (rightOf (atCell tape p q) w p)=none
      ↔ exits (d q (tape p)).dir w p := by
  unfold update
  rw [left_action,right_action _ _ _ _ hp,center_action]
  simp only [if_neg (show p≠p+1 by omega),if_neg (show p+1≠p by omega),if_pos rfl]
  simp only [left_boundary,right_boundary]
  change (if exits (d q (tape p)).dir w p then _ else _) = none ↔ _
  by_cases e : exits (d q (tape p)).dir w p <;> simp [e]

/-- Every cell of a nonescaping row has its exact next physical value. -/
theorem local_step (d : Q→A→Ins A Q) (tape : Nat→A) (w p : Nat) (q : Q)
    (hp : p<w) (safe : ¬exits (d q (tape p)).dir w p) (x : Nat) (hx : x<w) :
    let i := d q (tape p)
    update d (leftOf (atCell tape p q) x) (atCell tape p q x) (rightOf (atCell tape p q) w x)=
      some (atCell (writeAt tape p i.symbol) (dest i.dir p) i.state x) := by
  dsimp only
  unfold update
  rw [left_action,right_action _ _ _ _ hp,center_action]
  by_cases cp : x=p
  · subst x
    simp only [if_neg (show p≠p+1 by omega),if_neg (show p+1≠p by omega),if_pos rfl]
    change (if ((d q (tape p)).dir=.left ∧ (leftOf (atCell tape p q) p).isNone=true) ∨
      ((d q (tape p)).dir=.right ∧ (rightOf (atCell tape p q) w p).isNone=true)
      then none else some (Cell.mk (d q (tape p)).symbol (sends (d q (tape p)) .stay))) = _
    simp only [left_boundary,right_boundary]
    change (if exits (d q (tape p)).dir w p then _ else _) = _
    rw [if_neg safe]
    cases dir : (d q (tape p)).dir with
    | left =>
      have pos : p≠0 := by simpa [exits,dir] using safe
      simp [sends,dir,atCell,writeAt,dest,show p≠p-1 by omega]
    | stay => simp [sends,dir,atCell,writeAt,dest]
    | right => simp [sends,dir,atCell,writeAt,dest]
  · by_cases l : x=p+1
    · have r : x+1≠p := by omega
      simp only [if_pos l,if_neg cp,if_neg r]
      cases dir : (d q (tape p)).dir <;>
        simp [sends,dir,atCell,writeAt,dest,cp,show x≠p-1 by omega,l,show p+1≠p-1 by omega]
    · by_cases r : x+1=p
      · simp only [if_neg l,if_neg cp,if_pos r]
        cases dir : (d q (tape p)).dir <;>
          simp [sends,dir,atCell,writeAt,dest,cp,l,show x=p-1 by omega,show p-1≠p by omega,show p-1≠p+1 by omega]
      · simp only [if_neg l,if_neg cp,if_neg r]
        cases dir : (d q (tape p)).dir <;>
          simp [sends,dir,atCell,writeAt,dest,cp,l,show x≠p-1 by omega]

end P455MachineLocal
