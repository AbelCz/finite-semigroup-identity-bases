import Problem455PaddedMatchings
import Problem455PaddedSlots



namespace P455PaddedWord
open P455PaddedPorts P455PaddedMatchings P455RectangleRank
abbrev W := List Nat

def matching (h w : Nat) : Nat → List Block
  | 0 => horizontal h w false
  | 1 => horizontal h w true
  | 2 => vertical h w false
  | 3 => vertical h w true
  | _+4 => wrap (w*h)

def portChunks (h w n : Nat) :=
  (List.range n).flatMap fun k => letters (matching h w k)

def tagPhase (t : Nat) (tag : Nat → List Bool) (k : Nat) :=
  (List.range t).flatMap (mutableCell fun i => (tag i)[k]?.getD false)

def columnCells (h w : Nat) := (List.range h).flatMap fun y => (List.range w).map (idAt w y)

def suffix (h w k : Nat) (tag : Nat → List Bool) : W :=
  (List.range k).flatMap (tagPhase (w*h) tag) ++ (columnCells h w).flatMap roles

def middle (h w k : Nat) (tag : Nat → List Bool) : W := portChunks h w 5 ++ suffix h w k tag
def tail (t : Nat) : W := (List.range t).flatMap (mutableCell (constant false))

theorem matching_unique {h w : Nat} (size : 1<w*h) (k : Nat) :
    ((matching h w k).flatMap cells).Nodup := by
  cases k with
  | zero => exact horizontal_unique .. 
  | succ k => cases k with
    | zero => exact horizontal_unique ..
    | succ k => cases k with
      | zero => exact vertical_unique ..
      | succ k => cases k with
        | zero => exact vertical_unique ..
        | succ k => exact wrap_unique size

theorem matching_cells {h w : Nat} (size : 1<w*h) (k i : Nat) :
    i∈(matching h w k).flatMap cells ↔ i<w*h := by
  cases k with
  | zero => exact horizontal_cells ..
  | succ k => cases k with
    | zero => exact horizontal_cells ..
    | succ k => cases k with
      | zero => exact vertical_cells ..
      | succ k => cases k with
        | zero => exact vertical_cells ..
        | succ k => exact wrap_cells size i

theorem columns_eq (h w : Nat) :
    columnCells h w=(horizontal h w false).flatMap cells := by
  change _ = (lines h w false (idAt w)).flatMap cells
  simp [columnCells,lines,List.flatMap_assoc,line_cells]

theorem columns_unique (h w : Nat) : (columnCells h w).Nodup := by
  rw [columns_eq]; exact horizontal_unique ..

theorem columns_cells (h w i : Nat) : i∈columnCells h w ↔ i<w*h := by
  rw [columns_eq]; exact horizontal_cells ..

end P455PaddedWord
