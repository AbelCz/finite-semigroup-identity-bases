import Problem455WriterLocal

namespace P455WriterProgram
open P455EffectiveMachine P455MachineLocal P455MachineCleanup P455MachineTable P455PaddedTiles P455EffectiveWriter

def dimension (m : Raw) := g m*((q m+2)+1)
def neighbour (i : Nat) : Option Nat := if i=0 then none else some (i-1)
def line (m : Raw) (n l c : Nat) := (List.range (n+1)).map fun r => localValue m (neighbour l) c (neighbour r)
def slab (m : Raw) (n l : Nat) := (List.range n).flatMap (line m n l)
def grid (m : Raw) (n : Nat) := (List.range (n+1)).flatMap (slab m n)

def machineData (m : Raw) : P455WriterTiles.MachineData :=
  let n := dimension m
  (n,(List.range n).map (fun c => decide (c%(g m)=marker m)),blank m,g m*(start m+1)+marker m,
    g m*((q m+1)+1)+marker m,grid m n)

theorem get_slab (m : Raw) (n : Nat) (l : Nat) : (slab m n l).length=n*(n+1) := by
  simp [slab,line,List.length_flatMap,Function.comp_def,List.map_const']

theorem get_grid (m : Raw) (l c r : Nat) (hl : l < dimension m + 1) (hc : c < dimension m)
    (hr : r < dimension m+1) :
    (grid m (dimension m))[P455WriterTiles.address (dimension m) l c r]? = some (localValue m (neighbour l) c (neighbour r)) := by
  let n := dimension m
  change (grid m n)[(l*n+c)*(n+1)+r]?=_
  rw [show (l*n+c)*(n+1)+r=l*(n*(n+1))+(c*(n+1)+r) by rw [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]]
  have D : c*(n+1)+r<n*(n+1) := calc
    _ < c*(n+1)+(n+1) := Nat.add_lt_add_left hr _
    _ = (c+1)*(n+1) := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hc
  have hl' : l < (List.range (n+1)).length := by simpa only [List.length_range] using hl
  have hc' : c < (List.range n).length := by simpa only [List.length_range] using hc
  have hr' : r < (List.range (n+1)).length := by simpa only [List.length_range] using hr
  rw [grid,flat_lookup _ _ (get_slab m n) _ _ _ hl' D,List.getElem_range,slab,
      flat_lookup _ (n+1) (by intro; simp [line]) _ _ _ hc' hr,List.getElem_range,line,
      List.getElem?_map,List.getElem?_eq_getElem hr',List.getElem_range]; rfl

theorem letter_lt (x : Option (Fin n)) : letter x<n+1 := by
  cases x with
  | none => simp [letter]
  | some a => simp [letter]

theorem neighbour_letter (x : Option (Fin n)) : neighbour (letter x)=x.map Fin.val := by
  cases x <;> simp [letter,neighbour]

theorem machineData_models (M : Ordinary ng nq) :
    P455WriterTiles.Models (machineData (data M)) (compile (normalized M)) := by
  constructor
  · rfl
  · intro c
    simp only [P455WriterTiles.marker,machineData,List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simpa only [List.length_range] using c.isLt),List.getElem_range]
    change decide (c.val%ng=M.marker.val)=decide ((dec (normalized M) c).sym=M.marker)
    simp only [Fin.ext_iff]; rfl
  · intro b; cases b <;> simp [machineData,P455WriterTiles.initial,data,g,start,marker,blank,compile,enc,headIndex,normalized,old]
  · rfl
  · intro l c r
    change (grid (data M) (dimension (data M)))[P455WriterTiles.address (dimension (data M)) (letter l) c.val (letter r)]?.getD none=_
    rw [get_grid _ _ _ _ (letter_lt l) c.isLt (letter_lt r),neighbour_letter,neighbour_letter]
    exact localValue_spec M l c r

def fromBits (w : List Bool) := machineData (blankRaw w)

theorem fromBits_self (M : Ordinary ng nq) (A : Alphabet M) :
    P455WriterTiles.Models (fromBits (selfBits M A)) (compile (normalized (diagonalInput M A).2)) := by
  unfold fromBits; rw [blank_self]; exact machineData_models _

end P455WriterProgram
