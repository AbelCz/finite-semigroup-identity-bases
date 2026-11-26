import Problem455Packed

/- Numerical data consumed by the tile catalogue. The local transition list is
   row-major in (left neighbour, centre symbol, right neighbour) order. -/
namespace P455WriterTiles
open P455PaddedTiles

abbrev MachineData := Nat × List Bool × Nat × Nat × Nat × List (Option Nat)

def size (D : MachineData) := D.1
def marker (D : MachineData) (c : Nat) := D.2.1[c]?.getD false
def initial (D : MachineData) (left : Bool) := if left then D.2.2.2.1 else D.2.2.1
def accept (D : MachineData) := D.2.2.2.2.1
def address (n l c r : Nat) := (l*n+c)*(n+1)+r
def update (D : MachineData) (l c r : Nat) : Option Nat :=
  D.2.2.2.2.2[address D.1 l c r]?.getD none

structure Models (D : MachineData) {n} (M : MachineTable n) : Prop where
  dim : size D = n
  marks : ∀ c, marker D c.val = M.marker c
  start : ∀ b, initial D b = (M.initial b).val
  final : accept D = M.accept.val
  step : ∀ l c r, update D (letter l) c.val (letter r) = (M.next l c r).map Fin.val

end P455WriterTiles
