import Problem455TableSemantics

/- A self-delimiting bit encoding for the table problem. The order,
   followed by the n^2 entries in row-major order, are unary numerals. -/
namespace P455TableBits
open P455Table P455TableSemantics

def unary (n : Nat) := List.replicate n true ++ [false]

def readNat : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::xs => some (0,xs)
  | true::xs => (readNat xs).map fun (n,rest) => (n+1,rest)

theorem read_unary (n : Nat) (s : List Bool) : readNat (unary n++s)=some (n,s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (readNat (unary n++s)).map _ = _
    rw [ih]; rfl

def readMany (read : List Bool → Option (A × List Bool)) :
    Nat → List Bool → Option (List A × List Bool)
  | 0, s => some ([],s)
  | n+1, s => do
      let (a,rest) ← read s
      let (tail,last) ← readMany read n rest
      return (a::tail,last)

theorem read_many {read : List Bool → Option (A × List Bool)} (emit : A → List Bool)
    (xs : List A) (ok : ∀ x∈xs, ∀ s, read (emit x ++ s)=some (x,s)) (rest : List Bool) :
    readMany read xs.length (xs.flatMap emit ++ rest)=some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readMany,ok a List.mem_cons_self]
    simp [ih (fun x m => ok x (List.mem_cons_of_mem a m))]

def row (xs : List Nat) := xs.flatMap unary
def encode (T : Matrix) := unary T.length ++ T.flatMap row

def parse (s : List Bool) : Option Matrix := do
  let (n,rest) ← readNat s
  let (rows,last) ← readMany (readMany readNat n) n rest
  if last.isEmpty then some rows else none

theorem roundtrip {T : Matrix} (square : ∀ xs∈T, xs.length=T.length) : parse (encode T)=some T := by
  have row_ok (xs : List Nat) (mem : xs∈T) (s : List Bool) :
      readMany readNat T.length (row xs ++ s)=some (xs,s) := by
    rw [←square xs mem]
    exact read_many unary xs (fun x _ => read_unary x) s
  have result := read_many row T row_ok []
  simp only [List.append_nil] at result
  simp [parse,encode,read_unary,result]

theorem matrix_roundtrip (X : FiniteOps) : parse (encode (matrix X))=some (matrix X) :=
  roundtrip (fun xs m => (P455Table.square X xs m).1.trans (matrix_length X).symm)

def Separates (answer : List Bool → Bool → Prop) := ∀ T : Matrix, SemigroupTable T →
  ∃ b, answer (encode T) b ∧ (b=true ↔ HasBasis T)

end P455TableBits
