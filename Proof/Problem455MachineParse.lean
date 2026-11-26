import Problem455EffectiveMachineDiagonal
import Problem455TableBits

/- Constructive bit-level decoding for the ordinary program and the two
   input-alphabet names in the diagonal construction. -/
namespace P455MachineParse
open P455EffectiveMachine P455MachineLocal P455MachineCleanup
open P455TableBits (readNat readMany read_unary read_many)
abbrev Bits := List Bool
abbrev Parser (α : Type) := Bits → Option (α × Bits)
abbrev Programs := (g : Nat) × (q : Nat) × Code g q

def asFin (n k : Nat) : Option (Fin n) := if h : k<n then some ⟨k,h⟩ else none
@[simp] theorem asFin_val (x : Fin n) : asFin n x.val = some x := by simp [asFin,x.isLt]

def decodeEntry (g q : Nat) : Nat → Option (Option (Ins (Fin g) (Fin q)))
  | 0 => some none
  | k+1 => do
     let z ← asFin q ((k/3)/g)
     let a ← asFin g ((k/3)%g)
     let d := if k%3=0 then Direction.left else if k%3=1 then Direction.stay else Direction.right
     return some ⟨z,a,d⟩

theorem entry_roundtrip (x : Option (Ins (Fin g) (Fin q))) : decodeEntry g q (entryCode g x)=some x := by
  cases x with
  | none => rfl
  | some ins =>
    obtain ⟨z,a,d⟩ := ins
    have gp : 0<g := Nat.zero_lt_of_lt a.isLt
    have split₁ : (g*z.val+a.val)/g=z.val := by rw [Nat.mul_add_div gp,Nat.div_eq_of_lt a.isLt,Nat.add_zero]
    have split₂ : (g*z.val+a.val)%g=a.val := by rw [Nat.mul_add_mod,Nat.mod_eq_of_lt a.isLt]
    have code' : 1+3*(g*z.val+a.val)+dirCode d = (3*(g*z.val+a.val)+dirCode d)+1 := by omega
    change decodeEntry g q (1+3*(g*z.val+a.val)+dirCode d)=_
    rw [code']
    have small : dirCode d < 3 := by cases d <;> decide
    simp only [decodeEntry,Nat.mul_add_div (by decide : 0<3),Nat.div_eq_of_lt small,
      Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt small,split₁,split₂,asFin_val,Option.bind_some]
    cases d <;> rfl

def fromN (f : Nat → Option α) : Parser α := fun s=>do
  let (k,tail) ← readNat s
  let a ← f k
  return (a,tail)
def readVec (n : Nat) (parse : Parser α) : Parser (Vector α n) := fun s=>do
  let (xs,tail) ← readMany parse n s
  if h : xs.length=n then return (⟨xs.toArray,by simpa using h⟩,tail) else none

theorem vec_read (parse : Parser α) (emit : α → Bits) (ok : ∀ x s,parse (emit x++s)=some (x,s))
    (v : Vector α n) (s : Bits) : readVec n parse (v.toList.flatMap emit++s)=some (v,s) := by
  have h := read_many emit v.toList (fun x _ => ok x) s
  rw [Vector.length_toList] at h
  simp [readVec,h,Vector.length_toList]

def rowBits (g : Nat) (v : Vector (Option (Ins (Fin g) (Fin q))) g) :=
  v.toList.flatMap (fun x => unary (entryCode g x))

def parsePayload : Parser Programs := fun s=>do
  let (g,t) ← readNat s
  let (q,t) ← readNat t
  let (mark,t) ← fromN (asFin g) t
  let (blank,t) ← fromN (asFin g) t
  let (start,t) ← fromN (asFin q) t
  let (rows,t) ← readVec q (readVec g (fromN (decodeEntry g q))) t
  return (⟨g,q,mark,blank,start,rows⟩,t)

theorem payload_roundtrip (C : Code g q) (s : Bits) : parsePayload (C.bits++s)=some (⟨g,q,C⟩,s) := by
  have one (x : Option (Ins (Fin g) (Fin q))) (t : Bits) :
      fromN (decodeEntry g q) (unary (entryCode g x)++t)=some (x,t) := by
    simp [fromN,show P455EffectiveMachine.unary=P455TableBits.unary from rfl,read_unary,entry_roundtrip]
  have row_read (v : Vector (Option (Ins (Fin g) (Fin q))) g) (t : Bits) :
      readVec g (fromN (decodeEntry g q)) (rowBits g v++t)=some (v,t) := vec_read _ _ one v t
  have rows := vec_read _ _ row_read C.rows s
  have eq : C.bits = unary g ++ unary q ++ unary C.marker.val ++ unary C.blank.val ++ unary C.start.val ++
      C.rows.toList.flatMap (rowBits g) := by
    simp only [Code.bits,Code.numerals,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    congr 1
    generalize C.rows.toList = xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.append_cancel_left_eq] at ih; simp [List.flatMap_append,rowBits,List.flatMap_map,Function.comp_def,ih]
  have readN (k : Nat) (t : Bits) : readNat (unary k++t)=some (k,t) := read_unary k t
  have readF {m} (a : Fin m) (t : Bits) : fromN (asFin m) (unary a.val++t)=some (a,t) := by simp [fromN,readN]
  rw [eq]
  simp [parsePayload,List.append_assoc,readN,readF,rows]


def exactParse (p : Parser α) (s : Bits) : Option α := do
  let (v,t) ← p s
  if t.isEmpty then some v else none
def parseCode := exactParse parsePayload
@[simp] theorem code_roundtrip (C : Code g q) : parseCode C.bits=some ⟨g,q,C⟩ := by
  have ok := payload_roundtrip C []
  simp [parseCode,exactParse,List.append_nil] at ok ⊢
  rw [ok]; rfl
end P455MachineParse
