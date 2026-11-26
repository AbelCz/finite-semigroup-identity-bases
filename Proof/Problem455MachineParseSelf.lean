import Problem455MachineParse
import Problem455EffectiveMachineWriter

namespace P455MachineParse
open P455EffectiveMachine P455MachineCleanup P455EffectiveWriter
abbrev Source := (g : Nat) × (q : Nat) × (M : Ordinary g q) × Alphabet M
abbrev RawOrdinary := (g : Nat) × (q : Nat) × Ordinary g q

def digits (a b : Fin g) : Bool → Fin g | false => a | true => b
def mkSource (M : Ordinary g q) (a b : Fin g) : Option Source :=
  if ok : a≠M.marker ∧ b≠M.marker ∧ a≠M.blank ∧ b≠M.blank ∧ a≠b then
    some ⟨g,q,M,⟨digits a b,fun v=>by cases v <;> first | exact ok.1 | exact ok.2.1,
      fun v=>by cases v <;> first | exact ok.2.2.1 | exact ok.2.2.2.1,ok.2.2.2.2⟩⟩
  else none

theorem mkSource_ok (M : Ordinary g q) (A : Alphabet M) :
    mkSource M (A.bit false) (A.bit true)=some ⟨g,q,M,A⟩ := by
  have h := And.intro (A.away false) (And.intro (A.away true)
    (And.intro (A.ink false) (And.intro (A.ink true) A.distinct)))
  rw [mkSource,dif_pos h]
  have e : digits (A.bit false) (A.bit true)=A.bit := funext (fun v=>by cases v <;> rfl)
  cases A
  simp_all

def parseSelf (s : Bits) : Option Source := do
  let (a,t) ← P455TableBits.readNat s
  let (b,t) ← P455TableBits.readNat t
  let ⟨g,_q,c⟩ ← parseCode t
  let M ← c.decode
  let a' ← asFin g a
  let b' ← asFin g b
  mkSource M a' b'

theorem self_roundtrip (M : Ordinary g q) (A : Alphabet M) :
    parseSelf (selfBits M A)=some ⟨g,q,M,A⟩ := by
  have readN (k : Nat) (t : Bits) : P455TableBits.readNat (unary k++t)=some (k,t) := P455TableBits.read_unary k t
  simp [parseSelf,selfBits,List.append_assoc,readN,code_roundtrip,quote_decode,mkSource_ok]

def blankSource (s : Bits) : Option RawOrdinary := do
  let ⟨g,_,M,A⟩ ← parseSelf s
  let ⟨q,Q⟩ := diagonalInput M A
  return ⟨g,q,Q⟩
theorem blankSource_self (M : Ordinary g q) (A : Alphabet M) :
    blankSource (selfBits M A)=some ⟨g,(diagonalInput M A).1,(diagonalInput M A).2⟩ := by
  simp [blankSource,self_roundtrip]
end P455MachineParse
