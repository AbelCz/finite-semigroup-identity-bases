import Mathlib.Computability.TMToPartrec



namespace P455MathlibCode
open Turing Turing.PartrecToTM2

def pos : List Bool → PosNum
  | [] => .one
  | true :: xs => .bit1 (pos xs)
  | false :: xs => .bit0 (pos xs)

def wire (xs : List Bool) : Nat := pos xs.reverse

def letter : Bool → Γ' | false => .bit0 | true => .bit1

theorem trPos (xs : List Bool) : trPosNum (pos xs) = xs.map letter ++ [.bit1] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [pos,trPosNum,letter,ih]

theorem raw_main (xs : List Bool) :
    (trList [wire xs]).reverse = .cons :: .bit1 :: xs.map letter := by
  simp [wire,trNat,PosNum.of_to_nat,trNum,trPos,← List.map_reverse]

theorem pos_injective : Function.Injective pos := by
  intro xs
  induction xs with
  | nil => rintro (_|⟨_ | _,_⟩) h <;> simp [pos] at *
  | cons b xs ih =>
    rintro (_ | ⟨c,cs⟩) h
    · cases b <;> simp [pos] at h
    · cases b <;> cases c <;> simp [pos] at h ⊢ <;> exact ih h

theorem wire_injective : Function.Injective wire := by
  intro x y h
  have hn := congrArg (fun n : Nat => (n : Num)) h
  simp only [wire,PosNum.of_to_nat,Num.pos.injEq] at hn
  simpa using congrArg List.reverse (pos_injective hn)

def op (b : Bool) (n : Nat) := if b = true then (n+n)+1 else n+n

theorem pos_fold (xs : List Bool) : (pos xs : Nat) = xs.foldr op 1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [pos,op,List.foldr,PosNum.cast_bit0,PosNum.cast_bit1,ih]

theorem wire_prim : Primrec wire := by
  have h : Primrec (fun z : Bool × Nat => op z.1 z.2) := by
    exact Primrec.ite (Primrec.eq.comp Primrec.fst (.const true))
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd Primrec.snd) (.const 1))
      (Primrec.nat_add.comp Primrec.snd Primrec.snd)
  exact (Primrec.list_foldr Primrec.list_reverse (.const 1) (h.comp Primrec.snd).to₂).of_eq
    fun xs => (pos_fold xs.reverse).symm

def candidate (n : Nat) := (Encodable.decode (α := List Bool) n).getD []
def check (z n : Nat) : Option (List Bool) :=
  if wire (candidate n) = z then some (candidate n) else none

theorem check_prim : Primrec₂ check := by
  have h : Primrec candidate := Primrec.option_getD.comp Primrec.decode (.const [])
  exact (Primrec.ite (Primrec.eq.comp (wire_prim.comp (h.comp Primrec.snd)) Primrec.fst)
    (Primrec.option_some.comp (h.comp Primrec.snd)) (.const none)).to₂

theorem find_wire (x : List Bool) : x ∈ Nat.rfindOpt (check (wire x)) := by
  have ok : check (wire x) (Encodable.encode x) = some x := by simp [check,candidate]
  have d := Nat.rfindOpt_dom.mpr ⟨_,x,ok⟩
  have h := Part.get_mem d
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec h
  unfold check at hn
  split at hn
  next ht => exact Eq.mp (congrArg (fun b => b ∈ Nat.rfindOpt (check (wire x)))
    ((Option.some.inj hn).symm.trans (wire_injective ht))) h
  next => contradiction

/-- One finite partial-recursive instruction tree, fixed before all inputs,
    operates on the sentinel-terminated positive integer wire codes. -/
theorem compile {f : List Bool → List Bool} (hf : Computable f) :
    ∃ c : ToPartrec.Code, ∀ x, [wire (f x)] ∈ c.eval [wire x] := by
  let F : Nat →. Nat := fun n => (Nat.rfindOpt (check n)).map (fun x => wire (f x))
  have hF : Partrec F := (Partrec.rfindOpt check_prim.to_comp).map (((wire_prim.to_comp.comp hf).comp Computable.snd).to₂)
  obtain ⟨c,hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hF)
  refine ⟨c,fun x => ?_⟩
  let v : List.Vector Nat 1 := ⟨[wire x],rfl⟩
  rw [show c.eval [wire x] = _ from hc v]
  exact (Part.mem_map_iff _).mpr ⟨_,(Part.mem_map_iff _).mpr ⟨_,find_wire x,rfl⟩,rfl⟩

end P455MathlibCode
