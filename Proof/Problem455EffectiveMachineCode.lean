import Problem455MachineCleanup

/- Explicit finite instruction arrays for the machines of the reduction. -/
namespace P455EffectiveMachine
open P455MachineLocal P455MachineCleanup

structure Code (g q : Nat) where
  marker : Fin g
  blank : Fin g
  start : Fin q
  rows : Vector (Vector (Option (Ins (Fin g) (Fin q))) g) q

def Code.read (C : Code g q) (s : Fin q) (a : Fin g) := (C.rows.get s).get a

def Code.Safe (C : Code g q) : Prop := C.blank ≠ C.marker ∧ ∀ s a,
  match C.read s a with
  | none => True
  | some i => (i.symbol=C.marker ↔ a=C.marker) ∧ (a=C.marker → i.dir≠.left)

def finiteAll (p : Fin n → Prop) (d : ∀ i,Decidable (p i)) : Decidable (∀ i,p i) := by
  let f (i : Fin n) := @decide (p i) (d i)
  apply decidable_of_iff ((List.finRange n).all f=true)
  rw [List.all_eq_true]
  constructor
  · intro h i
    have mem : i∈List.finRange n := by
      have bound : i.val < (List.finRange n).length := by simp
      simpa using (List.getElem_mem (l:=List.finRange n) bound)
    exact of_decide_eq_true (h i mem)
  · intro h i _
    exact @decide_eq_true (p i) (d i) (h i)

instance (C : Code g q) : Decidable C.Safe := by
  let p (s : Fin q) (a : Fin g) := match C.read s a with
    | none => True
    | some i => (i.symbol=C.marker ↔ a=C.marker) ∧ (a=C.marker → i.dir≠.left)
  let check (s : Fin q) (a : Fin g) : Decidable (p s a) := by
    unfold p; split <;> infer_instance
  letI alld : Decidable (∀ s a,p s a) := finiteAll _ (fun s => finiteAll _ (check s))
  change Decidable (C.blank≠C.marker ∧ ∀ s a,p s a)
  infer_instance

def Code.machine (C : Code g q) (v : C.Safe) : Ordinary g q where
  marker := C.marker
  blank := C.blank
  blank_ne := v.1
  start := C.start
  delta := C.read
  keeps := by
    intro s a i e
    have h := v.2 s a
    rw [e] at h
    exact h.1
  leftSafe := by
    intro s i e
    have h := v.2 s C.marker
    rw [e] at h
    exact h.2 rfl

def Code.decode (C : Code g q) : Option (Ordinary g q) :=
  if h : C.Safe then some (C.machine h) else none

def quote (M : Ordinary g q) : Code g q :=
  ⟨M.marker,M.blank,M.start,Vector.ofFn (fun s => Vector.ofFn (M.delta s))⟩

@[simp] theorem read_quote (M : Ordinary g q) (s a) : (quote M).read s a=M.delta s a := by
  simp [Code.read,quote,Vector.get]

theorem safe_quote (M : Ordinary g q) : (quote M).Safe := by
  refine ⟨M.blank_ne,fun s a => ?_⟩
  rw [read_quote]
  cases e : M.delta s a with
  | none => trivial
  | some i =>
    exact ⟨M.keeps s a i e, fun h => M.leftSafe s i (by change a=M.marker at h; simpa [h] using e)⟩

@[simp] theorem quote_decode (M : Ordinary g q) : (quote M).decode=some M := by
  rw [Code.decode,dif_pos (safe_quote M)]
  congr 1
  have ext (X Y : Ordinary g q) (mr : X.marker=Y.marker) (bl : X.blank=Y.blank)
      (st : X.start=Y.start) (dt : X.delta=Y.delta) : X=Y := by
    cases X; cases Y; simp_all
  exact ext _ _ rfl rfl rfl (funext fun s => funext fun a => read_quote M s a)

/-- Names and a rectangular array of ordinary natural numbers give the public
machine-code payload. 0 is an undefined instruction. 1+3*(g*s+a)+d codes
a next state s, write symbol a and direction d (left/stay/right). -/
def dirCode : Direction → Nat | .left => 0 | .stay => 1 | .right => 2

def entryCode (g : Nat) (i : Option (Ins (Fin g) (Fin q))) : Nat :=
  match i with
  | none => 0
  | some x => 1+3*(g*x.state.val+x.symbol.val)+dirCode x.dir

def Code.numerals (C : Code g q) : List Nat :=
  [g,q,C.marker.val,C.blank.val,C.start.val] ++
  C.rows.toList.flatMap (fun row => row.toList.map (entryCode g))

def unary (n : Nat) := List.replicate n true ++ [false]

def Code.bits (C : Code g q) : List Bool := C.numerals.flatMap unary

end P455EffectiveMachine
