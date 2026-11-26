import Problem455EffectiveMachineCode

/- A diagonal argument for actual deterministic finite-control one-head
machines. Input is a finite Boolean word over two tape symbols. -/
namespace P455EffectiveMachine
open P455MachineLocal P455MachineCleanup P455MachineTable

structure Alphabet (M : Ordinary g q) where
  bit : Bool → Fin g
  away : ∀ b, bit b ≠ M.marker
  ink : ∀ b, bit b ≠ M.blank
  distinct : bit false ≠ bit true

/-- Position zero holds the permanent marker. Input occupies positions
1 through length. All further cells are initially blank. -/
def inputTape (M : Ordinary g q) (A : Alphabet M) (w : List Bool) : Nat → Fin g
  | 0 => M.marker
  | x+1 => (w[x]?).elim M.blank A.bit

def inputConfig (M : Ordinary g q) (A : Alphabet M) (w : List Bool) : Config g q :=
  ⟨inputTape M A w,0,M.start⟩

def follow (M : Ordinary g q) (c : Config g q) : Nat → Config g q
  | 0 => c
  | t+1 => once M (follow M c t)

def HALT (M : Ordinary g q) (c : Config g q) := ∃ t, instruction M (follow M c t)=none

def selfBits (M : Ordinary g q) (A : Alphabet M) : List Bool :=
  unary (A.bit false).val ++ unary (A.bit true).val ++ (quote M).bits

def SelfHalt (M : Ordinary g q) (A : Alphabet M) :=
  HALT M (inputConfig M A (selfBits M A))

theorem inputTape_blank (M : Ordinary g q) (A : Alphabet M) :
    inputConfig M A [] = config₀ M := by
  have tape : inputTape M A [] = fun x => if x=0 then M.marker else M.blank := by
    funext x; cases x <;> simp [inputTape]
  simp [inputConfig,config₀,tape]

theorem blank_run (M : Ordinary g q) (t : Nat) : follow M (config₀ M) t = original M t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [follow,original,ih]

theorem blank_halts (M : Ordinary g q) : HALT M (config₀ M) ↔ ∃ t, stopped M t := by
  simp only [HALT,stopped,blank_run]

theorem rest (M : Ordinary g q) (c : Config g q) {t} (h : instruction M (follow M c t)=none) (k) :
    follow M c (t+k)=follow M c t := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Nat.add_succ,follow,ih,once,h]

theorem unique_halt (M : Ordinary g q) (c : Config g q) {a b}
    (ha : instruction M (follow M c a)=none) (hb : instruction M (follow M c b)=none) :
    follow M c a=follow M c b := by
  by_cases le : a≤b
  · have e := rest M c ha (b-a)
    rw [show a+(b-a)=b by omega] at e
    exact e.symm
  · have e := rest M c hb (a-b)
    rw [show b+(a-b)=a by omega] at e
    exact e

def trap (M : Ordinary g q) (answer : Fin q → Bool) : Ordinary g q where
  marker := M.marker
  blank := M.blank
  blank_ne := M.blank_ne
  start := M.start
  delta := fun s a =>
    match M.delta s a with
    | some i => some i
    | none => if answer s then some ⟨s,a,.stay⟩ else none
  keeps := by
    intro s a i eq
    cases h : M.delta s a with
    | some j => simp only [h,Option.some.injEq] at eq; exact M.keeps s a i (eq ▸ h)
    | none =>
      simp only [h] at eq
      split at eq <;> simp_all <;> subst i <;> simp
  leftSafe := by
    intro s i eq
    cases h : M.delta s M.marker with
    | some j => simp only [h,Option.some.injEq] at eq; exact M.leftSafe s i (eq ▸ h)
    | none =>
      simp only [h] at eq
      split at eq <;> simp_all <;> subst i <;> simp

def liftAlphabet (M : Ordinary g q) (A : Alphabet M) (answer : Fin q → Bool) : Alphabet (trap M answer) :=
  ⟨A.bit,A.away,A.ink,A.distinct⟩

theorem write_same (f : Nat → Fin g) (p) : writeAt f p (f p) = f := by
  funext i; by_cases h : i=p <;> simp [writeAt,h]

theorem once_trap (M : Ordinary g q) (ans) (c : Config g q) : once (trap M ans) c = once M c := by
  cases c with
  | mk tape pos state =>
    cases e : M.delta state (tape pos) with
    | some i => simp [once,instruction,trap,e]
    | none => cases h : ans state <;> simp [once,instruction,trap,e,h,dest,write_same]

theorem follow_trap (M : Ordinary g q) (ans) (c : Config g q) (t) :
    follow (trap M ans) c t = follow M c t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [follow,ih,once_trap]

theorem stop_trap (M : Ordinary g q) (ans) (c : Config g q) :
    instruction (trap M ans) c=none ↔ instruction M c=none ∧ ans c.state=false := by
  cases e : M.delta c.state (c.tape c.pos) <;> cases h : ans c.state <;> simp [instruction,trap,e,h]

theorem halt_trap_iff (M : Ordinary g q) (ans) (c : Config g q) {t}
    (ended : instruction M (follow M c t)=none) :
    HALT (trap M ans) c ↔ ans (follow M c t).state=false := by
  constructor
  · rintro ⟨i,hi⟩
    rw [follow_trap,stop_trap] at hi
    exact unique_halt M c hi.1 ended ▸ hi.2
  · intro h
    exact ⟨t,by rw [follow_trap,stop_trap]; exact ⟨ended,h⟩⟩

/-- A decider may have any finite work alphabet and arbitrary finite
control. On the code of a binary-input machine it must halt and its
Boolean output is read from the final control state. No behavior on
ill-formed encodings is required. -/
def DecidesSelf (D : Ordinary g q) (A : Alphabet D) (answer : Fin q→Bool) : Prop :=
  ∀ {g' q'} (P : Ordinary g' q') (B : Alphabet P),
    let c := inputConfig D A (selfBits P B)
    ∃ t, instruction D (follow D c t)=none ∧
      (answer (follow D c t).state=true ↔ SelfHalt P B)

theorem no_self_decider (D : Ordinary g q) (A : Alphabet D) (answer : Fin q → Bool) :
    ¬DecidesSelf D A answer := by
  intro correct
  let P := trap D answer
  let B := liftAlphabet D A answer
  let c := inputConfig D A (selfBits P B)
  have same : inputConfig P B (selfBits P B)=c := rfl
  obtain ⟨t,halt,ok⟩ := correct P B
  change instruction D (follow D c t)=none at halt
  change (answer (follow D c t).state=true ↔ HALT P (inputConfig P B (selfBits P B))) at ok
  rw [same] at ok
  have contradiction := ok.trans (halt_trap_iff D answer c halt)
  cases e : answer (follow D c t).state <;> simp [e] at contradiction

end P455EffectiveMachine
