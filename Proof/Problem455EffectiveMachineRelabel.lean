import Problem455EffectiveMachineChain



namespace P455EffectiveRelabel
open P455MachineLocal P455MachineCleanup P455MachineTable P455EffectiveMachine
open P455EffectiveChain

structure Emb (g h : Nat) where
  enc : Fin g → Fin h
  back : Fin h → Fin g
  undo : ∀ a, back (enc a)=a

theorem Emb.inj (e : Emb g h) (a b) : e.enc a=e.enc b ↔ a=b := by
  constructor
  · intro eq; simpa only [e.undo] using congrArg e.back eq
  · intro eq; rw [eq]

def mapped (e : Emb g h) (i : Ins (Fin g) (Fin q)) : Ins (Fin h) (Fin q) :=
  ⟨i.state,e.enc i.symbol,i.dir⟩

def expand (M : Ordinary g q) (e : Emb g h) : Ordinary h q where
  marker := e.enc M.marker
  blank := e.enc M.blank
  blank_ne := fun equ => M.blank_ne ((e.inj ..).mp equ)
  start := M.start
  delta s x := if x=e.enc (e.back x) then (M.delta s (e.back x)).map (mapped e) else none
  keeps := by
    intro s x i yes
    split at yes
    next right =>
      cases st : M.delta s (e.back x) with
      | none => simp [st] at yes
      | some z =>
        rw [st] at yes; obtain rfl := Option.some.inj yes
        change e.enc z.symbol=e.enc M.marker ↔ x=e.enc M.marker
        exact (e.inj ..).trans ((M.keeps _ _ _ st).trans
          ⟨fun eq => right.trans (congrArg e.enc eq), fun eq =>
            (e.inj ..).mp (right.symm.trans eq)⟩)
    next => contradiction
  leftSafe := by
    intro s i yes
    simp only [e.undo,if_true] at yes
    cases st : M.delta s M.marker with
    | none => simp [st] at yes
    | some z =>
      rw [st] at yes; obtain rfl := Option.some.inj yes
      exact M.leftSafe _ _ st

def alpha (M : Ordinary g q) (A : Alphabet M) (e : Emb g h) : Alphabet (expand M e) where
  bit b := e.enc (A.bit b)
  away b eq := A.away b ((e.inj ..).mp eq)
  ink b eq := A.ink b ((e.inj ..).mp eq)
  distinct eq := A.distinct ((e.inj ..).mp eq)

def conf (e : Emb g h) (c : Config g q) : Config h q := ⟨fun j => e.enc (c.tape j),c.pos,c.state⟩

theorem input_tape (M : Ordinary g q) (A : Alphabet M) (e : Emb g h) (w : List Bool) (j) :
    inputTape (expand M e) (alpha M A e) w j = e.enc (inputTape M A w j) := by
  cases j with
  | zero => rfl
  | succ j => cases eq : w[j]? <;> simp [inputTape,eq,expand,alpha]

theorem exp_instruction (M : Ordinary g q) (e : Emb g h) (c : Config g q) :
    instruction (expand M e) (conf e c)=(instruction M c).map (mapped e) := by
  simp [instruction,expand,conf,e.undo]

theorem exp_once (M : Ordinary g q) (e : Emb g h) (c : Config g q) :
    once (expand M e) (conf e c)=conf e (once M c) := by
  unfold once; rw [exp_instruction]
  cases st : instruction M c with
  | none => rfl
  | some z =>
    have tape : writeAt (conf e c).tape c.pos (e.enc z.symbol)=fun j=>e.enc (writeAt c.tape c.pos z.symbol j) := by
      funext j; by_cases eq : j=c.pos <;> simp [conf,writeAt,eq]
    exact congrArg (fun f => Config.mk f (dest z.dir c.pos) z.state) tape

theorem exp_run (M : Ordinary g q) (A : Alphabet M) (e : Emb g h) (w t) :
    follow (expand M e) (inputConfig (expand M e) (alpha M A e) w) t=
      conf e (follow M (inputConfig M A w) t) := by
  induction t with
  | zero =>
    exact congrArg (fun f => Config.mk f 0 M.start) (funext (input_tape M A e w))
  | succ t ih => simp only [follow,ih,exp_once]

theorem exp_answers (M : Ordinary g q) (A : Alphabet M) (e : Emb g h) {ans w b}
    (out : Answers M A ans w b) : Answers (expand M e) (alpha M A e) ans w b := by
  obtain ⟨t,stop,ok⟩ := out
  refine ⟨t,?_⟩
  simp only [exp_run]
  constructor
  · rw [exp_instruction,stop]; rfl
  · exact ok

/-- The distinguished four symbols occupy exactly 0 (marker), 1 (blank),
2 (false) and 3 (true). Other symbols retain their index at the chosen
offset. This allows two unrelated scratch alphabets to coexist. -/
def number (M : Ordinary g q) (A : Alphabet M) (base : Nat) (a : Fin g) :=
  if a=M.marker then 0 else if a=M.blank then 1 else if a=A.bit false then 2 else if a=A.bit true then 3 else base+a.val

def denumber (M : Ordinary g q) (A : Alphabet M) (base y : Nat) :=
  if y=0 then M.marker else if y=1 then M.blank else if y=2 then A.bit false else if y=3 then A.bit true
  else if h : y-base<g then (⟨y-base,h⟩ : Fin g) else M.blank

theorem number_lt (M : Ordinary g q) (A : Alphabet M) (lo : 4≤base) (hi : base+g ≤ h) (a : Fin g) :
    number M A base a < h := by
  have small := a.isLt
  unfold number
  split <;> (first | omega | split <;> (first | omega | split <;> (first | omega | split <;> omega)))

theorem denumber_number (M : Ordinary g q) (A : Alphabet M) (lo : 4≤base) (a : Fin g) :
    denumber M A base (number M A base a)=a := by
  unfold number
  split
  next eq => simp [denumber,eq]
  next =>
    split
    next eq => simp [denumber,eq]
    next =>
      split
      next eq => simp [denumber,eq]
      next =>
        split
        next eq => simp [denumber,eq]
        next =>
          have zero : base+a.val≠0 := by omega
          have one : base+a.val≠1 := by omega
          have two : base+a.val≠2 := by omega
          have three : base+a.val≠3 := by omega
          simp [denumber,zero,one,two,three,Nat.add_sub_cancel_left,a.isLt]

def common (M : Ordinary g q) (A : Alphabet M) (lo : 4≤base) (hi : base+g≤h) : Emb g h :=
  ⟨fun a => ⟨number M A base a,number_lt M A lo hi a⟩,fun a => denumber M A base a.val,denumber_number M A lo⟩

@[simp] theorem mark_number (M : Ordinary g q) (A : Alphabet M) (base) : number M A base M.marker=0 := by
  simp [number]

@[simp] theorem blank_number (M : Ordinary g q) (A : Alphabet M) (base) : number M A base M.blank=1 := by
  simp [number,M.blank_ne]

@[simp] theorem bit_number (M : Ordinary g q) (A : Alphabet M) (base) (b : Bool) :
    number M A base (A.bit b)=if b then 3 else 2 := by
  cases b <;> simp [number,A.away,A.ink,Ne.symm A.distinct]

end P455EffectiveRelabel
