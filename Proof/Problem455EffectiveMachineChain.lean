import Problem455EffectiveMachineDiagonal

/- An executable finite-control composition of a tape transducer and a
decision machine. The transition at the writer's terminal configuration
changes control to the reader and leaves the entire tape unchanged. -/
namespace P455EffectiveChain
open P455EffectiveMachine P455MachineLocal P455MachineCleanup P455MachineTable

def left (r) (s : Fin q) : Fin (q+r) := ⟨s.val,by have := s.isLt; omega⟩
def right (q) (s : Fin r) : Fin (q+r) := ⟨q+s.val,by have := s.isLt; omega⟩

def insMap (f : Fin q → Fin r) (i : Ins (Fin g) (Fin q)) : Ins (Fin g) (Fin r) := ⟨f i.state,i.symbol,i.dir⟩
def rename (f : Fin q → Fin r) (c : Config g q) : Config g r := ⟨c.tape,c.pos,f c.state⟩

def seqDelta (W : Ordinary g q) (D : Ordinary g r) (s : Fin (q+r)) (a : Fin g) :
    Option (Ins (Fin g) (Fin (q+r))) :=
  if h : s.val<q then
    match W.delta ⟨s.val,h⟩ a with
    | some i => some (insMap (left r) i)
    | none => some ⟨right q D.start,a,.stay⟩
  else (D.delta ⟨s.val-q,by have := s.isLt; omega⟩ a).map (insMap (right q))

theorem left_delta (W : Ordinary g q) (D : Ordinary g r) (s a) :
    seqDelta W D (left r s) a = match W.delta s a with
    | some i => some (insMap (left r) i)
    | none => some ⟨right q D.start,a,.stay⟩ := by simp [seqDelta,left,s.isLt]

theorem right_delta (W : Ordinary g q) (D : Ordinary g r) (s a) :
    seqDelta W D (right q s) a=(D.delta s a).map (insMap (right q)) := by
  have h : ¬ q+s.val<q := by omega
  simp [seqDelta,right,h,Nat.add_sub_cancel_left]

def chain (W : Ordinary g q) (D : Ordinary g r) (mark : W.marker=D.marker) : Ordinary g (q+r) where
  marker := W.marker
  blank := W.blank
  blank_ne := W.blank_ne
  start := left r W.start
  delta := seqDelta W D
  keeps := by
    intro s a i eq
    by_cases h : s.val<q
    · let j : Fin q := ⟨s.val,h⟩
      have e : s=left r j := rfl
      rw [e,left_delta] at eq
      cases d : W.delta j a with
      | none => rw [d] at eq; obtain rfl := Option.some.inj eq; rfl
      | some z => rw [d] at eq; obtain rfl := Option.some.inj eq; exact W.keeps _ _ _ d
    · let j : Fin r := ⟨s.val-q,by have := s.isLt; omega⟩
      have e : s=right q j := Fin.ext (by dsimp [j,right]; omega)
      rw [e,right_delta] at eq
      cases d : D.delta j a with
      | none => simp [d] at eq
      | some z =>
        rw [d] at eq; obtain rfl := Option.some.inj eq
        exact mark ▸ D.keeps _ _ _ d
  leftSafe := by
    intro s i eq
    by_cases h : s.val<q
    · let j : Fin q := ⟨s.val,h⟩
      have e : s=left r j := rfl
      rw [e,left_delta] at eq
      cases d : W.delta j W.marker with
      | none => rw [d] at eq; obtain rfl := Option.some.inj eq; exact Direction.noConfusion
      | some z => rw [d] at eq; obtain rfl := Option.some.inj eq; exact W.leftSafe _ _ d
    · let j : Fin r := ⟨s.val-q,by have := s.isLt; omega⟩
      have e : s=right q j := Fin.ext (by dsimp [j,right]; omega)
      rw [e,right_delta,mark] at eq
      cases d : D.delta j D.marker with
      | none => simp [d] at eq
      | some z => rw [d] at eq; obtain rfl := Option.some.inj eq; exact D.leftSafe _ _ d

def liftAlphabet (W : Ordinary g q) (D : Ordinary g r) (mark) (A : Alphabet W) : Alphabet (chain W D mark) :=
  ⟨A.bit,A.away,A.ink,A.distinct⟩

def out (q) (ans : Fin r→Bool) (s : Fin (q+r)) : Bool :=
  if h : s.val<q then false else ans ⟨s.val-q,by have := s.isLt; omega⟩

theorem out_right (q) (ans : Fin r→Bool) (s) : out q ans (right q s)=ans s := by
  have h : ¬ q+s.val<q := by omega
  simp [out,right,h,Nat.add_sub_cancel_left]

theorem left_step (W : Ordinary g q) (D : Ordinary g r) (mark) (c : Config g q)
    (live : instruction W c≠none) :
    once (chain W D mark) (rename (left r) c)=rename (left r) (once W c) := by
  cases c with
  | mk tape pos s =>
    cases e : W.delta s (tape pos) with
    | none => exact False.elim (live e)
    | some i => simp [once,instruction,chain,rename,left_delta,e,insMap]

theorem shift_control (W : Ordinary g q) (D : Ordinary g r) (mark) (c : Config g q)
    (halt : instruction W c=none) :
    once (chain W D mark) (rename (left r) c)=rename (right q) ⟨c.tape,c.pos,D.start⟩ := by
  change W.delta c.state (c.tape c.pos)=none at halt
  simp [once,instruction,chain,rename,left_delta,halt,write_same,dest]

theorem right_step (W : Ordinary g q) (D : Ordinary g r) (mark) (c : Config g r) :
    once (chain W D mark) (rename (right q) c)=rename (right q) (once D c) := by
  cases c with
  | mk tape pos s => cases e : D.delta s (tape pos) <;> simp [once,instruction,chain,rename,right_delta,e,insMap]

theorem follows_left (W : Ordinary g q) (D : Ordinary g r) (mark) (c : Config g q) (t)
    (before : ∀ j, j<t → instruction W (follow W c j)≠none) :
    follow (chain W D mark) (rename (left r) c) t=rename (left r) (follow W c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [follow,ih (fun j h => before j (by omega)),left_step _ _ _ _ (before t (by omega)),follow]

theorem follows_right (W : Ordinary g q) (D : Ordinary g r) (mark) (c : Config g r) (t) :
    follow (chain W D mark) (rename (right q) c) t=rename (right q) (follow D c t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [follow,ih,right_step]

theorem follow_add (M : Ordinary g q) (c : Config g q) (t k) :
    follow M c (t+k)=follow M (follow M c t) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (once M) ih

theorem earliest (P : Nat→Prop) (t : Nat) (hit : P t) : ∃ j, P j ∧ ∀ i, i<j → ¬P i := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases h : ∃ j, j<t ∧ P j
    · obtain ⟨j,lt,yes⟩ := h; exact ih j lt yes
    · exact ⟨t,hit,fun i lt yes => h ⟨i,lt,yes⟩⟩

def Delivers (W : Ordinary g q) (A : Alphabet W) (x : List Bool) (D : Ordinary g r)
    (B : Alphabet D) (y : List Bool) : Prop :=
  ∃ t, let c := follow W (inputConfig W A x) t
       instruction W c=none ∧ c.pos=0 ∧ c.tape=inputTape D B y

def Answers (D : Ordinary g q) (B : Alphabet D) (ans : Fin q → Bool) (y : List Bool) (v : Bool) : Prop :=
  ∃ t, let c := follow D (inputConfig D B y) t
       instruction D c=none ∧ ans c.state=v

theorem answers_chain (W : Ordinary g q) (D : Ordinary g r) (mark : W.marker=D.marker)
    (A : Alphabet W) (B : Alphabet D) (ans : Fin r→Bool) {x y v}
    (produces : Delivers W A x D B y) (reads : Answers D B ans y v) :
    Answers (chain W D mark) (liftAlphabet W D mark A) (out q ans) x v := by
  obtain ⟨t,atT,pos,tape⟩ := produces
  obtain ⟨k,stopped,verdict⟩ := reads
  let c := inputConfig W A x
  let C := chain W D mark
  obtain ⟨j,atJ,before⟩ := earliest (fun i => instruction W (follow W c i)=none) t atT
  have eq : follow W c j=follow W c t := unique_halt W c atJ atT
  have env : (⟨(follow W c j).tape,(follow W c j).pos,D.start⟩ : Config g r)=inputConfig D B y := by
    rw [eq]; change (⟨(follow W (inputConfig W A x) t).tape,(follow W (inputConfig W A x) t).pos,D.start⟩ : Config g r)=_
    rw [pos,tape]; rfl
  let ini := inputConfig C (liftAlphabet W D mark A) x
  have ini_eq : ini=rename (left r) c := rfl
  have start : follow C ini (j+1)=rename (right q) (inputConfig D B y) := by
    rw [ini_eq,follow,follows_left _ _ _ _ _ before,shift_control _ _ _ _ atJ,env]
  have final : follow C ini (j+1+k)=rename (right q) (follow D (inputConfig D B y) k) := by
    rw [follow_add,start,follows_right]
  refine ⟨j+1+k,?_⟩
  change instruction C (follow C ini (j+1+k))=none ∧ out q ans (follow C ini (j+1+k)).state=v
  rw [final]
  constructor
  · simpa only [instruction,C,chain,rename,right_delta,Option.map_eq_none'] using stopped
  · exact (out_right ..).trans verdict

end P455EffectiveChain
