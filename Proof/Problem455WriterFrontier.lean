import Problem455EffectiveMachineChain

/- A simulated blank and a never-scanned blank have different physical codes.
   Thus the used interval can be erased even if it contains arbitrary blank gaps. -/
namespace P455WriterFrontier
open P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine

def ink (a : Fin g) : Fin (g+1) := ⟨a.val, by have := a.isLt; omega⟩
def fresh (g : Nat) : Fin (g+1) := ⟨g, by omega⟩
theorem ink_inj {a b : Fin g} : ink a=ink b ↔ a=b := ⟨fun h => Fin.ext (congrArg (fun z : Fin (g+1) => z.val) h),congrArg ink⟩
theorem ink_ne_fresh (a : Fin g) : ink a ≠ fresh g := by
  intro h; have v := congrArg Fin.val h; change a.val=g at v; exact (Nat.ne_of_lt a.isLt) v

def eraseTag (blank : Fin g) (a : Fin (g+1)) : Fin g :=
  if h : a.val<g then ⟨a.val,h⟩ else blank

@[simp] theorem erase_ink (blank a : Fin g) : eraseTag blank (ink a)=a := by simp [eraseTag,ink,a.isLt]
@[simp] theorem erase_fresh (blank : Fin g) : eraseTag blank (fresh g)=blank := by simp [eraseTag,fresh]

theorem erase_marker (M : Ordinary g q) (a : Fin (g+1)) :
    eraseTag M.blank a=M.marker ↔ a=ink M.marker := by
  by_cases h : a.val<g
  · simp only [eraseTag,h,↓reduceDIte]
    constructor
    · intro e; exact Fin.ext (congrArg (fun z : Fin g => z.val) e)
    · intro e; exact Fin.ext (congrArg (fun z : Fin (g+1) => z.val) e)
  · have ne : a≠ink M.marker := by
      intro eq; subst a; exact h M.marker.isLt
    simp [eraseTag,h,M.blank_ne,ne]

def tagIns (i : Ins (Fin g) (Fin q)) : Ins (Fin (g+1)) (Fin q) :=
  ⟨i.state,ink i.symbol,i.dir⟩

def monitor (M : Ordinary g q) : Ordinary (g+1) q where
  marker := ink M.marker
  blank := fresh g
  blank_ne := Ne.symm (ink_ne_fresh _)
  start := M.start
  delta z a := (M.delta z (eraseTag M.blank a)).map tagIns
  keeps := by
    intro z a i e
    cases h : M.delta z (eraseTag M.blank a) with
    | none => simp [h] at e
    | some j =>
      rw [h] at e
      change some (tagIns j)=some i at e
      have e := Option.some.inj e
      subst i; exact ink_inj.trans ((M.keeps _ _ _ h).trans (erase_marker M a))
  leftSafe := by
    intro z i e
    simp only [erase_ink] at e
    cases h : M.delta z M.marker with
    | none => simp [h] at e
    | some j =>
      rw [h] at e
      change some (tagIns j)=some i at e
      have e := Option.some.inj e
      subst i; exact M.leftSafe _ _ h

def alphabet (M : Ordinary g q) (A : Alphabet M) : Alphabet (monitor M) where
  bit b := ink (A.bit b)
  away b h := A.away b (ink_inj.mp h)
  ink b := ink_ne_fresh (A.bit b)
  distinct h := A.distinct (ink_inj.mp h)

def tape (n : Nat) (f : Nat → Fin g) (j : Nat) := if j≤n then ink (f j) else fresh g
def liftCfg (n : Nat) (c : Config g q) : Config (g+1) q := ⟨tape n c.tape,c.pos,c.state⟩

def Good (M : Ordinary g q) (c : Config g q) (n : Nat) : Prop :=
  c.pos≤n+1 ∧ (∀ j, n<j → c.tape j=M.blank) ∧ (∀ j, c.tape j=M.marker ↔ j=0)

theorem input_good (M : Ordinary g q) (A : Alphabet M) (x : List Bool) :
    Good M (inputConfig M A x) x.length := by
  refine ⟨Nat.zero_le _,?_,?_⟩
  · intro j h; cases j with
    | zero => omega
    | succ i => simp [inputConfig,inputTape,List.getElem?_eq_none (show x.length≤i by omega)]
  · intro j; cases j with
    | zero => simp [inputConfig,inputTape]
    | succ i =>
      change (x[i]?).elim M.blank A.bit=M.marker ↔ i+1=0
      cases x[i]? with
      | none => simp [M.blank_ne]
      | some b => simp [A.away]

theorem input_eq (M : Ordinary g q) (A : Alphabet M) (x : List Bool) :
    inputConfig (monitor M) (alphabet M A) x=liftCfg x.length (inputConfig M A x) := by
  suffices h : inputTape (monitor M) (alphabet M A) x=tape x.length (inputTape M A x) by
    change (⟨_,0,M.start⟩ : Config (g+1) q)=⟨_,0,M.start⟩
    rw [h]
    rfl
  funext j
  cases j with
  | zero => simp [inputTape,tape,monitor]
  | succ i =>
    by_cases h : i<x.length
    · simp [inputTape,tape,show i+1≤x.length by omega,List.getElem?_eq_getElem h,alphabet]
    · simp [inputTape,tape,show ¬ i+1≤x.length by omega,List.getElem?_eq_none (show x.length≤i by omega),monitor]

theorem ins_eq (M : Ordinary g q) {c : Config g q} {n} (h : Good M c n) :
    instruction (monitor M) (liftCfg n c)=(instruction M c).map tagIns := by
  change (M.delta c.state (eraseTag M.blank (tape n c.tape c.pos))).map _=_
  by_cases p : c.pos≤n
  · simp [tape,p,instruction]
  · simp [tape,p,instruction,h.2.1 c.pos (by omega)]

theorem good_step (M : Ordinary g q) {c : Config g q} {n} (h : Good M c n) {i}
    (e : instruction M c=some i) :
    Good M (once M c) (max n c.pos) := by
  have pos := h.1
  have p : c.pos ≤ max n c.pos := Nat.le_max_right _ _
  simp only [once,e,Good]
  refine ⟨?_,?_,?_⟩
  · cases i.dir <;> simp [dest] <;> omega
  · intro j lt
    have ne : j≠c.pos := by omega
    simp [writeAt,ne,h.2.1 j (by omega)]
  · intro j
    by_cases eq : j=c.pos
    · subst j; simpa [writeAt] using (M.keeps _ _ _ e).trans (h.2.2 c.pos)
    · simp [writeAt,eq,h.2.2]

theorem step_eq (M : Ordinary g q) {c : Config g q} {n} (h : Good M c n) {i}
    (e : instruction M c=some i) :
    once (monitor M) (liftCfg n c)=liftCfg (max n c.pos) (once M c) := by
  have k : writeAt (tape n c.tape) c.pos (ink i.symbol)=
      tape (max n c.pos) (writeAt c.tape c.pos i.symbol) := by
    funext j
    by_cases eq : j=c.pos
    · subst j; simp [tape,writeAt,Nat.le_max_right]
    · have pos := h.1
      have iff : j≤max n c.pos ↔ j≤n := by omega
      simp [writeAt,tape,eq,iff]
  have s := ins_eq M h
  rw [e] at s
  change instruction (monitor M) (liftCfg n c)=some (tagIns i) at s
  rw [once,s]
  simp only [once,e,liftCfg,tagIns,k]

theorem simulates (M : Ordinary g q) (A : Alphabet M) (x : List Bool) (t : Nat) :
    ∃ n, Good M (follow M (inputConfig M A x) t) n ∧
      follow (monitor M) (inputConfig (monitor M) (alphabet M A) x) t=
        liftCfg n (follow M (inputConfig M A x) t) := by
  induction t with
  | zero => exact ⟨_,input_good M A x,input_eq M A x⟩
  | succ t ih =>
    obtain ⟨n,ok,sim⟩ := ih
    let c := follow M (inputConfig M A x) t
    change ∃ k, Good M (once M c) k ∧ once (monitor M) _=liftCfg k (once M c)
    rw [sim]
    cases e : instruction M c with
    | none =>
      have stop := ins_eq M ok
      change instruction (monitor M) (liftCfg n c)=(instruction M c).map tagIns at stop
      rw [e] at stop
      exact ⟨n,by simpa [once,e] using ok,by simp [once,e,stop,c] at *⟩
    | some i => exact ⟨_,good_step M ok e,step_eq M ok e⟩

end P455WriterFrontier
