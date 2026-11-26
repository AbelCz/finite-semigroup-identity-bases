import Problem455EffectiveMachineDiagonal

/- Compile a finite straight-line initialization script into ordinary finite
control, preserving halting from arbitrary tapes and positions. -/
namespace P455EffectivePrefix
open P455EffectiveMachine P455MachineLocal P455MachineTable P455MachineCleanup

inductive Cmd (g : Nat) | right | left | putRight (v : Fin g)

structure Env (g : Nat) where
  tape : Nat → Fin g
  pos : Nat

def Env.start (env : Env g) (M : Ordinary g q) : Config g q := ⟨env.tape,env.pos,M.start⟩

def write (mark : Fin g) (cmd : Cmd g) (a : Fin g) :=
  match cmd with
  | .putRight v => if a=mark ∨ v=mark then a else v
  | _ => a

def motion (mark : Fin g) (cmd : Cmd g) (a : Fin g) : Direction :=
  match cmd with
  | .left => if a=mark then .stay else .left
  | _ => .right

def effect (mark : Fin g) (cmd : Cmd g) (env : Env g) : Env g :=
  let a := env.tape env.pos
  ⟨writeAt env.tape env.pos (write mark cmd a),dest (motion mark cmd a) env.pos⟩

theorem write_marker (mark : Fin g) (cmd : Cmd g) (a) :
    write mark cmd a=mark ↔ a=mark := by
  cases cmd <;> simp [write]
  split <;> simp_all

theorem safe_motion (mark : Fin g) (cmd : Cmd g) : motion mark cmd mark ≠ .left := by
  cases cmd <;> simp [motion]

def old (s : Fin q) : Fin (q+1) := ⟨s.val,by have := s.isLt; omega⟩
def head (q) : Fin (q+1) := ⟨q,by omega⟩
def liftIns (i : Ins (Fin g) (Fin q)) : Ins (Fin g) (Fin (q+1)) := ⟨old i.state,i.symbol,i.dir⟩

def push (M : Ordinary g q) (cmd : Cmd g) : Ordinary g (q+1) where
  marker := M.marker
  blank := M.blank
  blank_ne := M.blank_ne
  start := head q
  delta s a := if h : s.val<q then (M.delta ⟨s.val,h⟩ a).map liftIns
    else some ⟨old M.start,write M.marker cmd a,motion M.marker cmd a⟩
  keeps := by
    intro s a i eq
    split at eq
    next h =>
      cases e : M.delta ⟨s.val,h⟩ a with
      | none => simp [e] at eq
      | some j => rw [e] at eq; change some (liftIns j) = some i at eq; obtain rfl := Option.some.inj eq; exact M.keeps _ _ _ e
    next =>
      simp only [Option.some.injEq] at eq
      subst i; exact write_marker .. 
  leftSafe := by
    intro s i eq
    split at eq
    next h =>
      cases e : M.delta ⟨s.val,h⟩ M.marker with
      | none => simp [e] at eq
      | some j => rw [e] at eq; change some (liftIns j) = some i at eq; obtain rfl := Option.some.inj eq; exact M.leftSafe _ _ e
    next =>
      simp only [Option.some.injEq] at eq
      subst i; exact safe_motion M.marker cmd

def liftConfig (c : Config g q) : Config g (q+1) := ⟨c.tape,c.pos,old c.state⟩

theorem old_ins (M : Ordinary g q) (cmd) (s a) :
    (push M cmd).delta (old s) a=(M.delta s a).map liftIns := by
  simp [push,old,s.isLt]

theorem head_ins (M : Ordinary g q) (cmd) (a) :
    (push M cmd).delta (head q) a=some ⟨old M.start,write M.marker cmd a,motion M.marker cmd a⟩ := by
  simp [push,head]

theorem once_old (M : Ordinary g q) (cmd) (c : Config g q) :
    once (push M cmd) (liftConfig c)=liftConfig (once M c) := by
  cases c with
  | mk tape pos s =>
    cases h : M.delta s (tape pos) <;> simp [once,instruction,liftConfig,old_ins,h,liftIns]

theorem after_one (M : Ordinary g q) (cmd) (e : Env g) (t) :
    follow (push M cmd) (e.start (push M cmd)) (t+1)=
      liftConfig (follow M ((effect M.marker cmd e).start M) t) := by
  induction t with
  | zero =>
    change once (push M cmd) ⟨e.tape,e.pos,head q⟩=_
    simp [once,instruction,head_ins,follow,liftConfig,effect,Env.start]
  | succ t ih => rw [follow,ih,once_old,follow]

theorem push_iff (M : Ordinary g q) (cmd) (e : Env g) :
    HALT (push M cmd) (e.start (push M cmd)) ↔ HALT M ((effect M.marker cmd e).start M) := by
  constructor
  · rintro ⟨t,fin⟩
    cases t with
    | zero =>
      change (push M cmd).delta (head q) (e.tape e.pos)=none at fin
      simp [head_ins] at fin
    | succ t =>
      refine ⟨t,?_⟩
      rw [after_one] at fin
      simp only [instruction,liftConfig,old_ins,Option.map_eq_none'] at fin
      exact fin
  · rintro ⟨t,fin⟩
    refine ⟨t+1,?_⟩
    rw [after_one]
    simpa only [instruction,liftConfig,old_ins,Option.map_eq_none'] using fin

def install (M : Ordinary g q) : List (Cmd g) → (s : Nat) × Ordinary g s
  | [] => ⟨q,M⟩
  | c::cs => let N := install M cs; ⟨N.1+1,push N.2 c⟩

theorem installed_marker (M : Ordinary g q) (cs) : (install M cs).2.marker=M.marker := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

theorem installed_blank (M : Ordinary g q) (cs) : (install M cs).2.blank=M.blank := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

def perform (mark : Fin g) (cs : List (Cmd g)) (e : Env g) := cs.foldl (fun z c => effect mark c z) e

theorem install_iff (M : Ordinary g q) (cs) (e : Env g) :
    HALT (install M cs).2 (e.start (install M cs).2) ↔ HALT M ((perform M.marker cs e).start M) := by
  induction cs generalizing e with
  | nil => rfl
  | cons c cs ih =>
    exact (push_iff (install M cs).2 c e).trans (by rw [installed_marker]; exact ih _)

end P455EffectivePrefix
