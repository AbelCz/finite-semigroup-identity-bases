import Problem455MachineTrace



namespace P455MachineCleanup
open P455MachineLocal P455MachineTable P455PaddedTiles

structure Ordinary (g q : Nat) where
  marker : Fin g
  blank : Fin g
  blank_ne : blank≠marker
  start : Fin q
  delta : Fin q→Fin g→Option (Ins (Fin g) (Fin q))
  keeps : ∀ z a ins, delta z a=some ins → (ins.symbol=marker ↔ a=marker)
  leftSafe : ∀ z ins, delta z marker=some ins → ins.dir≠.left

def old (z : Fin q) : Fin (q+2) := ⟨z.val,by have := z.isLt; omega⟩
def cleanState (q : Nat) : Fin (q+2) := ⟨q,by omega⟩
def acceptState (q : Nat) : Fin (q+2) := ⟨q+1,by omega⟩

def extend (ins : Ins (Fin g) (Fin q)) : Ins (Fin g) (Fin (q+2)) :=
  ⟨old ins.state,ins.symbol,ins.dir⟩

def trans (M : Ordinary g q) (z : Fin (q+2)) (a : Fin g) : Ins (Fin g) (Fin (q+2)) :=
  if h : z.val<q then
    match M.delta ⟨z.val,h⟩ a with
    | none => ⟨cleanState q,a,.stay⟩
    | some i => extend i
  else if z.val=q then
    if a=M.marker then ⟨acceptState q,a,.stay⟩ else ⟨cleanState q,a,.left⟩
  else ⟨acceptState q,a,.stay⟩

theorem old_step (M : Ordinary g q) (z : Fin q) (a : Fin g) : trans M (old z) a =
    match M.delta z a with
    | none => ⟨cleanState q,a,.stay⟩
    | some i => extend i := by simp [trans,old,z.isLt]

theorem clean_step (M : Ordinary g q) (a : Fin g) : trans M (cleanState q) a =
    if a=M.marker then ⟨acceptState q,a,.stay⟩ else ⟨cleanState q,a,.left⟩ := by
  simp [trans,cleanState]

def normalized (M : Ordinary g q) : TM g (q+2) where
  marker := M.marker
  blank := M.blank
  blank_ne := M.blank_ne
  start := old M.start
  accept := acceptState q
  distinct := by intro e; have v := congrArg Fin.val e; change M.start.val=q+1 at v; have := M.start.isLt; omega
  delta := trans M
  keeps := by
    intro z a
    unfold trans
    split
    next bound =>
      cases e : M.delta ⟨z.val,bound⟩ a with
      | none => rfl
      | some i => exact M.keeps _ _ _ e
    next =>
      split
      · split <;> rfl
      · rfl
  leftSafe := by
    intro z
    unfold trans
    split
    next bound =>
      cases e : M.delta ⟨z.val,bound⟩ M.marker with
      | none => simp
      | some i => exact M.leftSafe _ _ e
    next =>
      split <;> simp
  stationary := by simp [trans,acceptState,show ¬q+1<q by omega]

def config₀ (M : Ordinary g q) : Config g q :=
  ⟨fun x=>if x=0 then M.marker else M.blank,0,M.start⟩

def instruction (M : Ordinary g q) (c : Config g q) := M.delta c.state (c.tape c.pos)

def once (M : Ordinary g q) (c : Config g q) : Config g q :=
  match instruction M c with
  | none => c
  | some ins => ⟨writeAt c.tape c.pos ins.symbol,dest ins.dir c.pos,ins.state⟩

def original (M : Ordinary g q) : Nat→Config g q
  | 0 => config₀ M
  | t+1 => once M (original M t)

def stopped (M : Ordinary g q) (t : Nat) := instruction M (original M t)=none

def lift (c : Config g q) : Config g (q+2) := ⟨c.tape,c.pos,old c.state⟩

theorem simulates (M : Ordinary g q) (t : Nat) (prior : ∀ j,j<t→¬stopped M j) :
    run (normalized M) t=lift (original M t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have now := prior t (by omega)
    change step (normalized M) (run (normalized M) t) = lift (once M (original M t))
    rw [ih (fun j lt=>prior j (by omega))]
    cases eq : instruction M (original M t) with
    | none => exact (now eq).elim
    | some ins =>
      have instr : trans M (old (original M t).state) ((original M t).tape (original M t).pos)=extend ins := by
        rw [old_step]; change (match instruction M (original M t) with | none => _ | some i => extend i) = _
        rw [eq]
      simp [step,normalized,lift,instr,once,eq,extend]

private theorem eventually_clean (M : Ordinary g q) (p : Nat) :
    ∀ t, (run (normalized M) t).pos=p → (run (normalized M) t).state=cleanState q →
      ∃ s,Genuine (normalized M) s := by
  induction p with
  | zero =>
    intro t pos state
    have marker := (marker_iff (normalized M) t 0).mpr rfl
    change (run (normalized M) t).tape 0=M.marker at marker
    refine ⟨t+1,?_⟩
    change dest (trans M _ _).dir _=0 ∧ (trans M _ _).state=acceptState q
    rw [state,pos,marker,clean_step]
    simp [dest]
  | succ p ih =>
    intro t pos state
    have neq : (run (normalized M) t).tape (p+1)≠M.marker := by
      intro e; have z := (marker_iff (normalized M) t (p+1)).mp e; omega
    apply ih (t+1)
    · change dest (trans M _ _).dir _=p
      rw [state,pos,clean_step,if_neg neq]; simp [dest]
    · change (trans M _ _).state=cleanState q
      rw [state,pos,clean_step,if_neg neq]

private theorem first_stop (M : Ordinary g q) (t : Nat) (h : stopped M t) :
    ∃ j, stopped M j ∧ (∀ i,i<j→¬stopped M i) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases early : ∃ i,i<t ∧ stopped M i
    · obtain ⟨i,lt,yes⟩ := early; exact ih i lt yes
    · exact ⟨t,h,fun i lt st=>early ⟨i,lt,st⟩⟩

theorem halts_iff_genuine (M : Ordinary g q) :
    (∃ t,stopped M t) ↔ ∃ s,Genuine (normalized M) s := by
  constructor
  · rintro ⟨t,yes⟩
    obtain ⟨j,st,prior⟩ := first_stop M t yes
    have exactAt := simulates M j prior
    have instr : trans M (old (original M j).state) ((original M j).tape (original M j).pos) =
        ⟨cleanState q,(original M j).tape (original M j).pos,.stay⟩ := by
      rw [old_step]; unfold stopped instruction at st; rw [st]
    apply eventually_clean M (original M j).pos (j+1)
    · change (step (normalized M) (run (normalized M) j)).pos=_
      rw [exactAt]; simp [normalized,step,lift,instr,dest]
    · change (step (normalized M) (run (normalized M) j)).state=_
      rw [exactAt]; simp [normalized,step,lift,instr]
  · rintro ⟨s,_,accept⟩
    apply Classical.byContradiction
    intro none
    have eq := simulates M s (fun j _ h=>none ⟨j,h⟩)
    rw [eq] at accept
    have indices := congrArg Fin.val accept
    change (original M s).state.val=q+1 at indices
    have := (original M s).state.isLt; omega

/-- Compilation targets the very same numerical tile system as the word
testers. The halt may occur at *any* tape position, including at time zero. -/
theorem halts_iff_trace (M : Ordinary g q) : (∃ t,stopped M t) ↔
    ∃ w s, Nonempty (AcceptingTrace (compile (normalized M)) w s) :=
  (halts_iff_genuine M).trans (trace_iff (normalized M))

theorem halts_iff_rectangles (M : Ordinary g q) : (∃ t,stopped M t) ↔
    ∃ w, ∀ k, ∃ h, 1<h ∧ k<2*(w*h) ∧ Nonempty (Rectangle (compile (normalized M)) w h) :=
  (halts_iff_genuine M).trans (rectangles_iff (normalized M))

end P455MachineCleanup
