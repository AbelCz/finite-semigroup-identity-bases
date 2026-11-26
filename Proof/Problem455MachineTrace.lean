import Problem455MachineTable



namespace P455MachineTable
open P455MachineLocal P455PaddedTiles

private theorem left_agree {u v : Nat→Fin n} {w x : Nat} (hx : x<w) (eq : ∀ j,j<w→u j=v j) :
    leftAt u x=leftAt v x := by
  by_cases e : x=0 <;> simp [leftAt,e,eq (x-1) (by omega)]

private theorem right_agree {u v : Nat→Fin n} {w x : Nat} (hx : x<w) (eq : ∀ j,j<w→u j=v j) :
    rightAt u w x=rightAt v w x := by
  by_cases e : x+1=w
  · simp [rightAt,e]
  · simp [rightAt,e,eq _ (by omega : x+1<w)]

private theorem next_inside {d : Direction} {p w : Nat} (hp : p<w) (safe : ¬exits d w p) : dest d p<w := by
  cases d <;> simp [exits,dest] at * <;> omega

theorem agrees (M : TM g q) {w s : Nat} (T : AcceptingTrace (compile M) w s) :
    ∀ t,t≤s → (run M t).pos<w ∧ ∀ x,x<w → T.rows t x=row M t x := by
  intro t; induction t with
  | zero =>
    intro _
    refine ⟨T.positive,?_⟩
    intro x hx
    rw [T.start x hx]
    by_cases e : x=0 <;> simp [compile,row,run,init,atCell,e]
  | succ t ih =>
    intro st
    obtain ⟨hp,eq⟩ := ih (by omega)
    have moves (x : Nat) (hx : x<w) :=
      T.steps t (by omega) x hx
    have atStep (x : Nat) (hx : x<w) :
        (compile M).next (leftAt (row M t) x) (row M t x) (rightAt (row M t) w x)=some (T.rows (t+1) x) := by
      simpa only [left_agree hx eq,right_agree hx eq,eq x hx] using moves x hx
    let p := (run M t).pos
    let z := (run M t).state
    let tape := (run M t).tape
    have safe : ¬exits (M.delta z (tape p)).dir w p := by
      intro bad
      have e := (defined_at_head M.delta tape w p z hp).mpr bad
      have observed := atStep p hp
      change (update M.delta _ (dec M (enc _)) _).map enc=_ at observed
      rw [left_dec,right_dec,dec_enc] at observed
      change (update M.delta (leftOf (atCell tape p z) p) (atCell tape p z p) (rightOf (atCell tape p z) w p)).map enc=_ at observed
      rw [e] at observed
      contradiction
    refine ⟨next_inside hp safe,?_⟩
    intro x hx
    exact Option.some.inj ((atStep x hx).symm.trans (local_value M t w x hp safe hx))

def Genuine (M : TM g q) (t : Nat) := (run M t).pos=0 ∧ (run M t).state=M.accept

theorem genuine_of_trace (M : TM g q) {w s : Nat} (T : AcceptingTrace (compile M) w s) : Genuine M s := by
  have eq := ((agrees M T s (by omega)).2 0 T.positive).symm.trans T.accept
  have old := enc_inj M eq
  change atCell (run M s).tape (run M s).pos (run M s).state 0=⟨M.marker,some M.accept⟩ at old
  have head := congrArg Cell.head old
  by_cases e : (run M s).pos=0
  · exact ⟨e,by simpa [atCell,e] using head⟩
  · simp [atCell,Ne.symm e] at head

theorem fixed_accept (M : TM g q) {s : Nat} (accepts : Genuine M s) : run M (s+1)=run M s := by
  have fixedCfg (c : Config g q) (at0 : c.pos=0) (state : c.state=M.accept) (eq0 : c.tape 0=M.marker) :
      step M c=c := by
    cases c with
    | mk tape pos st =>
      change pos=0 at at0; change st=M.accept at state
      subst pos; subst st
      change tape 0=M.marker at eq0
      have fixed : writeAt tape 0 M.marker=tape := by funext x; by_cases e : x=0 <;> simp [writeAt,e,eq0]
      simp [step,eq0,M.stationary,dest,fixed]
  exact fixedCfg (run M s) accepts.1 accepts.2 ((marker_iff M s 0).mpr rfl)

private theorem same_value (M : TM g q) {s : Nat} (genuine : Genuine M s) (x : Nat) :
    row M (s+1) x=row M s x := by unfold row; rw [fixed_accept M genuine]

/-- Every accepting trace of a compiled machine supplies its own full-row
stutter, including the unwritten cells and both strip boundaries. -/
theorem trace_stutters (M : TM g q) {w s : Nat} (T : AcceptingTrace (compile M) w s) :
    ∀ x,x<w → (compile M).next (leftAt (T.rows s) x) (T.rows s x) (rightAt (T.rows s) w x)=some (T.rows s x) := by
  have ⟨hp,eq⟩ := agrees M T s (by omega)
  have g := genuine_of_trace M T
  have safe : ¬exits (M.delta (run M s).state ((run M s).tape (run M s).pos)).dir w (run M s).pos := by
    simp [g.1,g.2,(marker_iff M s 0).mpr rfl,M.stationary,exits]
  intro x hx
  rw [left_agree hx eq,right_agree hx eq,eq x hx,local_value M s w x hp safe hx,same_value M g]

theorem trace_of_genuine (M : TM g q) {s : Nat} (g : Genuine M s) : Nonempty (AcceptingTrace (compile M) (s+2) s) := by
  refine ⟨⟨by omega,row M,?_,?_,?_,?_⟩⟩
  · intro x _; by_cases e : x=0 <;> simp [row,run,init,atCell,compile,e]
  · intro y _ x _; simp only [compile,row,dec_enc,atCell]
    by_cases e : x=0
    · simp [e,(marker_iff M y 0).mpr rfl]
    · have f : (run M y).tape x ≠ M.marker := fun h=>e ((marker_iff M y x).mp h)
      simp [e,f]
  · intro y hy x hx; exact local_value M _ _ _ (by have := head_bound M y; omega) (physical_safe M (by omega)) hx
  · simp [row,compile,atCell,g.1,g.2,(marker_iff M s 0).mpr rfl]

theorem trace_iff (M : TM g q) : (∃ t,Genuine M t) ↔ ∃ w s, Nonempty (AcceptingTrace (compile M) w s) := by
  constructor
  · rintro ⟨s,g⟩; exact ⟨_,s,trace_of_genuine M g⟩
  · rintro ⟨w,s,⟨T⟩⟩; exact ⟨s,genuine_of_trace M T⟩

theorem rectangles_iff (M : TM g q) : (∃ t,Genuine M t) ↔
    ∃ w, ∀ k, ∃ h, 1<h ∧ k<2*(w*h) ∧ Nonempty (Rectangle (compile M) w h) :=
  (trace_iff M).trans (trace_iff_rectangles (fun T => trace_stutters M T))

end P455MachineTable
