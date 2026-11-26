import Problem455CellClassGrid




namespace P455CellClassHalting
open P455RectangleRank P455PaddedMatchings P455PaddedTiles P455PaddedWord P455Witness
open P455CellClassGrid P455CellClassClean P455CellClassSnake P455SlotSaturation P455GridRows
variable {n w h : Nat} {M : MachineTable n}

private def cert (R : Rectangle M w h) (y x v z : Nat) : EdgeCertificate :=
  ⟨cell R y x,cell R v z,cell R y (x+1),cell R y (x-1),cell R (y+1) x,cell R (y-1) x,cell R (y+1) (x+1)⟩

private theorem guard {R : Rectangle M w h} {b : Bool} {q : Query}
    (met : b=true → H R q) : H R (flagQ b q) := by
  cases b <;> first | exact True.intro | exact met rfl

theorem local_grid (R : Rectangle M w h) (size : 1<w*h) {y x : Nat} (hy : y<h) (hx : x<w)
    (v z : Nat) : H R (localCert (system n) (cert R y x v z)) := by
  have flags := R.flags y hy x hx
  rw [← coordinates (R:=R) hy hx] at flags
  let a := cell R y x
  have right (on : (!(system n).right a.tag) = true) : x+1<w := by
    by_cases e : x+1=w
    · change (!(system n).right (cell R y x).tag) = true at on; rw [flags.2.1] at on; simp [e] at on
    · omega
  have left (on : (!(system n).left a.tag) = true) : 0<x := by
    by_cases e : x=0
    · change (!(system n).left (cell R y x).tag) = true at on; rw [flags.1] at on; simp [e] at on
    · omega
  have down (on : (!(system n).bottom a.tag) = true) : y+1<h := by
    by_cases e : y+1=h
    · change (!(system n).bottom (cell R y x).tag) = true at on; rw [flags.2.2.2.1] at on; simp [e] at on
    · omega
  have up (on : (!(system n).top a.tag) = true) : 0<y := by
    by_cases e : y=0
    · change (!(system n).top (cell R y x).tag) = true at on; rw [flags.2.2.1] at on; simp [e] at on
    · omega
  let ord := orders R size
  refine ⟨guard (fun on => (right_iff R size ord hy hx hy (right on)).mpr ⟨rfl,rfl⟩),
    guard (fun on => (right_iff R size ord hy (by have := left on; omega) hy hx).mpr
      ⟨rfl,by have := left on; omega⟩),
    guard (fun on => (down_iff R size ord hy hx (down on) hx).mpr ⟨rfl,rfl⟩),
    guard (fun on => (down_iff R size ord (by have := up on; omega) hx hy hx).mpr
      ⟨by have := up on; omega,rfl⟩),guard ?_,True.intro⟩
  intro on; obtain ⟨rr,dd⟩ := Bool.and_eq_true_iff.mp on
  exact ⟨(down_iff R size ord hy (right rr) (down dd) (right rr)).mpr ⟨rfl,rfl⟩,
    (right_iff R size ord (down dd) hx (down dd) (right rr)).mpr ⟨rfl,rfl⟩⟩

private theorem end_flag (R : Rectangle M w h) {y x} (hy : y<h) (hx : x<w) :
    endOfRow (system n) (cell R y x) = (if odd y then decide (x=0) else decide (x+1=w)) := by
  have f := R.flags y hy x hx
  simp [endOfRow,coordinates hy hx,f.1,f.2.1,f.2.2.2.2.1]

theorem next_grid (R : Rectangle M w h) (size : 1<w*h) {i : Nat} (lt : i+1<w*h) :
    At (widthCode n+16) (allowed M) (system n) (zero R) i (i+1) := by
  obtain ⟨y,hy,x,hx,v,hv,z,hz,si,sj,next⟩ := stepping lt
  let e := cert R y x v z
  have readA : H R (typedNode e.a) := cell_typed R size (id_bound hy hx)
  have readB : H R (typedNode e.b) := cell_typed R size (id_bound hv hz)
  have early := (orders R size).first i (i+1) (by omega) lt
  have go : H R (earlier e.a.owner 0 e.b.owner 0) := by
    simpa only [e,cert,cell,node,si,sj] using early
  have f := R.flags y hy x hx
  have finish := end_flag R hy hx
  change endOfRow (system n) e.a = _ at finish
  have row : (system n).oddRow e.a.tag=odd y := by change (system n).oddRow (cell R y x).tag=_; rw [coordinates hy hx,f.2.2.2.2.1]
  have bot : (system n).bottom e.a.tag=decide (y+1=h) := by change (system n).bottom (cell R y x).tag=_; rw [coordinates hy hx,f.2.2.2.1]
  refine ⟨e,congrArg owner si,congrArg mate si,congrArg owner sj,congrArg mate sj,readA,readB,
    local_grid R size hy hx v z,?_⟩
  rcases next with ⟨par,rows,cols⟩|⟨par,rows,prev⟩|⟨rows,cols,endRow⟩
  · subst v; subst z
    have st : endOfRow (system n) e.a=false := by rw [finish]; simp [par,show x+1≠w by omega]
    simp only [chosenSuccessor,st,Bool.false_and,Bool.false_eq_true,if_false,row,par]
    exact ⟨rfl,go⟩
  · subst v
    have st : endOfRow (system n) e.a=false := by rw [finish]; simp [par,show x≠0 by omega]
    have pred : x-1=z := by omega
    simp only [chosenSuccessor,st,Bool.false_and,Bool.false_eq_true,if_false,row,par,if_true]
    exact ⟨by change cell R y (x-1) = cell R y z; rw [pred],go⟩
  · subst v; subst z
    have st : endOfRow (system n) e.a=true := by
      cases par : odd y <;> simp [rowEnd,par] at endRow <;> rw [finish] <;> simp [par,endRow]
    have nb : (system n).bottom e.a.tag=false := by rw [bot]; simp [show y+1≠h by omega]
    simp only [chosenSuccessor,st,nb,Bool.true_and,Bool.false_eq_true,if_false,if_true]
    exact ⟨rfl,go⟩

theorem wrap_grid (R : Rectangle M w h) (size : 1<w*h) :
    At (widthCode n+16) (allowed M) (system n) (zero R) (w*h-1) 0 := by
  obtain ⟨y,hy,x,hx,bottom,endRow,si⟩ := last_cell (show 0<w*h by omega)
  let e := cert R y x 0 0
  have top := R.positiveH; have left := R.positiveW
  have f := R.flags y hy x hx
  have z := R.flags 0 top 0 left
  have first := first_id w
  have readA : H R (typedNode e.a) := cell_typed R size (id_bound hy hx)
  have readB : H R (typedNode e.b) := cell_typed R size (id_bound top left)
  have st : endOfRow (system n) e.a=true := by
    change endOfRow (system n) (cell R y x)=true; rw [end_flag R hy hx]
    cases par : odd y <;> simp [rowEnd,par] at endRow <;> simp [par,endRow]
  have bot : (system n).bottom e.a.tag=true := by
    change (system n).bottom (cell R y x).tag = true; rw [coordinates hy hx,f.2.2.2.1]; simp [bottom]
  have boundI := id_bound hy hx
  have boundJ := id_bound top left
  have ne : idAt w y x ≠ idAt w 0 0 := by rw [si,first]; omega
  have active : H R (orientedPort 4 e.a e.b) := by
    apply (port size (orders R size) (4 : Fin 5) boundI boundJ ne).mpr
    exact (wrap_edge ..).mpr ⟨si,first⟩
  have go : H R (earlier e.b.owner 0 e.a.owner 0) := by
    apply (orders R size).first _ _ _ boundI
    rw [first,si]; omega
  refine ⟨e,congrArg owner si,congrArg mate si,congrArg owner first,congrArg mate first,
    readA,readB,local_grid R size hy hx 0 0,?_⟩
  simp only [chosenSuccessor,st,bot,Bool.true_and,if_true,allQ,Holds]
  refine ⟨?_,.inl active,go,True.intro⟩
  change ((system n).top (cell R 0 0).tag && (system n).left (cell R 0 0).tag &&
    !(system n).oddRow (cell R 0 0).tag && !(system n).oddColumn (cell R 0 0).tag)=true
  rw [coordinates top left,z.1,z.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2]
  decide

noncomputable def data (R : Rectangle M w h) (size : 1<w*h) :
    Data (widthCode n+16) (allowed M) (system n) (w*h) (middle h w (widthCode n) (labels R)) (tail (w*h)) :=
  ⟨literal_phases R size,P455CellClassPadded.names size _ _,P455CellClass.canonical_final _,
    small_slots size _ _,functional size (orders R size),fun _ hi => next_grid R size hi,fun _ => wrap_grid R size⟩

/-- One fixed monoid for every padding. The only input is an accepting
    finite-table run with the stated stationary last update and proper
    initial markers. No existential word layout, query or identity is
    supplied by the caller. -/
theorem no_basis_of_run {s : Nat} (run : Run M w s) (basis : List (List Nat × List Nat))
    (sound : ∀ u v, (u,v) ∈ basis → (P455FullSingleton.model (widthCode n+16) (allowed M) (system n)).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (P455FullSingleton.model (widthCode n+16) (allowed M) (system n)).Valid U V ∧
      ¬ P455FirstRewrite.Derives (fun u v => (u,v) ∈ basis) U V := by
  apply P455CellClassClean.no_basis (by omega) _ basis sound
  intro k
  obtain ⟨height,_,big,⟨R⟩⟩ := unbounded run (k+2)
  have size : 1<w*height := by omega
  exact ⟨w*height,middle height w (widthCode n) (labels R),tail (w*height),by omega,⟨data R size⟩⟩

end P455CellClassHalting
