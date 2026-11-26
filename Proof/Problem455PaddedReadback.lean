import Problem455PaddedTiles




namespace P455PaddedTiles
open P455Witness
variable {n w h : Nat} {M : MachineTable n}

private theorem clip {v : Nat} (hv : 0<v) (k : Nat) : min k (v-1)<v := by
  have := Nat.min_le_right k (v-1)
  omega

noncomputable def readTile (R : Rectangle M w h) (y x : Nat) : Tile n :=
  (R.eligible (min y (h-1)) (clip R.positiveH _) (min x (w-1)) (clip R.positiveW _)).choose

theorem read_tile_data (R : Rectangle M w h) (y x : Nat) (hy : y<h) (hx : x<w) :
    code (readTile R y x)=R.tag y x ∧ Admitted M (readTile R y x) := by
  have d := (R.eligible (min y (h-1)) (clip R.positiveH _) (min x (w-1)) (clip R.positiveW _)).choose_spec
  refine ⟨?_,d.2⟩
  change code (readTile R y x) = R.tag (min y (h-1)) (min x (w-1)) ∧ _ at d
  simpa only [Nat.min_eq_left (by omega : y≤h-1),Nat.min_eq_left (by omega : x≤w-1)] using d.1

private theorem read_flags (R : Rectangle M w h) (y x : Nat) (hy : y<h) (hx : x<w) :
    (readTile R y x).left=decide (x=0) ∧ (readTile R y x).right=decide (x+1=w) ∧
    (readTile R y x).top=decide (y=0) ∧ (readTile R y x).bottom=decide (y+1=h) := by
  have f := R.flags y hy x hx
  rw [← (read_tile_data R y x hy hx).1] at f
  exact ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1⟩

theorem read_horizontal (R : Rectangle M w h) (y x : Nat) (hy : y<h) (hx : x+1<w) :
    Horizontal (readTile R y x) (readTile R y (x+1)) := by
  obtain ⟨a,b,pa,pb,H⟩ := R.right y hy x hx
  have ea := code_inj (pa.trans (read_tile_data R y x hy (by omega)).1.symm)
  have eb := code_inj (pb.trans (read_tile_data R y (x+1) hy hx).1.symm)
  simpa only [ea,eb] using H

theorem read_vertical (R : Rectangle M w h) (y x : Nat) (hy : y+1<h) (hx : x<w) :
    Vertical (readTile R y x) (readTile R (y+1) x) := by
  obtain ⟨a,b,pa,pb,V⟩ := R.down y hy x hx
  have ea := code_inj (pa.trans (read_tile_data R y x (by omega) hx).1.symm)
  have eb := code_inj (pb.trans (read_tile_data R (y+1) x hy hx).1.symm)
  simpa only [ea,eb] using V

noncomputable def centers (R : Rectangle M w h) (y x : Nat) := (readTile R y x).c

theorem read_triple (R : Rectangle M w h) (y x : Nat) (hy : y<h) (hx : x<w) :
    (readTile R y x).l=leftAt (centers R y) x ∧
    (readTile R y x).r=rightAt (centers R y) w x := by
  have d := (read_tile_data R y x hy hx).2
  have f := read_flags R y x hy hx
  constructor
  · by_cases e : x=0
    · have b := d.2.1.symm.trans f.1
      simp [e] at b
      simpa [leftAt,e] using b
    · have p := (read_horizontal R y (x-1) hy (by omega)).2.2.2.2.2.2.1
      simpa [leftAt,e,centers,show x-1+1=x by omega] using p
  · by_cases e : x+1=w
    · have b := d.2.2.1.symm.trans f.2.1
      simp [e] at b
      simpa [rightAt,e] using b
    · have p := (read_horizontal R y x hy (by omega)).2.2.2.2.2.2.2
      simpa [rightAt,e,centers] using p

/-- A trace on w cells, ending with the accepting center at its leftmost
cell. Stuttering beyond the last row uses the specific machine table. -/
structure AcceptingTrace (M : MachineTable n) (w s : Nat) where
  positive : 0<w
  rows : Nat → Nat → Fin n
  start : ∀ x, x<w → rows 0 x = M.initial (decide (x=0))
  marks : ∀ y, y≤s → ∀ x, x<w → M.marker (rows y x)=decide (x=0)
  steps : ∀ y, y<s → ∀ x, x<w →
    M.next (leftAt (rows y) x) (rows y x) (rightAt (rows y) w x)=some (rows (y+1) x)
  accept : rows s 0=M.accept

noncomputable def read_trace (R : Rectangle M w h) : AcceptingTrace M w (h-1) where
  positive := R.positiveW
  rows := centers R
  start := by
    intro x hx
    have d := (read_tile_data R 0 x R.positiveH hx).2
    have f := read_flags R 0 x R.positiveH hx
    exact ((d.2.2.2.2.2.1 (by simpa using f.2.2.1)).2).trans (congrArg M.initial f.1)
  marks := by
    intro y hy x hx
    have lt : y<h := by have := R.positiveH; omega
    exact (read_tile_data R y x lt hx).2.2.2.2.1.trans (read_flags R y x lt hx).1
  steps := by
    intro y hy x hx
    have lt : y<h := by omega
    have upd := (read_tile_data R y x lt hx).2.1
    have triple := read_triple R y x lt hx
    rw [triple.1,triple.2] at upd
    exact upd.trans (congrArg some (read_vertical R y x (by omega) hx).2.2.2.2.2.2)
  accept := by
    have hy : h-1<h := by have := R.positiveH; omega
    have e : h-1+1=h := by have := R.positiveH; omega
    have f := read_flags R (h-1) 0 hy R.positiveW
    exact (read_tile_data R (h-1) 0 hy R.positiveW).2.2.2.2.2.2.2
      (by simpa [e] using f.2.2.2) (by simpa using f.1)

theorem trace_iff_rectangles
    (stationary : ∀ {w s}, (T : AcceptingTrace M w s) → ∀ x, x<w →
      M.next (leftAt (T.rows s) x) (T.rows s x) (rightAt (T.rows s) w x)=some (T.rows s x)) :
    (∃ w s, Nonempty (AcceptingTrace M w s)) ↔
      (∃ w, ∀ k, ∃ h, 1<h ∧ k<2*(w*h) ∧ Nonempty (Rectangle M w h)) := by
  constructor
  · rintro ⟨w,s,⟨t⟩⟩
    let r : Run M w s := ⟨t.positive,t.rows,t.start,t.marks,t.steps,t.accept,stationary t⟩
    exact ⟨w,unbounded r⟩
  · rintro ⟨w,rects⟩
    obtain ⟨h,_,_,⟨r⟩⟩ := rects 0
    exact ⟨w,h-1,⟨read_trace r⟩⟩

end P455PaddedTiles
