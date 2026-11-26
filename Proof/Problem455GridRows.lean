import Problem455EdgeProduct



namespace P455GridRows
open P455Witness P455Paths Problem455.Slots

/-- Horizontal and vertical compatible tile pairs obey the flags in the
    machine construction. The bare `Tiles` structure does not impose them. -/
structure Laws (ts : Tiles) : Prop where
  horiz : ∀ a b, ts.horizontal a b →
    ts.right a=false ∧ ts.left b=false ∧ ts.top a=ts.top b ∧
    ts.bottom a=ts.bottom b ∧ ts.oddRow a=ts.oddRow b ∧ ts.oddColumn b= !ts.oddColumn a
  vert : ∀ a b, ts.vertical a b →
    ts.bottom a=false ∧ ts.top b=false ∧ ts.left b=ts.left a ∧
    ts.right b=ts.right a ∧ ts.oddColumn b=ts.oddColumn a ∧ ts.oddRow b= !ts.oddRow a

def Arrow (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) (ts : Tiles) (e : EdgeCertificate) :=
  Holds r allow mark w (typedNode e.a) ∧ Holds r allow mark w (typedNode e.b) ∧
  Holds r allow mark w (localCert ts e) ∧ Holds r allow mark w (chosenSuccessor ts e)

def Functional (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) (ts : Tiles) (a : Node) :=
  ∀ (d : Dir) (b c : Node), Holds r allow mark w (neighbor ts a b d) →
    Holds r allow mark w (neighbor ts a c d) → b=c

private theorem active {r allow mark w q b} (h : Holds r allow mark w (flagQ (!b) q))
    (off : b=false) : Holds r allow mark w q := by simpa only [off,Bool.not_false,flagQ,if_true] using h

/-- The diagonal must be the down-neighbor of the already visited right-hand
    upper cell. No functionality on either of the two proposed lower cells. -/
theorem descend_pair {r allow mark w ts} (law : Laws ts) (x y : EdgeCertificate)
    (hX : Holds r allow mark w (localCert ts x)) (hY : Holds r allow mark w (localCert ts y))
    (fx : Functional r allow mark w ts x.a) (fy : Functional r allow mark w ts y.a)
    (edge : Holds r allow mark w (rightward ts x.a y.a)) (nb : ts.bottom x.a.tag=false) :
    Holds r allow mark w (downward ts x.a x.down) ∧
    Holds r allow mark w (downward ts y.a y.down) ∧
    Holds r allow mark w (rightward ts x.down y.down) := by
  have lawH := law.horiz _ _ edge.1
  have nr := lawH.1
  have ny : ts.bottom y.a.tag=false := lawH.2.2.2.1.symm.trans nb
  have square : Holds r allow mark w (downward ts x.right x.diagonal) ∧
      Holds r allow mark w (rightward ts x.down x.diagonal) := by
    simpa [flagQ,nr,nb,Holds] using hX.2.2.2.2.1
  have toY := fx .right x.right y.a (active hX.1 nr) edge
  have downY := active hY.2.2.1 ny
  have d : x.diagonal = y.down := fy .down _ _ (toY ▸ square.1) downY
  exact ⟨active hX.2.2.1 nb,downY,d ▸ square.2⟩

theorem enters_down {r allow mark w ts} (e : EdgeCertificate) (arr : Arrow r allow mark w ts e)
    (endRow : endOfRow ts e.a = true) (notBottom : ts.bottom e.a.tag = false) : e.b = e.down := by
  have suc := arr.2.2.2
  simp only [chosenSuccessor,endRow,notBottom,Bool.and_false,Bool.false_eq_true,if_false,if_true] at suc
  exact suc.1.symm

private theorem goes_right {r allow mark w ts} (e : EdgeCertificate) (arr : Arrow r allow mark w ts e)
    (odd : ts.oddRow e.a.tag=false) (right : ts.right e.a.tag=false) :
    Holds r allow mark w (rightward ts e.a e.b) := by
  have endRow : endOfRow ts e.a = false := by simp [endOfRow,odd,right]
  have suc := arr.2.2.2
  simp only [chosenSuccessor,endRow,Bool.false_and,Bool.false_eq_true,if_false,odd] at suc
  exact suc.1 ▸ active arr.2.2.1.1 right

private theorem goes_left {r allow mark w ts} (e : EdgeCertificate) (arr : Arrow r allow mark w ts e)
    (odd : ts.oddRow e.a.tag=true) (left : ts.left e.a.tag=false) :
    Holds r allow mark w (rightward ts e.b e.a) := by
  have endRow : endOfRow ts e.a = false := by simp [endOfRow,odd,left]
  have suc := arr.2.2.2
  simp only [chosenSuccessor,endRow,Bool.false_and,Bool.false_eq_true,if_false,odd,if_true] at suc
  exact suc.1 ▸ active arr.2.2.1.2.1 left

/-- An arbitrary candidate row is forced onto the cycle once its first cell
    is known to lie there. Induction obtains functionality from the trace
    before identifying its next cell. Width one is n=0. -/
theorem trace_row {r allow mark w ts} (law : Laws ts) (atCell : Nat → EdgeCertificate)
    (arrow : ∀ i, Arrow r allow mark w ts (atCell i))
    (continuous : ∀ i, (atCell i).b=(atCell (i+1)).a)
    (functional : ∀ i, Functional r allow mark w ts (atCell i).a)
    (row : Nat → Node) (n start : Nat) (odd : Bool)
    (init : (atCell start).a=row 0)
    (rowOdd : ∀ j, j≤n → ts.oddRow (row j).tag=odd)
    (links : ∀ j, j<n → Holds r allow mark w
      (if odd then rightward ts (row (j+1)) (row j) else rightward ts (row j) (row (j+1)))) :
    ∀ j, j≤n → (atCell (start+j)).a=row j := by
  intro j
  induction j with
  | zero => intro _; exact init
  | succ j ih =>
    intro le
    have here := ih (by omega)
    have p : ts.oddRow (atCell (start+j)).a.tag=odd := here ▸ rowOdd j (by omega)
    have one := links j (by omega)
    have eq : (atCell (start+j)).b=row (j+1) := by
      cases odd with
      | false =>
        have R : Holds r allow mark w (rightward ts (atCell (start+j)).a (row (j+1))) := here ▸ one
        have next := goes_right _ (arrow (start+j)) p (law.horiz _ _ R.1).1
        exact functional _ .right _ _ next R
      | true =>
        have L : Holds r allow mark w (rightward ts (row (j+1)) (atCell (start+j)).a) := here ▸ one
        have next := goes_left _ (arrow (start+j)) p (law.horiz _ _ L.1).2.1
        exact functional _ .left _ _ next L
    exact (continuous _).symm.trans eq

/-- Positive left-to-right ordering of a nonbottom upper row; its cells are
    given by positions in the trace. This yields the entire lower right chain
    and its vertical links, even before the new row is known to be on the trace. -/
theorem lower_row {r allow mark w ts} (law : Laws ts) (atCell : Nat → EdgeCertificate)
    (arrow : ∀ i, Arrow r allow mark w ts (atCell i))
    (functional : ∀ i, Functional r allow mark w ts (atCell i).a)
    (index : Nat → Nat) (n : Nat)
    (edges : ∀ j, j<n → Holds r allow mark w (rightward ts (atCell (index j)).a (atCell (index (j+1))).a))
    (nonbottom : ∀ j, j≤n → ts.bottom (atCell (index j)).a.tag=false) :
    (∀ j, j≤n → Holds r allow mark w (downward ts (atCell (index j)).a (atCell (index j)).down)) ∧
    (∀ j, j<n → Holds r allow mark w (rightward ts (atCell (index j)).down (atCell (index (j+1))).down)) := by
  refine ⟨fun j hj => active (arrow (index j)).2.2.1.2.2.1 (nonbottom _ hj),?_⟩
  intro j hj
  exact (descend_pair law _ _ (arrow _).2.2.1 (arrow _).2.2.1
    (functional _) (functional _) (edges j hj) (nonbottom j (by omega))).2.2


/-- Turn a directed indexed comparison in the actual word into a strict
    numerical rank. Every stamped occurrence appears in just one position. -/
private theorem idx_lt (a b : Event) (ls : List Event) (nd : ls.Nodup)
    (sub : [a,b].Sublist ls) : ls.idxOf a < ls.idxOf b := by
  induction ls with
  | nil => cases sub
  | cons x ls ih =>
    obtain ⟨fresh,distinct⟩ := List.nodup_cons.mp nd
    cases sub with
    | cons _ sub =>
      have hitA : a ∈ ls := sub.subset (by simp)
      have hitB : b ∈ ls := sub.subset (by simp)
      have xa : x ≠ a := fun eq => fresh (eq ▸ hitA)
      have xb : x ≠ b := fun eq => fresh (eq ▸ hitB)
      simpa only [List.idxOf_cons,cond_eq_if,beq_iff_eq,if_neg xa,if_neg xb,
        if_neg (Ne.symm xa),if_neg (Ne.symm xb),Nat.add_lt_add_iff_right] using ih distinct sub
    | cons₂ _ sub =>
      have hit : b ∈ ls := sub.subset List.mem_cons_self
      have ab : a ≠ b := fun eq => fresh (eq ▸ hit)
      simp [List.idxOf_cons,cond_eq_if,beq_iff_eq,ab,Ne.symm ab]

def position (w : W) (a : Node) := (events w).idxOf (a.owner,0)
def Return (ts : Tiles) (e : EdgeCertificate) :=
  endOfRow ts e.a && ts.bottom e.a.tag

theorem forward_increases {r allow mark w ts} (e : EdgeCertificate)
    (arr : Arrow r allow mark w ts e) (forward : Return ts e=false) :
    position w e.a < position w e.b := by
  have h := arr.2.2.2
  change (endOfRow ts e.a && ts.bottom e.a.tag)=false at forward
  simp only [chosenSuccessor,forward,Bool.false_eq_true,if_false] at h
  exact idx_lt _ _ _ (stamp_unique _ _) h.2.2

/-- On an indefinitely continued trace of genuine arrows (in particular a
    repeated directed cycle), a return occurs beyond every starting index. -/
theorem later_return {r allow mark w ts} (atCell : Nat → EdgeCertificate)
    (arrow : ∀ i, Arrow r allow mark w ts (atCell i))
    (continuous : ∀ i, (atCell i).b=(atCell (i+1)).a) (start : Nat) :
    ∃ offset, Return ts (atCell (start+offset))=true := by
  apply Classical.byContradiction
  intro none
  have forward (j) : Return ts (atCell (start+j))=false := by
    cases e : Return ts (atCell (start+j)) with
    | false => rfl
    | true => exact (none ⟨j,e⟩).elim
  have grows (j) : j ≤ position w (atCell (start+j)).a := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have inc := forward_increases _ (arrow _) (forward j)
      rw [continuous] at inc
      exact Nat.lt_of_le_of_lt ih inc
  have impossible := grows ((events w).length+1)
  have bound (z : Event) : (events w).idxOf z ≤ (events w).length := by
    by_cases h : z ∈ events w
    · exact Nat.le_of_lt (List.idxOf_lt_length h)
    · exact Nat.le_of_eq (List.idxOf_eq_length h)
  have c := bound ((atCell (start+((events w).length+1))).a.owner,0)
  unfold position at impossible
  omega

theorem return_target {r allow mark w ts} (e : EdgeCertificate) (arr : Arrow r allow mark w ts e)
    (back : Return ts e=true) :
    ts.top e.b.tag=true ∧ ts.left e.b.tag=true ∧ ts.oddRow e.b.tag=false ∧ ts.oddColumn e.b.tag=false := by
  have h := arr.2.2.2
  change (endOfRow ts e.a && ts.bottom e.a.tag)=true at back
  simp only [chosenSuccessor,back,if_true] at h
  simpa [and_assoc] using h.1

/-- Column reached after j snake steps in a row with last column n. -/
def column (n : Nat) (odd : Bool) (j : Nat) := if odd then n-j else j

/-- Descend from the traveled end of a nonbottom row, reverse direction, and
    identify each prospective cell in the lower row with its actual trace
    index. Only the old row is initially known to be on the trace. -/
theorem advance_row {r allow mark w ts} (law : Laws ts) (atCell : Nat → EdgeCertificate)
    (arrow : ∀ i, Arrow r allow mark w ts (atCell i))
    (continuous : ∀ i, (atCell i).b=(atCell (i+1)).a)
    (functional : ∀ i, Functional r allow mark w ts (atCell i).a)
    (index : Nat → Nat) (n : Nat) (odd : Bool)
    (edges : ∀ j, j<n → Holds r allow mark w (rightward ts (atCell (index j)).a (atCell (index (j+1))).a))
    (nonbottom : ∀ j, j≤n → ts.bottom (atCell (index j)).a.tag=false)
    (parity : ∀ j, j≤n → ts.oddRow (atCell (index j)).a.tag=odd)
    (left : ts.left (atCell (index 0)).a.tag=true) (right : ts.right (atCell (index n)).a.tag=true) :
    let last := column n (!odd) 0
    let start := index last+1
    ∀ j, j≤n → (atCell (start+column n (!odd) j)).a=(atCell (index j)).down := by
  let last := column n (!odd) 0
  let start := index last+1
  let row (j : Nat) := (atCell (index (column n (!odd) j))).down
  have lastBound : last≤n := by cases odd <;> simp [last,column]
  have ending : endOfRow ts (atCell (index last)).a=true := by
    rw [endOfRow,parity last lastBound]
    cases odd <;> simp_all only [last,column,Bool.not_false,Bool.not_true,if_true,
      Bool.false_eq_true,if_false,Nat.sub_zero]
  obtain ⟨v,h⟩ := lower_row law atCell arrow functional index n edges nonbottom
  have init : (atCell start).a=row 0 :=
    (continuous _).symm.trans (enters_down _ (arrow _) ending (nonbottom _ lastBound))
  have rowOdd (j) (le : j≤n) : ts.oddRow (row j).tag= !odd := by
    have c : column n (!odd) j ≤ n := by cases odd <;> simp [column,le,Nat.sub_le]
    exact (law.vert _ _ (v _ c).1).2.2.2.2.2.trans (congrArg Bool.not (parity _ c))
  have adjacent (j) (le : j<n) : Holds r allow mark w
      (if !odd then rightward ts (row (j+1)) (row j) else rightward ts (row j) (row (j+1))) := by
    cases odd with
    | true => exact h j le
    | false =>
      have u := h (n-(j+1)) (by omega)
      have ix : n-(j+1)+1=n-j := by omega
      simpa only [row,column,Bool.not_false,if_true,ix] using u
  have trace := trace_row law atCell arrow continuous functional row n start (!odd) init rowOdd adjacent
  dsimp only
  intro j le
  have c : column n (!odd) j ≤ n := by cases odd <;> simp [column,le,Nat.sub_le]
  have twice : column n (!odd) (column n (!odd) j)=j := by cases odd <;> simp [column] <;> omega
  simpa only [row,twice,start,last] using trace (column n (!odd) j) c

end P455GridRows
