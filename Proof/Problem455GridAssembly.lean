import Problem455GridRows



namespace P455GridAssembly
open P455GridRows P455Witness Problem455.Slots
abbrev W := List Nat

structure Rectangle (allow : Tag → Prop) (ts : Tiles) where
  height : Nat
  width : Nat
  tile : Nat → Nat → Tag
  allowed : ∀ i j, i ≤ height → j ≤ width → allow (tile i j)
  horiz : ∀ i j, i ≤ height → j < width → ts.horizontal (tile i j) (tile i (j+1))
  vert : ∀ i j, i < height → j ≤ width → ts.vertical (tile i j) (tile (i+1) j)
  left : ∀ i j, i ≤ height → j ≤ width → (ts.left (tile i j) = true ↔ j=0)
  right : ∀ i j, i ≤ height → j ≤ width → (ts.right (tile i j) = true ↔ j=width)
  top : ∀ i j, i ≤ height → j ≤ width → (ts.top (tile i j) = true ↔ i=0)
  bottom : ∀ i j, i ≤ height → j ≤ width → (ts.bottom (tile i j) = true ↔ i=height)

structure Row {r : Nat} {allow : Tag → Prop} {mark : Marking} {w : W} (ts : Tiles)
    (c : Nat → EdgeCertificate) (s n : Nat) (odd : Bool) : Prop where
  parity : ∀ j, j≤n → ts.oddRow (c (s+column n odd j)).a.tag=odd
  left : ts.left (c (s+column n odd 0)).a.tag=true
  right : ts.right (c (s+column n odd n)).a.tag=true
  links : ∀ j, j<n → Holds r allow mark w
    (rightward ts (c (s+column n odd j)).a (c (s+column n odd (j+1))).a)

private theorem min_bounded (p : Nat → Prop) (j : Nat) (yes : p j) :
    ∃ a, p a ∧ ∀ b, b<a → ¬ p b := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases e : ∃ k, k < j ∧ p k
    · obtain ⟨k,lt,ok⟩ := e
      exact ih k lt ok
    · exact ⟨j,yes,fun b lt pb => e ⟨b,lt,pb⟩⟩

private theorem right_step {r allow mark w ts} (c : Nat → EdgeCertificate)
    (arr : ∀ i, Arrow r allow mark w ts (c i)) (cont : ∀ i,(c i).b=(c (i+1)).a)
    (i : Nat) (p : ts.oddRow (c i).a.tag=false) (q : ts.right (c i).a.tag=false) :
    Holds r allow mark w (rightward ts (c i).a (c (i+1)).a) := by
  have ending : endOfRow ts (c i).a=false := by simp [endOfRow,p,q]
  have hs := (arr i).2.2.2
  simp only [chosenSuccessor,ending,Bool.false_and,Bool.false_eq_true,if_false,p] at hs
  have h := (arr i).2.2.1.1
  simp only [q,Bool.not_false,flagQ,if_true] at h
  rw [← cont, ← hs.1]
  exact h

private theorem first_row {r allow mark w ts} (law : Laws ts) (c : Nat → EdgeCertificate)
    (arr : ∀ i, Arrow r allow mark w ts (c i)) (cont : ∀ i,(c i).b=(c (i+1)).a)
    (s : Nat) (left : ts.left (c s).a.tag=true) (par : ts.oddRow (c s).a.tag=false) :
    ∃ n, @Row r allow mark w ts c s n false := by
  obtain ⟨j,ret⟩ := later_return c arr cont s
  have parity (a) (before : ∀ k, k<a → ts.right (c (s+k)).a.tag≠true) :
      ts.oddRow (c (s+a)).a.tag=false := by
    induction a with
    | zero => simpa using par
    | succ a ih =>
      have p := ih (fun k lt => before k (by omega))
      have q : ts.right (c (s+a)).a.tag=false := by
        have n := before a (by omega)
        cases b : ts.right (c (s+a)).a.tag <;> simp_all
      have step := right_step c arr cont (s+a) p q
      exact (law.horiz _ _ step.1).2.2.2.2.1.symm.trans p
  have hasRight : ∃ a, ts.right (c (s+a)).a.tag=true := by
    apply Classical.byContradiction; intro missing
    have noR (a) : ts.right (c (s+a)).a.tag≠true := fun ok => missing ⟨a,ok⟩
    have p := parity j (fun k _ => noR k)
    have q : ts.right (c (s+j)).a.tag=false := by
      cases b : ts.right (c (s+j)).a.tag <;> simp_all
    simp [Return,endOfRow,p,q] at ret
  obtain ⟨a,ha⟩ := hasRight
  obtain ⟨n,last,prior⟩ := min_bounded (fun i => ts.right (c (s+i)).a.tag=true) a ha
  refine ⟨n,?_,?_,?_,?_⟩
  · intro k le; exact parity k (fun b lt => prior b (by omega))
  · simpa [column] using left
  · exact last
  · intro k lt
    have p := parity k (fun b lb => prior b (by omega))
    have q : ts.right (c (s+k)).a.tag=false := by
      have off := prior k lt
      cases b : ts.right (c (s+k)).a.tag <;> simp_all
    exact right_step c arr cont (s+k) p q

private theorem row_const (n : Nat) (f : Nat → Bool) (step : ∀ j, j<n → f j = f (j+1)) :
    ∀ j, j≤n → f j = f 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => intro le; exact (step j (by omega)).symm.trans (ih (by omega))

private theorem next_row {r allow mark w ts} (law : Laws ts) (c : Nat → EdgeCertificate)
    (arr : ∀ i, Arrow r allow mark w ts (c i)) (cont : ∀ i,(c i).b=(c (i+1)).a)
    (funct : ∀ i, Functional r allow mark w ts (c i).a)
    {s n odd} (row : @Row r allow mark w ts c s n odd)
    (nonbottom : ∀ j, j≤n → ts.bottom (c (s+column n odd j)).a.tag=false) :
    @Row r allow mark w ts c (s+n+1) n (!odd) ∧
    ∀ j, j≤n → Holds r allow mark w
      (downward ts (c (s+column n odd j)).a (c ((s+n+1)+column n (!odd) j)).a) := by
  let ix (j : Nat) := s+column n odd j
  have tr := advance_row law c arr cont funct ix n odd row.links nonbottom row.parity row.left row.right
  have en : ix (column n (!odd) 0)=s+n := by cases odd <;> simp [ix,column]
  simp only [en] at tr
  obtain ⟨vs,hs⟩ := lower_row law c arr funct ix n row.links nonbottom
  have down (j : Nat) (le : j≤n) : Holds r allow mark w
      (downward ts (c (ix j)).a (c ((s+n+1)+column n (!odd) j)).a) := by
    rw [tr j le]; exact vs j le
  refine ⟨⟨?_,?_,?_,?_⟩,down⟩
  · intro j le
    exact (law.vert _ _ (down j le).1).2.2.2.2.2.trans (congrArg Bool.not (row.parity _ le))
  · exact (law.vert _ _ (down 0 (by omega)).1).2.2.1.trans row.left
  · exact (law.vert _ _ (down n (by omega)).1).2.2.2.1.trans row.right
  · intro j lt; rw [tr j (by omega),tr (j+1) (by omega)]; exact hs _ lt

/-- A suffix of a rectangle indexed by its specified first row. Only this
    first row may be top. Its actual top flag is supplied by the trace. -/
private structure Strip (allow : Tag → Prop) (ts : Tiles) (n : Nat) (first : Nat → Tag) where
  h : Nat
  t : Nat → Nat → Tag
  head : ∀ j, j≤n → t 0 j=first j
  ok : ∀ i j, i≤h → j≤n → allow (t i j)
  horizontal : ∀ i j, i≤h → j<n → ts.horizontal (t i j) (t i (j+1))
  vertical : ∀ i j, i<h → j≤n → ts.vertical (t i j) (t (i+1) j)
  l : ∀ i j, i≤h → j≤n → (ts.left (t i j)=true ↔ j=0)
  r : ∀ i j, i≤h → j≤n → (ts.right (t i j)=true ↔ j=n)
  b : ∀ i j, i≤h → j≤n → (ts.bottom (t i j)=true ↔ i=h)
  noTop : ∀ i j, 0<i → i≤h → j≤n → ts.top (t i j)=false

private theorem build {r allow mark w ts} (law : Laws ts) (c : Nat → EdgeCertificate)
    (arr : ∀ i, Arrow r allow mark w ts (c i)) (cont : ∀ i,(c i).b=(c (i+1)).a)
    (funct : ∀ i, Functional r allow mark w ts (c i).a)
    (J : Nat) (ret : Return ts (c J)=true) (fuel : Nat) :
    ∀ s n odd, s≤J → J-s≤fuel → @Row r allow mark w ts c s n odd →
    Nonempty (Strip allow ts n (fun j => (c (s+column n odd j)).a.tag)) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro s n odd bound time row
    let tag (j : Nat) := (c (s+column n odd j)).a.tag
    have ok (j : Nat) : allow (tag j) := (arr _).1.2.2.1
    have H (j) (lt : j<n) : ts.horizontal (tag j) (tag (j+1)) := (row.links j lt).1
    have L (j) (le : j≤n) : ts.left (tag j)=true ↔ j=0 := by
      cases j with
      | zero => simp [tag,row.left]
      | succ j => simp [(law.horiz _ _ (H j (by omega))).2.1]
    have R (j) (le : j≤n) : ts.right (tag j)=true ↔ j=n := by
      by_cases eq : j=n
      · subst j; simp [tag,row.right]
      · have lt : j<n := by omega
        simp [(law.horiz _ _ (H j lt)).1,eq]
    have B := row_const n (fun j => ts.bottom (tag j)) (fun j lt => (law.horiz _ _ (H j lt)).2.2.2.1)
    cases bot : ts.bottom (tag 0) with
    | true =>
      refine ⟨⟨0,fun _ => tag,fun _ _ => rfl,fun _ j _ _ => ok j,
        fun _ j _ lt => H j lt,fun _ _ lt _ => by omega,fun _ j _ => L j,
        fun _ j _ => R j,?_,fun _ _ pos le _ => by omega⟩⟩
      intro i j il jl
      have bi := (B j jl).trans bot
      simp [bi,Nat.le_zero.mp il]
    | false =>
      have nonbottom (j : Nat) (le : j≤n) : ts.bottom (tag j)=false := (B j le).trans bot
      have nextLe : s+n+1≤J := by
        apply Classical.byContradiction; intro short
        have small : J-s≤n := by omega
        let j := column n odd (J-s)
        have inRow : j≤n := by cases odd <;> simp [j,column,small,Nat.sub_le]
        have atJ : s+column n odd j=J := by cases odd <;> simp [j,column] <;> omega
        have off := nonbottom j inRow
        change ts.bottom (c (s+column n odd j)).a.tag=false at off
        rw [atJ] at off
        simp [Return,off] at ret
      obtain ⟨low,V⟩ := next_row law c arr cont funct row nonbottom
      obtain ⟨below⟩ := ih (J-(s+n+1)) (by omega) (s+n+1) n (!odd) nextLe (by omega) low
      let t : Nat → Nat → Tag
        | 0 => tag
        | i+1 => below.t i
      refine ⟨⟨below.h+1,t,fun _ _ => rfl,?_,?_,?_,?_,?_,?_,?_⟩⟩
      · intro i j le jl; cases i with
        | zero => exact ok j
        | succ i => exact below.ok i j (by omega) jl
      · intro i j le jl; cases i with
        | zero => exact H j jl
        | succ i => exact below.horizontal i j (by omega) jl
      · intro i j lt jl; cases i with
        | zero =>
          change ts.vertical (tag j) (below.t 0 j)
          rw [below.head _ jl]; exact (V j jl).1
        | succ i => exact below.vertical i j (by omega) jl
      · intro i j le jl; cases i with
        | zero => exact L j jl
        | succ i => exact below.l i j (by omega) jl
      · intro i j le jl; cases i with
        | zero => exact R j jl
        | succ i => exact below.r i j (by omega) jl
      · intro i j le jl; cases i with
        | zero => change ts.bottom (tag j)=true ↔ _; simp [nonbottom j jl]
        | succ i => exact (below.b i j (by omega) jl).trans (by omega)
      · intro i j pos le jl
        cases i with
        | zero => omega
        | succ i =>
          cases i with
          | zero =>
            change ts.top (below.t 0 j)=false
            rw [below.head _ jl]; exact (law.vert _ _ (V j jl).1).2.1
          | succ i => exact below.noTop _ j (by omega) (by omega) jl

/-- Any indefinitely continued trace of actual arrows, with directional
    functionality at each visited source, gives a positive legal rectangle.
    The hypotheses only concern the trace in the original word. -/
theorem rectangle_of_trace {r allow mark w ts} (law : Laws ts) (c : Nat → EdgeCertificate)
    (arr : ∀ i, Arrow r allow mark w ts (c i)) (cont : ∀ i,(c i).b=(c (i+1)).a)
    (funct : ∀ i, Functional r allow mark w ts (c i).a) : Nonempty (Rectangle allow ts) := by
  obtain ⟨k,ret⟩ := later_return c arr cont 0
  simp only [Nat.zero_add] at ret
  have start := return_target _ (arr k) ret
  rw [cont] at start
  let s := k+1
  obtain ⟨n,row⟩ := first_row law c arr cont s start.2.1 start.2.2.1
  obtain ⟨off,ending⟩ := later_return c arr cont s
  have tops := row_const n (fun j => ts.top (c (s+j)).a.tag)
    (fun j lt => (law.horiz _ _ (row.links j lt).1).2.2.1)
  obtain ⟨box⟩ := build law c arr cont funct (s+off) ending off s n false (by omega) (by omega) row
  refine ⟨⟨box.h,n,box.t,box.ok,box.horizontal,box.vertical,box.l,box.r,?_,box.b⟩⟩
  intro i j le jl
  cases i with
  | zero =>
    rw [box.head j jl]
    have same := (tops j jl).trans (by simpa [s] using start.1)
    simpa [column] using (show ts.top (c (s+j)).a.tag=true ↔ 0=0 from by simp [same])
  | succ i => simp [box.noTop _ j (by omega) le jl]

end P455GridAssembly
