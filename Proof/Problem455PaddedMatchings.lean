import Problem455PaddedPorts
import Problem455PaddedTiles



namespace P455PaddedMatchings
open P455PaddedPorts P455PaddedTiles

def idAt (w y x : Nat) := w*y + (if odd y then w-1-x else x)

private theorem offset_lt {w x : Nat} (y : Nat) (hx : x<w) :
    (if odd y then w-1-x else x)<w := by split <;> omega

theorem id_inj {w y x z q : Nat} (hx : x<w) (hq : q<w) (eq : idAt w y x=idAt w z q) :
    y=z ∧ x=q := by
  have wt : 0<w := by omega
  have div := congrArg (· / w) eq
  simp only [idAt,Nat.mul_add_div wt,Nat.div_eq_of_lt (offset_lt y hx),
    Nat.div_eq_of_lt (offset_lt z hq),Nat.add_zero] at div
  subst z
  simp only [idAt,Nat.add_left_cancel_iff] at eq
  split at eq <;> omega

theorem id_bound {w h y x : Nat} (hy : y<h) (hx : x<w) : idAt w y x < w*h := by
  have le := Nat.mul_le_mul_left w (show y+1≤h by omega)
  rw [Nat.mul_add,Nat.mul_one] at le
  have off := offset_lt y hx
  unfold idAt; omega

theorem id_covers {w h i : Nat} (lt : i<w*h) :
    ∃ y<h, ∃ x<w, idAt w y x=i := by
  have wpos : 0<w := by
    cases w with
    | zero => simp at lt
    | succ => omega
  let y := i/w
  let j := i%w
  have jo : j<w := Nat.mod_lt _ wpos
  have ex := Nat.mod_add_div i w
  have yl : y<h := by
    by_cases e : y<h
    · exact e
    · have mul := Nat.mul_le_mul_left w (show h≤y by omega)
      change w*h≤w*(i/w) at mul
      omega
  refine ⟨y,yl,if odd y then w-1-j else j,offset_lt y jo,?_⟩
  unfold idAt
  by_cases e : odd y=true
  · simp [e]
    have z : w-1-(w-1-j)=j := by omega
    rw [z]
    dsimp [y,j]; omega
  · simp [e]
    dsimp [y,j]; omega

def pairs (f : Nat → Nat) (start : Nat) : Nat → List Block
  | 0 => []
  | 1 => [.single (f start)]
  | n+2 => .pair (f start) (f (start+1)) :: pairs f (start+2) n

def line (skip : Bool) (f : Nat → Nat) (size : Nat) :=
  if skip then match size with
    | 0 => []
    | k+1 => .single (f 0) :: pairs f 1 k
  else pairs f 0 size

private theorem pair_cells (f : Nat→Nat) (s n : Nat) :
    (pairs f s n).flatMap cells = (List.range' s n).map f := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n =>
        simp [pairs,cells,ih n (by omega) (s+2),List.range'_succ]

theorem line_cells (skip : Bool) (f : Nat→Nat) (n : Nat) :
    (line skip f n).flatMap cells=(List.range n).map f := by
  cases skip
  · simp [line,pair_cells,List.range_eq_range']
  · cases n with
    | zero => rfl
    | succ n => simp [line,cells,pair_cells,List.range_eq_range',List.range'_succ]

private theorem pair_edge (f : Nat → Nat) (s n a b : Nat) :
    Block.pair a b ∈ pairs f s n ↔
      ∃ k, k+1<n ∧ k%2=0 ∧ a=f (s+k) ∧ b=f (s+k+1) := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases n with
    | zero => simp [pairs]
    | succ n => cases n with
      | zero => simp [pairs]
      | succ n =>
        simp only [pairs,List.mem_cons,Block.pair.injEq]
        rw [ih n (by omega)]
        constructor
        · rintro (⟨ea,eb⟩|⟨k,lt,par,ea,eb⟩)
          · exact ⟨0,by omega,rfl,by simpa using ea,by simpa using eb⟩
          · exact ⟨k+2,by omega,by omega,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ea,
              by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using eb⟩
        · rintro ⟨k,lt,par,ea,eb⟩
          by_cases e : k=0
          · subst k; exact .inl ⟨by simpa using ea,by simpa using eb⟩
          · have kk : s+2+(k-2)=s+k := by omega
            exact .inr ⟨k-2,by omega,by omega,by simpa only [kk] using ea,by simpa only [kk] using eb⟩

theorem line_edge (skip : Bool) (f : Nat→Nat) (size a b : Nat) :
    Block.pair a b ∈ line skip f size ↔
      ∃ k, k+1<size ∧ odd k=skip ∧ a=f k ∧ b=f (k+1) := by
  cases skip
  · simp only [line,Bool.false_eq_true,if_false,pair_edge,Nat.zero_add]
    constructor
    · rintro ⟨k,lt,p,u,v⟩; exact ⟨k,lt,by simp [odd,p],u,v⟩
    · rintro ⟨k,lt,p,u,v⟩; exact ⟨k,lt,by simp [odd] at p; omega,u,v⟩
  · cases size with
    | zero => simp [line]
    | succ n =>
      simp only [line,if_true,List.mem_cons,Block.noConfusion,reduceCtorEq,false_or,pair_edge]
      constructor
      · rintro ⟨k,lt,p,u,v⟩
        refine ⟨k+1,by omega,?_,?_,?_⟩
        · simp [odd,show (k+1)%2=1 by omega]
        · simpa [Nat.add_comm] using u
        · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using v
      · rintro ⟨k,lt,p,u,v⟩; simp [odd] at p
        exact ⟨k-1,by omega,by omega,by simpa [show 1+(k-1)=k by omega] using u,
          by simpa [show 1+(k-1)=k by omega] using v⟩

def lines (m n : Nat) (skip : Bool) (f : Nat→Nat→Nat) :=
  (List.range m).flatMap fun z=>line skip (f z) n

private theorem flatten_lines (m n : Nat) (skip : Bool) (f : Nat→Nat→Nat) :
    (lines m n skip f).flatMap cells=(List.range m).flatMap (fun z=>(List.range n).map (f z)) := by
  simp [lines,List.flatMap_assoc,line_cells]

theorem lines_unique (m n : Nat) (skip : Bool) (f : Nat→Nat→Nat)
    (inj : ∀ z<m, ∀ x<n, ∀ t<m, ∀ j<n, f z x=f t j → z=t ∧ x=j) :
    ((lines m n skip f).flatMap cells).Nodup := by
  rw [flatten_lines]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro z hz
    apply List.pairwise_map.mpr
    exact List.nodup_range.imp_of_mem (fun hx hj ne eq => ne
      (inj z (List.mem_range.mp hz) _ (List.mem_range.mp hx) z (List.mem_range.mp hz) _ (List.mem_range.mp hj) eq).2)
  · apply List.nodup_range.imp_of_mem
    intro z t hz ht ne a ha b hb eq
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    exact ne (inj z (List.mem_range.mp hz) x (List.mem_range.mp hx) t (List.mem_range.mp ht) j (List.mem_range.mp hj) eq).1

def horizontal (h w : Nat) (skip : Bool) := lines h w skip (idAt w)
def vertical (h w : Nat) (skip : Bool) := lines w h skip (fun x y=>idAt w y x)

theorem horizontal_unique (h w : Nat) (skip : Bool) :
    ((horizontal h w skip).flatMap cells).Nodup :=
  lines_unique _ _ _ _ (fun _ _ _ hx _ _ _ hj eq=>id_inj hx hj eq)

theorem vertical_unique (h w : Nat) (skip : Bool) :
    ((vertical h w skip).flatMap cells).Nodup :=
  lines_unique _ _ _ _ (fun _ hx _ _ _ hj _ _ eq=>And.symm (id_inj hx hj eq))

theorem horizontal_cells (h w i : Nat) (skip : Bool) :
    i∈(horizontal h w skip).flatMap cells ↔ i<w*h := by
  rw [horizontal,flatten_lines]
  constructor
  · intro m; obtain ⟨y,hy,mx⟩ := List.mem_flatMap.mp m
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mx
    exact id_bound (List.mem_range.mp hy) (List.mem_range.mp hx)
  · intro lt; obtain ⟨y,hy,x,hx,eq⟩ := id_covers lt
    exact List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hy,List.mem_map.mpr ⟨x,List.mem_range.mpr hx,eq⟩⟩

theorem vertical_cells (h w i : Nat) (skip : Bool) :
    i∈(vertical h w skip).flatMap cells ↔ i<w*h := by
  rw [vertical,flatten_lines]
  constructor
  · intro m; obtain ⟨x,hx,my⟩ := List.mem_flatMap.mp m
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp my
    exact id_bound (List.mem_range.mp hy) (List.mem_range.mp hx)
  · intro lt; obtain ⟨y,hy,x,hx,eq⟩ := id_covers lt
    exact List.mem_flatMap.mpr ⟨x,List.mem_range.mpr hx,List.mem_map.mpr ⟨y,List.mem_range.mpr hy,eq⟩⟩

theorem horizontal_edge (h w a b : Nat) (skip : Bool) :
    Block.pair a b∈horizontal h w skip ↔
      ∃ y<h, ∃ x, x+1<w ∧ odd x=skip ∧ a=idAt w y x ∧ b=idAt w y (x+1) := by
  simp [horizontal,lines,List.mem_flatMap,line_edge]

theorem vertical_edge (h w a b : Nat) (skip : Bool) :
    Block.pair a b∈vertical h w skip ↔
      ∃ x<w, ∃ y, y+1<h ∧ odd y=skip ∧ a=idAt w y x ∧ b=idAt w (y+1) x := by
  simp [vertical,lines,List.mem_flatMap,line_edge]

def wrap (t : Nat) : List Block :=
  .pair (t-1) 0 :: ((List.range t).filter fun i=>0<i && i<t-1).map Block.single

theorem wrap_edge (t a b : Nat) : Block.pair a b ∈ wrap t ↔ a=t-1 ∧ b=0 := by
  simp [wrap,List.mem_map]

private theorem flatten_singles (xs : List Nat) : (xs.map Block.single).flatMap cells=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [cells,ih]

theorem wrap_unique {t : Nat} (ht : 1<t) : ((wrap t).flatMap cells).Nodup := by
  simp only [wrap,List.flatMap_cons,cells,flatten_singles,List.cons_append,List.nil_append]
  simp [List.nodup_cons,show t-1≠0 by omega]
  exact List.Pairwise.filter _ List.nodup_range

theorem wrap_cells {t : Nat} (ht : 1<t) (i : Nat) : i∈(wrap t).flatMap cells ↔ i<t := by
  simp only [wrap,List.flatMap_cons,cells,flatten_singles,List.cons_append,List.nil_append,List.mem_cons,List.mem_filter,
    List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
  omega

end P455PaddedMatchings
