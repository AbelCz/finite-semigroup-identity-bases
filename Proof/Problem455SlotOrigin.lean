import Problem455FactorSlots
import Problem455DonorInterval



namespace P455SlotOrigin
open Problem455.Slots

theorem event_bounds (n : Nat → Nat) (w : Word) (a j : Nat)
    (hj : (a,j) ∈ stamp n w) : n a ≤ j ∧ j < n a + w.count a := by
  induction w generalizing n with
  | nil => simp [stamp] at hj
  | cons b w ih =>
    rcases List.mem_cons.mp hj with he | he
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      simp [List.count_cons]
    · have h := ih (advance n [b]) he
      simp only [advance, List.count_cons, List.count_nil] at *
      omega

/-- The i-th (zero-based) occurrence exists exactly when the count exceeds i.
    This direction supplies a literal cut with its prefix count. -/
theorem occurrence_cut (w : Word) (x i : Nat) (hi : i < w.count x) :
    ∃ l t, w = l ++ x :: t ∧ l.count x = i := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    by_cases h : a = x
    · subst a
      cases i with
      | zero => exact ⟨[],w,rfl,rfl⟩
      | succ i =>
        have c : i < w.count x := by simpa [List.count_cons] using hi
        obtain ⟨l,t,e,ei⟩ := ih i c
        exact ⟨x::l,t,by simp [e],by simp [List.count_cons,ei]⟩
    · have c : i < w.count x := by simpa [List.count_cons,h,Ne.symm h] using hi
      obtain ⟨l,t,e,ei⟩ := ih i c
      exact ⟨a::l,t,by simp [e],by simp [List.count_cons,h,Ne.symm h,ei]⟩

theorem slot_cut (w : Word) (x i : Nat) (hi : i+1 < w.count x) :
    ∃ l mid t, w = l ++ [x] ++ mid ++ [x] ++ t ∧ l.count x = i ∧ x ∉ mid := by
  obtain ⟨l,suffix,e,ei⟩ := occurrence_cut w x i (by omega)
  have hs : x ∈ suffix := by
    apply List.count_pos_iff.mp
    rw [e,List.count_append,ei] at hi
    simp only [List.count_cons_self] at hi
    omega
  obtain ⟨mid,t,et,hn⟩ := List.eq_append_cons_of_mem hs
  exact ⟨l,mid,t,by simp [e,et,List.append_assoc],ei,hn⟩

private theorem trim_start {α : Type} (a : α) (xs l v : List α)
    (h : a ∉ l) (sub : (a :: xs).Sublist (l ++ v)) : (a::xs).Sublist v := by
  induction l with
  | nil => simpa using sub
  | cons b l ih =>
    cases sub with
    | cons _ sub => exact ih (fun m => h (by simp [m])) sub
    | cons₂ _ _ => exact (h (by simp)).elim

private theorem framed_iff {α : Type} (l m t : List α) (a b y : α)
    (ha : a ∉ l) (hb : b ∉ t) :
    [a,y,b].Sublist (l ++ (a :: m ++ [b]) ++ t) ↔ y ∈ m := by
  constructor
  · intro sub
    rw [List.append_assoc] at sub
    have inner := (trim_start a _ l _ ha sub).reverse
    simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,
        List.append_nil,List.nil_append,List.singleton_append,List.cons_append] at inner
    rw [List.append_assoc] at inner
    have back := (trim_start b _ t.reverse _ (by simpa using hb) inner).reverse
    have mid : [a,y,b].Sublist (a :: (m ++ [b])) := by simpa using back
    have last : ([y] ++ [b]).Sublist (m ++ [b]) := List.cons_sublist_cons.mp mid
    simpa using (List.append_sublist_append_right [b]).mp last
  · intro hy
    have sub : ([y] : List α).Sublist m := by simpa using hy
    have sub₂ := (List.append_sublist_append_right [b]).mpr sub
    exact List.sublist_append_of_sublist_left (List.sublist_append_of_sublist_right (sub₂.cons₂ a))

/-- Slot membership in a fixed literal split, including a possibly deficient
    occupant. The occupant's own occurrence number is existential. -/
theorem occupies_at_cut (l mid t : Word) (x y : Nat) (hn : x ∉ mid) :
    occupies (l ++ [x] ++ mid ++ [x] ++ t) x (l.count x) y ↔ y ∈ mid := by
  let n := advance (fun _ => 0) (l ++ [x])
  let n' := advance (fun _ => 0) (l ++ [x] ++ mid ++ [x])
  have nm : (advance n mid) x = l.count x+1 := by
    simp [n,advance,List.count_append,List.count_eq_zero.mpr hn]
  have ne : n' x = l.count x+2 := by
    simp [n',advance,List.count_append,List.count_eq_zero.mpr hn]
  have eq : events (l ++ [x] ++ mid ++ [x] ++ t) =
      events l ++ ((x,l.count x) :: stamp n mid ++ [(x,l.count x+1)]) ++ stamp n' t := by
    unfold events
    simp only [stamp_append,stamp,List.append_nil,advance_append,n,n']
    simp [advance,List.count_append,List.count_eq_zero.mpr hn,List.append_assoc, Nat.add_assoc]
  have ha : (x,l.count x) ∉ events l := by
    intro h
    have hh := (event_bounds (fun _ => 0) l x _ h).2
    omega
  have hb : (x,l.count x+1) ∉ stamp n' t := by
    intro h
    have hh := (event_bounds n' t x _ h).1
    omega
  unfold occupies sees
  rw [eq]
  constructor
  · rintro ⟨j,hj⟩
    exact stamped_mem_label n mid (y,j) ((framed_iff _ _ _ _ _ _ ha hb).mp hj)
  · intro hy
    rw [← labels_of_stamp n mid] at hy
    obtain ⟨⟨a,j⟩,he,rfl⟩ := List.mem_map.mp hy
    exact ⟨j,(framed_iff _ _ _ _ _ _ ha hb).mpr he⟩

theorem supplier (v : Word) (h : Nat → Word) (l k : Word) (x s t i r : Nat)
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (hx : v.count x = r) (hs : s ∈ h x) (hout : t ∉ h x)
    (ho : occupies (l ++ v.flatMap h ++ k) s i t)
    (guard : ∀ y, occupies v x i y → v.count y = r) :
    ∃ y, occupies v x i y ∧ t ∈ h y ∧ v.count y = r ∧ x ≠ y := by
  have cb : (v.flatMap h).count s ≤ r := by
    have c := cap s
    simp only [List.count_append] at c
    omega
  have sat := (P455DonorInterval.exclusive h v x s r hr hx hs cb).2.2
  have hf := (saturated_factor_occupies l (v.flatMap h) k s i t r cap sat).mp ho
  have bound : i+1 < v.count x := by
    obtain ⟨j,hj⟩ := hf
    have he : (s,i+1) ∈ events (v.flatMap h) := hj.mem (by simp)
    have hh := (event_bounds (fun _ => 0) _ s _ he).2
    omega
  obtain ⟨L,I,R,cut,idx,cons⟩ := slot_cut v x i bound
  obtain ⟨p,q,split,_⟩ := List.eq_append_cons_of_mem hs
  have image : h x = p ++ [s] ++ q := by simpa [List.append_assoc] using split
  obtain ⟨_,_,_,hni,hw,hi,_⟩ :=
    P455DonorInterval.consecutive_interval h v L I R x s p q r cut cons image hx cb
  have hit : t ∈ q ++ I.flatMap h ++ p := by
    rw [← idx, ← hi, hw] at hf
    exact (occupies_at_cut _ _ _ _ _ hni).mp hf
  obtain ⟨y,hy,don⟩ := P455DonorInterval.interior_supplier h I x s t p q image hit hout
  have occ : occupies v x i y := by
    rw [cut,← idx]
    exact (occupies_at_cut _ _ _ _ _ cons).mpr hy
  exact ⟨y,occ,don,guard y occ,fun eq => hout (eq ▸ don)⟩

/-- A terminal slot may include the boundary donor. No contact or
    separate-block assumption is needed for this disjunction. -/
theorem supplier_or_boundary (v : Word) (h : Nat → Word) (l k : Word) (x s t i r : Nat)
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (hx : v.count x = r) (hs : s ∈ h x)
    (ho : occupies (l ++ v.flatMap h ++ k) s i t)
    (guard : ∀ y, occupies v x i y → v.count y = r) :
    t ∈ h x ∨ ∃ y, occupies v x i y ∧ t ∈ h y ∧ v.count y = r ∧ x ≠ y := by
  by_cases bound : t ∈ h x
  · exact .inl bound
  · exact .inr (supplier v h l k x s t i r hr cap hx hs bound ho guard)

end P455SlotOrigin
