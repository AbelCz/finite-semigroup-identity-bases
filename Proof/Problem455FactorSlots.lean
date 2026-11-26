import Problem455ObservationBridge




namespace Problem455.Slots

def shift (n : Nat → Nat) (e : Event) : Event := (e.1, n e.1 + e.2)
def unshift (n : Nat → Nat) (e : Event) : Event := (e.1, e.2 - n e.1)

@[simp] theorem unshift_shift (n : Nat → Nat) (e : Event) :
    unshift n (shift n e) = e := by cases e; simp [unshift, shift, Nat.add_sub_cancel_left]

theorem stamp_shift (extra n : Nat → Nat) (w : Word) :
    stamp (fun x => extra x + n x) w = (stamp n w).map (shift extra) := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih =>
    have he : advance (fun x => extra x + n x) [a] =
      (fun x => extra x + advance n [a] x) := by funext x; simp [advance, Nat.add_assoc]
    simp only [stamp, List.map_cons, he, ih, shift]

theorem labels_of_stamp (n : Nat → Nat) (w : Word) :
    (stamp n w).map Prod.fst = w := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih => simp [stamp, ih]

theorem stamped_mem_label (n : Nat → Nat) (w : Word) (e : Event)
    (h : e ∈ stamp n w) : e.1 ∈ w := by
  rw [← labels_of_stamp n w]
  exact List.mem_map_of_mem h

theorem events_of_factor (l f t : Word) :
    events (l ++ f ++ t) =
      events l ++ ((events f).map (shift (fun a => l.count a)) ++
        stamp (fun a => l.count a + f.count a) t) := by
  have hn : advance (fun _ => 0) l = (fun a => l.count a) := by funext a; simp [advance]
  have hh := stamp_shift (fun a => l.count a) (fun _ => 0) f
  simp only [Nat.add_zero] at hh
  simp only [List.append_assoc, events, stamp_append, hn, hh]
  rfl

private theorem trim_left {α : Type} {a : α} {pat u v : List α}
    (ha : a ∉ u) (h : (a :: pat).Sublist (u ++ v)) : (a :: pat).Sublist v := by
  induction u with
  | nil => exact h
  | cons c u ih =>
    cases h with
    | cons _ h => exact ih (fun hh => ha (by simp [hh])) h
    | cons₂ _ _ => exact False.elim (ha (by simp))

private theorem trim_three {α : Type} {a e b : α} {l f t : List α}
    (ha : a ∉ l) (hb : b ∉ t) :
    [a,e,b].Sublist (l ++ (f ++ t)) ↔ [a,e,b].Sublist f := by
  constructor
  · intro h
    have h' := (trim_left ha h).reverse
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.singleton_append] at h'
    have hh := (trim_left (by simpa using hb : b ∉ t.reverse) h').reverse
    simpa using hh
  · intro h
    exact List.sublist_append_of_sublist_right (List.sublist_append_of_sublist_left h)

/-- No assumption on the number of outside copies of the occupant. Its
    occurrence number is shifted on entering the surrounding word. -/
theorem factor_occupies (l f t : Word) (owner i a : Nat) (hl : owner ∉ l) (ht : owner ∉ t) :
    occupies (l ++ f ++ t) owner i a ↔ occupies f owner i a := by
  have hz := List.count_eq_zero.mpr hl
  have left : (owner, i) ∉ events l := fun hm => hl (stamped_mem_label _ _ _ hm)
  have right : (owner, i + 1) ∉ stamp (fun x => l.count x + f.count x) t :=
    fun hm => ht (stamped_mem_label _ _ _ hm)
  let n := fun x => l.count x
  have shiftS : ∀ j, unshift n (owner,j) = (owner,j) := by simp [unshift, n, hz]
  have shiftF : ∀ j, shift n (owner,j) = (owner,j) := by simp [shift,n,hz]
  constructor
  · rintro ⟨k,h⟩
    unfold sees at h
    rw [events_of_factor] at h
    have hh := ((trim_three left right).mp h).map (unshift n)
    refine ⟨k-n a,?_⟩
    simpa [sees, List.map_map, Function.comp_def, Nat.add_sub_cancel_left, shiftS, unshift, shift, n, hz] using hh
  · rintro ⟨k,h⟩
    refine ⟨n a+k,?_⟩
    unfold sees
    rw [events_of_factor]
    apply (trim_three left right).mpr
    have hh := h.map (shift n)
    simpa [shiftF, shift, n, hz] using hh

/-- In a capped variant, saturation in a factor supplies the owner hypothesis.
    This also applies to non-consecutive arbitrary slot endpoints through the
    underlying three-event trimming lemma. -/
theorem saturated_factor_occupies (l f t : Word) (owner i a r : Nat)
    (cap : P455Closure.Cap r (l ++ f ++ t)) (sat : f.count owner = r) :
    occupies (l ++ f ++ t) owner i a ↔ occupies f owner i a := by
  have h := cap owner
  simp only [List.count_append, sat] at h
  exact factor_occupies l f t owner i a
    (List.count_eq_zero.mp (by omega)) (List.count_eq_zero.mp (by omega))

theorem saturated_factor_sees (l f t : Word) (pat : List Event) (r : Nat)
    (cap : P455Closure.Cap r (l ++ f ++ t))
    (sat : ∀ e ∈ pat, f.count e.1 = r) :
    sees (l ++ f ++ t) pat ↔ sees f pat := by
  have fresh : ∀ e ∈ pat, l.count e.1 = 0 ∧ e.1 ∉ t := by
    intro e he
    have hh := cap e.1
    simp only [List.count_append, sat e he] at hh
    exact ⟨by omega,List.count_eq_zero.mp (by omega)⟩
  let n := fun x => l.count x
  have left : ∀ e ∈ pat, e ∉ events l := fun e he hc =>
    (List.count_eq_zero.mp (fresh e he).1) (stamped_mem_label _ _ _ hc)
  have right : ∀ e ∈ pat, e ∉ stamp (fun x => l.count x + f.count x) t := fun e he hc =>
    (fresh e he).2 (stamped_mem_label _ _ _ hc)
  have hs : pat.map (shift n) = pat := by
    conv => rhs; rw [← List.map_id (l := pat)]
    apply List.map_congr_left
    intro e he
    simp [shift,n,(fresh e he).1]
  have hr : pat.map (unshift n) = pat := by
    conv => rhs; rw [← List.map_id (l := pat)]
    apply List.map_congr_left
    intro e he
    simp [unshift,n,(fresh e he).1]
  unfold sees
  rw [events_of_factor]
  constructor
  · intro h
    have mid := (h.of_sublist_append_right left).of_sublist_append_left right
    have hh := mid.map (unshift n)
    simpa [hr, List.map_map, Function.comp_def, Nat.add_sub_cancel_left, unshift, shift, n] using hh
  · intro h
    have hh := h.map (shift n)
    rw [hs] at hh
    exact List.sublist_append_of_sublist_right (List.sublist_append_of_sublist_left hh)

/- If an occupant is not saturated, its occurrence number can change even
   when the owner is saturated. Here 3 is the owner and the leading 7 is
   outside the factor. These closed examples are separate from the lemmas. -/
example : sees [3,7,3] [(3,0),(7,0),(3,1)] := by unfold sees; decide
example : ¬ sees [7,3,7,3] [(3,0),(7,0),(3,1)] := by unfold sees; decide
example : sees [7,3,7,3] [(3,0),(7,1),(3,1)] := by unfold sees; decide

end Problem455.Slots
