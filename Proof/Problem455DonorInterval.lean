import Std




namespace P455DonorInterval
universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Count the contributions of one chosen donor and all other variables
    separately, with equality for every source word. -/
theorem split_contributions (h : α → List β) (w : List α) (x : α) (s : β) :
    (w.flatMap h).count s = w.count x * (h x).count s +
      ((w.filter (fun a => decide (a ≠ x))).flatMap h).count s := by
  induction w with
  | nil => simp
  | cons a w ih =>
    by_cases e : a = x
    · subst a
      simp [List.count_cons, Nat.add_mul, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · simp [List.count_cons, e, Ne.symm e, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- A label contributed by a positively saturated source variable is
    contributed exactly once per occurrence, and by no other variable
    present in the evaluated side. A global cap only on this label suffices. -/
theorem exclusive (h : α → List β) (w : List α) (x : α) (s : β) (r : Nat)
    (hr : 0 < r) (hx : w.count x = r) (mem : s ∈ h x)
    (bound : (w.flatMap h).count s ≤ r) :
    (h x).count s = 1 ∧
    (∀ y ∈ w, y ≠ x → s ∉ h y) ∧ (w.flatMap h).count s = r := by
  have spl := split_contributions h w x s
  rw [hx] at spl
  have pos := List.count_pos_iff.mpr mem
  have one : (h x).count s = 1 := by
    apply Classical.byContradiction
    intro diff
    have two : 2 ≤ (h x).count s := by omega
    have ge := Nat.mul_le_mul_left r two
    rw [Nat.mul_two] at ge
    omega
  rw [one,Nat.mul_one] at spl
  have none : s ∉ (w.filter (fun a => decide (a ≠ x))).flatMap h :=
    List.count_eq_zero.mp (by omega)
  refine ⟨one,?_,by omega⟩
  intro y hy hne in_y
  apply none
  exact List.mem_flatMap.mpr ⟨y,List.mem_filter.mpr ⟨hy,by simpa using hne⟩,in_y⟩

/-- Within any chosen sublist of the evaluated source, occurrence numbers
    for an exclusively supplied label agree with those of its source variable. -/
theorem count_on_subword (h : α → List β) (w u : List α) (x : α) (s : β)
    (inside : ∀ y ∈ u, y ∈ w) (single : (h x).count s = 1)
    (exclusive : ∀ y ∈ w, y ≠ x → s ∉ h y) :
    (u.flatMap h).count s = u.count x := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have rest := ih (fun y hy => inside y (by simp [hy]))
    by_cases eq : a = x
    · subst a; simp [List.count_cons,single,rest,Nat.add_comm]
    · have na := exclusive a (inside a (by simp)) eq
      simp [List.count_cons,eq,Ne.symm eq,List.count_eq_zero.mpr na,rest]

/-- The literal open interval between corresponding consecutive copies of s.
    The final equality identifies the zero-based index of its left endpoint;
    the absence clause certifies consecutiveness in the output word. -/
theorem consecutive_interval (h : α → List β) (U L I R : List α)
    (x : α) (s : β) (p q : List β) (r : Nat)
    (cut : U = L ++ [x] ++ I ++ [x] ++ R) (consecutive : x ∉ I)
    (image : h x = p ++ [s] ++ q)
    (saturated : U.count x = r) (bounded : (U.flatMap h).count s ≤ r) :
    (∀ y ∈ U, y ≠ x → s ∉ h y) ∧ s ∉ p ∧ s ∉ q ∧
    s ∉ q ++ I.flatMap h ++ p ∧
    U.flatMap h = (L.flatMap h ++ p) ++ [s] ++ (q ++ I.flatMap h ++ p) ++
                   [s] ++ (q ++ R.flatMap h) ∧
    (L.flatMap h ++ p).count s = L.count x ∧ (U.flatMap h).count s = r := by
  have hr : 0 < r := by
    rw [← saturated]
    exact List.count_pos_iff.mpr (by simp [cut])
  have hx : s ∈ h x := by simp [image]
  obtain ⟨single,noOther,full⟩ := exclusive h U x s r hr saturated hx bounded
  have single' := single
  simp only [image,List.count_append,List.count_singleton_self] at single'
  have hp : s ∉ p := List.count_eq_zero.mp (by omega)
  have hq : s ∉ q := List.count_eq_zero.mp (by omega)
  have inner : (I.flatMap h).count s = I.count x := count_on_subword h U I x s
    (fun y hy => by simp [cut,hy]) single noOther
  have hi : s ∉ I.flatMap h := List.count_eq_zero.mp (inner.trans (List.count_eq_zero.mpr consecutive))
  have left := count_on_subword h U L x s (fun y hy => by simp [cut,hy]) single noOther
  exact ⟨noOther,hp,hq,by simp [hp,hq,hi],by simp [cut,image,List.flatMap_append,List.append_assoc],
    by simp [left,List.count_eq_zero.mpr hp],full⟩

omit [DecidableEq α] [DecidableEq β] in
/-- Once an occupant is excluded from the boundary donor's image, some
    literal name of the open source slot supplies it. No global condition
    on the other images or gap alphabets enters this inference. -/
theorem interior_supplier (h : α → List β) (I : List α) (x : α) (s t : β)
    (p q : List β) (image : h x = p ++ [s] ++ q)
    (occupies : t ∈ q ++ I.flatMap h ++ p) (other : t ∉ h x) :
    ∃ y ∈ I, t ∈ h y := by
  have nowhere := other
  simp only [image,List.mem_append,List.mem_singleton,not_or] at nowhere
  simp only [List.mem_append] at occupies
  rcases occupies with (hq | hi) | hp
  · exact False.elim (nowhere.2 hq)
  · exact List.mem_flatMap.mp hi
  · exact False.elim (nowhere.1.1 hp)

/-- If the literal output is a factor of a capped enclosing variant, every
    copy of s occurs in that factor. In particular external context cannot
    change the absolute occurrence indices of its two slot endpoints. -/
theorem enclosing_context (F left right : List β) (s : β) (r : Nat)
    (saturated : F.count s = r) (capped : (left ++ F ++ right).count s ≤ r) :
    s ∉ left ∧ s ∉ right := by
  simp only [List.count_append,saturated] at capped
  exact ⟨List.count_eq_zero.mp (by omega),List.count_eq_zero.mp (by omega)⟩

end P455DonorInterval
