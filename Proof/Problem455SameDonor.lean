import Problem455BlockBridge



namespace Problem455SameDonor
open Problem455Swap

private theorem count_le_output {β : Type} [DecidableEq β] (h : β → Word)
    (x : β) (a : Nat) (ha : a ∈ h x) (v : List β) :
    v.count x ≤ occ a (v.flatMap h) := by
  have pos : 0 < occ a (h x) := by
    rw [Problem455BlockBridge.occ_count]
    exact List.count_pos_iff.mpr ha
  induction v with
  | nil => simp [occ]
  | cons b v ih =>
    simp only [List.flatMap_cons, occ_append]
    by_cases e : b = x
    · subst b; simp [List.count_cons]; omega
    · simp [List.count_cons, e]; omega

private theorem count_le_edge {β : Type} [DecidableEq β] (h : β → Word)
    (x : β) (a b : Nat) (hab : 0 < bigram a b (h x)) (v : List β) :
    v.count x ≤ bigram a b (v.flatMap h) := by
  induction v with
  | nil => simp [bigram]
  | cons z v ih =>
    simp only [List.flatMap_cons, bigram_append]
    by_cases e : z = x
    · subst z; simp [List.count_cons]; omega
    · simp [List.count_cons, e]; omega

private theorem transJoined {e : Nat → Nat → Prop} {a b c : Nat}
    (h1 : Joined e a b) (h2 : Joined e b c) : Joined e a c := by
  induction h2 with
  | refl => exact h1
  | extend _ z ih => exact .extend ih z

private theorem symmJoined {e : Nat → Nat → Prop} {a b : Nat}
    (h : Joined e a b) : Joined e b a := by
  induction h with
  | refl => exact .refl _
  | extend _ z ih => exact transJoined (.extend (.refl _) z.symm) ih

private theorem headConnected (r : Nat) (F : Word) (a : Nat) (t : Word)
    (links : ∀ i j, 0 < bigram i j (a :: t) → Link r F i j) :
    ∀ b ∈ a :: t, Joined (Link r F) a b := by
  induction t generalizing a with
  | nil =>
    intro b hb
    have := List.mem_singleton.mp hb
    subst b; exact .refl _
  | cons c t ih =>
    intro b hb
    rcases List.mem_cons.mp hb with h | hb
    · subst b; exact .refl _
    · have ac : Link r F a c := links a c (by simp [bigram, hit]; omega)
      have tailLinks : ∀ i j, 0 < bigram i j (c :: t) → Link r F i j := by
        intro i j pos
        apply links
        change 0 < hit i j (some a) (some c) + bigram i j (c :: t)
        omega
      exact transJoined (.extend (.refl _) (.inl ac)) (ih c tailLinks b hb)

/-- Under the cap, every label in the image of an r-occurring source variable
    is saturated and all such labels belong to one maximal repeated block.
    There is no condition on substitutions of any other source variable. -/
theorem sameDonor {β : Type} [DecidableEq β] {r : Nat} (v : List β)
    (h : β → Word) (x : β) (hx : v.count x = r)
    (hc : ∀ a, (v.flatMap h).count a ≤ r) (a b : Nat) (ha : a ∈ h x) (hb : b ∈ h x) :
    SameBlock r (v.flatMap h) a b := by
  have cap' : cap r (v.flatMap h) := by
    intro j; rw [Problem455BlockBridge.occ_count]; exact hc j
  have sat (i : Nat) (hi : i ∈ h x) : occ i (v.flatMap h) = r := by
    have lower := count_le_output h x i hi v
    have upper := cap' i
    omega
  have links (i j : Nat) (ij : 0 < bigram i j (h x)) : Link r (v.flatMap h) i j := by
    have lower := count_le_edge h x i j ij v
    have upper := out_bound i j (j+1) (by omega) (v.flatMap h)
    have ceiling := cap' i
    unfold Link
    omega
  refine ⟨sat a ha,sat b hb,?_⟩
  cases eq : h x with
  | nil => simp [eq] at ha
  | cons c t =>
    rw [eq] at ha hb links
    exact transJoined (symmJoined (headConnected r _ c t links a ha))
      (headConnected r _ c t links b hb)

private theorem multiplicity_lower {β : Type} [DecidableEq β] (v : List β) (h : β → Word)
    (x : β) (a : Nat) : v.count x * (h x).count a ≤ (v.flatMap h).count a := by
  induction v with
  | nil => simp
  | cons b v ih =>
    simp only [List.flatMap_cons, List.count_append]
    by_cases e : b = x
    · subst b
      simp [List.count_cons, Nat.add_mul]
      omega
    · simp [List.count_cons, e]; omega

/-- A named letter donated by x appears exactly once in h(x), and no other
    variable USED by v donates that letter. Variables absent from v are
    legitimately unconstrained. -/
theorem uniqueDonor {β : Type} [DecidableEq β] {r : Nat} (v : List β)
    (h : β → Word) (x : β) (rpos : 0 < r) (hx : v.count x = r)
    (hc : ∀ a, (v.flatMap h).count a ≤ r) (a : Nat) (ha : a ∈ h x) :
    (h x).count a = 1 ∧ ∀ y ∈ v, y ≠ x → a ∉ h y := by
  constructor
  · have m := multiplicity_lower v h x a
    rw [hx] at m
    have p := List.count_pos_iff.mpr ha
    have c := hc a
    by_cases hn : (h x).count a = 1
    · exact hn
    · exfalso
      have two : 2 ≤ (h x).count a := by omega
      have bad := Nat.mul_le_mul_left r two
      omega
  · intro y hy yx ay
    obtain ⟨l,t,e⟩ := List.append_of_mem hy
    have h1 := count_le_output h x a ha l
    have h2 := count_le_output h x a ha t
    rw [Problem455BlockBridge.occ_count] at h1 h2
    have yPos := List.count_pos_iff.mpr ay
    have c := hc a
    simp only [e,List.flatMap_append,List.flatMap_cons,List.count_append] at c
    simp [e,List.count_append,List.count_cons,yx] at hx
    omega

end Problem455SameDonor
