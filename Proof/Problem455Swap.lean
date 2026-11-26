import Std





namespace Problem455Swap

abbrev Word := List Nat

def occ (a : Nat) : Word → Nat
  | [] => 0
  | b :: w => (if a = b then 1 else 0) + occ a w

def cap (r : Nat) (w : Word) : Prop := ∀ a, occ a w ≤ r

def hit (x y : Nat) (left right : Option Nat) : Nat :=
  if left = some x ∧ right = some y then 1 else 0

def bigram (x y : Nat) : Word → Nat
  | [] => 0
  | a :: w => hit x y (some a) w.head? + bigram x y w

def Link (r : Nat) (w : Word) (x y : Nat) : Prop := bigram x y w = r

theorem occ_append (a : Nat) (u v : Word) : occ a (u ++ v) = occ a u + occ a v := by
  induction u with
  | nil => simp [occ]
  | cons b u ih => simp [occ, ih, Nat.add_assoc]

theorem bigram_append (x y : Nat) (u v : Word) :
    bigram x y (u ++ v) = bigram x y u + bigram x y v + hit x y u.getLast? v.head? := by
  induction u with
  | nil => simp [bigram, hit]
  | cons a u ih =>
    cases u with
    | nil => simp [bigram, hit, Nat.add_comm]
    | cons b w =>
      change hit x y (some a) (some b) + bigram x y ((b :: w) ++ v) = _
      rw [ih]
      simp [bigram, List.getLast?_cons_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem out_bound (x y z : Nat) (hyz : y ≠ z) (w : Word) :
    bigram x y w + bigram x z w ≤ occ x w := by
  induction w with
  | nil => simp [bigram, occ]
  | cons a w ih =>
    simp only [bigram, occ]
    unfold hit
    split <;> split <;> split <;> simp_all <;> omega

theorem in_bound (x z y : Nat) (hxz : x ≠ z) (w : Word) :
    bigram x y w + bigram z y w ≤ occ y w.tail := by
  induction w with
  | nil => simp [bigram, occ]
  | cons a w ih =>
    cases w with
    | nil => simp [bigram, hit, occ]
    | cons b w =>
      change hit x y (some a) (some b) + bigram x y (b :: w) +
        (hit z y (some a) (some b) + bigram z y (b :: w)) ≤ occ y (b :: w)
      simp only [List.tail_cons] at ih
      simp only [occ]
      unfold hit
      split <;> split <;> split <;> simp_all <;> omega

theorem tail_occ_le (a : Nat) (w : Word) : occ a w.tail ≤ occ a w := by
  cases w <;> simp [occ]

def Factor (u w : Word) : Prop := ∃ l t, w = l ++ u ++ t

theorem factor_pos (x y : Nat) {u w : Word} (hu : Factor u w)
    (h : 0 < bigram x y u) : 0 < bigram x y w := by
  obtain ⟨l,t,rfl⟩ := hu
  rw [bigram_append, bigram_append]
  omega

def privatePhase (p q : Word) := p ++ p ++ q ++ p ++ q ++ q

private theorem private_boundaries {p q w : Word} {i j s t : Nat}
    (hf : Factor (privatePhase p q) w)
    (hp : p.head? = some i) (hq : q.head? = some j)
    (ep : p.getLast? = some s) (eq : q.getLast? = some t) :
    0 < bigram s i w ∧ 0 < bigram s j w ∧ 0 < bigram t i w ∧ 0 < bigram t j w := by
  have pn : p ≠ [] := by intro e; simp [e] at hp
  have qn : q ≠ [] := by intro e; simp [e] at hq
  refine ⟨factor_pos _ _ hf ?_, factor_pos _ _ hf ?_, factor_pos _ _ hf ?_, factor_pos _ _ hf ?_⟩ <;>
    simp only [privatePhase, bigram_append, List.getLast?_append, ep, eq, hp, hq] <;>
    simp [hit] <;> omega

private theorem safe_ends {p q w : Word} {i j s t x y r : Nat}
    (hc : cap r w) (hf : Factor (privatePhase p q) w)
    (hp : p.head? = some i) (hq : q.head? = some j)
    (ep : p.getLast? = some s) (eq : q.getLast? = some t)
    (hij : i ≠ j) (hst : s ≠ t) (hxy : Link r w x y) :
    x ≠ s ∧ x ≠ t ∧ y ≠ i ∧ y ≠ j := by
  obtain ⟨hsi,hsj,hti,htj⟩ := private_boundaries hf hp hq ep eq
  have outs (a : Nat) (hai : 0 < bigram a i w) (haj : 0 < bigram a j w) : x ≠ a := by
    intro h; subst a
    by_cases hy : y = i
    · subst y
      have b := out_bound x i j hij w
      have c := hc x
      unfold Link at hxy
      omega
    · have b := out_bound x y i hy w
      have c := hc x
      unfold Link at hxy
      omega
  have ins (a : Nat) (hsa : 0 < bigram s a w) (hta : 0 < bigram t a w) : y ≠ a := by
    intro h; subst a
    by_cases hx : x = s
    · subst x
      have b := in_bound s t y hst w
      have c := hc y
      have d := tail_occ_le y w
      unfold Link at hxy
      omega
    · have b := in_bound x s y hx w
      have c := hc y
      have d := tail_occ_le y w
      unfold Link at hxy
      omega
  exact ⟨outs s hsi hsj, outs t hti htj, ins i hsi hti, ins j hsj htj⟩

private theorem safe_count_swap {p q : Word} {i j s t x y : Nat} (l u : Word)
    (hp : p.head? = some i) (hq : q.head? = some j)
    (ep : p.getLast? = some s) (eq : q.getLast? = some t)
    (h : x ≠ s ∧ x ≠ t ∧ y ≠ i ∧ y ≠ j) :
    bigram x y (l ++ p ++ q ++ u) = bigram x y (l ++ q ++ p ++ u) := by
  obtain ⟨xs,xt,yi,yj⟩ := h
  simp only [bigram_append, List.getLast?_append, ep, eq, hp, hq]
  simp [hit, Ne.symm xs, Ne.symm xt, Ne.symm yi, Ne.symm yj]
  omega




theorem repeatedLink_swap {p q : Word} {i j s t r : Nat} (l u : Word)
    (hp : p.head? = some i) (hq : q.head? = some j)
    (ep : p.getLast? = some s) (eq : q.getLast? = some t)
    (hij : i ≠ j) (hst : s ≠ t)
    (hc : cap r (l ++ p ++ q ++ u))
    (hf : Factor (privatePhase p q) (l ++ p ++ q ++ u))
    (hg : Factor (privatePhase p q) (l ++ q ++ p ++ u)) (x y : Nat) :
    Link r (l ++ p ++ q ++ u) x y ↔ Link r (l ++ q ++ p ++ u) x y := by
  have hd : cap r (l ++ q ++ p ++ u) := by
    intro a
    have b := hc a
    simp only [occ_append] at b ⊢
    omega
  constructor
  · intro h
    have good := safe_ends hc hf hp hq ep eq hij hst h
    exact (safe_count_swap l u hp hq ep eq good).symm.trans h
  · intro h
    have good := safe_ends hd hg hp hq ep eq hij hst h
    exact (safe_count_swap l u hp hq ep eq good).trans h

/-- Nonoriented finite paths generate the repeated-block partition on
    saturated letters. Singletons occur as paths of length zero. -/
inductive Joined (edges : Nat → Nat → Prop) : Nat → Nat → Prop where
  | refl (x) : Joined edges x x
  | extend {x y z} : Joined edges x y → (edges y z ∨ edges z y) → Joined edges x z

def SameBlock (r : Nat) (w : Word) (x y : Nat) : Prop :=
  occ x w = r ∧ occ y w = r ∧ Joined (Link r w) x y

theorem sameBlock_swap {p q : Word} {i j s t r : Nat} (l u : Word)
    (hp : p.head? = some i) (hq : q.head? = some j)
    (ep : p.getLast? = some s) (eq : q.getLast? = some t)
    (hij : i ≠ j) (hst : s ≠ t)
    (hc : cap r (l ++ p ++ q ++ u))
    (hf : Factor (privatePhase p q) (l ++ p ++ q ++ u))
    (hg : Factor (privatePhase p q) (l ++ q ++ p ++ u)) (x y : Nat) :
    SameBlock r (l ++ p ++ q ++ u) x y ↔ SameBlock r (l ++ q ++ p ++ u) x y := by
  have e : Link r (l ++ p ++ q ++ u) = Link r (l ++ q ++ p ++ u) :=
    funext fun a => funext fun b => propext (repeatedLink_swap l u hp hq ep eq hij hst hc hf hg a b)
  simp only [SameBlock, e, occ_append]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨by omega, by omega, h3⟩

/-- Every repeated link inside a proper or improper literal factor remains
    a link of a capped enclosing word. To pull a block distinction back
    from the enclosing tester, only this direction is needed. -/
theorem link_factor {r x y : Nat} {w u : Word} (f : Factor u w)
    (hc : cap r w) (h : Link r u x y) : Link r w x y := by
  have bound := out_bound x y (y+1) (by omega) w
  have ceil := hc x
  obtain ⟨l,t,rfl⟩ := f
  unfold Link at *
  rw [bigram_append, bigram_append] at bound ⊢
  omega

private theorem joined_of_imp {e d : Nat → Nat → Prop} {a b : Nat}
    (h : ∀ x y, e x y → d x y) (j : Joined e a b) : Joined d a b := by
  induction j with
  | refl => exact .refl _
  | extend walk last ih =>
    exact .extend ih (last.imp (h _ _) (h _ _))

theorem sameBlock_factor {r x y : Nat} {w u : Word} (f : Factor u w)
    (hc : cap r w) (h : SameBlock r u x y) : SameBlock r w x y := by
  obtain ⟨hx,hy,hj⟩ := h
  refine ⟨?_,?_,joined_of_imp (fun _ _ hh => link_factor f hc hh) hj⟩
  all_goals
    obtain ⟨l,t,rfl⟩ := f
    have bx := hc x
    have by' := hc y
    simp only [occ_append] at bx by' ⊢
    omega

end Problem455Swap
