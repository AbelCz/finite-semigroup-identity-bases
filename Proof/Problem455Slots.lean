import Std
 
namespace Problem455.Slots

abbrev Word := List Nat
abbrev Event := Nat × Nat

def advance (n : Nat → Nat) (w : Word) : Nat → Nat :=
  fun a => n a + w.count a

def stamp (n : Nat → Nat) : Word → List Event
  | [] => []
  | a :: w => (a, n a) :: stamp (advance n [a]) w

def events (w : Word) := stamp (fun _ => 0) w

theorem advance_append (n : Nat → Nat) (u v : Word) :
    advance (advance n u) v = advance n (u ++ v) := by
  funext a
  simp [advance, List.count_append, Nat.add_assoc]

theorem stamp_append (n : Nat → Nat) (u v : Word) :
    stamp n (u ++ v) = stamp n u ++ stamp (advance n u) v := by
  induction u generalizing n with
  | nil =>
    have hn : advance n [] = n := by funext a; simp [advance]
    simp [stamp, hn]
  | cons a u ih =>
    simp only [List.cons_append, stamp, ih]
    rw [advance_append]
    rfl

theorem stamp_at (n : Nat → Nat) (m : Nat) (u : Word)
    (nd : u.Nodup) (hm : ∀ a ∈ u, n a = m) :
    stamp n u = u.map (fun a => (a, m)) := by
  induction u generalizing n with
  | nil => rfl
  | cons a u ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp nd
    simp only [stamp, List.map_cons]
    rw [hm a (by simp), ih _ rest]
    intro b hb
    have hne : a ≠ b := by intro eq; exact fresh (eq ▸ hb)
    simp [advance, hne, Ne.symm hne, hm b (by simp [hb])]

structure Move (m : Nat) where
  pre : Word
  p : Word
  q : Word
  post : Word
  dp : p.Nodup
  dq : q.Nodup
  disjoint : ∀ a ∈ p, a ∉ q
  indexP : ∀ a ∈ p, pre.count a = m
  indexQ : ∀ a ∈ q, pre.count a = m

def before {m : Nat} (s : Move m) := s.pre ++ (s.p ++ (s.q ++ s.post))
def after {m : Nat} (s : Move m) := s.pre ++ (s.q ++ (s.p ++ s.post))
def tagged (m : Nat) (w : Word) : List Event := w.map (fun a => (a, m))

theorem move_events {m : Nat} (s : Move m) :
    ∃ lo hi : List Event,
      events (before s) = lo ++ (tagged m s.p ++ (tagged m s.q ++ hi)) ∧
      events (after s) = lo ++ (tagged m s.q ++ (tagged m s.p ++ hi)) := by
  let n := fun a => s.pre.count a
  have hn : advance (fun _ => 0) s.pre = n := by funext a; simp [advance, n]
  have hp : stamp n s.p = tagged m s.p := stamp_at _ _ _ s.dp s.indexP
  have hq : stamp n s.q = tagged m s.q := stamp_at _ _ _ s.dq s.indexQ
  have hp' : stamp (advance n s.q) s.p = tagged m s.p := by
    apply stamp_at _ _ _ s.dp
    intro a ha
    simp [advance, List.count_eq_zero.mpr (s.disjoint a ha), n, s.indexP a ha]
  have hq' : stamp (advance n s.p) s.q = tagged m s.q := by
    apply stamp_at _ _ _ s.dq
    intro a ha
    have fresh : a ∉ s.p := fun hp => s.disjoint a hp ha
    simp [advance, List.count_eq_zero.mpr fresh, n, s.indexQ a ha]
  have merge : advance (advance n s.p) s.q = advance (advance n s.q) s.p := by
    funext a
    simp [advance, Nat.add_right_comm]
  refine ⟨events s.pre, stamp (advance (advance n s.q) s.p) s.post, ?_, ?_⟩
  · simp only [events, before, stamp_append, hn]
    change _ ++ (stamp n s.p ++ (stamp (advance n s.p) s.q ++ _)) = _
    rw [hp, hq', merge]
  · simp only [events, after, stamp_append, hn]
    change _ ++ (stamp n s.q ++ (stamp (advance n s.q) s.p ++ _)) = _
    rw [hq, hp']

def select {α : Type} [DecidableEq α] (keep w : List α) : List α :=
  w.filter (fun e => decide (e ∈ keep))

theorem select_append {α : Type} [DecidableEq α] (keep u v : List α) :
    select keep (u ++ v) = select keep u ++ select keep v := List.filter_append ..

theorem select_nil {α : Type} [DecidableEq α] (keep w : List α)
    (h : ∀ a ∈ w, a ∉ keep) : select keep w = [] := by
  apply List.filter_eq_nil_iff.mpr
  simpa using h

theorem selected_swap {α : Type} [DecidableEq α] (keep lo p q hi : List α)
    (nc : (∀ a ∈ p, a ∉ keep) ∨ (∀ a ∈ q, a ∉ keep)) :
    select keep (lo ++ (p ++ (q ++ hi))) = select keep (lo ++ (q ++ (p ++ hi))) := by
  rcases nc with h | h
  · simp [select_append, select_nil keep p h]
  · simp [select_append, select_nil keep q h]

theorem protected_projection {m : Nat} (s : Move m) (keep : List Nat)
    (nc : (∀ a ∈ s.p, a ∉ keep) ∨ (∀ a ∈ s.q, a ∉ keep)) :
    select keep (before s) = select keep (after s) :=
  selected_swap keep _ _ _ _ nc

theorem observed_events {m : Nat} (s : Move m) (keep : List Event)
    (nc : (∀ a ∈ s.p, (a,m) ∉ keep) ∨ (∀ a ∈ s.q, (a,m) ∉ keep)) :
    select keep (events (before s)) = select keep (events (after s)) := by
  obtain ⟨lo, hi, h, h'⟩ := move_events s
  rw [h, h']
  apply selected_swap
  simpa [tagged] using nc

/- Observable order measured directly by the sublist relation on the word
of indexed occurrences.  The pattern need not consist of consecutive events. -/
def sees (w : Word) (pattern : List Event) := pattern.Sublist (events w)

theorem sublist_select_self {α : Type} [DecidableEq α] (t w : List α) :
    t.Sublist (select t w) ↔ t.Sublist w := by
  constructor
  · intro h
    exact h.trans (List.filter_sublist ..)
  · intro h
    have hf := h.filter (fun x => decide (x ∈ t))
    have self : t.filter (fun x => decide (x ∈ t)) = t := by
      apply List.filter_eq_self.mpr
      simp
    rwa [self] at hf

theorem sees_invariant {m : Nat} (s : Move m) (t : List Event)
    (nc : (∀ a ∈ s.p, (a,m) ∉ t) ∨ (∀ a ∈ s.q, (a,m) ∉ t)) :
    sees (before s) t ↔ sees (after s) t := by
  unfold sees
  rw [← sublist_select_self t (events (before s)),
      ← sublist_select_self t (events (after s)), observed_events s t nc]

theorem immutable_pattern {m : Nat} (s : Move m) (t : List Event)
    (hm : ∀ e ∈ t, e.2 ≠ m) :
    sees (before s) t ↔ sees (after s) t := by
  apply sees_invariant
  left
  exact fun a _ he => hm (a,m) he rfl

/- An occupant can have mutable occurrence index. Only the two specified
owner endpoints must be immutable. This covers unit-erasing as well as
multiletter representatives once their literal product has been located. -/
theorem open_slot_event {m : Nat} (s : Move m) (owner i j : Nat) (e : Event)
    (hi : i ≠ m) (hj : j ≠ m) :
    sees (before s) [(owner,i),e,(owner,j)] ↔
      sees (after s) [(owner,i),e,(owner,j)] := by
  apply sees_invariant
  by_cases h : e.1 ∈ s.p
  · right
    intro a ha
    have diff : (a,m) ≠ e := by
      intro eq
      have : a = e.1 := congrArg Prod.fst eq
      exact s.disjoint e.1 h (this ▸ ha)
    simp [diff, Ne.symm hi, Ne.symm hj]
  · left
    intro a ha
    have diff : (a,m) ≠ e := by
      intro eq
      have : a = e.1 := congrArg Prod.fst eq
      exact h (this ▸ ha)
    simp [diff, Ne.symm hi, Ne.symm hj]

def slotStart (i : Nat) : Prop :=
  i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 9 ∨ i = 11

def occupies (w : Word) (owner i a : Nat) : Prop :=
  ∃ j, sees w [(owner,i),(a,j),(owner,i+1)]

theorem seven_slots {k : Nat} (s : Move (14+k)) (owner i a : Nat)
    (hi : slotStart i) :
    occupies (before s) owner i a ↔ occupies (after s) owner i a := by
  have h1 : i ≠ 14+k := by unfold slotStart at hi; omega
  have h2 : i+1 ≠ 14+k := by unfold slotStart at hi; omega
  exact exists_congr (fun j => open_slot_event s owner i (i+1) (a,j) h1 h2)


def pair (a b : Nat) (bit : Bool) : Word := if bit then [b,a] else [a,b]

def profilePrefix (a b : Nat) (tag : List Bool) : Word :=
  [a,a,b,a,b,b] ++ (List.replicate 5 [a,b,a,b]).flatten ++
    tag.flatMap (pair a b) ++ [a,b]

def profile (a b : Nat) (tag : List Bool) (bit : Bool) : Word :=
  profilePrefix a b tag ++ (pair a b bit ++ [a,b])

def typed (w : Word) (a b : Nat) (tag : List Bool) : Prop :=
  ∃ bit, select [a,b] w = profile a b tag bit

theorem tag_length (a b : Nat) (tag : List Bool) :
    (tag.flatMap (pair a b)).length = 2 * tag.length := by
  induction tag with
  | nil => rfl
  | cons bit t ih => cases bit <;> simp [pair, ih] <;> omega

theorem profile_prefix_length (a b : Nat) (tag : List Bool) :
    (profilePrefix a b tag).length = 2 * (14+tag.length) := by
  unfold profilePrefix
  simp only [List.length_append, tag_length]
  change 6 + 20 + (2*tag.length) + 2 = _
  omega

theorem length_select_pair (a b : Nat) (hab : a ≠ b) (w : Word) :
    (select [a,b] w).length = w.count a + w.count b := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    unfold select at *
    simp at ih
    by_cases hca : c = a
    · subst c
      simp [List.count_cons, hab, Ne.symm hab, ih]; omega
    · by_cases hcb : c = b
      · subst c
        simp [List.count_cons, hab, Ne.symm hab, ih]; omega
      · simp [List.count_cons, hca, hcb, Ne.symm hca, Ne.symm hcb, ih]

theorem select_lone (a b : Nat) (w : Word) (hd : w.Nodup)
    (ha : a ∈ w) (hb : b ∉ w) :
    select [a,b] w = [a] := by
  induction w with
  | nil => simp at ha
  | cons c w ih =>
    obtain ⟨hc,ht⟩ := List.nodup_cons.mp hd
    by_cases hca : c = a
    · subst c
      have hnil : select [a,b] w = [] := by
        apply select_nil
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hc (e ▸ hx),fun e => hb (by simp [e ▸ hx])⟩
      simpa [select, List.filter_cons] using congrArg (List.cons a) hnil
    · have hc' : c ≠ b := fun h => hb (by simp [h])
      have ha' : a ∈ w := by simpa [Ne.symm hca] using ha
      have hb' : b ∉ w := fun h => hb (by simp [h])
      simpa [select, hca, hc'] using ih ht ha' hb'

theorem select_pair_symm (a b : Nat) (w : Word) : select [b,a] w = select [a,b] w := by
  unfold select
  apply List.filter_congr
  intro x _
  simp [or_comm]

private theorem exchange_at_split (a b : Nat) (lo hi fixed tail : Word)
    (len : lo.length = fixed.length) (bit : Bool) :
    (∃ b', lo ++ (pair a b bit ++ hi) = fixed ++ (pair a b b' ++ tail)) →
    (∃ b', lo ++ (pair a b (!bit) ++ hi) = fixed ++ (pair a b b' ++ tail)) := by
  rintro ⟨old,h⟩
  have eqPre : lo = fixed := by
    have ht := congrArg (List.take lo.length) h
    simpa [len] using ht
  subst fixed
  have he := List.append_cancel_left h
  have eqHi : hi = tail := by
    have hd := congrArg (List.drop 2) he
    cases bit <;> cases old <;> simpa [pair] using hd
  exact ⟨!bit,by rw [eqHi]⟩

theorem type_forward {m : Nat} (s : Move m) (a b : Nat) (tag : List Bool)
    (hab : a ≠ b) (hm : m = 14 + tag.length) :
    typed (before s) a b tag → typed (after s) a b tag := by
  let keep := [a,b]
  by_cases hp : ∀ x ∈ s.p, x ∉ keep
  · intro e
    unfold typed at *
    rw [← protected_projection s [a,b] (.inl hp)]; exact e
  by_cases hq : ∀ x ∈ s.q, x ∉ keep
  · intro e
    unfold typed at *
    rw [← protected_projection s [a,b] (.inr hq)]; exact e
  have shape : (a ∈ s.p ∧ b ∈ s.q) ∨ (b ∈ s.p ∧ a ∈ s.q) := by
    by_cases hap : a ∈ s.p
    · left
      refine ⟨hap,?_⟩
      apply Classical.byContradiction
      intro hbn
      apply hq
      intro x hx
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun eq => s.disjoint a hap (eq ▸ hx), fun eq => hbn (eq ▸ hx)⟩
    · have hbp : b ∈ s.p := by
        apply Classical.byContradiction
        intro hbn
        apply hp
        intro x hx
        simp only [keep, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun eq => hap (eq ▸ hx), fun eq => hbn (eq ▸ hx)⟩
      right
      refine ⟨hbp,?_⟩
      apply Classical.byContradiction
      intro han
      apply hq
      intro x hx
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun eq => han (eq ▸ hx),fun eq => s.disjoint b hbp (eq ▸ hx)⟩
  obtain ⟨bit,hp1,hq1,ca,cb⟩ :
      ∃ bit : Bool, select [a,b] s.p ++ select [a,b] s.q = pair a b bit ∧
        select [a,b] s.q ++ select [a,b] s.p = pair a b (!bit) ∧
        s.pre.count a = m ∧ s.pre.count b = m := by
    rcases shape with ⟨pa,qb⟩ | ⟨pb,qa⟩
    · have p' := select_lone a b s.p s.dp pa (fun pb => s.disjoint b pb qb)
      have q' := select_lone b a s.q s.dq qb (s.disjoint a pa)
      rw [select_pair_symm] at q'
      exact ⟨false,by rw [p',q']; rfl,by rw [p',q']; rfl,s.indexP a pa,s.indexQ b qb⟩
    · have p' := select_lone b a s.p s.dp pb (fun pa => s.disjoint a pa qa)
      rw [select_pair_symm] at p'
      have q' := select_lone a b s.q s.dq qa (s.disjoint b pb)
      exact ⟨true,by rw [p',q']; rfl,by rw [p',q']; rfl,s.indexQ a qa,s.indexP b pb⟩
  have len : (select [a,b] s.pre).length = (profilePrefix a b tag).length := by
    rw [length_select_pair a b hab, ca, cb, hm, profile_prefix_length]; omega
  unfold typed before after profile
  simp only [select_append]
  rw [← List.append_assoc (select [a,b] s.p), hp1,
      ← List.append_assoc (select [a,b] s.q), hq1]
  exact exchange_at_split a b _ _ _ _ len bit

end Problem455.Slots
