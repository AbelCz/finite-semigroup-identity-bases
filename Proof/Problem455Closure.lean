




import Std

namespace P455Closure

universe u
variable {α : Type u} [DecidableEq α]

def Cap (r : Nat) (w : List α) : Prop := ∀ a, w.count a ≤ r

/-- false denotes block p and true denotes block q. -/
def phasePair (b : Bool) : List Bool := [b, !b]



def fixedPhases (tag : List Bool) : List Bool :=
  (List.replicate 5 [false,true,false,true]).flatten ++ tag.flatMap phasePair ++ phasePair false

/-- The fillers before fixed phase tokens, before the mutable pair, and
    before the two final tokens may be arbitrary lists, including empty.
    A frame spans from the first p to the last q. -/
structure Frame (α : Type u) where
  pHead : α
  pTail : List α
  qInit : List α
  qLast : α
  tag : List Bool
  middle : List (List α × Bool)
  beforeMutable : List α
  beforeFinalP : List α
  beforeFinalQ : List α

namespace Frame
variable (f : Frame α)
def p := f.pHead :: f.pTail
def q := f.qInit ++ [f.qLast]
def pair (b : Bool) := if b then f.q ++ f.p else f.p ++ f.q
def early := f.p ++ f.p ++ f.q ++ f.p ++ f.q ++ f.q
def mid := f.middle.flatMap fun e => e.1 ++ (if e.2 then f.q else f.p)
def core (b : Bool) := f.early ++ f.mid ++ f.beforeMutable ++ f.pair b ++
                        f.beforeFinalP ++ f.p ++ f.beforeFinalQ ++ f.q

/-- The count condition explicitly encodes that the r designated copies
    of each block exhaust its alphabet; all intervening fillers are inert
    for the two blocks. Mark may be stored in either order. -/
def Valid (r : Nat) (Allowed : List Bool → Prop) (Mark : α → α → Prop) : Prop :=
  r = 16 + f.tag.length ∧ Allowed f.tag ∧ f.middle.map Prod.snd = fixedPhases f.tag ∧
  f.p.Nodup ∧ f.q.Nodup ∧ (∀ a ∈ f.p, a ∉ f.q) ∧
  (∀ a ∈ f.p, ∀ b ∈ f.q, ¬ Mark a b ∧ ¬ Mark b a) ∧
  (∀ a, a ∈ f.p ∨ a ∈ f.q → (f.core false).count a = r)

theorem count_core (a : α) (b : Bool) : (f.core b).count a = (f.core (!b)).count a := by
  cases b <;> simp [core, pair, List.count_append] <;> omega

omit [DecidableEq α] in
theorem core_starts (b : Bool) : ∃ tail, f.core b = f.pHead :: tail := by
  simp [core, early, p]

omit [DecidableEq α] in
theorem core_ends (b : Bool) : ∃ ini, f.core b = ini ++ [f.qLast] := by
  unfold core q
  rw [← List.append_assoc]
  exact ⟨_, rfl⟩

private theorem count_tag_pairs (tag : List Bool) (side : Bool) :
    (tag.flatMap phasePair).count side = tag.length := by
  induction tag with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> cases side <;> simp_all [phasePair,List.count_cons,Nat.add_comm]

private theorem fixed_count (tag : List Bool) (side : Bool) :
    (fixedPhases tag).count side = 11 + tag.length := by
  cases side <;> simp [fixedPhases,count_tag_pairs,phasePair,List.count_cons,Nat.add_comm,
    List.replicate_succ] <;> omega

private theorem token_count_le (p q : List α) (a : α) (side : Bool)
    (has : 1 ≤ (if side then q else p).count a) (es : List (List α × Bool)) :
    (es.map Prod.snd).count side ≤
      (es.flatMap fun e => e.1 ++ (if e.2 then q else p)).count a := by
  induction es with
  | nil => simp
  | cons hd es ih =>
    obtain ⟨w,b⟩ := hd
    cases b <;> cases side <;>
      simp only [Bool.false_eq_true,if_false,if_true] at has <;>
      simp [List.count_cons] <;> omega

private theorem index_of_order {r : Nat} (hr : r = 16 + f.tag.length)
    (hmid : f.middle.map Prod.snd = fixedPhases f.tag) (bit : Bool) (l t : List α)
    (hc : Cap r (l ++ f.core bit ++ t)) (a : α) (ha : a ∈ f.p ∨ a ∈ f.q) :
    (l ++ f.early ++ f.mid ++ f.beforeMutable).count a = 14 + f.tag.length := by
  have hcap := hc a
  have hpq : 1 ≤ f.p.count a ∨ 1 ≤ f.q.count a := ha.imp List.count_pos_iff.mpr List.count_pos_iff.mpr
  have h1 : 11 + f.tag.length ≤ f.mid.count a := by
    rcases hpq with hp | hq
    · have h := token_count_le f.p f.q a false (by simpa using hp) f.middle
      simpa [hmid,fixed_count,mid] using h
    · have h := token_count_le f.p f.q a true (by simpa using hq) f.middle
      simpa [hmid,fixed_count,mid] using h
  have h2 : 3 ≤ f.early.count a := by simp [early]; omega
  have h3 : 1 ≤ (f.pair bit).count a := by cases bit <;> simp [pair] <;> omega
  simp only [core,List.count_append] at hcap ⊢
  omega

/-- Every block label has zero-based occurrence index 14+k at the mutable
    pair. Counts are derived from the actual profile and the cap; neither
    an index hypothesis nor any restriction on outsiders in context is needed. -/
theorem mutable_index {r : Nat} {Allowed : List Bool → Prop} {Mark : α → α → Prop}
    (hf : f.Valid r Allowed Mark) (bit : Bool) (l t : List α)
    (hc : Cap r (l ++ f.core bit ++ t)) (a : α) (ha : a ∈ f.p ∨ a ∈ f.q) :
    (l ++ f.early ++ f.mid ++ f.beforeMutable).count a = 14 + f.tag.length := by
  exact f.index_of_order hf.1 hf.2.2.1 bit l t hc a ha

/-- Literal occurrence exhaustion follows from the phase order and cap.
    This shows the saturation field in Valid cannot exclude any capped
    arrangement of the prescribed blocks, including arrangements with
    previously unrestricted fillers. -/
theorem saturation_of_order {r : Nat} (hr : r = 16 + f.tag.length)
    (hmid : f.middle.map Prod.snd = fixedPhases f.tag) (bit : Bool) (l t : List α)
    (hc : Cap r (l ++ f.core bit ++ t)) (a : α) (ha : a ∈ f.p ∨ a ∈ f.q) :
    (f.core false).count a = r := by
  have hc' : Cap r ([] ++ f.core false ++ []) := by
    intro z
    have hh := hc z
    have hd : (f.core bit).count z = (f.core false).count z := by
      cases bit with
      | false => rfl
      | true => exact f.count_core z true
    simp only [List.count_append,hd, List.count_nil] at *
    omega
  have idx := f.index_of_order hr hmid false [] [] hc' a ha
  have bound := hc' a
  have sup : 1 ≤ f.p.count a ∨ 1 ≤ f.q.count a :=
    ha.imp List.count_pos_iff.mpr List.count_pos_iff.mpr
  simp only [List.nil_append,List.append_nil] at idx bound
  simp only [core,pair,Bool.false_eq_true,if_false,List.count_append] at idx bound ⊢
  omega

theorem valid_of_capped_shape {r : Nat} {Allowed : List Bool → Prop} {Mark : α → α → Prop}
    (hr : r = 16 + f.tag.length) (ht : Allowed f.tag)
    (order : f.middle.map Prod.snd = fixedPhases f.tag)
    (dp : f.p.Nodup) (dq : f.q.Nodup) (apart : ∀ a ∈ f.p, a ∉ f.q)
    (unmarked : ∀ a ∈ f.p, ∀ b ∈ f.q, ¬ Mark a b ∧ ¬ Mark b a)
    (bit : Bool) (l t : List α) (hc : Cap r (l ++ f.core bit ++ t)) :
    f.Valid r Allowed Mark :=
  ⟨hr,ht,order,dp,dq,apart,unmarked,f.saturation_of_order hr order bit l t hc⟩

/-- A capped enclosing context contributes no extra occurrence of any
    moved label, for either choice of the mutable order. -/
theorem context_fresh {r : Nat} {Allowed : List Bool → Prop} {Mark : α → α → Prop}
    (hf : f.Valid r Allowed Mark) (bit : Bool) (l t : List α)
    (hc : Cap r (l ++ f.core bit ++ t)) (a : α) (ha : a ∈ f.p ∨ a ∈ f.q) :
    a ∉ l ∧ a ∉ t := by
  have hs := hf.2.2.2.2.2.2.2 a ha
  have hs' : (f.core bit).count a = r := by
    cases bit with
    | false => exact hs
    | true => exact (f.count_core a true).trans hs
  have hh := hc a
  simp only [List.count_append,hs'] at hh
  exact ⟨List.count_eq_zero.mp (by omega),List.count_eq_zero.mp (by omega)⟩

def profileBits (tag : List Bool) (bit : Bool) : List Bool :=
  [false,false,true,false,true,true] ++ fixedPhases tag ++ phasePair bit ++ phasePair false

def profileWord (x y : α) (tag : List Bool) (bit : Bool) : List α :=
  (profileBits tag bit).map (fun b => if b then y else x)

omit [DecidableEq α] in
private theorem middle_trace (p q : List α) {x y : α} (hx : x ∈ p) (hy : y ∈ q)
    (es : List (List α × Bool)) :
    ((es.map Prod.snd).map (fun b => if b then y else x)).Sublist
      (es.flatMap fun e => e.1 ++ if e.2 then q else p) := by
  induction es with
  | nil => exact .slnil
  | cons e es ih =>
    obtain ⟨w,b⟩ := e
    have one : [if b then y else x].Sublist (w ++ (if b then q else p)) := by
      apply List.sublist_append_of_sublist_right
      cases b <;> simp [hx,hy]
    exact one.append ih

omit [DecidableEq α] in
private theorem profile_trace (bit : Bool) (x y : α) (hx : x ∈ f.p) (hy : y ∈ f.q)
    (order : f.middle.map Prod.snd = fixedPhases f.tag) :
    (profileWord x y f.tag bit).Sublist (f.core bit) := by
  have px := List.singleton_sublist.mpr hx
  have qy := List.singleton_sublist.mpr hy
  have ea := ((((px.append px).append qy).append px).append qy).append qy
  have mi := middle_trace f.p f.q hx hy f.middle
  rw [order] at mi
  have swapped : ((phasePair bit).map (fun b => if b then y else x)).Sublist (f.pair bit) := by
    cases bit with
    | false => exact px.append qy
    | true => exact qy.append px
  have pref := (ea.append mi).append (List.nil_sublist f.beforeMutable)
  have whole := (((((pref.append swapped).append (List.nil_sublist f.beforeFinalP)).append px).append
    (List.nil_sublist f.beforeFinalQ)).append qy)
  simpa only [profileWord,profileBits,core,early,List.map_append,List.append_nil,
    phasePair,List.map_cons,List.map_nil,Bool.false_eq_true,if_false,if_true,
    List.append_assoc,List.cons_append,List.nil_append] using whole

omit [DecidableEq α] in
private theorem pattern_length (x y : α) (tag : List Bool) (bit : Bool) :
    (profileWord x y tag bit).length = 2 * (16 + tag.length) := by
  have tl : (tag.flatMap phasePair).length = 2 * tag.length := by
    induction tag with
    | nil => rfl
    | cons b t ih => simp [phasePair,ih]; omega
  simp [profileWord,profileBits,fixedPhases,phasePair,List.replicate_succ,tl]
  omega

private theorem select_length (x y : α) (w : List α) :
    (w.filter (fun a => decide (a = x ∨ a = y))).length ≤ w.count x + w.count y := by
  induction w with
  | nil => simp
  | cons a as ih =>
    by_cases hx : a = x <;> by_cases hy : a = y <;>
      simp [hx,hy,List.count_cons,beq_iff_eq] at ih ⊢ <;> omega




theorem cross_projection {r : Nat} {Allowed : List Bool → Prop} {Mark : α → α → Prop}
    (hf : f.Valid r Allowed Mark) (bit : Bool) (l t : List α)
    (hc : Cap r (l ++ f.core bit ++ t)) (x y : α) (hx : x ∈ f.p) (hy : y ∈ f.q) :
    (l ++ f.core bit ++ t).filter (fun a => decide (a = x ∨ a = y)) =
      profileWord x y f.tag bit := by
  have tr := f.profile_trace bit x y hx hy hf.2.2.1
  have tr' : (profileWord x y f.tag bit).Sublist (l ++ f.core bit ++ t) :=
    List.sublist_append_of_sublist_left (List.sublist_append_of_sublist_right tr)
  let keep := fun (a : α) => decide (a = x ∨ a = y)
  have intact : (profileWord x y f.tag bit).filter keep = profileWord x y f.tag bit := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    cases b <;> simp [keep]
  have tt := tr'.filter keep
  rw [intact] at tt
  apply Eq.symm
  apply tt.eq_of_length_le
  have h := select_length x y (l ++ f.core bit ++ t)
  have h1 := hc x
  have h2 := hc y
  have hr := hf.1
  change ((l ++ f.core bit ++ t).filter (fun a => decide (a = x ∨ a = y))).length ≤ _
  rw [pattern_length]
  omega

end Frame

/-- A single literal permitted swap, with both words written in the same
    external context. All r copies of p and q are in the frame. -/
def Move (r : Nat) (Allowed : List Bool → Prop) (Mark : α → α → Prop)
    (u v : List α) : Prop :=
  ∃ (f : Frame α) (b : Bool) (l t : List α),
    f.Valid r Allowed Mark ∧ u = l ++ f.core b ++ t ∧
    v = l ++ f.core (!b) ++ t ∧ Cap r u

variable {r : Nat} {Allowed : List Bool → Prop} {Mark : α → α → Prop} {u v : List α}

namespace Move

theorem count_eq (h : Move r Allowed Mark u v) (a : α) : u.count a = v.count a := by
  obtain ⟨f,b,l,t,_,hu,hv,_⟩ := h
  rw [hu,hv]
  simp only [List.count_append, f.count_core a b]

theorem cap_left (h : Move r Allowed Mark u v) : Cap r u := by
  obtain ⟨_,_,_,_,_,_,_,hc⟩ := h
  exact hc

theorem cap_right (h : Move r Allowed Mark u v) : Cap r v := by
  intro a
  rw [← h.count_eq]
  exact h.cap_left a

theorem symm (h : Move r Allowed Mark u v) : Move r Allowed Mark v u := by
  have hc := h.cap_right
  obtain ⟨f,b,l,t,hf,hu,hv,_⟩ := h
  exact ⟨f,!b,l,t,hf,hv,by simpa using hu,hc⟩

/-- Extending a factor-local move to any capped context uses the same
    literal frame. Cap excludes a new occurrence of either block's labels. -/
theorem extend_of_cap (h : Move r Allowed Mark u v) (l t : List α)
    (hc : Cap r (l ++ u ++ t)) : Move r Allowed Mark (l ++ u ++ t) (l ++ v ++ t) := by
  obtain ⟨f,b,i,j,hf,hu,hv,_⟩ := h
  refine ⟨f,b,l ++ i,j ++ t,hf,?_,?_,hc⟩ <;> simp [hu,hv,List.append_assoc]

end Move

omit [DecidableEq α] in
/-- Two splittings of a word, when the prefix on the left avoids the
    displayed occurrence on the right. The shorter prefix is on the left. -/
private theorem stripBefore {a : α} {l p z s : List α}
    (h : l ++ z = p ++ a :: s) (ha : a ∉ l) :
    ∃ d, p = l ++ d ∧ z = d ++ a :: s := by
  induction l generalizing p with
  | nil => exact ⟨p, by simp, by simpa using h⟩
  | cons x l ih =>
    cases p with
    | nil =>
      have hx : x = a := (List.cons.inj h).1
      exact False.elim (ha (by simp [hx]))
    | cons y p =>
      obtain ⟨hxy,hrest⟩ := List.cons.inj h
      obtain ⟨d,hp,hz⟩ := ih hrest (fun hm => ha (by simp [hm]))
      exact ⟨d,by simp [hp,hxy],hz⟩

omit [DecidableEq α] in
/-- In two splittings of a word, the factor x contains the whole core
    whenever the left context avoids its first symbol and the right
    context avoids its last symbol. Either context may be empty. -/
theorem containCore {l x t i c j : List α} {a b : α}
    (h : l ++ x ++ t = i ++ c ++ j)
    (ha : a ∉ l) (hb : b ∉ t)
    (hfirst : ∃ s, c = a :: s) (hlast : ∃ k, c = k ++ [b]) :
    ∃ d e, i = l ++ d ∧ j = e ++ t ∧ x = d ++ c ++ e := by
  obtain ⟨s,hs⟩ := hfirst
  have h1 : l ++ (x ++ t) = i ++ a :: (s ++ j) := by simpa [hs,List.append_assoc] using h
  obtain ⟨d,hi,hxt⟩ := stripBefore h1 ha
  obtain ⟨k,hk⟩ := hlast
  have h2 : t.reverse ++ x.reverse = j.reverse ++ b :: (k.reverse ++ d.reverse) := by
    have h' : x ++ t = d ++ c ++ j := by simpa [hs,List.append_assoc] using hxt
    simpa [hk,List.reverse_append,List.append_assoc] using congrArg List.reverse h'
  obtain ⟨e,hj,_⟩ := stripBefore h2 (by simpa using hb)
  have hj' : j = e.reverse ++ t := by
    simpa [List.reverse_append] using congrArg List.reverse hj
  have hx : l ++ (x ++ t) = l ++ ((d ++ c ++ e.reverse) ++ t) := by
    simpa [hi,hj',List.append_assoc] using h
  exact ⟨d,e.reverse,hi,hj',List.append_cancel_right (List.append_cancel_left hx)⟩

/-- Restrict a witnessed global swap to a factor containing all copies
    of the boundary anchors. Saturation of the other moving labels is
    automatic once this entire frame has been recovered. -/
theorem Frame.restrict_of_saturated (f : Frame α) (b : Bool)
    (hf : f.Valid r Allowed Mark) (l x t i j : List α)
    (whole : l ++ x ++ t = i ++ f.core b ++ j) (cap : Cap r (l ++ x ++ t))
    (hp : x.count f.pHead = r) (hq : x.count f.qLast = r) :
    ∃ y, Move r Allowed Mark x y ∧ l ++ y ++ t = i ++ f.core (!b) ++ j := by
  have hpl := cap f.pHead
  have hqt := cap f.qLast
  simp only [List.count_append,hp,hq] at hpl hqt
  have hpl' : l.count f.pHead = 0 := by omega
  have hqt' : t.count f.qLast = 0 := by omega
  obtain ⟨d,e,hi,hj,hx⟩ := containCore whole (List.count_eq_zero.mp hpl')
    (List.count_eq_zero.mp hqt') (f.core_starts b) (f.core_ends b)
  have hxcap : Cap r x := by
    intro a
    have hh := cap a
    simp only [List.count_append] at hh
    omega
  refine ⟨d ++ f.core (!b) ++ e,⟨f,b,d,e,hf,hx,rfl,hxcap⟩,?_⟩
  simp [hi,hj,List.append_assoc]

end P455Closure
