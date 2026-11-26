import Problem455Witness
import Problem455FactorSlots
import Problem455DonorInterval




namespace P455ContactReflection
open Problem455.Slots P455Witness

def eventMap (d : Nat → Nat) (e : Event) : Event := (d e.1, e.2)

theorem select_stamped (keep w : W) (n n' : Nat → Nat)
    (eqn : ∀ a ∈ keep, n a = n' a) :
    (stamp n w).filter (fun e => decide (e.1 ∈ keep)) = stamp n' (select keep w) := by
  induction w generalizing n n' with
  | nil => rfl
  | cons a w ih =>
    by_cases ha : a ∈ keep
    · simp only [stamp, select, List.filter_cons, ha, decide_true, Bool.true_eq, if_true]
      rw [eqn a ha]
      congr 1
      apply ih
      intro b hb
      simp only [advance, eqn b hb]
    · simp only [stamp, select, List.filter_cons, ha, decide_false, Bool.false_eq_true, if_false]
      apply ih
      intro b hb
      have ab : a ≠ b := fun e => ha (e ▸ hb)
      simp [advance, eqn b hb, ab]

theorem sees_select (keep w : W) (pat : List Event) (support : ∀ e ∈ pat, e.1 ∈ keep)
    (seen : sees w pat) : sees (select keep w) pat := by
  have filtered := seen.filter (fun e => decide (e.1 ∈ keep))
  have self : pat.filter (fun e => decide (e.1 ∈ keep)) = pat := by
    apply List.filter_eq_self.mpr; simpa using support
  rw [self] at filtered
  unfold sees events at *
  rw [select_stamped keep w _ (fun _ => 0) (fun _ _ => rfl)] at filtered
  exact filtered

theorem select_sees (keep w : W) (pat : List Event) (seen : sees (select keep w) pat) :
    sees w pat := by
  unfold sees events at *
  rw [← select_stamped keep w (fun _ => 0) _ (fun _ _ => rfl)] at seen
  exact seen.trans (List.filter_sublist ..)

theorem stamp_map (d : Nat → Nat) (w keep : W) (n n' : Nat → Nat)
    (inside : ∀ a ∈ w, a ∈ keep) (dinj : ∀ a ∈ keep, ∀ b ∈ keep, d a = d b → a = b)
    (eqn : ∀ a ∈ keep, n a = n' (d a)) :
    (stamp n w).map (eventMap d) = stamp n' (w.map d) := by
  induction w generalizing n n' with
  | nil => rfl
  | cons a w ih =>
    have ha := inside a (by simp)
    simp only [stamp, List.map_cons, eventMap, eqn a ha, List.cons.injEq, true_and]
    apply ih _ _ (fun b hb => inside b (by simp [hb]))
    intro b hb
    by_cases eq : a = b
    · subst b; simp [advance,eqn a ha]
    · have ne : d a ≠ d b := fun e => eq (dinj a ha b hb e)
      simp [advance, eq, ne, eqn b hb]

theorem selected_donor_word {r : Nat} {v l k : W} {h : Nat → W}
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (keep : W) (d : Nat → Nat)
    (uniform : ∀ a ∈ keep, v.count (d a) = r ∧ a ∈ h (d a))
    (dinj : ∀ a ∈ keep, ∀ b ∈ keep, d a = d b → a = b) :
    (select keep (l ++ v.flatMap h ++ k)).map d = select (keep.map d) v := by
  have exclusive (a) (ha : a ∈ keep) :=
    P455DonorInterval.exclusive h v (d a) a r hr (uniform a ha).1 (uniform a ha).2
      (by have := cap a; simp only [List.count_append] at this; omega)
  have disjoint (a) (ha : a ∈ keep) := P455DonorInterval.enclosing_context
    (v.flatMap h) l k a r (exclusive a ha).2.2 (cap a)
  have sl := select_nil keep l (fun a hm ha => (disjoint a ha).1 hm)
  have sk := select_nil keep k (fun a hm ha => (disjoint a ha).2 hm)
  rw [select_append, select_append, sl, sk, List.nil_append, List.append_nil]
  have owner (x) (hx : x ∈ v) (a) (ha : a ∈ keep) (in_h : a ∈ h x) : d a = x := by
    by_cases eq : x = d a
    · exact eq.symm
    · exact ((exclusive a ha).2.1 x hx eq in_h).elim
  have per (x) (hx : x ∈ v) :
      (select keep (h x)).map d = select (keep.map d) [x] := by
    by_cases mem : x ∈ keep.map d
    · obtain ⟨a,ha,eq⟩ := List.mem_map.mp mem
      have all_a (b) (hb : b ∈ select keep (h x)) : b = a := by
        obtain ⟨in_h,keep_b⟩ := List.mem_filter.mp hb
        have kb : b ∈ keep := by simpa using keep_b
        exact dinj b kb a ha ((owner x hx b kb in_h).trans eq.symm)
      have ct : (select keep (h x)).count a = 1 := by
        rw [select, List.count_filter (by simpa using ha), ← eq, (exclusive a ha).1]
      have len := List.count_eq_length.mpr (fun b hb => (all_a b hb).symm)
      have one : select keep (h x) = List.replicate 1 a :=
        List.eq_replicate_iff.mpr ⟨len.symm.trans ct, all_a⟩
      rw [one]
      simp only [select, List.filter_cons, mem, decide_true, if_true, List.filter_nil, List.replicate_succ, List.replicate_zero, List.map_cons, List.map_nil, eq]
    · have none := select_nil keep (h x) (fun a in_h ha =>
        mem (List.mem_map.mpr ⟨a,ha,owner x hx a ha in_h⟩))
      rw [none]
      simp only [select, List.filter_cons, mem, decide_false, Bool.false_eq_true, if_false, List.filter_nil, List.map_nil]
  have fit (w : W) (sub : ∀ x ∈ w, x ∈ v) :
      (select keep (w.flatMap h)).map d = select (keep.map d) w := by
    induction w with
    | nil => rfl
    | cons a ws ih =>
      change (select keep (h a ++ ws.flatMap h)).map d = select (keep.map d) ([a] ++ ws)
      rw [select_append, List.map_append, select_append, per a (sub a (by simp)),
        ih (fun b hb => sub b (by simp [hb]))]
  exact fit v (fun _ hmem => hmem)

theorem reflect_order {r : Nat} {v l k : W} {h : Nat → W}
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (keep : W) (d : Nat → Nat)
    (uniform : ∀ a ∈ keep, v.count (d a) = r ∧ a ∈ h (d a))
    (dinj : ∀ a ∈ keep, ∀ b ∈ keep, d a = d b → a = b)
    (pat : List Event) (inside : ∀ e ∈ pat, e.1 ∈ keep)
    (seen : sees (l ++ v.flatMap h ++ k) pat) : sees v (pat.map (eventMap d)) := by
  have selected := sees_select keep _ pat inside seen
  apply select_sees (keep.map d)
  have named := selected.map (eventMap d)
  unfold sees events at *
  rw [stamp_map d _ keep _ (fun _ => 0)
    (fun a ha => by have := (List.mem_filter.mp ha).2; simpa using this) dinj (fun _ _ => rfl),
    selected_donor_word hr cap keep d uniform dinj] at named
  exact named

theorem map_profile (d : Nat → Nat) (a b : Nat) (tag : Tag) (bit : Bool) :
    (profile a b tag bit).map d = profile (d a) (d b) tag bit := by
  have bp (c : Bool) : (pair a b c).map d = pair (d a) (d b) c := by cases c <;> rfl
  have tp : (tag.flatMap (pair a b)).map d = tag.flatMap (pair (d a) (d b)) := by
    induction tag with
    | nil => rfl
    | cons c tag ih => simp [bp, ih]
  simp only [profile,profilePrefix,List.map_append,bp,tp]
  rfl

private theorem two_labels {r : Nat} {v l k : W} {h : Nat → W} {x y s t : Nat}
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (hx : v.count x = r) (hy : v.count y = r) (hxy : x ≠ y) (hs : s ∈ h x) (ht : t ∈ h y) :
    ∃ d : Nat → Nat, d s = x ∧ d t = y ∧
        (∀ a ∈ [s,t], v.count (d a) = r ∧ a ∈ h (d a)) ∧
        (∀ a ∈ [s,t], ∀ b ∈ [s,t], d a = d b → a = b) := by
  have hy' : y ∈ v := List.count_pos_iff.mp (by omega)
  have diff : s ≠ t := by
    intro eq
    have excl := P455DonorInterval.exclusive h v x s r hr hx hs
      (by have := cap s; simp only [List.count_append] at this; omega)
    exact excl.2.1 y hy' (Ne.symm hxy) (eq ▸ ht)
  let d := fun a => if a = s then x else y
  have p : d s = x := by simp [d]
  have q : d t = y := by simp [d, Ne.symm diff]
  refine ⟨d,p,q,?_,?_⟩
  · intro a mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact p.symm ▸ And.intro hx hs
    · exact q.symm ▸ And.intro hy ht
  · intro a ha b hb e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

theorem reflect_profile {r : Nat} {v l k : W} {h : Nat → W} {x y s t : Nat}
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (hx : v.count x = r) (hy : v.count y = r) (hxy : x ≠ y) (hs : s ∈ h x) (ht : t ∈ h y)
    (tag : Tag) (bit : Bool) (eq : select [s,t] (l ++ v.flatMap h ++ k) = profile s t tag bit) :
    select [x,y] v = profile x y tag bit := by
  obtain ⟨d,p,q,uniform,inj⟩ := two_labels hr cap hx hy hxy hs ht
  have e := selected_donor_word hr cap [s,t] d uniform inj
  rw [eq,map_profile] at e
  simpa only [List.map_cons,List.map_nil,p,q] using e.symm

theorem reflect_order_query {r : Nat} {v l k : W} {h : Nat → W}
    {allow : Tag → Prop} {mark : Marking}
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (keep : W) (d : Nat → Nat)
    (uniform : ∀ a ∈ keep, v.count (d a) = r ∧ a ∈ h (d a))
    (dinj : ∀ a ∈ keep, ∀ b ∈ keep, d a = d b → a = b)
    (pat : List Event) (inside : ∀ e ∈ pat, e.1 ∈ keep)
    (seen : Holds r allow mark (l ++ v.flatMap h ++ k) (.order pat)) :
    Holds r allow mark v (.order (pat.map (eventMap d))) := by
  obtain ⟨imm, order⟩ := seen
  refine ⟨?_, reflect_order hr cap keep d uniform dinj pat inside order⟩
  rintro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  exact imm a ha

theorem reflect_contact {r : Nat} {allow : Tag → Prop} {mark : Marking}
    {v l k : W} {h : Nat → W} {x y s t : Nat}
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (hx : v.count x = r) (hy : v.count y = r) (hxy : x ≠ y) (hs : s ∈ h x) (ht : t ∈ h y)
    (c : ContactChoice) :
    Holds r allow mark (l ++ v.flatMap h ++ k) (contact r s t c) →
      Holds r allow mark v (contact r x y c) := by
  cases c with
  | record tag rev =>
    cases rev
    · rintro ⟨_,len,code,bit,eq⟩
      exact ⟨hxy,len,code,bit,reflect_profile hr cap hx hy hxy hs ht tag bit eq⟩
    · rintro ⟨_,len,code,bit,eq⟩
      exact ⟨Ne.symm hxy,len,code,bit,reflect_profile hr cap hy hx (Ne.symm hxy) ht hs tag bit eq⟩
  | port phase rev =>
    obtain ⟨d,p,q,uniform,inj⟩ := two_labels hr cap hx hy hxy hs ht
    have orders := @reflect_order_query r v l k h allow mark hr cap [s,t] d uniform inj
    have left (i j : Nat) (sig : Holds r allow mark (l ++ v.flatMap h ++ k) (earlier s i t j)) :
        Holds r allow mark v (earlier x i y j) := by
      have o := orders [(s,i),(t,j)] (by simp) sig
      simpa [eventMap,p,q,earlier] using o
    have right (i j : Nat) (sig : Holds r allow mark (l ++ v.flatMap h ++ k) (earlier t i s j)) :
        Holds r allow mark v (earlier y i x j) := by
      have o := orders [(t,i),(s,j)] (by simp) sig
      simpa [eventMap,p,q,earlier] using o
    intro core
    obtain ⟨_,_,_,early,ordered,_⟩ := core
    refine ⟨hxy,hx,hy,?_,?_,True.intro⟩
    · rcases early with ⟨o,_⟩ | ⟨o,_⟩
      · exact Or.inl ⟨left 2 0 o,True.intro⟩
      · exact Or.inr ⟨right 2 0 o,True.intro⟩
    · let i := 3 + 2 * phase.val
      cases rev with
      | false =>
        have o := orders [(s,i),(t,i),(s,i+1),(t,i+1)] (by simp) ordered
        simpa [eventMap,p,q,i] using o
      | true =>
        have o := orders [(t,i),(s,i),(t,i+1),(s,i+1)] (by simp) ordered
        simpa [eventMap,p,q,i] using o

end P455ContactReflection
