import Problem455Witness
import Problem455DonorInterval
import Problem455FactorSlots



namespace P455ContactGeometry
open Problem455.Slots P455Witness

/-- Erasing unselected labels preserves the indices of selected labels. -/
theorem project_stamp (keep w : Word) (n n' : Nat → Nat)
    (agree : ∀ a ∈ keep, n a = n' a) :
    stamp n (select keep w) = (stamp n' w).filter (fun e => decide (e.1 ∈ keep)) := by
  induction w generalizing n n' with
  | nil => rfl
  | cons a w ih =>
    by_cases ha : a ∈ keep
    · simp only [select, List.filter_cons, decide_eq_true ha, if_true, stamp]
      rw [agree a ha]
      congr 1
      apply ih
      intro b hb
      simp [advance, agree b hb]
    · simp only [select, List.filter_cons, decide_eq_false ha, Bool.false_eq_true, if_false, stamp]
      apply ih
      intro b hb
      have ne : a ≠ b := fun e => ha (e ▸ hb)
      simp [advance, ne, Ne.symm ne, agree b hb]

theorem projected_events_sublist (keep w : Word) : (events (select keep w)).Sublist (events w) := by
  rw [events, project_stamp keep w (fun _ => 0) (fun _ => 0) (fun _ _ => rfl)]
  exact List.filter_sublist ..

private theorem profile_initial {a b : Nat} (ab : a ≠ b) (tag : Tag) (bit : Bool) :
    [(a,0),(a,1),(b,0),(a,2),(b,1),(b,2)].Sublist (events (profile a b tag bit)) := by
  have shape : ∃ t : Word, profile a b tag bit = [a,a,b,a,b,b] ++ t := by
    unfold profile profilePrefix
    simp only [List.append_assoc]
    exact ⟨_,rfl⟩
  obtain ⟨t,e⟩ := shape
  rw [e,events,stamp_append]
  have pre : stamp (fun _ => 0) [a,a,b,a,b,b] = [(a,0),(a,1),(b,0),(a,2),(b,1),(b,2)] := by
    simp [stamp,advance,ab,Ne.symm ab]
  rw [pre]
  exact List.sublist_append_left ..

/-- A record supplies the two open slot witnesses and an early order that
    cannot occur between two labels donated by one uniform variable. -/
private theorem record_geometry {z : Word} {a b : Nat} {tag : Tag}
    (ab : a ≠ b) (typ : typed z a b tag) :
    occupies z a 1 b ∧ occupies z b 0 a ∧ sees z [(a,1),(b,0)] := by
  obtain ⟨bit,eq⟩ := typ
  have initial := profile_initial ab tag bit
  rw [← eq] at initial
  have sub := initial.trans (projected_events_sublist [a,b] z)
  refine ⟨⟨0,?_⟩,⟨2,?_⟩,?_⟩
  · exact (List.Sublist.cons _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (List.nil_sublist _))))).trans sub
  · exact (List.Sublist.cons _ (.cons _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (List.nil_sublist _)))))).trans sub
  · exact (List.Sublist.cons _ (.cons₂ _ (.cons₂ _ (List.nil_sublist _)))).trans sub

/-- The seven slots and the obstruction to a shared donor follow from
    the actual record or port contact. The port can be read in either direction. -/
theorem geometry {r allow mark z a b c} (hc : Holds r allow mark z (contact r a b c)) :
    (∃ i, slotStart i ∧ occupies z a i b) ∧
    (∃ i, 0 < i ∧ (sees z [(a,i),(b,0)] ∨ sees z [(b,i),(a,0)])) := by
  cases c with
  | record tag rev =>
    cases rev
    · obtain ⟨ab,_,_,typ⟩ := hc
      obtain ⟨slot,_,ord⟩ := record_geometry ab typ
      exact ⟨⟨1,by simp [slotStart],slot⟩,⟨1,by decide,.inl ord⟩⟩
    · obtain ⟨ba,_,_,typ⟩ := hc
      obtain ⟨_,slot,ord⟩ := record_geometry ba typ
      exact ⟨⟨0,by simp [slotStart],slot⟩,⟨1,by decide,.inr ord⟩⟩
  | port phase rev =>
    let i := 3+2*phase.val
    have hi : slotStart i := by have := phase.isLt; unfold i slotStart; omega
    have early : Holds r allow mark z (earlyDisjoint [a] [b]) := hc.2.2.2.1
    have ord : sees z [(a,2),(b,0)] ∨ sees z [(b,2),(a,0)] := by
      rcases early with e | e
      · exact .inl e.1.2
      · exact .inr e.1.2
    refine ⟨⟨i,hi,?_⟩,⟨2,by decide,ord⟩⟩
    cases rev
    · have seq : sees z [(a,i),(b,i),(a,i+1),(b,i+1)] := hc.2.2.2.2.1.2
      exact ⟨i,(List.Sublist.cons₂ _ (.cons₂ _ (.cons₂ _ (List.nil_sublist _)))).trans seq⟩
    · have seq : sees z [(b,i),(a,i),(b,i+1),(a,i+1)] := hc.2.2.2.2.1.2
      exact ⟨i+1,(List.Sublist.cons _ (.refl _)).trans seq⟩

theorem contact_slot {r allow mark z a b c} (hc : Holds r allow mark z (contact r a b c)) :
    ∃ i, slotStart i ∧ occupies z a i b := (geometry hc).1

/-- Membership of a stamped occurrence gives inclusive lower and exclusive
    upper bounds from the prefix counter and the number of copies in the segment. -/
theorem stamp_range (n : Nat → Nat) (w : Word) {a i : Nat} (h : (a,i) ∈ stamp n w) :
    n a ≤ i ∧ i < n a + w.count a := by
  induction w generalizing n with
  | nil => simp [stamp] at h
  | cons b w ih =>
    rcases List.mem_cons.mp h with head | tail
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj head
      simp [List.count_cons]
    · have z := ih _ tail
      by_cases e : b = a
      · subst b; simp [advance,List.count_cons] at z ⊢; omega
      · simp [advance,List.count_cons,e,Ne.symm e] at z ⊢; omega

private theorem impossible_order {z f t : Word} {a b i : Nat} (eq : z = f ++ t)
    (low : f.count a ≤ i) (positive : 0 < f.count b) : ¬ sees z [(a,i),(b,0)] := by
  intro e
  have h : [(a,i),(b,0)].Sublist (events f ++ stamp (advance (fun _ => 0) f) t) := by
    simpa only [sees, eq, events, stamp_append] using e
  have first : (a,i) ∉ events f := by
    intro mem
    have bad := (stamp_range (fun _ => 0) f mem).2
    simp only [Nat.zero_add] at bad
    omega
  have last : (b,0) ∉ stamp (advance (fun _ => 0) f) t := by
    intro mem
    have := stamp_range (advance (fun _ => 0) f) t mem
    simp [advance] at this
    omega
  have strip {α : Type} {x y : α} {l k : List α} (n : x ∉ l)
      (s : [x,y].Sublist (l ++ k)) : [x,y].Sublist k := by
    induction l with
    | nil => exact s
    | cons j l ih =>
      cases s with
      | cons _ rest => exact ih (fun e => n (by simp [e])) rest
      | cons₂ _ _ => exact (n (by simp)).elim
  exact last ((strip first h).subset (by simp))

/-- Initial source/prefix split at the first occurrence of one used name. -/
private theorem first_split (x : Nat) (v : Word) (occ : x ∈ v) :
    ∃ l t, v = l ++ x :: t ∧ x ∉ l := by
  induction v with
  | nil => simp at occ
  | cons a v ih =>
    by_cases e : a = x
    · subst a; exact ⟨[],v,rfl,by simp⟩
    · obtain ⟨l,t,eq,nh⟩ := ih (by simpa [Ne.symm e] using occ)
      exact ⟨a::l,t,by simp [eq],by simp [e,Ne.symm e,nh]⟩

/-- Two labels from the same donor each have exactly one occurrence in
    the prefix ending at its first image, even if the labels coincide. -/
theorem same_image_no_early {r : Nat} {v : Word} {h : Nat → Word}
    {l t : Word} {x a b i : Nat} (hr : 0 < r)
    (bound : P455Closure.Cap r (l ++ v.flatMap h ++ t))
    (hx : v.count x = r) (ha : a ∈ h x) (hb : b ∈ h x) (hi : 0 < i) :
    ¬ sees (l ++ v.flatMap h ++ t) [(a,i),(b,0)] := by
  have px : x ∈ v := List.count_pos_iff.mp (hx ▸ hr)
  obtain ⟨pre,post,cut,avoid⟩ := first_split x v px
  have bounds (j : Nat) (mem : j ∈ h x) : (l ++ pre.flatMap h ++ h x).count j = 1 := by
    have bb := bound j
    simp only [List.count_append] at bb
    obtain ⟨one,exclusive,sat⟩ := P455DonorInterval.exclusive h v x j r hr hx mem (by omega)
    have fresh : j ∉ pre.flatMap h := by
      intro z
      obtain ⟨y,hy,yj⟩ := List.mem_flatMap.mp z
      exact exclusive y (by simp [cut,hy]) (fun e => avoid (e ▸ hy)) yj
    have left : l.count j = 0 := by omega
    simp [List.count_append,left,List.count_eq_zero.mpr fresh,one]
  have eq : l ++ v.flatMap h ++ t = (l ++ pre.flatMap h ++ h x) ++ (post.flatMap h ++ t) := by
    simp [cut,List.flatMap_append,List.append_assoc]
  exact impossible_order eq (by rw [bounds a ha]; omega) (by rw [bounds b hb]; decide)

/-- An actual contact to a label donated by x cannot be another letter of
    h(x). Saturation is required only of the owner donor. -/
theorem contact_excludes_image {r allow mark} {v : Word} {h : Nat → Word}
    {l t : Word} {x a b c} (hr : 0 < r)
    (bound : P455Closure.Cap r (l ++ v.flatMap h ++ t))
    (hx : v.count x = r) (ha : a ∈ h x)
    (hc : Holds r allow mark (l ++ v.flatMap h ++ t) (contact r a b c)) : b ∉ h x := by
  intro hb
  obtain ⟨i,hi,ord⟩ := (geometry hc).2
  rcases ord with ord | ord
  · exact same_image_no_early hr bound hx ha hb hi ord
  · exact same_image_no_early hr bound hx hb ha hi ord

end P455ContactGeometry
