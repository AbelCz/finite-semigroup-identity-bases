import Problem455ContactLift




namespace P455Retained
open Problem455.Slots P455Witness P455Paths P455ContactLift

structure Expansion (v : W) (e : Nat → W) (kept : Nat → Prop) : Prop where
  literal : ∀ x ∈ v, kept x → e x = [x]
  gaps : ∀ g ∈ v, ¬ kept g → v.count g = 1 ∧ e g ≠ [] ∧ ∀ a ∈ e g, ¬ kept a

/-- Projecting onto any chosen retained labels commutes with expansion. -/
theorem Expansion.select_eq {v e kept} (exp : Expansion v e kept)
    (s keep : W) (sub : ∀ a ∈ s, a ∈ v) (hk : ∀ a ∈ keep, kept a) :
    select keep (s.flatMap e) = select keep s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have hx := sub x (by simp)
    have rs := ih (fun a ha => sub a (by simp [ha]))
    change select keep (e x ++ xs.flatMap e) = select keep ([x] ++ xs)
    rw [select_append,select_append,rs]
    by_cases keep_x : kept x
    · rw [exp.literal x hx keep_x]
    · have gap := exp.gaps x hx keep_x
      rw [select_nil keep (e x) (fun a ha ab => gap.2.2 a ha (hk a ab))]
      have no : x ∉ keep := fun h => keep_x (hk x h)
      simp [select,no]

theorem Expansion.count_eq {v e kept} (exp : Expansion v e kept)
    (s : W) (sub : ∀ a ∈ s, a ∈ v) (x : Nat) (hx : kept x) :
    (s.flatMap e).count x = s.count x := by
  have h := congrArg (List.count x) (exp.select_eq s [x] sub (by simpa using hx))
  simpa [select] using h

theorem Expansion.small_cap {v e kept r} (exp : Expansion v e kept) (hr : 1 < r)
    (cap : P455Closure.Cap r (v.flatMap e)) : P455Closure.Cap r v := by
  intro x
  by_cases use : x ∈ v
  · by_cases k : kept x
    · rw [← exp.count_eq v (fun _ h => h) x k]; exact cap x
    · rw [(exp.gaps x use k).1]; omega
  · rw [List.count_eq_zero.mpr use]; omega

theorem contact_counts {r allow mark v x y c} (cap : P455Closure.Cap r v)
    (h : Holds r allow mark v (contact r x y c)) : v.count x = r ∧ v.count y = r := by
  cases c with
  | record tag rev =>
    cases rev
    · exact record_counts cap h
    · exact (record_counts cap h).symm
  | port phase rev => exact ⟨h.2.1,h.2.2.1⟩

theorem Expansion.contact {v e kept r allow mark x y} (exp : Expansion v e kept) (hr : 1 < r)
    (cap : P455Closure.Cap r (v.flatMap e)) (c : ContactChoice)
    (edge : Holds r allow mark v (P455Witness.contact r x y c)) :
    Holds r allow mark (v.flatMap e) (P455Witness.contact r x y c) := by
  obtain ⟨xc,yc⟩ := contact_counts (exp.small_cap hr cap) edge
  have used (a) (count : v.count a = r) : kept a := by
    apply Classical.byContradiction
    intro k
    have hm : a ∈ v := List.count_pos_iff.mp (by omega)
    have := (exp.gaps a hm k).1; omega
  have xx := used x xc
  have yy := used y yc
  have eq (a b) (ha : kept a) (hb : kept b) : select [a,b] (v.flatMap e) = select [a,b] v :=
    exp.select_eq v [a,b] (fun _ h => h) (by simpa using And.intro ha hb)
  have ord (pat : List Event) (inside : ∀ a ∈ pat, a.1 ∈ [x,y])
      (old : Holds r allow mark v (.order pat)) : Holds r allow mark (v.flatMap e) (.order pat) := by
    refine ⟨old.1, P455ContactReflection.select_sees [x,y] _ pat ?_⟩
    rw [eq x y xx yy]
    exact P455ContactReflection.sees_select _ _ _ inside old.2
  cases c with
  | record tag rev =>
    cases rev with
    | false =>
      obtain ⟨ne,len,tag,bit,hp⟩ := edge
      exact ⟨ne,len,tag,bit,(eq x y xx yy).trans hp⟩
    | true =>
      obtain ⟨ne,len,tag,bit,hp⟩ := edge
      exact ⟨ne,len,tag,bit,(eq y x yy xx).trans hp⟩
  | port port rev =>
    obtain ⟨ne,_,_,early,order,_⟩ := edge
    refine ⟨ne,(exp.count_eq _ (fun _ h => h) x xx).trans xc,
      (exp.count_eq _ (fun _ h => h) y yy).trans yc,?_,?_,True.intro⟩
    · rcases early with l|rr
      · exact .inl ⟨ord _ (by simp) l.1,True.intro⟩
      · exact .inr ⟨ord _ (by simp) rr.1,True.intro⟩
    · cases rev <;> exact ord _ (by simp) order

theorem Expansion.walk {v e kept r allow mark} (exp : Expansion v e kept) (hr : 1 < r)
    (cap : P455Closure.Cap r (v.flatMap e)) (s : Nat) (p : List Step)
    (walk : Walk r allow mark v s p) : Walk r allow mark (v.flatMap e) s p := by
  induction p generalizing s with
  | nil => exact True.intro
  | cons step ps ih => exact ⟨exp.contact hr cap step.2 walk.1, ih _ walk.2⟩

theorem Expansion.near {v e kept r allow mark} (exp : Expansion v e kept) (hr : 1 < r)
    (cap : P455Closure.Cap r (v.flatMap e)) {s t J : Nat} (near : Near r allow mark v s t J) :
    Near r allow mark (v.flatMap e) s t J := by
  obtain ⟨p,h,ep,le⟩ := near
  exact ⟨p,exp.walk hr cap s p h,ep,le⟩

/-- An occurrence in a small open slot contributes every letter of its
    expansion inside the corresponding literal open slot of the original.
    For an unretained variable the nonempty gap gives a genuine occupant. -/
theorem Expansion.in_original_slot {v e kept} (exp : Expansion v e kept) (x i y : Nat) (kx : kept x)
    (ho : occupies v x i y) (a : Nat) (ha : a ∈ e y) : occupies (v.flatMap e) x i a := by
  obtain ⟨j,hj⟩ := ho
  have hm : (x,i+1) ∈ events v := hj.mem (by simp)
  have bound : i+1 < v.count x := by simpa using (P455SlotOrigin.event_bounds (fun _ => 0) _ x _ hm).2
  obtain ⟨L,I,R,cut,idx,cons⟩ := P455SlotOrigin.slot_cut v x i bound
  have hy : y ∈ I := by
    apply (P455SlotOrigin.occupies_at_cut L I R x y cons).mp
    rw [←cut,idx]; exact ⟨j,hj⟩
  have hI : (I.flatMap e).count x = I.count x := exp.count_eq I (fun a h => by simp [cut,h]) x kx
  have fresh : x ∉ I.flatMap e := List.count_eq_zero.mp (hI.trans (List.count_eq_zero.mpr cons))
  have pref := exp.count_eq L (fun a h => by simp [cut,h]) x kx
  have ex := exp.literal x (by simp [cut]) kx
  have expanded : v.flatMap e =
      (L.flatMap e) ++ [x] ++ I.flatMap e ++ [x] ++ R.flatMap e := by
    simp [cut,ex,List.flatMap_append]
  rw [expanded,←idx,←pref]
  exact (P455SlotOrigin.occupies_at_cut _ _ _ _ _ fresh).mpr (List.mem_flatMap.mpr ⟨y,hy,ha⟩)

theorem Expansion.slot_guard {v e kept r} (exp : Expansion v e kept)
    (x i : Nat) (kx : kept x)
    (original : ∀ a, occupies (v.flatMap e) x i a → kept a ∧ (v.flatMap e).count a = r) :
    ∀ y, occupies v x i y → v.count y = r := by
  intro y ho
  obtain ⟨j,obs⟩ := ho
  have used : y ∈ v := stamped_mem_label _ _ (y,j) (obs.mem (by simp))
  by_cases ky : kept y
  · have mem : y ∈ e y := by rw [exp.literal y used ky]; simp
    have claim := (original y (exp.in_original_slot x i y kx ⟨j,obs⟩ y mem)).2
    exact (exp.count_eq v (fun _ h => h) y ky).symm.trans claim
  · have gap := exp.gaps y used ky
    obtain ⟨a,ha⟩ : ∃ a, a ∈ e y := by
      cases he : e y with
      | nil => exact (gap.2.1 he).elim
      | cons a rest => exact ⟨a,by simp⟩
    exact (gap.2.2 a ha (original a (exp.in_original_slot x i y kx ⟨j,obs⟩ a ha)).1).elim

/-- Derive the guard on the actual smaller rule from the retention of the
    original radius-J contact ball and the uniformity of its slot occupants. -/
theorem Expansion.guard {v e kept r allow mark seed J} (exp : Expansion v e kept)
    (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    (original : ∀ x, Near r allow mark (v.flatMap e) seed x J →
      kept x ∧ ∀ i, slotStart i → ∀ y, occupies (v.flatMap e) x i y →
        kept y ∧ (v.flatMap e).count y = r) :
    Guard r allow mark v seed J := by
  intro x near i hi
  obtain ⟨kx,slots⟩ := original x (exp.near hr cap near)
  exact exp.slot_guard x i kx (slots i hi)

end P455Retained
