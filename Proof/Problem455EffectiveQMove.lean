import Problem455EffectiveQ


namespace P455EffectiveQMove
open P455Closure P455EffectiveQ
abbrev W := List Nat

def capB (r : Nat) (u : W) := u.all fun a => decide (u.count a ≤ r)

theorem cap_iff (r : Nat) (u : W) : capB r u=true ↔ Cap r u := by
  simp only [capB,List.all_eq_true,decide_eq_true_eq,Cap]
  constructor
  · intro h a; by_cases m : a∈u
    · exact h a m
    · simp [List.count_eq_zero_of_not_mem m]
  · exact fun h a _ => h a

def validB (r : Nat) (tags : List (List Bool)) (marks : Nat → Nat → Bool) (f : Frame Nat) :=
  decide (r = 16 + f.tag.length ∧ f.tag∈tags ∧ f.middle.map Prod.snd=fixedPhases f.tag ∧
    f.p.Nodup ∧ f.q.Nodup ∧ (∀ a∈f.p, a∉f.q) ∧
    (∀ a∈f.p, ∀ b∈f.q, marks a b=false ∧ marks b a=false) ∧
    (∀ a∈f.p++f.q,(f.core false).count a=r))

theorem valid_iff {tags marks allow mark} (tag_ok : ∀ t, t∈tags ↔ allow t)
    (mark_ok : ∀ a b,marks a b=true ↔ mark a b)
    (r : Nat) (f : Frame Nat) : validB r tags marks f=true ↔ f.Valid r allow mark := by
  have unmarked (a b) : marks a b=false ↔ ¬mark a b := by
    rw [←mark_ok]; cases marks a b <;> decide
  simp only [validB,decide_eq_true_eq,Frame.Valid,tag_ok,unmarked,List.mem_append]

def entries (u : W) := (words u).flatMap (fun g => [(g,false),(g,true)])

def frames (tags : List (List Bool)) (u : W) : List (Frame Nat) :=
  tags.flatMap fun t => u.flatMap fun a => (words u).flatMap fun p =>
  (words u).flatMap fun q => u.flatMap fun z =>
  (Problem455Finite.wordsUpTo (entries u) (fixedPhases t).length).flatMap fun es =>
  (words u).flatMap fun m => (words u).flatMap fun l =>
  (words u).map fun n => ⟨a,p,q,z,t,es,m,l,n⟩

private theorem left {u a b : W} (h : u.Sublist a) : u.Sublist (a++b) :=
  h.trans (List.sublist_append_left _ _)
private theorem right {u a b : W} (h : u.Sublist b) : u.Sublist (a++b) :=
  h.trans (List.sublist_append_right _ _)

theorem frame_mem {tags allow r mark} (tag_ok : ∀ t,t∈tags ↔ allow t)
    (f : Frame Nat) (b : Bool) (l t : W) (fv : f.Valid r allow mark) :
    f ∈ frames tags (l++f.core b++t) := by
  let u := l++f.core b++t
  have core : (f.core b).Sublist u := left (right (List.Sublist.refl _))
  have within (s : W) (hs : s.Sublist (f.core b)) : s.Sublist u := hs.trans core
  have early : f.early.Sublist u := within _ (left (left (left (left (left (left (left (.refl _))))))))
  have pp : f.p.Sublist u :=
    (show f.p.Sublist f.early from left (left (left (left (left (.refl _)))))).trans early
  have qq : f.q.Sublist u := (right (.refl _) : f.q.Sublist f.early).trans early
  have a : f.pHead∈u := pp.subset (by simp [Frame.p])
  have z : f.qLast∈u := qq.subset (by simp [Frame.q])
  have pt : f.pTail∈words u := subword ((List.sublist_cons_self ..).trans pp)
  have qi : f.qInit∈words u := subword ((List.sublist_append_left ..).trans qq)
  have mid : f.mid.Sublist u := within _ (left (left (left (left (left (left (right (.refl _))))))))
  have m : f.beforeMutable∈words u := subword (within _ (left (left (left (left (left (right (.refl _))))))))
  have p : f.beforeFinalP∈words u := subword (within _ (left (left (left (right (.refl _))))))
  have n : f.beforeFinalQ∈words u := subword (within _ (left (right (.refl _))))
  have es : f.middle ∈ Problem455Finite.wordsUpTo (entries u) (fixedPhases f.tag).length := by
    have sz := congrArg List.length fv.2.2.1
    apply Problem455Finite.covered _ _ _ (by simpa using Nat.le_of_eq sz)
    rintro ⟨g,v⟩ mem
    have item : g.Sublist f.mid := by
      let B := fun e : W×Bool => e.1 ++ (if e.2 then f.q else f.p)
      have item : (B (g,v)).Sublist ((f.middle.map B).flatten) :=
        List.sublist_flatten_of_mem (List.mem_map_of_mem mem)
      exact (List.sublist_append_left g _).trans (by simpa [Frame.mid,List.flatMap_def,B] using item)
    have gg := subword (item.trans mid)
    apply List.mem_flatMap.mpr
    exact ⟨g,gg,by cases v <;> simp⟩
  change f ∈ frames tags u
  simp only [frames,List.mem_flatMap,List.mem_map]
  exact ⟨f.tag,(tag_ok _).mpr fv.2.1,f.pHead,a,f.pTail,pt,f.qInit,qi,f.qLast,z,f.middle,es,
    f.beforeMutable,m,f.beforeFinalP,p,f.beforeFinalQ,n,rfl⟩

theorem min_length {r allow} {mark : Nat → Nat → Prop} {u v : W} (h : Move r allow mark u v) : r ≤ u.length := by
  obtain ⟨f,b,l,t,valid,rfl,_,_⟩ := h
  have sat := valid.2.2.2.2.2.2.2 f.pHead (.inl (by simp [Frame.p]))
  have count : (f.core b).count f.pHead=r := by
    cases b with
    | false => exact sat
    | true => exact (f.count_core f.pHead true).trans sat
  have len := List.count_le_length (a := f.pHead) (l := f.core b)
  simp only [List.length_append]
  omega

def moveB (r : Nat) (tags : List (List Bool)) (marks : Nat → Nat → Bool) (u v : W) :=
  decide (r ≤ u.length) && capB r u && (frames tags u).any fun f => validB r tags marks f && [false,true].any fun b =>
    (words u).any fun l => (words u).any fun t =>
      decide (u=l++f.core b++t ∧ v=l++f.core (!b)++t)

theorem move_iff {tags marks allow mark} (tag_ok : ∀ t,t∈tags ↔ allow t)
    (mark_ok : ∀ a b,marks a b=true ↔ mark a b)
    (r : Nat) (u v : W) : moveB r tags marks u v=true ↔ Move r allow mark u v := by
  simp only [moveB,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq,
    cap_iff,valid_iff tag_ok mark_ok]
  constructor
  · rintro ⟨⟨_,cap⟩,f,_,fv,b,_,l,_,t,_,src,dst⟩; exact ⟨f,b,l,t,fv,src,dst,cap⟩
  · intro h
    have len := min_length h
    obtain ⟨f,b,l,t,fv,rfl,rfl,cp⟩ := h
    exact ⟨⟨len,cp⟩,f,frame_mem tag_ok f b l t fv,fv,b,by cases b <;> simp,l,
      subword (left (left (.refl _))),t,subword (right (.refl _)),rfl,rfl⟩

def markedEq {tags : List (List Bool)} {marks : Nat → Nat → Bool}
    {allow : List Bool → Prop} {mark : Nat → Nat → Prop} (tag_ok : ∀ t,t∈tags ↔ allow t)
    (mark_ok : ∀ a b,marks a b=true ↔ mark a b) (r : Nat) (T : W) :
    DecidableEq (P455Quotient.Q (Problem455Finite.rules r allow mark) T) :=
  P455EffectiveQ.decEq _ (moveB r tags marks) (move_iff tag_ok mark_ok r) T

end P455EffectiveQMove
