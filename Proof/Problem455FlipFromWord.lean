import Problem455ChartSchedule
import Problem455PrivatePhase
import Problem455CellClassFrames



namespace P455FlipFromWord
open P455Witness P455Closure P455ChartSchedule P455Structural P455CellClassFrames Problem455.Slots
abbrev W := List Nat

private theorem profile_head (x y : Nat) (tag : Tag) :
    profilePrefix x y tag = early x y ++ phase x y tag := by
  have tags : (tag.flatMap phasePair).map (token x y)=tag.flatMap (Problem455.Slots.pair x y) := by
    induction tag with
    | nil => rfl
    | cons c cs ih => cases c <;> simp [List.flatMap_cons,ih,phasePair,token,Problem455.Slots.pair]
  simp [profilePrefix,early,phase,fixedPhases,List.replicate_succ,tags,phasePair,token]

theorem literal {r allow} (n : Node) (pre post : W) (b : Bool)
    (cap : P455Closure.Cap r (pre++Problem455.Slots.pair n.owner n.mate b++post))
    (rec : Holds r allow (fun _ _ => False) (pre++Problem455.Slots.pair n.owner n.mate b++post) (typedNode n))
    (clean : Closed (pre++Problem455.Slots.pair n.owner n.mate b++post) n.owner n.mate)
    (cx : pre.count n.owner=r-2) (cy : pre.count n.mate=r-2) :
    Nonempty (Literal r allow (pre++Problem455.Slots.pair n.owner n.mate b++post)
      (pre++Problem455.Slots.pair n.owner n.mate (!b)++post) n) := by
  let x := n.owner
  let y := n.mate
  let k := [x,y]
  obtain ⟨ne,len,allowed,b',pr⟩ := rec
  have neq : x≠y := ne
  have projPair (c : Bool) : select k (Problem455.Slots.pair x y c)=Problem455.Slots.pair x y c := by
    cases c <;> simp [select,Problem455.Slots.pair,k]
  change select k (pre++Problem455.Slots.pair x y b++post)=profile x y n.tag b' at pr
  rw [select_append, select_append, projPair,profile,List.append_assoc] at pr
  have length : (select k pre).length=(profilePrefix x y n.tag).length := by
    rw [length_select_pair _ _ neq,profile_prefix_length]
    change pre.count n.owner + pre.count n.mate = 2*(14+n.tag.length)
    omega
  obtain ⟨headEq,tailEq⟩ := List.append_inj pr length
  obtain ⟨_,endEq⟩ := List.append_inj tailEq (by cases b <;> cases b' <;> rfl)
  obtain ⟨_,l,t,cut,lx,ly⟩ := clean
  have prefix₁ : (l++early x y) <+: (pre++Problem455.Slots.pair x y b++post) := ⟨t,cut.symm⟩
  have prefix₂ : pre <+: (pre++Problem455.Slots.pair x y b++post) :=
    ⟨_,(List.append_assoc ..).symm⟩
  have before : (l++early x y) <+: pre := by
    rcases List.prefix_or_prefix_of_prefix prefix₁ prefix₂ with yes|reverse
    · exact yes
    · obtain ⟨u,eq⟩ := reverse
      have h := congrArg (List.count x) eq
      have nl : l.count x=0 := List.count_eq_zero.mpr lx
      have small : (early x y).count x=3 := by simp [early,List.count_cons,neq,Ne.symm neq]
      simp only [List.count_append,nl,small,Nat.zero_add] at h
      change pre.count x=r-2 at cx; omega
  obtain ⟨m,meq⟩ := before
  have erase : select k l=[] := select_nil _ _ (fun z mem h => by
    rcases (show z=x ∨ z=y by simpa [k] using h) with rfl|rfl
    · exact lx mem
    · exact ly mem)
  have fixedEarly : select k (early x y)=early x y := by simp [select,k,early]
  rw [← meq,select_append,select_append,erase,fixedEarly,List.nil_append,profile_head] at headEq
  have mid := List.append_cancel_left headEq
  have subM : (phase x y n.tag).Sublist m := mid ▸ List.filter_sublist ..
  have subZ : [x,y].Sublist post := endEq ▸ List.filter_sublist ..
  have cc : P455Closure.Cap r (displayed l x y m post false) := by
    intro a
    have h := cap a
    have eq (c : Bool) : (Problem455.Slots.pair x y c).count a =
        (Problem455.Slots.pair x y false).count a := by
      cases c <;> simp [Problem455.Slots.pair,List.count_cons,Nat.add_comm,Nat.add_left_comm]
    change (pre++Problem455.Slots.pair x y b++post).count a ≤ r at h
    simp only [← meq,displayed,List.count_append,eq b] at h ⊢
    exact h
  obtain ⟨f,h,hp,hq,hf,words⟩ := from_phases neq n.tag len allowed l m post subM subZ cc
  refine ⟨⟨f,b,l,h,hp,hq,hf,?_,?_⟩⟩ <;>
    simpa only [x,y,displayed,meq] using (words _)

end P455FlipFromWord
