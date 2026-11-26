import Problem455PaddedIndexed
import Problem455SlotOrigin



namespace P455PaddedPorts
open P455RectangleRank Problem455.Slots

def Covered (w : W) (a k : Nat) := ∃ small : W, small.length≤4 ∧
  ∀ z, occupies w a k z → z∈small

private theorem trim {α : Type} (a : α) (t l m : List α) (h : a∉l)
    (sub : (a::t).Sublist (l++m)) : (a::t).Sublist m := by
  induction l with
  | nil => exact sub
  | cons z l ih =>
    cases sub with
    | cons _ s => exact ih (fun mem=>h (List.mem_cons_of_mem _ mem)) s
    | cons₂ _ _ => exact (h List.mem_cons_self).elim

/-- If the two bounding indexed occurrences are in one literal factor,
the occupant occurs in that factor, even if other copies occur elsewhere. -/
theorem occupant_in_factor (l m t : W) (a k z : Nat) (start : l.count a≤k)
    (finish : k+1<l.count a+m.count a) (occ : occupies (l++m++t) a k z) : z∈m := by
  obtain ⟨j,sub⟩ := occ
  unfold sees at sub
  rw [events_of_factor] at sub
  have nl : (a,k)∉events l := by
    intro e; have := (P455ContactGeometry.stamp_range (fun _=>0) l e).2
    omega
  have nt : (a,k+1) ∉ stamp (fun x=>l.count x+m.count x) t := by
    intro e; have := (P455ContactGeometry.stamp_range (fun x=>l.count x+m.count x) t e).1
    omega
  have rest := trim _ _ _ _ nl sub
  have back := rest.reverse
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append,List.singleton_append] at back
  have small := (trim _ _ _ _ (by simpa using nt : (a,k+1) ∉ (stamp (fun x=>l.count x+m.count x) t).reverse) back).reverse
  have mid : [(a,k),(z,j),(a,k+1)].Sublist ((events m).map (shift (fun x=>l.count x))) := by simpa using small
  obtain ⟨e,em,ev⟩ := List.mem_map.mp (mid.subset (by simp : (z,j)∈[(a,k),(z,j),(a,k+1)]))
  have lab := congrArg Prod.fst ev
  change e.1=z at lab
  rw [←lab]; exact stamped_mem_label (fun _=>0) m e em

theorem private_slot_bound (l t : W) (c a k : Nat) (role : a∈roles c) (lo : l.count a=0)
    (early : k=0 ∨ k=1) : Covered (l++privateCell c++t) a k := by
  refine ⟨roles c,by simp [roles],?_⟩
  intro z occ
  have ne : owner c≠mate c := by simp [owner,mate]
  have count : (privateCell c).count a=3 := by
    rcases (show a=owner c ∨ a=mate c by simpa [roles] using role) with rfl|rfl <;>
      simp [privateCell,List.count_cons,ne,Ne.symm ne]
  have mem := occupant_in_factor l (privateCell c) t a k z (by omega) (by omega) occ
  simpa [privateCell,roles,or_assoc,or_left_comm,or_comm] using mem

private theorem letters_split (l t : List Block) :
    letters (l++t)=letters l++letters t := by simp [letters,phase,List.flatMap_append]

private theorem block_letters (b : Block) (t : List Block) :
    letters (b::t)=(cells b).flatMap roles ++ (cells b).flatMap roles ++ letters t := by
  simp [letters,phase,List.flatMap_cons,List.flatMap_append,List.append_assoc]

private theorem role_from (x a c : Nat) (m : a∈roles c) (same : a∈roles x) : c=x := by
  simp only [roles,List.mem_cons,List.not_mem_nil,or_false] at m same
  unfold owner mate at m same; omega

private theorem index_mem (bs : List Block) (a c : Nat) (role : a∈roles c)
    (m : a∈letters bs) : c∈bs.flatMap cells := by
  obtain ⟨x,hx,mx⟩ := List.mem_flatMap.mp m
  have eq := role_from _ _ _ role mx
  rw [eq]
  obtain ⟨b,hb,inBlock⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨b,hb,by simpa using inBlock⟩

theorem matching_slot_bound {bs : List Block} (nd : (bs.flatMap cells).Nodup)
    {l t : W} (c a k : Nat) (role : a∈roles c) (present : c∈bs.flatMap cells)
    (index : l.count a=k) : Covered (l++letters bs++t) a k := by
  obtain ⟨b,inBs,inBlock⟩ := List.mem_flatMap.mp present
  obtain ⟨pre,post,e⟩ := List.append_of_mem inBs
  subst bs
  simp only [List.flatMap_append,List.flatMap_cons] at nd
  have ds := (List.pairwise_append.mp nd).2.2
  have noPre : a∉letters pre := by
    intro hm
    exact ds c (index_mem pre a c role hm) c (List.mem_append_left _ inBlock) rfl
  let names := (cells b).flatMap roles
  have has : a∈names := List.mem_flatMap.mpr ⟨c,inBlock,role⟩
  have size : names.length≤4 := by cases b <;> simp [names,cells,roles]
  have positive := List.count_pos_iff.mpr has
  have cut : l++letters (pre++b::post)++t=(l++letters pre)++(names++names)++(letters post++t) := by
    rw [letters_split,block_letters]; simp [names,List.append_assoc]
  have left : (l++letters pre).count a=k := by simp [List.count_eq_zero.mpr noPre,index]
  refine ⟨names,size,?_⟩
  intro z occ
  rw [cut] at occ
  have hit := occupant_in_factor (l++letters pre) (names++names) (letters post++t) a k z
    (by omega) (by simp only [List.count_append] at left ⊢; omega) occ
  simpa using hit

end P455PaddedPorts
