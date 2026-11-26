import Problem455PaddedWordSlots
import Problem455PortReflection


namespace P455PaddedWord
open P455PaddedPorts P455PaddedMatchings P455RectangleRank P455Witness Problem455.Slots

private theorem in_stamp (n : Nat→Nat) (w : List Nat) {a j : Nat}
    (lo : n a≤j) (hi : j<n a+w.count a) : (a,j)∈stamp n w := by
  obtain ⟨p,t,e,ct⟩ := P455SlotOrigin.occurrence_cut w a (j-n a) (by omega)
  rw [e,stamp_append,stamp]
  apply List.mem_append_right
  have idx : advance n p a=j := by simp [advance,ct]; omega
  rw [idx]; exact List.mem_cons_self

theorem sees_across (l t : List Nat) (a i b j : Nat) (inL : i<l.count a)
    (inR : l.count b≤j) (both : j<(l++t).count b) : sees (l++t) [(a,i),(b,j)] := by
  unfold sees events
  rw [stamp_append]
  have left : (a,i)∈stamp (fun _=>0) l := in_stamp _ l (by omega) (by simpa using inL)
  have right : (b,j)∈stamp (advance (fun _=>0) l) t := by
    apply in_stamp <;> simp [advance,List.count_append] at * <;> omega
  exact ((List.singleton_sublist.mpr left).append (List.singleton_sublist.mpr right) :
    ([(a,i)]++[(b,j)]).Sublist _)

theorem early_order {h w k : Nat} (size : 1<w*h) (tag : Nat→Tag) (bits : Nat→Bool)
    (allow : Tag→Prop) (mark : Marking) {i j a b e f : Nat} (lt : i<j) (last : j<w*h)
    (ra : a∈roles i) (rb : b∈roles j) (ei : e<3) (fi : f<3) :
    Holds (k+16) allow mark (text h w k tag bits) (earlier a e b f) := by
  refine ⟨?_,?_⟩
  · intro u m
    rcases (show u=(a,e) ∨ u=(b,f) by simpa using m) with rfl|rfl <;> dsimp <;> omega
  · obtain ⟨post,cut⟩ := private_cut tag bits last
    have total := word_count (k:=k) size tag bits j b rb
    rw [if_pos last] at total
    change (text h w k tag bits).count b=_ at total
    rw [cut,List.append_assoc] at total ⊢
    apply sees_across
    · simpa [private_counts i a ra,lt] using ei
    · simp [private_counts j b rb]
    · omega

theorem early_groups {h w k : Nat} (size : 1<w*h) (tag : Nat→Tag) (bits : Nat→Bool)
    (allow : Tag→Prop) (mark : Marking) {i j : Nat} (ne : i≠j) (li : i<w*h) (lj : j<w*h) :
    Holds (k+16) allow mark (text h w k tag bits) (earlyDisjoint (roles i) (roles j)) := by
  by_cases e : i<j
  · apply Or.inl
    exact (P455PortReflection.earlyBefore_iff ..).mpr
      (fun _ ra _ rb => early_order size tag bits allow mark e lj ra rb (by decide) (by decide))
  · apply Or.inr
    exact (P455PortReflection.earlyBefore_iff ..).mpr
      (fun _ ra _ rb => early_order size tag bits allow mark (by omega : j<i) li ra rb (by decide) (by decide))

theorem first_owner {h w k : Nat} (size : 1<w*h) (tag : Nat→Tag) (bits : Nat→Bool)
    (allow : Tag→Prop) (mark : Marking) {i j : Nat} (lt : i<j) (last : j<w*h) :
    Holds (k+16) allow mark (text h w k tag bits) (earlier (owner i) 0 (owner j) 0) :=
  early_order size tag bits allow mark lt last (by simp [roles]) (by simp [roles]) (by decide) (by decide)

private theorem adjacent_column_cut {h w y x : Nat} (ly : y<h) (lx : x+1<w) :
    ∃ l t, columnCells h w=l++idAt w y x::idAt w y (x+1)::t := by
  let restRow := List.range' (x+1+1) (w-(x+1+1))
  have ec := range_cut lx
  rw [List.range_succ] at ec
  change List.range w=(List.range x ++ [x]) ++ (x+1) :: restRow at ec
  have er := range_cut ly
  let emit := fun z=>(List.range w).map (idAt w z)
  refine ⟨(List.range y).flatMap emit ++ (List.range x).map (idAt w y),
    restRow.map (idAt w y) ++ (List.range' (y+1) (h-(y+1))).flatMap emit,?_⟩
  unfold columnCells
  rw [er,List.flatMap_append,List.flatMap_cons]
  change _ ++ (emit y ++ _) = _
  have row : emit y=(List.range x).map (idAt w y) ++ idAt w y x :: idAt w y (x+1) :: restRow.map (idAt w y) := by
    unfold emit; rw [ec]; simp [List.map_append,List.append_assoc]
  rw [row]; simp [List.append_assoc,emit]

private theorem tags_counts {h w k : Nat} (tag : Nat→Tag) {i a : Nat} (role : a∈roles i) (lt : i<w*h) :
    ((List.range k).flatMap (tagPhase (w*h) tag)).count a=k := by
  have z := suffix_count (h:=h) (w:=w) (k:=k) tag i a role
  rw [if_pos lt,suffix,List.count_append,count_role _ i a (by simpa [roles] using role),
    count_one (columns_unique h w) ((columns_cells h w i).mpr lt)] at z
  omega

/-- True for the left-to-right adjacent coordinates on both row parities.
Their numeric snake IDs may be increasing or decreasing. -/
theorem column_order {h w k : Nat} (size : 1<w*h) (tag : Nat→Tag) (bits : Nat→Bool)
    (allow : Tag→Prop) (mark : Marking) {y x : Nat} (ly : y<h) (lx : x+1<w) :
    Holds (k+16) allow mark (text h w k tag bits)
      (earlier (owner (idAt w y x)) (13+k) (owner (idAt w y (x+1))) (13+k)) := by
  let i := idAt w y x
  let j := idAt w y (x+1)
  have ix : i<w*h := id_bound ly (by omega)
  have jx : j<w*h := id_bound ly lx
  obtain ⟨l,t,cut⟩ := adjacent_column_cut ly lx
  have nd := columns_unique h w
  rw [cut] at nd
  have dedup := List.pairwise_append.mp nd
  have noJ : j∉l ++ [i] := by
    intro m
    rcases List.mem_append.mp m with m|m
    · exact dedup.2.2 j m j (by simp [i,j]) rfl
    · have ne := (List.nodup_cons.mp dedup.2.1).1
      have eq : j=i := by simpa using m
      exact ne (List.mem_cons.mpr (.inl eq.symm))
  let core := (List.range (w*h)).flatMap privateCell ++ portChunks h w 5 ++
    (List.range k).flatMap (tagPhase (w*h) tag)
  let L := core ++ (l++[i]).flatMap roles
  let Z := (j::t).flatMap roles ++ (List.range (w*h)).flatMap (mutableCell bits) ++ tail (w*h)
  have whole : text h w k tag bits=L++Z := by
    change columnCells h w=l++i::j::t at cut
    simp [text,word,middle,suffix,cut,L,Z,core,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have occur (u : Nat) (hu : u<w*h) : core.count (owner u)=13+k := by
    have role : owner u∈roles u := by simp [roles]
    simp [core,List.count_append,private_counts u _ role,chunks_count size 5 u _ role,tags_counts tag role hu,hu]; omega
  have left : 13+k<L.count (owner i) := by
    have one := List.count_pos_iff.mpr (show i∈l++[i] by simp)
    dsimp only [L]
    rw [List.count_append,count_role _ i _ (.inl rfl),occur i ix]; omega
  have right : L.count (owner j)=13+k := by
    dsimp only [L]
    rw [List.count_append,count_role _ j _ (.inl rfl),occur j jx,List.count_eq_zero.mpr noJ,Nat.add_zero]
  have total := word_count (k:=k) size tag bits j (owner j) (by simp [roles])
  rw [if_pos jx] at total
  change (text h w k tag bits).count (owner j)=_ at total
  change Holds (k+16) allow mark (text h w k tag bits) (earlier (owner i) (13+k) (owner j) (13+k))
  rw [whole] at total ⊢
  refine ⟨?_,sees_across _ _ _ _ _ _ left (by omega) (by omega)⟩
  intro e m
  rcases (show e=(_,13+k) ∨ e=(_,13+k) by simpa using m) with rfl|rfl <;> dsimp <;> omega

end P455PaddedWord
