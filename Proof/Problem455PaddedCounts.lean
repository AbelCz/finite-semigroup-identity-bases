import Problem455PaddedWord


namespace P455PaddedWord
open P455PaddedMatchings P455PaddedPorts P455RectangleRank Problem455.Slots

private theorem cell_role {i a : Nat} (h : a∈roles i) : a=owner i ∨ a=mate i := by simpa [roles] using h

theorem absent_other {i j a : Nat} (r : a∈roles i) (different : i≠j) : a∉roles j := by
  intro m; have p := cell_role r; have q := cell_role m; unfold owner mate at p q; omega

private theorem range_count (i t : Nat) : (List.range t).count i=(if i<t then 1 else 0) := by
  by_cases h : i<t
  · simp [h,count_one List.nodup_range (List.mem_range.mpr h)]
  · simp [h,List.count_eq_zero.mpr (fun m=>h (List.mem_range.mp m))]

private theorem weighted (f : Nat→List Nat) (i a v : Nat) (s : List Nat)
    (w : ∀ j,(f j).count a=(if j=i then v else 0)) : (s.flatMap f).count a=v*s.count i := by
  induction s with
  | nil => simp
  | cons j s ih =>
    by_cases e : j=i
    · subst j; simp [List.flatMap_cons,List.count_append,w,ih,List.count_cons,Nat.mul_add,Nat.add_comm]
    · simp [List.flatMap_cons,List.count_append,w,ih,List.count_cons,e,Ne.symm e]

theorem private_counts (i a : Nat) (role : a∈roles i) (t : Nat) :
    ((List.range t).flatMap privateCell).count a=if i<t then 3 else 0 := by
  have ne : owner i≠mate i := by unfold owner mate; omega
  have ct (j : Nat) : (privateCell j).count a=if j=i then 3 else 0 := by
    by_cases e : j=i
    · subst j; rcases cell_role role with rfl|rfl <;> simp [privateCell,List.count_cons,ne,Ne.symm ne]
    · have no := absent_other role (Ne.symm e)
      have no' : a∉privateCell j := by simpa [roles,privateCell,or_assoc,or_left_comm,or_comm] using no
      simp [List.count_eq_zero.mpr no',e]
  rw [weighted _ _ _ _ _ ct,range_count]; split <;> simp

theorem mutable_counts (i a : Nat) (role : a∈roles i) (bits : Nat→Bool) (t : Nat) :
    ((List.range t).flatMap (mutableCell bits)).count a=if i<t then 1 else 0 := by
  have ne : owner i≠mate i := by unfold owner mate; omega
  have ct (j : Nat) : (mutableCell bits j).count a=if j=i then 1 else 0 := by
    by_cases e : j=i
    · subst j; rcases cell_role role with rfl|rfl <;> cases b : bits i <;> simp [mutableCell,b,List.count_cons,ne,Ne.symm ne]
    · have no := absent_other role (Ne.symm e)
      have no' : a∉mutableCell bits j := by cases b : bits j <;> simpa [roles,mutableCell,b,or_comm] using no
      simp [List.count_eq_zero.mpr no',e]
  rw [weighted _ _ _ _ _ ct,range_count,Nat.one_mul]

theorem port_count {h w : Nat} (size : 1<w*h) (q i a : Nat) (role : a∈roles i) :
    (letters (matching h w q)).count a=if i<w*h then 2 else 0 := by
  rw [letters,count_role _ i a (cell_role role),count_phase]
  by_cases e : i<w*h
  · simp [e,count_one (matching_unique size q) ((matching_cells size q i).mpr e)]
  · simp [e,List.count_eq_zero.mpr (fun m=> e ((matching_cells size q i).mp m))]

private theorem select_roles (s : List Nat) (i : Nat) :
    select (roles i) (s.flatMap roles)=(List.replicate (s.count i) (roles i)).flatten := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    rw [List.flatMap_cons,select_append,ih]
    by_cases e : a=i
    · subst a; simp [roles,select,List.count_cons,List.replicate_succ]
    · have no := select_nil (roles i) (roles a) (fun _ h => absent_other h e)
      simp [no,List.count_cons,e,Ne.symm e]

theorem match_projection {h w : Nat} (size : 1<w*h) (q i : Nat) (lt : i<w*h) :
    select (roles i) (letters (matching h w q))=roles i++roles i := by
  rw [letters,select_roles,count_phase,count_one (matching_unique size q) ((matching_cells size q i).mpr lt)]
  simp

private theorem count_uniform (xs : List Nat) (a v : Nat) (f : Nat→List Nat)
    (each : ∀ j∈xs,(f j).count a=v) : (xs.flatMap f).count a=xs.length*v := by
  induction xs with
  | nil => simp
  | cons j t ih =>
    simp [List.flatMap_cons,List.count_append,each j List.mem_cons_self,
      ih (fun x hx=>each x (List.mem_cons_of_mem _ hx)),Nat.add_mul,Nat.add_comm]

theorem chunks_count {h w : Nat} (size : 1<w*h) (q i a : Nat) (role : a∈roles i) :
    (portChunks h w q).count a=q*(if i<w*h then 2 else 0) := by
  unfold portChunks
  rw [count_uniform _ _ _ _ (fun j _ => port_count size j i a role),List.length_range]

theorem suffix_count {h w k : Nat} (tag : Nat→List Bool) (i a : Nat) (role : a∈roles i) :
    (suffix h w k tag).count a=if i<w*h then k+1 else 0 := by
  unfold suffix
  have ct (j : Nat) : (tagPhase (w*h) tag j).count a = if i<w*h then 1 else 0 := mutable_counts i a role _ _
  rw [List.count_append,count_uniform (List.range k) a _ (tagPhase (w*h) tag) (fun j _ => ct j),
    List.length_range,count_role _ i a (cell_role role)]
  by_cases e : i<w*h
  · simp [e,count_one (columns_unique h w) ((columns_cells h w i).mpr e)]
  · simp [e,List.count_eq_zero.mpr (fun m=> e ((columns_cells h w i).mp m))]

theorem word_count {h w k : Nat} (size : 1<w*h) (tag : Nat→List Bool) (bits : Nat→Bool)
    (i a : Nat) (role : a∈roles i) :
    (word (w*h) (middle h w k tag) (tail (w*h)) bits).count a=if i<w*h then k+16 else 0 := by
  simp only [word,middle,tail,List.count_append,private_counts i a role,chunks_count size 5 i a role,
    suffix_count tag i a role,mutable_counts i a role]
  split <;> omega

theorem capped {h w k : Nat} (size : 1<w*h) (tag : Nat→List Bool) (bits : Nat→Bool) :
    P455Quotient.Cap (k+16) (word (w*h) (middle h w k tag) (tail (w*h)) bits) := by
  intro a
  have role : a∈roles (a/2) := by simp only [roles,List.mem_cons,List.not_mem_nil,or_false,owner,mate]; omega
  rw [word_count size tag bits _ a role]
  split <;> omega

end P455PaddedWord
