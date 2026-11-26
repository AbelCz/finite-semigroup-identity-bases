import Problem455PaddedCounts


namespace P455PaddedWord
open P455PaddedMatchings P455PaddedPorts P455RectangleRank Problem455.Slots P455Witness

def text (h w k : Nat) (tag : Nat→Tag) (bit : Nat→Bool) := word (w*h) (middle h w k tag) (tail (w*h)) bit

theorem range_cut {i n : Nat} (lt : i<n) :
    List.range n=List.range i ++ i :: List.range' (i+1) (n-(i+1)) := by
  have app := List.range'_append_1 (s:=0) (m:=i+1) (n:=n-(i+1))
  rw [show i+1+(n-(i+1))=n by omega] at app
  simpa [←List.range_eq_range',List.range_succ,List.append_assoc] using app.symm

theorem phase_cut {h w k : Nat} (tag : Nat→Tag) (bits : Nat→Bool) (p : Fin 5) :
    ∃ post, text h w k tag bits=
      (((List.range (w*h)).flatMap privateCell) ++ portChunks h w p.val) ++ letters (matching h w p.val) ++ post := by
  let rest := (List.range' (p.val+1) (5-(p.val+1))).flatMap fun a=>letters (matching h w a)
  refine ⟨rest ++ suffix h w k tag ++ (List.range (w*h)).flatMap (mutableCell bits) ++ tail (w*h),?_⟩
  have e : portChunks h w 5 = portChunks h w p.val ++ letters (matching h w p.val) ++ rest := by
    unfold portChunks
    conv => lhs; rw [range_cut p.isLt]
    simp [rest,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  simp [text,word,middle,e,List.append_assoc]

theorem phase_index {h w : Nat} (size : 1<w*h) (p : Fin 5) (i a : Nat)
    (lt : i<w*h) (role : a∈roles i) :
    (((List.range (w*h)).flatMap privateCell) ++ portChunks h w p.val).count a=3+2*p.val := by
  simp only [List.count_append,private_counts i a role,chunks_count size p.val i a role,if_pos lt]; omega

theorem private_cut {h w k : Nat} (tag : Nat→Tag) (bits : Nat→Bool) {i : Nat} (lt : i<w*h) :
    ∃ post,text h w k tag bits=(List.range i).flatMap privateCell ++ privateCell i ++ post := by
  let rest := (List.range' (i+1) (w*h-(i+1))).flatMap privateCell
  refine ⟨rest++middle h w k tag++(List.range (w*h)).flatMap (mutableCell bits)++tail (w*h),?_⟩
  have e : (List.range (w*h)).flatMap privateCell=(List.range i).flatMap privateCell ++ privateCell i ++ rest := by
    conv => lhs; rw [range_cut lt]
    simp [rest,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  simp [text,word,e,List.append_assoc]

theorem small_slots {h w k : Nat} (size : 1<w*h) (tag : Nat→Tag) (bits : Nat→Bool) :
    ∀ a∈text h w k tag bits, ∀ d, slotStart d → Covered (text h w k tag bits) a d := by
  intro a mem d sl
  let i := a/2
  have role : a∈roles i := by simp only [roles,List.mem_cons,List.not_mem_nil,or_false,owner,mate,i]; omega
  have lt : i<w*h := by
    have positive := List.count_pos_iff.mpr mem
    rw [text,word_count size tag bits i a role] at positive
    split at positive <;> omega
  by_cases early : d=0 ∨ d=1
  · obtain ⟨post,cut⟩ := private_cut tag bits lt
    rw [cut]; exact private_slot_bound _ _ i a d role (by simp [private_counts i a role]) early
  · have place : ∃ p : Fin 5, d=3+2*p.val := by
      unfold slotStart at sl
      rcases sl with e|e|e|e|e|e|e
      · exact (early (.inl e)).elim
      · exact (early (.inr e)).elim
      · exact ⟨0,e⟩
      · exact ⟨1,e⟩
      · exact ⟨2,e⟩
      · exact ⟨3,e⟩
      · exact ⟨4,e⟩
    obtain ⟨p,rfl⟩ := place
    obtain ⟨post,cut⟩ := phase_cut tag bits p
    rw [cut]; exact matching_slot_bound (matching_unique size _) i a _ role ((matching_cells size _ _).mpr lt)
      (phase_index size p i a lt role)

def node (tag : Nat→Tag) (i : Nat) : Node := ⟨owner i,mate i,tag i⟩

theorem port_iff {h w k : Nat} (size : 1<w*h) (tag : Nat→Tag) (bits : Nat→Bool)
    (allow : Tag→Prop) (mark : Marking) (p : Fin 5) {i j : Nat} (ne : i≠j) (li : i<w*h) (lj : j<w*h) :
    let H := Holds (k+16) allow mark (text h w k tag bits)
    H (orientedPort p.val (node tag i) (node tag j)) ↔ H (typedNode (node tag i)) ∧
      H (typedNode (node tag j)) ∧ H (earlyDisjoint (roles i) (roles j)) ∧ Block.pair i j∈matching h w p.val := by
  obtain ⟨post,cut⟩ := phase_cut tag bits p
  dsimp only
  rw [cut]
  exact oriented_port_iff (by omega) allow mark p _ _ ne (matching_unique size _) ((matching_cells size _ _).mpr li)
    ((matching_cells size _ _).mpr lj) (fun a m=> (List.mem_append.mp m).elim
      (fun x=>phase_index size p i a li x) (fun x=>phase_index size p j a lj x))

end P455PaddedWord
