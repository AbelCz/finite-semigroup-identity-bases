import Problem455CellClassClean
import Problem455PaddedCounts

/- Literal middle and final phases for the five grid matching lists, with
   independently assigned tile tags and the row-major column pass. -/
namespace P455CellClassPadded
open P455CellClassFrames P455RectangleRank P455PaddedWord P455Witness P455Closure
open Problem455.Slots
abbrev W := List Nat

private theorem part {α : Type} (f : α → W) {xs : List α} {x : α} (mem : x ∈ xs) :
    (f x).Sublist (xs.flatMap f) := by
  obtain ⟨l,k,rfl⟩ := List.append_of_mem mem
  simp only [List.flatMap_append,List.flatMap_cons]
  exact (List.sublist_append_left ..).trans (List.sublist_append_right ..)

private theorem parts (s : List Nat) (f g : Nat → W)
    (each : ∀ i ∈ s, (f i).Sublist (g i)) : (s.flatMap f).Sublist (s.flatMap g) := by
  induction s with
  | nil => exact .refl _
  | cons c cs ih =>
    exact (each c List.mem_cons_self).append (ih (fun j h => each j (List.mem_cons_of_mem _ h)))

private theorem port_sublist {bs : List P455PaddedPorts.Block} {i : Nat}
    (hi : i∈bs.flatMap P455PaddedPorts.cells) :
    (P455PaddedPorts.roles i ++ P455PaddedPorts.roles i).Sublist (P455PaddedPorts.letters bs) := by
  obtain ⟨block,m,inBlock⟩ := List.mem_flatMap.mp hi
  have v := part P455PaddedPorts.roles inBlock
  have piece := part (fun b => (P455PaddedPorts.cells b ++ P455PaddedPorts.cells b).flatMap P455PaddedPorts.roles) m
  simp only [P455PaddedPorts.letters,P455PaddedPorts.phase,List.flatMap_assoc]
  apply List.Sublist.trans _ piece
  dsimp only; rw [List.flatMap_append]; exact v.append v

private theorem ports {h w i : Nat} (size : 1<w*h) (ix : i<w*h) (k : Nat) :
    (List.replicate k (P455PaddedPorts.roles i ++ P455PaddedPorts.roles i)).flatten.Sublist
      (portChunks h w k) := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    have split : portChunks h w (k+1) = portChunks h w k ++ P455PaddedPorts.letters (matching h w k) := by
      simp [portChunks,List.range_succ]
    rw [split,List.replicate_succ',List.flatten_append]; simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
    exact ih.append (port_sublist ((matching_cells size k i).mpr ix))

private theorem enumerate (bs : List Bool) :
    (List.range bs.length).map (fun k => bs[k]?.getD false) = bs := by
  apply List.ext_getElem (by simp)
  intro j _ hj; simp [List.getElem?_eq_getElem hj]

private theorem tag_chunk (x y : Nat) (b : Bool) :
    (phasePair b).map (token x y) = pair x y b := by cases b <;> rfl

theorem tokens {h w k : Nat} (size : 1<w*h) (tag : Nat → Tag)
    (length : ∀ i<w*h, (tag i).length=k) {i : Nat} (ix : i<w*h) :
    (P455CellClassFrames.phase (owner i) (mate i) (tag i)).Sublist (middle h w k tag) := by
  have fromTags := parts (List.range k)
      (fun j => pair (owner i) (mate i) ((tag i)[j]?.getD false)) (tagPhase (w*h) tag)
      (by intro j _; exact part (mutableCell (fun u => (tag u)[j]?.getD false)) (List.mem_range.mpr ix))
  have proj : (tag i).flatMap (pair (owner i) (mate i)) =
      (List.range k).flatMap (fun j => pair (owner i) (mate i) ((tag i)[j]?.getD false)) := by
    conv => lhs; arg 2; rw [← enumerate (tag i)]
    rw [List.flatMap_map,length i ix]
  rw [← proj] at fromTags
  have col := part P455PaddedPorts.roles ((columns_cells h w i).mpr ix)
  have mid := (ports size ix 5).append (fromTags.append col)
  have shape : P455CellClassFrames.phase (owner i) (mate i) (tag i) =
      (List.replicate 5 (P455PaddedPorts.roles i ++ P455PaddedPorts.roles i)).flatten ++
        ((tag i).flatMap (pair (owner i) (mate i)) ++ P455PaddedPorts.roles i) := by
    unfold P455CellClassFrames.phase fixedPhases
    simp only [List.map_append,List.map_flatMap, tag_chunk,List.append_assoc]
    rfl
  rw [shape]
  simpa only [middle,suffix,List.append_assoc] using mid

private theorem role_small {i t a : Nat} (ix : i<t) (hr : a=owner i ∨ a=mate i) : a<2*t := by
  unfold owner mate at hr; omega

theorem names {h w : Nat} (size : 1<w*h) (k : Nat) (tag : Nat → Tag) (a : Nat)
    (mem : a∈middle h w k tag ++ tail (w*h)) : a<2*(w*h) := by
  have roleMem (j : Nat) (ix : j<w*h) (m : a∈P455PaddedPorts.roles j) :=
    role_small ix (by simpa [P455PaddedPorts.roles] using m : a=owner j ∨ a=mate j)
  have mutMem (f : Nat → Bool) (j : Nat) (ix : j<w*h) (m : a∈mutableCell f j) : a<2*(w*h) := by
    apply role_small ix
    cases b : f j <;> simpa [mutableCell,b,or_comm] using m
  simp only [middle,suffix,tail,portChunks,tagPhase,List.mem_append,List.mem_flatMap] at mem
  rcases mem with (⟨d,_,p⟩|(⟨_,_,j,inR,m⟩|⟨j,jc,m⟩))|⟨j,jr,m⟩
  · obtain ⟨j,mj,ma⟩ := List.mem_flatMap.mp p
    obtain ⟨block,inB,hj⟩ := List.mem_flatMap.mp mj
    have cell : j∈P455PaddedPorts.cells block := by simpa using hj
    exact roleMem j ((matching_cells size d j).mp (List.mem_flatMap.mpr ⟨block,inB,cell⟩)) ma
  · exact mutMem _ j (List.mem_range.mp inR) m
  · exact roleMem j ((columns_cells h w j).mp jc) m
  · exact mutMem _ j (List.mem_range.mp jr) m

def phases {h w k : Nat} {allow : Tag → Prop} (size : 1<w*h) (tag : Nat → Tag)
    (length : ∀ i<w*h, (tag i).length=k) (allowed : ∀ i<w*h,allow (tag i))
    :
    Phases (k+16) allow (w*h) (middle h w k tag) (tail (w*h)) where
  tag := tag
  length := fun i hi => by rw [length i hi]
  allowed := allowed
  tokens := fun _ hi => tokens size tag length hi
  finalPair := fun i hi => (P455CellClass.canonical_final (w*h) i hi) ▸ List.filter_sublist
  capped := P455PaddedWord.capped size tag _

end P455CellClassPadded
