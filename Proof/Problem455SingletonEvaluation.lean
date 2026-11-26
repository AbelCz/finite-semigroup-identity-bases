import Problem455RetainedVariant




namespace P455SingletonEvaluation
open P455Witness P455ContactLift P455CrossedSupport P455SourceFamilies P455SourceTheorem
open P455MarkedPath P455SlotSaturation P455SlotProduct P455RetainedVariant P455Compression
open P455Uncrossed P455PortReflection P455EdgeSource Problem455.Slots
abbrev W := List Nat

def Matches (n : Node) (x y : Nat) :=
  (n.owner = x ∧ n.mate = y) ∨ (n.owner = y ∧ n.mate = x)

def MarksOnly (mark : Marking) (c : Certificate) :=
  ∀ a b, mark a b → ∃ s : Bool, Matches (markedRecord c s) a b

theorem designated_marks (c : Certificate) : MarksOnly (sourceMarks id c) c := by
  intro a b hit
  cases c with
  | slot s => exact ⟨false,.inl ⟨hit.1.symm,hit.2.symm⟩⟩
  | functionality f => exact ⟨false,.inl ⟨hit.1.symm,hit.2.symm⟩⟩
  | edge e =>
    rcases hit with h|h
    · exact ⟨false,.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨true,.inl ⟨h.1.symm,h.2.symm⟩⟩

theorem pick_cross {c h mark x y} (only : MarksOnly mark c)
    (hit : ∃ a ∈ h x, ∃ b ∈ h y, mark a b ∨ mark b a) :
    ∃ s, Crosses (markedRecord c s) h x y := by
  obtain ⟨a,ax,b,by',ab|ba⟩ := hit
  · obtain ⟨s,⟨p,q⟩|⟨p,q⟩⟩ := only a b ab
    · exact ⟨s,.inl ⟨p ▸ ax,q ▸ by'⟩⟩
    · exact ⟨s,.inr ⟨p ▸ by',q ▸ ax⟩⟩
  · obtain ⟨s,⟨p,q⟩|⟨p,q⟩⟩ := only b a ba
    · exact ⟨s,.inr ⟨p ▸ by',q ▸ ax⟩⟩
    · exact ⟨s,.inl ⟨p ▸ ax,q ▸ by'⟩⟩

def Violation (r : Nat) (allow : Tag → Prop) (ts : Tiles) (w : W) (x y : Nat) :=
  ∃ (c : Certificate) (s : Bool), Matches (markedRecord c s) x y ∧
    Holds r allow (sourceMarks id c) w (c.query r ts)

theorem changed_anchor (c : Certificate) (s : Bool) (d : Nat → Nat) :
    markedRecord (transferred d c) s = sendNode d (markedRecord c s) := by
  cases c <;> cases s <;> rfl

theorem reindexed_marks (c : Certificate) (d : Nat → Nat) :
    sourceMarks id (transferred d c) = sourceMarks d c := by cases c <;> rfl

theorem compare_uniform {r allow mark T} (capT : P455Quotient.Cap r T)
    (ts : Tiles) (c : Certificate) (only : MarksOnly mark c)
    (tester : Holds r allow mark T (c.query r ts))
    (f : P455Closure.Frame Nat) (l k : W) (x y : Nat) (hp : f.p = [x]) (hq : f.q = [y])
    (fv : f.Valid r allow noMark) (capF : P455Closure.Cap r (side f l k false))
    (u₀ : W) (uf : UniformSlots r allow mark u₀ x y)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false))
    (val : Nat → P455Quotient.Q (rules r allow mark) T)
    (diff : P455Quotient.eval (rules r allow mark) capT val (ruleWord r allow noMark (side f l k false) x y) ≠
      P455Quotient.eval (rules r allow mark) capT val (ruleWord r allow noMark (side f l k true) x y)) :
    ∃ b : Bool, Violation r allow ts (side f l k b) x y := by
  let u := side f l k
  let R := rules r allow mark
  let names := retained r allow noMark (u false) x y
  have mv : P455Closure.Move r allow noMark (u false) (u true) := ⟨f,false,l,k,fv,rfl,rfl,capF⟩
  have cbit (b : Bool) : P455Closure.Cap r (u b) := by cases b; exact capF; exact mv.cap_right
  have fc (b : Bool) : ClosedFlip r allow (u b) x y := ⟨f,b,l,k,hp,hq,fv,rfl⟩
  obtain ⟨hr,cx,cy,_⟩ := flip_counts capF (fc false)
  have hi : 0 < r := by omega
  have hx : x ∈ names := mem_retained.mpr ⟨List.count_pos_iff.mp (cx.symm ▸ hi),.inl (.inl (P455Paths.near_self ..))⟩
  have hy : y ∈ names := mem_retained.mpr ⟨List.count_pos_iff.mp (cy.symm ▸ hi),.inl (.inr (P455Paths.near_self ..))⟩
  obtain ⟨g,L,K,gp,gq,gv,both,_⟩ := P455CompressedFrame.canonical_pair f l k names hx hy hp hq fv false capF
  have perm (b : Bool) : names.Perm (retained r allow noMark (u b) x y) := by
    cases b
    · exact List.Perm.refl _
    · exact same_retained mv x y
  have eq0 (b : Bool) : ruleWord r allow noMark (u b) x y = side g L K b :=
    (small_congr_names _ (perm b).symm).trans (both b)
  have eqm (b : Bool) : ruleWord r allow mark (u b) x y = side g L K b := by
    unfold ruleWord; rw [retained_remark (mark' := noMark)]; exact eq0 b
  have neq : P455Quotient.eval R capT val (side g L K false) ≠ P455Quotient.eval R capT val (side g L K true) := by
    rw [← eq0,← eq0]; exact diff
  obtain ⟨b,live,⟨h,represent⟩,_⟩ := difference_live_representatives capT g L K val neq
  have reps := fun a ha => (represent a ha).2
  have nd : P455Quotient.eval R capT val (side g L K b) ≠ P455Quotient.eval R capT val (side g L K (!b)) := by
    cases b
    · exact neq
    · exact Ne.symm neq
  obtain ⟨s,cs⟩ := pick_cross only (difference_crosses capT g L K b x y gp gq gv val h reps nd)
  let v := ruleWord r allow mark (u b) x y
  have repv : ∀ a ∈ v, P455Quotient.ofWord R T (h a) = val a := by rw [show v = _ from eqm b]; exact reps
  have livev : P455Quotient.eval R capT val v ≠ P455Quotient.zero R T := by rw [show v = _ from eqm b]; exact live
  have pb : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (u b) := by
    cases b; exact path; exact .snoc path mv
  have cb : Compressed r (u b) := by
    cases b
    · exact cmp
    · intro a z link
      exact cmp a z ((Problem455BlockBridge.move_link mv a z).mpr link)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,read,_⟩ := crossed_gadget capT (u b) (cbit b) x y (fc b)
    (uniform_variant pb uf) h val repv livev ts c tester s false cs
  let names' := retained r allow mark (u b) x y
  obtain ⟨_,ax,ay,_⟩ := flip_counts (cbit b) (fc b)
  have eqNames : names.Perm names' := by
    change names.Perm (retained r allow mark (u b) x y)
    rw [retained_remark (mark' := noMark)]; exact perm b
  have xcnt : v.count x = r := (counts_retained _ _ _ (eqNames.mem_iff.mp hx)).trans ax
  have ycnt : v.count y = r := (counts_retained _ _ _ (eqNames.mem_iff.mp hy)).trans ay
  have ev := P455Quotient.eval_rep R capT val v h repv
  have good := (P455Quotient.nonzero_iff R).mp (ev ▸ livev)
  have cap := P455Quotient.good_cap R capT good
  let d := donor v h r
  refine ⟨b,transferred d c,s,?_,?_⟩
  · rw [changed_anchor]
    rcases cs with ⟨o,m⟩|⟨o,m⟩
    · exact .inl ⟨donor_eq hi cap ⟨xcnt,o⟩,donor_eq hi cap ⟨ycnt,m⟩⟩
    · exact .inr ⟨donor_eq hi cap ⟨ycnt,o⟩,donor_eq hi cap ⟨xcnt,m⟩⟩
  · rw [reindexed_marks]; exact read cb

theorem compare {r allow mark T} (capT : P455Quotient.Cap r T)
    (ts : Tiles) (c : Certificate) (only : MarksOnly mark c)
    (tester : Holds r allow mark T (c.query r ts))
    (f : P455Closure.Frame Nat) (l k : W) (x y : Nat) (hp : f.p = [x]) (hq : f.q = [y])
    (fv : f.Valid r allow noMark) (capF : P455Closure.Cap r (side f l k false))
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀) (identity : Identity r allow u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false))
    (val : Nat → P455Quotient.Q (rules r allow mark) T)
    (diff : P455Quotient.eval (rules r allow mark) capT val (ruleWord r allow noMark (side f l k false) x y) ≠
      P455Quotient.eval (rules r allow mark) capT val (ruleWord r allow noMark (side f l k true) x y)) :
    ∃ b : Bool, Violation r allow ts (side f l k b) x y :=
  compare_uniform capT ts c only tester f l k x y hp hq fv capF u₀
    (uniform_of_identity cap₀ identity flip₀ changed) path cmp val diff

end P455SingletonEvaluation
