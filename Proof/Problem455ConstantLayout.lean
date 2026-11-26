import Problem455UniformCross




namespace P455ConstantLayout
open P455Witness P455SourceFamilies P455CrossedSupport P455SingletonEvaluation
open P455Uncrossed P455MarkedPath
abbrev W := List Nat

/-- One actual literal frame flip, with its two source names among the
designated cell pairs. All surrounding contexts count as part of the word. -/
def Flip (r : Nat) (allow : Tag → Prop) (used : Nat → Nat → Prop) (s t : W) :=
  ∃ (x y : Nat) (f : P455Closure.Frame Nat) (b : Bool) (l k : W), used x y ∧
    f.p = [x] ∧ f.q = [y] ∧ f.Valid r allow (fun _ _ => False) ∧
    s = side f l k b ∧ t = side f l k (!b)

abbrev Chain (r : Nat) (allow : Tag → Prop) (used : Nat → Nat → Prop) :=
  P455Quotient.Walk (Flip r allow used)

theorem contents {r allow used U V} (path : Chain r allow used U V) (a : Nat) :
    a ∈ U ↔ a ∈ V := by
  induction path with
  | refl => rfl
  | snoc _ mv ih =>
    obtain ⟨x,y,f,b,l,k,_,_,_,_,rfl,rfl⟩ := mv
    exact ih.trans (same_letters f l k b a)

theorem clear_chain {r allow used mark T U V} (capT : P455Quotient.Cap r T)
    (path : Chain r allow used U V) (h : Nat → W)
    (clear : ∀ x y, used x y → Unmarked mark h x y) :
    P455Quotient.ofWord (rules r allow mark) T (U.flatMap h) =
      P455Quotient.ofWord (rules r allow mark) T (V.flatMap h) := by
  induction path with
  | refl => rfl
  | snoc _ mv ih =>
    obtain ⟨x,y,f,b,l,k,pair,hp,hq,valid,rfl,rfl⟩ := mv
    exact ih.trans (uncrossed_words capT f l k b x y hp hq valid h (clear x y pair))

/-- The endpoint choice is shared across all checked pairs. No saturation,
compression, or absence of violations is required at mixed intermediates. -/
structure Layout (r : Nat) (allow : Tag → Prop) (ts : Tiles) (endWord : Bool → W) where
  used : Nat → Nat → Prop
  path : Chain r allow used (endWord false) (endWord true)
  uniform : ∀ b, ∀ a ∈ endWord b, (endWord b).count a = r
  compressed : ∀ b, Compressed r (endWord b)
  frame : ∀ b x y, used x y → ClosedFlip r allow (endWord b) x y
  clean : ∀ b x y, used x y → ¬ Violation r allow ts (endWord b) x y

/-- A generic quotient calculation. A crossing need be ruled out solely at
the live endpoint, for the very same representatives used along the path. -/
theorem compare {r allow used mark T} (capT : P455Quotient.Cap r T)
    (c : Certificate) (only : MarksOnly mark c) (endWord : Bool → W)
    (path : Chain r allow used (endWord false) (endWord true))
    (val : Nat → P455Quotient.Q (rules r allow mark) T)
    (reject : ∀ (b : Bool) (h : Nat → W),
      P455Quotient.Good (rules r allow mark) T ((endWord b).flatMap h) →
      ∀ x y, used x y → ∀ s, ¬ Crosses (markedRecord c s) h x y) :
    P455Quotient.eval (rules r allow mark) capT val (endWord false) =
      P455Quotient.eval (rules r allow mark) capT val (endWord true) := by
  classical
  apply Classical.byContradiction
  intro diff
  let R := rules r allow mark
  have live : ∃ b : Bool, P455Quotient.eval R capT val (endWord b) ≠ P455Quotient.zero R T := by
    by_cases h : P455Quotient.eval R capT val (endWord false) ≠ P455Quotient.zero R T
    · exact ⟨false,h⟩
    · exact ⟨true,fun e => diff ((Classical.not_not.mp h).trans e.symm)⟩
  obtain ⟨b,nz⟩ := live
  have existsRep (a : Nat) (ha : a ∈ endWord b) :=
    P455Quotient.nonzero_representative R (val a) (P455Quotient.live_inputs R capT val _ nz a ha)
  let h (a : Nat) := if yes : a ∈ endWord b then (existsRep a yes).choose else []
  have rep (a) (mem : a ∈ endWord b) : P455Quotient.ofWord R T (h a) = val a := by
    simpa only [h,dif_pos mem] using (existsRep a mem).choose_spec.2
  have value := P455Quotient.eval_rep R capT val _ h rep
  have good := (P455Quotient.nonzero_iff R).mp (value ▸ nz)
  have clear (x y) (use : used x y) : Unmarked mark h x y := by
    intro a ma z mz
    have nope : ¬ (mark a z ∨ mark z a) := by
      intro hit
      obtain ⟨s,cross⟩ := pick_cross only ⟨a,ma,z,mz,hit⟩
      exact reject b h good x y use s cross
    exact ⟨fun e => nope (.inl e),fun e => nope (.inr e)⟩
  have support (s : Bool) (a) (m : a ∈ endWord s) : a ∈ endWord b := by
    cases s <;> cases b
    · exact m
    · exact (contents path a).mp m
    · exact (contents path a).mpr m
    · exact m
  apply diff
  rw [P455Quotient.eval_rep R capT val (endWord false) h (fun a m => rep a (support false a m)),
      P455Quotient.eval_rep R capT val (endWord true) h (fun a m => rep a (support true a m))]
  exact clear_chain capT path h clear

/-- Marked Section 8 identity conditional on the actual finite layout and
its two endpoint geometries. Every live crossed evaluation transfers one
of the three designated tester families to that same constant endpoint. -/
theorem marked_equal {r allow ts mark T} (capT : P455Quotient.Cap r T)
    (endWord : Bool → W) (layout : Layout r allow ts endWord)
    (c : Certificate) (only : MarksOnly mark c) (tester : Holds r allow mark T (c.query r ts))
    (val : Nat → P455Quotient.Q (rules r allow mark) T) :
    P455Quotient.eval (rules r allow mark) capT val (endWord false) =
      P455Quotient.eval (rules r allow mark) capT val (endWord true) := by
  apply compare capT c only endWord layout.path val
  intro b h good x y used s cross
  apply layout.clean b x y used
  exact P455UniformCross.crossed_word capT ts c tester (endWord b) (layout.uniform b)
    (layout.compressed b) x y (layout.frame b x y used) h good s cross

end P455ConstantLayout
