import Problem455ActualGuards

/- Every distinguishing marked quotient valuation produces a forbidden
   incident edge on one of the actual source words. The two one-mark
   families have already been excluded by endpoint identity validity. -/
namespace P455LocalIdentity
open P455Witness P455SourceFamilies P455CrossedSupport P455SingletonEvaluation
open P455SlotSaturation P455GuardProduct P455ActualGuards P455Uncrossed
open P455MarkedPath P455Compression Problem455.Slots
abbrev W := List Nat

theorem marked_equal {r allow mark T} (capT : P455Quotient.Cap r T)
    (ts : Tiles) (c : Certificate) (only : MarksOnly mark c) (tester : Holds r allow mark T (c.query r ts))
    (f : P455Closure.Frame Nat) (l k : W) (x y : Nat) (hp : f.p = [x]) (hq : f.q = [y])
    (fv : f.Valid r allow noMark) (capF : P455Closure.Cap r (side f l k false))
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀) (identity : (product r allow ts).Valid u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false))
    (feasible : ∀ b, ¬ EdgeViolation r allow ts (side f l k b) x y)
    (v : Nat → P455Quotient.Q (rules r allow mark) T) :
    let keep := retained r allow noMark (side f l k false) x y
    P455Quotient.eval (rules r allow mark) capT v (small (side f l k false) keep) =
    P455Quotient.eval (rules r allow mark) capT v (small (side f l k true) keep) := by
  let mv : P455Closure.Move r allow noMark (side f l k false) (side f l k true) :=
    ⟨f,false,l,k,fv,rfl,rfl,capF⟩
  have per := P455RetainedVariant.same_retained (mark := noMark) mv x y
  apply Classical.byContradiction
  intro neq
  have diff : P455Quotient.eval (rules r allow mark) capT v (ruleWord r allow noMark (side f l k false) x y) ≠
      P455Quotient.eval (rules r allow mark) capT v (ruleWord r allow noMark (side f l k true) x y) := by
    intro eq
    apply neq
    dsimp only
    rw [P455RetainedVariant.small_congr_names (side f l k true) per]
    exact eq
  obtain ⟨b,bad⟩ := compare_uniform capT ts c only tester f l k x y hp hq fv capF u₀
    (P455GuardSubproduct.uniform cap₀ identity flip₀ changed) path cmp v diff
  have pb : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k b) := by
    cases b; exact path; exact .snoc path mv
  exact feasible b (only_edge cap₀ identity changed pb bad)

theorem coordinate_eval (val : Nat → Carrier r allow ts) (i : Index r allow ts) (w : W) :
    (product r allow ts).eval val w i = P455Quotient.eval i.R i.cap (fun x => val x i) w := by
  induction w with
  | nil => rfl
  | cons x w ih => exact congrArg (P455Quotient.mul i.R i.cap (val x i)) ih

theorem guard_coordinate (i : Index r allow ts) : ∃ c : Certificate,
    MarksOnly (P455SlotProduct.pairMark i.a i.b) c ∧
    Holds r allow (P455SlotProduct.pairMark i.a i.b) i.T (c.query r ts) := by
  obtain ⟨g,_,ax,ay,obs⟩ := i.accepted
  cases g with
  | slot s =>
    refine ⟨.slot s,?_,obs⟩
    intro a b h; exact ⟨false,.inl ⟨ax.trans h.1.symm,ay.trans h.2.symm⟩⟩
  | func f =>
    refine ⟨.functionality f,?_,obs⟩
    intro a b h; exact ⟨false,.inl ⟨ax.trans h.1.symm,ay.trans h.2.symm⟩⟩

end P455LocalIdentity
