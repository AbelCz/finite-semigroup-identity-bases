import Problem455BinaryEquality
import Problem455MarkedRank

/- Finite binary coordinates. Profile coordinates use their actual marked-
   move quotient with the empty set of marks. All other binary templates
   use the plain factor monoid. The unary power is included explicitly. -/
namespace P455BinaryProduct
open P455Witness P455FirstRewrite P455FirstTesters P455BinaryEquality P455SlotSaturation
open P455Uncrossed Problem455.Slots
abbrev W := List Nat

structure Index (r : Nat) (allow : Tag → Prop) where
  num : Fin (Problem455Finite.wordsUpTo [0,1] (2*r)).length
  prof : Bool
  cap : P455Closure.Cap r ((Problem455Finite.wordsUpTo [0,1] (2*r)).get num)
  ok : let T := (Problem455Finite.wordsUpTo [0,1] (2*r)).get num
       (T = power r ∨ (0 < T.count 0 ∧ 0 < T.count 1)) ∧ (prof = true ↔ IsProfile r allow T)

def Index.T (i : Index r allow) := (Problem455Finite.wordsUpTo [0,1] (2*r)).get i.num
def Index.R (i : Index r allow) := if i.prof then rules r allow noMark else plain r
theorem Index.bound (i : Index r allow) : P455Quotient.Cap i.R.r i.T := by
  cases b : i.prof <;> simpa [Index.R,b,plain,rules,Problem455Finite.rules] using i.cap

abbrev Carrier (r : Nat) (allow : Tag → Prop) := (i : Index r allow) → P455Quotient.Q i.R i.T
def model (r : Nat) (allow : Tag → Prop) : Model (Carrier r allow) where
  op := fun x y i => P455Quotient.mul i.R i.bound (x i) (y i)
  unit := fun i => P455Quotient.ofWord i.R i.T []
  assoc := fun x y z => funext (fun i => P455Quotient.mul_assoc i.R i.bound (x i) (y i) (z i))
  oneL := fun x => funext (fun i => (P455Quotient.unit_laws i.R i.bound (x i)).1)
  oneR := fun x => funext (fun i => (P455Quotient.unit_laws i.R i.bound (x i)).2)

theorem eval_at (i : Index r allow) (v : Nat → Carrier r allow) (w : W) :
    (model r allow).eval v w i = P455Quotient.eval i.R i.bound (fun x => v x i) w := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (P455Quotient.mul i.R i.bound (v a i)) ih

theorem empty_mark_eval {r allow T} (cap : P455Closure.Cap r T)
    (f : P455Closure.Frame Nat) (l k : W) (x y : Nat) (hp : f.p = [x]) (hq : f.q = [y])
    (fv : f.Valid r allow noMark) (val : Nat → P455Quotient.Q (rules r allow noMark) T) :
    P455Quotient.eval (rules r allow noMark) cap val (side f l k false) =
    P455Quotient.eval (rules r allow noMark) cap val (side f l k true) := by
  apply Classical.byContradiction
  intro diff
  obtain ⟨b,_,⟨h,rep⟩,_⟩ := difference_live_representatives cap f l k val diff
  have eq := uncrossed_eval cap f l k b x y hp hq fv val h (fun a m => (rep a m).2)
    (fun _ _ _ _ => ⟨id,id⟩)
  cases b
  · exact diff eq
  · exact diff eq.symm

theorem identity {r allow} (f : P455Closure.Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (fv : f.Valid r allow noMark) :
    (model r allow).Valid (side f l k false) (side f l k true) := by
  intro val; funext i; rw [eval_at,eval_at]
  have names : BinaryNames i.T := by
    intro a ha; have h := P455GuardSubproduct.letters (List.get_mem _ i.num) a ha
    simpa using h
  let w := side f l k
  have coord (R : P455Quotient.Rules Nat) (cap : P455Quotient.Cap R.r i.T)
      (eq : R = i.R) (any : ∀ v : Nat → P455Quotient.Q R i.T,
       P455Quotient.eval R cap v (w false) = P455Quotient.eval R cap v (w true)) :
      P455Quotient.eval i.R i.bound (fun x => val x i) (w false) =
        P455Quotient.eval i.R i.bound (fun x => val x i) (w true) := by subst R; exact any _
  cases bit : i.prof with
  | false =>
    apply coord (plain r) i.cap (by simp [Index.R,bit])
    exact plain_equal i.cap names (fun h => by have := i.ok.2.mpr h; simp_all) f l k x y hp hq fv
  | true =>
    apply coord (rules r allow noMark) i.cap (by simp [Index.R,bit])
    exact empty_mark_eval i.cap f l k x y hp hq fv

end P455BinaryProduct
