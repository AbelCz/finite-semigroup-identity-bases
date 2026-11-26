import Problem455LocalIdentity
import Problem455EdgeProduct



namespace P455MarkedRank
open P455Witness P455SourceFamilies P455CrossedSupport P455SingletonEvaluation
open P455SlotSaturation P455ActualGuards P455Uncrossed P455Compression P455FirstRewrite
open P455FirstTesters P455SupportBound Problem455.Slots
abbrev W := List Nat

def model (r : Nat) (allow : Tag → Prop) (ts : Tiles) :=
  combine (P455GuardProduct.product r allow ts) (P455EdgeProduct.product r allow ts)

theorem eval_pair {A B : Type} (M : Model A) (N : Model B) (v : Nat → A × B) (w : W) :
    (combine M N).eval v w = (M.eval (fun a => (v a).1) w,N.eval (fun a => (v a).2) w) := by
  induction w with
  | nil => rfl
  | cons a w ih => change (_,_) = (_,_); rw [ih]; rfl

theorem valid_pair {A B : Type} (M : Model A) (N : Model B) (u v : W) :
    (combine M N).Valid u v ↔ M.Valid u v ∧ N.Valid u v := by
  constructor
  · intro h; refine ⟨valid_left M N h,?_⟩
    intro f
    have e := h (fun a => (M.unit,f a))
    simpa only [eval_pair,Prod.mk.injEq] using (congrArg Prod.snd e)
  · rintro ⟨m,n⟩ val
    rw [eval_pair,eval_pair,m,n]

theorem endpoint_feasible {r allow ts u w x y} (cap : P455Closure.Cap r u)
    (ident : (model r allow ts).Valid u w) (changed : select [x,y] u ≠ select [x,y] w) :
    ¬ EdgeViolation r allow ts u x y := by
  rintro ⟨e,s,match',read⟩
  have obs := P455EdgeProduct.endpoint_observed cap ((valid_pair ..).mp ident).2 e read
  have diff := matched_change _ match' changed
  cases s
  · exact diff obs.1
  · exact diff obs.2

theorem edge_eval {r allow ts} (v : Nat → P455EdgeProduct.Carrier r allow ts)
    (i : P455EdgeProduct.Index r allow ts) (w : W) :
    (P455EdgeProduct.product r allow ts).eval v w i = P455Quotient.eval i.R i.cap (fun a => v a i) w := by
  induction w with
  | nil => rfl
  | cons x _ ih => exact congrArg (P455Quotient.mul i.R i.cap (v x i)) ih

theorem edge_coordinate {r allow ts} (i : P455EdgeProduct.Index r allow ts) : ∃ c : Certificate,
    MarksOnly (P455EdgeProduct.marks i.a i.b i.c i.d) c ∧
    Holds r allow (P455EdgeProduct.marks i.a i.b i.c i.d) i.T (c.query r ts) := by
  obtain ⟨e,ea,eb,ec,ed,_,obs⟩ := i.test
  refine ⟨.edge e,?_,obs⟩
  intro a b h
  rcases h with h|h
  · exact ⟨false,.inl ⟨ea.trans h.1.symm,eb.trans h.2.symm⟩⟩
  · exact ⟨true,.inl ⟨ec.trans h.1.symm,ed.trans h.2.symm⟩⟩

def boundN := 2*(1+28)*geometric 28 6
def bound (r : Nat) := boundN + r*boundN + 1

theorem small_valid {r allow ts} (f : P455Closure.Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (fv : f.Valid r allow noMark)
    (capF : P455Closure.Cap r (side f l k false))
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀)
    (identity : (P455GuardProduct.product r allow ts).Valid u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false)) (feasible : ∀ b, ¬ EdgeViolation r allow ts (side f l k b) x y) :
    let keep := retained r allow noMark (side f l k false) x y
    (model r allow ts).Valid (small (side f l k false) keep) (small (side f l k true) keep) := by
  dsimp only
  apply (valid_pair ..).mpr
  constructor
  · intro val; funext i
    obtain ⟨c,only,test⟩ := P455LocalIdentity.guard_coordinate i
    rw [P455LocalIdentity.coordinate_eval,P455LocalIdentity.coordinate_eval]
    exact P455LocalIdentity.marked_equal i.cap ts c only test f l k x y hp hq fv capF
      u₀ w cap₀ identity flip₀ changed path cmp feasible _
  · intro val; funext i
    obtain ⟨c,only,test⟩ := edge_coordinate i
    rw [edge_eval,edge_eval]
    exact P455LocalIdentity.marked_equal i.cap ts c only test f l k x y hp hq fv capF
      u₀ w cap₀ identity flip₀ changed path cmp feasible _

theorem bounded_step {r allow ts} (f : P455Closure.Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (fv : f.Valid r allow noMark)
    (capF : P455Closure.Cap r (side f l k false))
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀) (ident : (model r allow ts).Valid u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false)) (feasible : ∀ b, ¬ EdgeViolation r allow ts (side f l k b) x y) :
    P455FirstRewrite.Step (fun a b => (model r allow ts).Valid a b ∧ rank a b ≤ bound r)
      (side f l k false) (side f l k true) := by
  have idG := ((valid_pair ..).mp ident).1
  apply bounded_step_of_capacity (model r allow ts) (mark := noMark) f l k hp hq fv false capF
  · exact capacity cap₀ idG changed path flip₀ capF ⟨f,false,l,k,hp,hq,fv,rfl⟩ cmp
  · exact small_valid f l k x y hp hq fv capF u₀ w cap₀ idG flip₀ changed path cmp feasible

end P455MarkedRank
