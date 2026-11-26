import Problem455BinaryProduct
import Problem455StructuralProduct
import Problem455ProfileComponent
import Problem455Schedule




namespace P455FullSingleton
open P455Witness P455SourceFamilies P455CrossedSupport P455ActualGuards
open P455MarkedRank P455Uncrossed P455Compression P455FirstRewrite
open P455FirstTesters P455SlotSaturation P455SupportBound Problem455.Slots
abbrev W := List Nat

def model (r : Nat) (allow : Tag → Prop) (ts : Tiles) :=
  combine (product r) (combine (P455MarkedRank.model r allow ts)
    (combine (P455BinaryProduct.model r allow) (P455StructuralProduct.product r allow)))

private theorem short {r : Nat} (hr : 0 < r) (i : P455FirstTesters.Index r) : i.val.length < 2*r := by
  rcases i.property with p|b
  · rw [p,power,List.length_replicate]; omega
  · have count {w : W} (names : ∀ x ∈ w, x=0 ∨ x=1) : w.length = w.count 0 + w.count 1 := by
      induction w with
      | nil => rfl
      | cons x t ih =>
        have tail := ih (fun a m => names a (List.mem_cons_of_mem _ m))
        rcases names x List.mem_cons_self with h|h <;> simp [h,tail,List.count_cons] <;> omega
    have len := count b.1
    have ac := b.2.1 0; have bc := b.2.1 1; have under := b.2.2.2.2
    omega

theorem primitive_identity {r allow} (f : P455Closure.Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (fv : f.Valid r allow noMark) :
    (product r).Valid (side f l k false) (side f l k true) := by
  have hr : 0 < r := by have := fv.1; omega
  intro val; funext i
  have eq (w : W) : (product r).eval val w i = P455Quotient.eval (plain r) i.cap (fun x => val x i) w := by
    induction w with
    | nil => rfl
    | cons a w ih => exact congrArg (P455Quotient.mul (plain r) i.cap (val a i)) ih
  rw [eq,eq]
  have binary : P455BinaryEquality.BinaryNames i.val := by
    rcases i.property with e|b
    · intro a m; rw [e] at m; exact .inl (List.eq_of_mem_replicate m)
    · exact b.1
  have notProf : ¬ P455BinaryEquality.IsProfile r allow i.val := by
    rintro ⟨a,b,t,bit,_,len,_,profileEq⟩
    have lt := short hr i
    rw [profileEq,P455ProfileComponent.profile_length,len] at lt; omega
  exact P455BinaryEquality.plain_equal i.cap binary notProf f l k x y hp hq fv _

theorem guard_valid {r allow ts u v} (valid : (model r allow ts).Valid u v) :
    (P455GuardProduct.product r allow ts).Valid u v :=
  ((valid_pair ..).mp (((valid_pair ..).mp ((valid_pair ..).mp valid).2).1)).1

theorem small_valid {r allow ts} (f : P455Closure.Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (fv : f.Valid r allow noMark)
    (capF : P455Closure.Cap r (side f l k false))
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀) (valid : (model r allow ts).Valid u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false)) (feasible : ∀ b, ¬ EdgeViolation r allow ts (side f l k b) x y) :
    let keep := retained r allow noMark (side f l k false) x y
    (model r allow ts).Valid (small (side f l k false) keep) (small (side f l k true) keep) := by
  let u := side f l k false
  let keep := retained r allow noMark u x y
  obtain ⟨lt,cx,cy,_⟩ := flip_counts capF (show ClosedFlip r allow u x y from ⟨f,false,l,k,hp,hq,fv,rfl⟩)
  have hx : x ∈ keep := mem_retained.mpr ⟨List.count_pos_iff.mp (cx.symm ▸ (by omega : 0 < r)),.inl (.inl (P455Paths.near_self ..))⟩
  have hy : y ∈ keep := mem_retained.mpr ⟨List.count_pos_iff.mp (cy.symm ▸ (by omega : 0 < r)),.inl (.inr (P455Paths.near_self ..))⟩
  obtain ⟨g,L,K,gp,gq,gv,both,_⟩ := P455CompressedFrame.canonical_pair f l k keep hx hy hp hq fv false capF
  change (model r allow ts).Valid (small (side f l k false) keep) (small (side f l k true) keep)
  have mark := P455MarkedRank.small_valid f l k x y hp hq fv capF u₀ w cap₀ (guard_valid valid)
    flip₀ changed path cmp feasible
  refine (valid_pair ..).mpr ⟨?_,(valid_pair ..).mpr ⟨mark,(valid_pair ..).mpr ⟨?_,?_⟩⟩⟩
  · rw [both,both]; exact primitive_identity g L K x y gp gq gv
  · rw [both,both]; exact P455BinaryProduct.identity g L K x y gp gq gv
  · rw [both,both]; exact P455StructuralProduct.identity g L K x y gp gq gv

/-- The small identity is semantically proved in every coordinate above.
    Applying its common nonempty substitution is one ordinary semigroup
    deduction step on the actual source words. -/
theorem bounded_step {r allow ts} (f : P455Closure.Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (fv : f.Valid r allow noMark)
    (capF : P455Closure.Cap r (side f l k false))
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀) (ident : (model r allow ts).Valid u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ (side f l k false))
    (cmp : Compressed r (side f l k false)) (feasible : ∀ b, ¬ EdgeViolation r allow ts (side f l k b) x y) :
    P455FirstRewrite.Step (fun a b => (model r allow ts).Valid a b ∧ rank a b ≤ bound r)
      (side f l k false) (side f l k true) := by
  apply bounded_step_of_capacity (model r allow ts) (mark := noMark) f l k hp hq fv false capF
  · exact capacity cap₀ (guard_valid ident) changed path flip₀ capF ⟨f,false,l,k,hp,hq,fv,rfl⟩ cmp
  · exact small_valid f l k x y hp hq fv capF u₀ w cap₀ ident flip₀ changed path cmp feasible

theorem no_basis_of_witnesses {r allow ts} (hr : 0 < r)
    (unbounded : ∀ k, ∃ U V D, RankWitness (model r allow ts) r U V D ∧ k < D.length)
    (basis : List (W × W)) (sound : ∀ u v, (u,v) ∈ basis → (model r allow ts).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (model r allow ts).Valid U V ∧ ¬ Derives (fun u v => (u,v) ∈ basis) U V :=
  first_change_no_finite_basis _ r hr unbounded basis sound

end P455FullSingleton
