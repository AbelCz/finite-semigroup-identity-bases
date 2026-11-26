import Problem455FullSingleton



namespace P455Prefix
open P455FirstRewrite P455FirstTesters P455Quotient

abbrev Word := List Nat
def dropName (x : Nat) (u : Word) := u.filter (· != x)

/-- In a live product of arbitrary representatives in a capped coordinate,
    an input occurring too often must represent the unit. -/
theorem overflow_unit {R : Rules Nat} {T : Word} (cap : Cap R.r T)
    (v : Nat → Q R T) (u : Word) (x : Nat) (many : R.r < u.count x)
    (live : eval R cap v u ≠ zero R T) : v x = ofWord R T [] := by
  classical
  have mem : x ∈ u := List.count_pos_iff.mp (by omega)
  have reps (z) (hz : z ∈ u) := nonzero_representative R (v z) (live_inputs R cap v u live z hz)
  let h : Nat → Word := fun z => if hz : z ∈ u then (reps z hz).choose else []
  have rep (z) (hz : z ∈ u) : ofWord R T (h z) = v z := by
    simpa [h,hz] using (reps z hz).choose_spec.2
  have g := (nonzero_iff R).mp ((eval_rep R cap v u h rep) ▸ live)
  have bounded := good_cap R cap g
  have empty : h x = [] := by
    cases e : h x with
    | nil => rfl
    | cons a t =>
      have c : 1 ≤ (h x).count a := by rw [e]; simp
      have l := Nat.mul_le_mul_left (u.count x) c
      have split := P455DonorInterval.split_contributions h u x a
      have b := bounded a
      simp only [Nat.mul_one] at l
      omega
  simpa [empty] using (rep x mem).symm

private theorem unit_drop {R : Rules Nat} {T : Word} (cap : Cap R.r T)
    (v : Nat → Q R T) (x : Nat) (unit : v x = ofWord R T []) (u : Word) :
    eval R cap v u = eval R cap v (dropName x u) := by
  induction u with
  | nil => rfl
  | cons a t ih =>
    by_cases e : a = x
    · subst a; simpa [dropName,eval,unit,(unit_laws R cap _).1] using ih
    · simpa [dropName,eval,e] using congrArg (mul R cap (v a)) ih

theorem overflow_coordinate {R : Rules Nat} {T : Word} (cap : Cap R.r T)
    (v : Nat → Q R T) {u w : Word} {x : Nat}
    (cu : R.r < u.count x) (cw : R.r < w.count x)
    (same : dropName x u = dropName x w) : eval R cap v u = eval R cap v w := by
  by_cases hu : v x = ofWord R T []
  · rw [unit_drop cap v x hu u, unit_drop cap v x hu w,same]
  · have z (a : Word) (c : R.r < a.count x) : eval R cap v a = zero R T :=
      Classical.byContradiction (fun nz => hu (overflow_unit cap v a x c nz))
    rw [z u cu,z w cw]

private theorem power_eval {r : Nat} (i : Index r) (v : Nat → Carrier r) (w : Word) :
    (product r).eval v w i = eval (plain r) i.cap (fun a => v a i) w := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (mul (plain r) i.cap (v a i)) ih

/-- The erasure identity holds in the actual fixed product including all
    marked and unmarked coordinates. All variable evaluations are arbitrary. -/
theorem overflow_valid {r allow ts} {u w : Word} {x : Nat}
    (cu : r < u.count x) (cw : r < w.count x) (same : dropName x u = dropName x w) :
    (P455FullSingleton.model r allow ts).Valid u w := by
  apply (P455MarkedRank.valid_pair ..).mpr
  refine ⟨?_,(P455MarkedRank.valid_pair ..).mpr ⟨(P455MarkedRank.valid_pair ..).mpr ⟨?_,?_⟩,
    (P455MarkedRank.valid_pair ..).mpr ⟨?_,?_⟩⟩⟩
  · intro v; funext i; rw [power_eval,power_eval]
    exact overflow_coordinate i.cap _ cu cw same
  · intro v; funext i; rw [P455LocalIdentity.coordinate_eval,P455LocalIdentity.coordinate_eval]
    exact overflow_coordinate (R := i.R) (T := i.T) i.cap _ cu cw same
  · intro v; funext i; rw [P455MarkedRank.edge_eval,P455MarkedRank.edge_eval]
    exact overflow_coordinate (R := i.R) (T := i.T) i.cap _ cu cw same
  · intro v; funext i; rw [P455BinaryProduct.eval_at,P455BinaryProduct.eval_at]
    have capr : i.R.r = r := by
      cases h : i.prof <;> simp [P455BinaryProduct.Index.R,h,plain,P455Witness.rules,Problem455Finite.rules]
    exact overflow_coordinate i.bound _ (by simpa [capr] using cu) (by simpa [capr] using cw) same
  · intro v; funext i; rw [P455StructuralProduct.coordinate,P455StructuralProduct.coordinate]
    exact overflow_coordinate (R := plain r) (T := i.T) i.cap _ cu cw same

end P455Prefix
