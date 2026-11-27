import Problem455Quotient
set_option maxHeartbeats 3000000

namespace P455Quotient
variable {α : Type} [DecidableEq α] (R : Rules α)
variable {T : Word α}

private theorem twoSidedZero (hT : Cap R.r T) (a b : Q R T) :
    mul R hT (mul R hT a (zero R T)) b = zero R T := by
  rw [(absorbing R hT a).2, (absorbing R hT b).1]

private theorem twoSidedLength (hT : Cap R.r T)
    {a b : Q R T} {u v : Word α} (gu : Good R T u)
    (h : ofWord R T u = mul R hT (mul R hT a (ofWord R T v)) b) :
    v.length ≤ u.length ∧ (v.length = u.length → ofWord R T u = ofWord R T v) := by
  have nz := (nonzero_iff R).mpr gu
  have na : a ≠ zero R T := by
    intro e
    rw [e, (absorbing R hT _).1, (absorbing R hT _).1] at h
    exact nz h
  have nb : b ≠ zero R T := by
    intro e
    rw [e, (absorbing R hT _).2] at h
    exact nz h
  obtain ⟨l, _, rfl⟩ := nonzero_representative R a na
  obtain ⟨r, _, rfl⟩ := nonzero_representative R b nb
  change ofWord R T u = ofWord R T ((l ++ v) ++ r) at h
  have eqLen := (List.perm_iff_count.mpr (count_walk R ((same_nonzero_class R gu).mp h).2)).length_eq
  simp only [List.length_append] at eqLen
  refine ⟨by omega, fun e => ?_⟩
  have ln : l.length = 0 := by omega
  have rn : r.length = 0 := by omega
  simpa [List.length_eq_zero_iff.mp ln,List.length_eq_zero_iff.mp rn] using h

theorem quotient_j_trivial (hT : Cap R.r T) (x y : Q R T)
    (hxy : ∃ a b, x = mul R hT (mul R hT a y) b)
    (hyx : ∃ a b, y = mul R hT (mul R hT a x) b) : x = y := by
  obtain ⟨a,b,ha⟩ := hxy
  obtain ⟨c,d,hc⟩ := hyx
  by_cases nx : x = zero R T
  · rw [nx, twoSidedZero R hT] at hc
    exact nx.trans hc.symm
  by_cases ny : y = zero R T
  · rw [ny, twoSidedZero R hT] at ha
    exact ha.trans ny.symm
  obtain ⟨u,gu,rfl⟩ := nonzero_representative R x nx
  obtain ⟨v,gv,rfl⟩ := nonzero_representative R y ny
  obtain ⟨le, eq⟩ := twoSidedLength R hT gu ha
  exact eq (Nat.le_antisymm le (twoSidedLength R hT gv hc).1)

end P455Quotient

#print axioms P455Quotient.quotient_j_trivial
