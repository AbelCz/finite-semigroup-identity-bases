import Problem455Retained

/- End-to-end transport of a designated marked-word path to its original
   word after expanding the small rule's gaps. Both valuations may use the
   same Nat name for unrelated alphabet entries. Only e expands the rule;
   h supplies the actual tester representatives. -/
namespace P455OriginalWalk
open Problem455.Slots P455Witness P455Paths P455ContactLift P455Retained

def OriginalGuard (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W)
    (kept : Nat → Prop) (seed J : Nat) : Prop :=
  ∀ x, Near r allow mark u seed x J →
    kept x ∧ ∀ i, slotStart i → ∀ y, occupies u x i y → kept y ∧ u.count y = r

/-- Every output step of the recorded list is read in the original once its
    reached labels are replaced by their unique donors. No injectivity of the
    entire reached-label map is asserted. -/
theorem lift_walk {v e kept r allow mark seed J h l k s}
    (exp : Expansion v e kept) (hr : 1 < r) (capU : P455Closure.Cap r (v.flatMap e))
    (original : OriginalGuard r allow mark (v.flatMap e) kept seed J)
    (capZ : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (start : Supplies v h r seed s)
    (p : List Step) (len : p.length ≤ J)
    (walk : Walk r allow mark (l ++ v.flatMap h ++ k) s p) :
    let d := donor v h r
    let y := d (endpoint s p)
    Walk r allow mark (v.flatMap e) seed (relabel d p) ∧
      endpoint seed (relabel d p) = y ∧ (relabel d p).length = p.length ∧ kept y ∧
      Supplies v h r y (endpoint s p) ∧ Supplies (v.flatMap e) h r y (endpoint s p) := by
  let d := donor v h r
  have pos : 0 < r := by omega
  have eq : d s = seed := donor_eq pos (factor_cap capZ) start
  obtain ⟨small,supply⟩ := P455ContactLift.lift_walk pos capZ start (exp.guard hr capU original) p len walk
  have large := exp.walk hr capU seed _ small
  have ep : endpoint seed (relabel d p) = d (endpoint s p) := by rw [← eq,endpoint_relabel]
  have lp : (relabel d p).length = p.length := by simp [relabel]
  have reach : Near r allow mark (v.flatMap e) seed (d (endpoint s p)) J :=
    ⟨relabel d p,large,ep,lp ▸ len⟩
  have ky := (original _ reach).1
  exact ⟨large,ep,lp,ky,supply,(exp.count_eq v (fun _ h => h) _ ky).trans supply.1,supply.2⟩

theorem lift_near {v e kept r allow mark seed J h l k s a n}
    (exp : Expansion v e kept) (hr : 1 < r) (capU : P455Closure.Cap r (v.flatMap e))
    (original : OriginalGuard r allow mark (v.flatMap e) kept seed J)
    (capZ : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (start : Supplies v h r seed s)
    (bound : n ≤ J) (near : Near r allow mark (l ++ v.flatMap h ++ k) s a n) :
    let y := donor v h r a
    Near r allow mark (v.flatMap e) seed y n ∧ kept y ∧
      Supplies v h r y a ∧ Supplies (v.flatMap e) h r y a := by
  obtain ⟨p,walk,ea,len⟩ := near
  obtain ⟨w,ep,lp,kp,small,full⟩ := lift_walk exp hr capU original capZ start p (Nat.le_trans len bound) walk
  rw [ea] at ep kp small full
  exact ⟨⟨_,w,ep,lp ▸ len⟩,kp,small,full⟩

end P455OriginalWalk
