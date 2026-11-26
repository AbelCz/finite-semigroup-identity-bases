import Problem455GadgetPaths
import Problem455ContactGeometry
import Problem455SlotOrigin
import Problem455ContactReflection




namespace P455ContactLift
open Problem455.Slots P455Witness P455Paths

def Supplies (v : W) (h : Nat → W) (r x s : Nat) := v.count x = r ∧ s ∈ h x
noncomputable def donor (v : W) (h : Nat → W) (r s : Nat) : Nat := by
  classical
  exact if hs : ∃ x, Supplies v h r x s then hs.choose else 0

theorem factor_cap {v l k : W} {h : Nat → W} {r : Nat}
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) : P455Closure.Cap r (v.flatMap h) := by
  intro s; have hs := cap s; simp only [List.count_append] at hs; omega

theorem donor_eq {v h r x s} (hr : 0 < r) (cap : P455Closure.Cap r (v.flatMap h))
    (supply : Supplies v h r x s) : donor v h r s = x := by
  classical
  have existsDonor : ∃ y, Supplies v h r y s := ⟨x,supply⟩
  have other := existsDonor.choose_spec
  have used : existsDonor.choose ∈ v := List.count_pos_iff.mp (other.1.symm ▸ hr)
  have exc := (P455DonorInterval.exclusive h v x s r hr supply.1 supply.2 (cap s)).2.1
  unfold donor; rw [dif_pos existsDonor]
  exact Classical.byContradiction (fun ne => exc _ used ne other.2)

def Guard (r : Nat) (allow : Tag → Prop) (mark : Marking) (v : W) (seed J : Nat) : Prop :=
  ∀ x, Near r allow mark v seed x J → ∀ i, slotStart i →
    ∀ y, occupies v x i y → v.count y = r

theorem guard_uniform {r allow mark v seed J} (uniform : ∀ x ∈ v, v.count x = r) :
    Guard r allow mark v seed J := by
  intro _ _ _ _ y hy
  obtain ⟨j,sub⟩ := hy
  have hm : (y,j) ∈ events v := sub.subset (by simp)
  exact uniform y (stamped_mem_label _ _ _ hm)

theorem contact_step {r allow mark v h l k x s t} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (sup : Supplies v h r x s)
    (guard : ∀ i, slotStart i → ∀ y, occupies v x i y → v.count y = r)
    (c : ContactChoice) (hc : Holds r allow mark (l ++ v.flatMap h ++ k) (contact r s t c)) :
    let y := donor v h r t
    Supplies v h r y t ∧ x ≠ y ∧ Holds r allow mark v (contact r x y c) := by
  obtain ⟨i,slot,occ⟩ := P455ContactGeometry.contact_slot hc
  have ext := P455ContactGeometry.contact_excludes_image hr cap sup.1 sup.2 hc
  obtain ⟨y,_,ht,hy,ne⟩ := P455SlotOrigin.supplier v h l k x s t i r hr cap sup.1 sup.2 ext occ (guard i slot)
  have g : Supplies v h r y t := ⟨hy,ht⟩
  have refl := P455ContactReflection.reflect_contact hr cap sup.1 hy ne sup.2 ht c hc
  simpa only [donor_eq hr (factor_cap cap) g] using And.intro g (And.intro ne refl)

def relabel (d : Nat → Nat) (p : List Step) := p.map fun bc => (d bc.1,bc.2)

theorem endpoint_relabel (d : Nat → Nat) (s : Nat) (p : List Step) :
    endpoint (d s) (relabel d p) = d (endpoint s p) := by
  induction p generalizing s with
  | nil => rfl
  | cons head p ih => exact ih head.1

/-- Each step comes from the concrete record/port test in the enclosing word.
    Induction keeps the length of the source prefix to which the guard applies. -/
theorem transfer_from {r allow mark v h l k seed J} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (guard : Guard r allow mark v seed J)
    (s : Nat) (p : List Step) (n : Nat) (sup : Supplies v h r (donor v h r s) s)
    (near : Near r allow mark v seed (donor v h r s) n) (bound : n+p.length ≤ J)
    (walk : Walk r allow mark (l ++ v.flatMap h ++ k) s p) :
    Walk r allow mark v (donor v h r s) (relabel (donor v h r) p) ∧
    Supplies v h r (donor v h r (endpoint s p)) (endpoint s p) := by
  induction p generalizing n s with
  | nil => exact ⟨True.intro,sup⟩
  | cons bc rest ih =>
    obtain ⟨b,c⟩ := bc
    have len : n+1+rest.length ≤ J := by simpa [Nat.add_assoc,Nat.add_comm 1 rest.length] using bound
    have g := guard _ (near_mono near (by omega))
    obtain ⟨next,_,edge⟩ := contact_step hr cap sup g c walk.1
    have more := near_trans near (near_one c edge)
    obtain ⟨tail,last⟩ := ih b (n+1) next more len walk.2
    exact ⟨⟨edge,tail⟩,last⟩

theorem lift_walk {r allow mark v h l k s seed J} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (start : Supplies v h r seed s)
    (guard : Guard r allow mark v seed J) (p : List Step) (bound : p.length ≤ J)
    (walk : Walk r allow mark (l ++ v.flatMap h ++ k) s p) :
    Walk r allow mark v seed (relabel (donor v h r) p) ∧
    Supplies v h r (donor v h r (endpoint s p)) (endpoint s p) := by
  have eq := donor_eq hr (factor_cap cap) start
  simpa only [eq] using transfer_from hr cap guard s p 0 (eq.symm ▸ start)
    (eq.symm ▸ near_self seed 0) (by simpa using bound) walk

theorem lift_near {r allow mark v h l k s seed J a n} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (start : Supplies v h r seed s)
    (guard : Guard r allow mark v seed J) (bound : n ≤ J)
    (near : Near r allow mark (l ++ v.flatMap h ++ k) s a n) :
    Supplies v h r (donor v h r a) a ∧ Near r allow mark v seed (donor v h r a) n := by
  obtain ⟨p,w,ep,len⟩ := near
  obtain ⟨sw,sup⟩ := lift_walk hr cap start guard p (Nat.le_trans len bound) w
  rw [ep] at sup
  refine ⟨sup,relabel (donor v h r) p,sw,?_,by simpa [relabel] using len⟩
  have eq := donor_eq hr (factor_cap cap) start
  rw [← eq,endpoint_relabel,ep]

end P455ContactLift
