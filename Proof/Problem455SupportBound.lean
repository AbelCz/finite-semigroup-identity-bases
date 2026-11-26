import Problem455SmallRank
import Problem455CrossedSupport



namespace P455SupportBound
open P455Witness P455Paths P455ContactGeometry P455CrossedSupport Problem455.Slots
open P455FirstRewrite (names mem_names names_distinct size_le)

noncomputable def occupants (u : W) (t i : Nat) : W := by
  classical
  exact (names u).filter (fun a => decide (occupies u t i a))

theorem mem_occupants {u : W} {t i a : Nat} : a ∈ occupants u t i ↔ occupies u t i a := by
  classical
  simp only [occupants,List.mem_filter,mem_names,decide_eq_true_eq,and_iff_right_iff_imp]
  rintro ⟨j,seen⟩
  exact stamped_mem_label _ _ (a,j) (seen.subset (by simp))

def Capacity (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y K : Nat) :=
  ∀ t, InBall r allow mark u x y t → ∀ i, slotStart i → (occupants u t i).length ≤ K

private def starts : W := [0,1,3,5,7,9,11]
private theorem in_starts (i : Nat) : i ∈ starts ↔ slotStart i := by simp [starts,slotStart]

private theorem flat_bound (u : W) (F : Nat → W) (K : Nat) (b : ∀ t ∈ u, (F t).length ≤ K) :
    (u.flatMap F).length ≤ u.length*K := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have v := ih (fun t ht => b t (List.mem_cons_of_mem _ ht))
    have h := b a List.mem_cons_self
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    omega

/-- Includes all seven literal slots of a reached vertex. It may overcount
    non-neighbors. Outside the radius-six ball there is no outgoing list. -/
noncomputable def next (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y t : Nat) : W := by
  classical
  exact if InBall r allow mark u x y t then starts.flatMap (occupants u t) else []

private theorem next_bound {r allow mark u x y K} (cap : Capacity r allow mark u x y K)
    (t : Nat) : (next r allow mark u x y t).length ≤ 7*K := by
  classical
  by_cases ball : InBall r allow mark u x y t
  · rw [next,if_pos ball]
    exact flat_bound starts (occupants u t) K (fun i hi => cap t ball i ((in_starts i).mp hi))
  · simp [next,ball]

private theorem next_slot {r allow mark u x y t i a} (ball : InBall r allow mark u x y t)
    (slot : slotStart i) (o : occupies u t i a) : a ∈ next r allow mark u x y t := by
  classical
  rw [next,if_pos ball]
  exact List.mem_flatMap.mpr ⟨i,(in_starts i).mpr slot,mem_occupants.mpr o⟩

/-- 1 + D + ... + D^j. -/
def geometric (D : Nat) : Nat → Nat | 0 => 1 | j+1 => 1+D*geometric D j

private def explore (F : Nat → W) : Nat → Nat → W
  | 0, t => [t]
  | j+1, t => t :: (F t).flatMap (explore F j)

private theorem seed_mem (F : Nat → W) (j t : Nat) : t ∈ explore F j t := by
  cases j <;> exact List.mem_cons_self

private theorem explore_bound (F : Nat → W) (D : Nat) (bound : ∀ t, (F t).length ≤ D) (j t : Nat) :
    (explore F j t).length ≤ geometric D j := by
  induction j generalizing t with
  | zero => simp [geometric,explore]
  | succ j ih =>
    have s := flat_bound (F t) (explore F j) (geometric D j) (fun a _ => ih a)
    have b := Nat.mul_le_mul_right (geometric D j) (bound t)
    simp only [geometric,explore,List.length_cons]; omega

private theorem walked {r allow mark u x y} (source t : Nat) (seed : source=x ∨ source=y)
    (n j : Nat) (budget : n+j ≤ 6) (pre : Near r allow mark u source t n)
    (p : List Step) (walk : Walk r allow mark u t p) (len : p.length ≤ j) :
    endpoint t p ∈ explore (next r allow mark u x y) j t := by
  induction p generalizing t n j with
  | nil => exact seed_mem _ _ _
  | cons e p ih =>
    obtain ⟨a,c⟩ := e
    cases j with
    | zero => simp at len
    | succ j =>
      have ball : InBall r allow mark u x y t :=
        seed.elim (fun eq => .inl (eq ▸ near_mono pre (by omega))) (fun eq => .inr (eq ▸ near_mono pre (by omega)))
      obtain ⟨i,slot,occ⟩ := contact_slot walk.1
      have into := next_slot ball slot occ
      have more := near_trans pre (near_one c walk.1)
      have cont := ih a (n+1) j (by omega) more walk.2 (by simp_all)
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a,into,cont⟩)

theorem retained_bound {r allow mark u x y K} (cap : Capacity r allow mark u x y K) :
    (names (retained r allow mark u x y)).length ≤
      2*(1+7*K)*geometric (7*K) 6 := by
  let F := next r allow mark u x y
  let D := 7*K
  let ball := explore F 6 x ++ explore F 6 y
  let covered := ball ++ ball.flatMap F
  have all (b) (hb : InBall r allow mark u x y b) : b ∈ ball := by
    have mem (s) (origin : s=x ∨ s=y) (near : Near r allow mark u s b 6) : b ∈ explore F 6 s := by
      obtain ⟨p,wp,eq,len⟩ := near
      exact eq ▸ walked s s origin 0 6 (by decide) (near_self s 0) p wp len
    exact List.mem_append.mpr (hb.imp (mem x (.inl rfl)) (mem y (.inr rfl)))
  have included (a) (ha : a ∈ names (retained r allow mark u x y)) : a ∈ covered := by
    obtain ⟨_,needs⟩ := mem_retained.mp ((mem_names _ _).mp ha)
    unfold covered
    apply List.mem_append.mpr
    rcases needs with b | ⟨t,i,reach,slot,occ⟩
    · exact .inl (all a b)
    · exact .inr (List.mem_flatMap.mpr ⟨t,all t reach,next_slot reach slot occ⟩)
  have fb (a) : (F a).length ≤ D := next_bound cap a
  have count := size_le (names_distinct _) included
  have size : ball.length ≤ 2*geometric D 6 := by
    have bx := explore_bound F D fb 6 x
    have by' := explore_bound F D fb 6 y
    dsimp only [ball]; rw [List.length_append]; omega
  have more := flat_bound ball F D (fun t _ => fb t)
  have gross : covered.length ≤ ball.length*(1+D) := by
    dsimp only [covered]; rw [List.length_append,Nat.mul_add,Nat.mul_one]; omega
  have lim := Nat.mul_le_mul_right (1+D) size
  have fin := Nat.le_trans count (Nat.le_trans gross lim)
  simpa only [D,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using fin

theorem retained_bound_four {r allow mark u x y} (cap : Capacity r allow mark u x y 4) :
    (names (retained r allow mark u x y)).length ≤ 2*(1+28)*geometric 28 6 := retained_bound cap


/-- The owner cannot itself be a literal occupant between two consecutive
    indexed copies, whether or not the containing word is capped. -/
theorem owner_absent (u : W) (t i : Nat) : ¬ occupies u t i t := by
  intro occ
  obtain ⟨j,hj⟩ := occ
  have mem : (t,i+1) ∈ events u := hj.mem (by simp)
  have b := (P455SlotOrigin.event_bounds (fun _ => 0) u t (i+1) mem).2
  obtain ⟨l,mid,k,cut,index,fresh⟩ := P455SlotOrigin.slot_cut u t i (by omega)
  have occ' : occupies u t i t := ⟨j,hj⟩
  rw [cut,←index] at occ'
  exact fresh ((P455SlotOrigin.occupies_at_cut l mid k t t fresh).mp occ')

/-- An overfull genuine protected slot supplies five distinct saturated
    occupants and their literal terminal witness in a compressed source. -/
theorem overflow_of_more {r allow mark u x y t i}
    (uniform : UniformSlots r allow mark u x y) (cmp : P455SourceFamilies.Compressed r u)
    (ball : InBall r allow mark u x y t) (slot : slotStart i)
    (over : 4 < (occupants u t i).length) :
    ∃ xs, Holds r allow mark u (terminalSlot r t i (.overflow xs)) := by
  classical
  let xs := (occupants u t i).take 5
  have inside (a) (ha : a ∈ xs) : occupies u t i a :=
    mem_occupants.mp ((List.take_sublist _ _).subset ha)
  have nodup : xs.Nodup :=
    (names_distinct u).sublist (List.Sublist.trans (List.take_sublist _ _) List.filter_sublist)
  have uniq : (t::xs).Nodup := List.nodup_cons.mpr ⟨fun h => owner_absent u t i (inside t h),nodup⟩
  refine ⟨xs,List.length_take_of_le (by omega),
    (P455TerminalTransfer.block_separation _).mpr
      (uniq.imp (fun ne => P455SourceFamilies.compressed_separates cmp ne)),?_,True.intro⟩
  apply (allQ_iff _).mpr
  intro q mem
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
  have occ := inside a ha
  exact ⟨uniform t ball i slot a occ,slot,occ⟩

theorem capacity_of_no_overflow {r allow mark u x y}
    (uniform : UniformSlots r allow mark u x y) (cmp : P455SourceFamilies.Compressed r u)
    (none : ∀ t, InBall r allow mark u x y t → ∀ i, slotStart i →
      ∀ xs, ¬ Holds r allow mark u (terminalSlot r t i (.overflow xs))) :
    Capacity r allow mark u x y 4 := by
  intro t ball i slot
  exact Nat.le_of_not_lt (fun h => by
    obtain ⟨xs,w⟩ := overflow_of_more uniform cmp ball slot h
    exact none t ball i slot xs w)


/-- Uniform one-step rank under the actual source geometric guard and validity
    of the canonical smaller identity. Bound depends only on the fixed r. -/
theorem bounded_step_of_capacity {A : Type} (M : P455FirstRewrite.Model A)
    {r allow mark} (f : P455Closure.Frame Nat) (l k : W) {x y : Nat}
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (b : Bool) (cap : P455Closure.Cap r (P455Uncrossed.side f l k b))
    (capacity : Capacity r allow mark (P455Uncrossed.side f l k b) x y 4)
    (semantic :
      let keep := retained r allow mark (P455Uncrossed.side f l k b) x y
      M.Valid (P455Compression.small (P455Uncrossed.side f l k b) keep)
        (P455Compression.small (P455Uncrossed.side f l k (!b)) keep)) :
    let N := 2*(1+28)*geometric 28 6
    P455FirstRewrite.Step (fun u v => M.Valid u v ∧ P455FirstRewrite.rank u v ≤ N+r*N+1)
      (P455Uncrossed.side f l k b) (P455Uncrossed.side f l k (!b)) := by
  let u := P455Uncrossed.side f l k b
  let keep := retained r allow mark u x y
  have flip : ClosedFlip r allow u x y := ⟨f,b,l,k,hp,hq,valid,rfl⟩
  obtain ⟨hr,cx,cy,_⟩ := flip_counts cap flip
  have hx : x ∈ keep := mem_retained.mpr
    ⟨List.count_pos_iff.mp (cx.symm ▸ (by omega : 0 < r)),.inl (.inl (near_self x 6))⟩
  have hy : y ∈ keep := mem_retained.mpr
    ⟨List.count_pos_iff.mp (cy.symm ▸ (by omega : 0 < r)),.inl (.inr (near_self y 6))⟩
  have step := P455SmallRank.bounded_step M f l k keep hx hy hp hq valid b cap semantic
  have small : (names keep).length ≤ 2*(1+28)*geometric 28 6 := retained_bound_four capacity
  have scaled := Nat.mul_le_mul_left r small
  obtain ⟨U,V,L,R,h,hyp,nu,nv,ne,src,dst⟩ := step
  refine ⟨U,V,L,R,h,?_,nu,nv,ne,src,dst⟩
  rcases hyp with ⟨val,rnk⟩|⟨val,rnk⟩
  · exact .inl ⟨val,by omega⟩
  · exact .inr ⟨val,by omega⟩

end P455SupportBound
