import Problem455SingletonEvaluation




namespace P455UniformCross
open P455Witness P455SourceFamilies P455SourceTheorem P455OriginalWalk
open P455ContactLift P455CrossedSupport P455SingletonEvaluation Problem455.Slots

theorem crossed {r allow mark T} (capT : P455Quotient.Cap r T)
    (ts : Tiles) (c : Certificate) (tester : Holds r allow mark T (c.query r ts))
    (U : List Nat) (uniform : ∀ a ∈ U, U.count a = r) (cmp : Compressed r U)
    (x y : Nat) (flip : ClosedFlip r allow U x y)
    (val : Nat → P455Quotient.Q (rules r allow mark) T) (h : Nat → List Nat)
    (reps : ∀ a ∈ U, P455Quotient.ofWord (rules r allow mark) T (h a) = val a)
    (live : P455Quotient.eval (rules r allow mark) capT val U ≠ P455Quotient.zero (rules r allow mark) T)
    (s : Bool) (cross : Crosses (markedRecord c s) h x y) :
    Violation r allow ts U x y := by
  have capU : P455Closure.Cap r U := by
    intro a
    by_cases ha : a ∈ U
    · exact Nat.le_of_eq (uniform a ha)
    · simp [List.count_eq_zero.mpr ha]
  obtain ⟨hr,cx,cy,_⟩ := flip_counts capU flip
  have pos : 0 < r := by omega
  obtain ⟨seed,side,img⟩ := choose_seed c s false cross
  have source : Supplies U h r seed (startLabel c s false) :=
    ⟨side.elim (fun eq => eq ▸ cx) (fun eq => eq ▸ cy),img⟩
  let ident := fun a : Nat => [a]
  have exp : P455Retained.Expansion U ident (fun _ => True) :=
    ⟨fun _ _ _ => rfl, fun _ _ f => (f True.intro).elim⟩
  have back : U.flatMap ident = U := by simp [ident]
  have guard : OriginalGuard r allow mark (U.flatMap ident) (fun _ => True) seed 6 := by
    rw [back]
    intro t _
    refine ⟨True.intro,?_⟩
    intro i _ a occ
    obtain ⟨j,seen⟩ := occ
    exact ⟨True.intro,uniform a (stamped_mem_label _ _ (a,j) (seen.subset (by simp)))⟩
  obtain ⟨_,_,_,_,_,_,_,read,_⟩ := arbitrary_reps_original_gadget capT val U h reps live ts c tester
    s false seed hr source exp (back.symm ▸ capU) guard
  rw [back] at read
  let R := rules r allow mark
  have ev := P455Quotient.eval_rep R capT val U h reps
  have good := (P455Quotient.nonzero_iff R).mp (ev ▸ live)
  have capH := P455Quotient.good_cap R capT good
  let d := donor U h r
  refine ⟨transferred d c,s,?_,?_⟩
  · rw [changed_anchor]
    rcases cross with ⟨xo,ym⟩|⟨yo,xm⟩
    · exact .inl ⟨donor_eq pos capH ⟨cx,xo⟩,donor_eq pos capH ⟨cy,ym⟩⟩
    · exact .inr ⟨donor_eq pos capH ⟨cy,yo⟩,donor_eq pos capH ⟨cx,xm⟩⟩
  · rw [reindexed_marks]; exact read cmp

theorem crossed_word {r allow mark T} (capT : P455Quotient.Cap r T)
    (ts : Tiles) (c : Certificate) (tester : Holds r allow mark T (c.query r ts))
    (U : List Nat) (uniform : ∀ a ∈ U, U.count a = r) (cmp : Compressed r U)
    (x y : Nat) (flip : ClosedFlip r allow U x y) (h : Nat → List Nat)
    (good : P455Quotient.Good (rules r allow mark) T (U.flatMap h))
    (s : Bool) (cross : Crosses (markedRecord c s) h x y) : Violation r allow ts U x y := by
  let R := rules r allow mark
  let val := fun a => P455Quotient.ofWord R T (h a)
  apply crossed capT ts c tester U uniform cmp x y flip val h (fun _ _ => rfl) _ s cross
  rw [P455Quotient.eval_rep R capT val U h (fun _ _ => rfl)]
  exact (P455Quotient.nonzero_iff R).mpr good

end P455UniformCross
