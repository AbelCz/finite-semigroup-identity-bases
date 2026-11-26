import Problem455LocalIdentity




namespace P455BinaryEquality
open P455Witness P455Closure P455Uncrossed P455SlotSaturation P455FirstTesters
open Problem455.Slots
abbrev W := List Nat

def BinaryNames (T : W) := ∀ a ∈ T, a=0 ∨ a=1
def IsProfile (r : Nat) (allow : Tag → Prop) (T : W) :=
  ∃ a b tag bit, a ≠ b ∧ tag.length+16 = r ∧ allow tag ∧ T = profile a b tag bit

theorem binary_move_profile {r allow T V} (h : Move r allow noMark T V)
    (two : BinaryNames T) : IsProfile r allow T := by
  obtain ⟨f,bit,l,k,ok,rfl,_,cap⟩ := h
  let a := f.pHead
  let b := f.qLast
  have ap : a ∈ f.p := by simp [a,Frame.p]
  have bq : b ∈ f.q := by simp [b,Frame.q]
  have ab := fun e : a = b => ok.2.2.2.2.2.1 a ap (e ▸ bq)
  have hr : 0 < r := by have := ok.1; omega
  have mem (z : Nat) (hz : z ∈ f.p ∨ z ∈ f.q) : z ∈ l ++ f.core bit ++ k := by
    have count : (f.core bit).count z = r := by
      have cz := ok.2.2.2.2.2.2.2 z hz
      cases bit; exact cz; exact (f.count_core z true).trans cz
    have ins := List.count_pos_iff.mp (count.symm ▸ hr)
    simp [ins]
  have az := two _ (mem a (.inl ap))
  have bz := two _ (mem b (.inr bq))
  have all : ∀ z ∈ l ++ f.core bit ++ k, z=a ∨ z=b := by
    intro z hz; rcases az with ha|ha <;> rcases bz with hb|hb <;> rcases two _ hz with h|h <;> simp_all
  have pr := f.cross_projection ok bit l k cap a b ap bq
  have eq : (l ++ f.core bit ++ k).filter (fun z => decide (z=a ∨ z=b)) = _ :=
    List.filter_eq_self.mpr (fun z hz => decide_eq_true (all z hz))
  rw [eq,P455SlotProduct.profile_eq] at pr
  exact ⟨a,b,f.tag,bit,ab,by have := ok.1; omega,ok.2.1,pr⟩

theorem no_move_in_factor {r allow U V T} (capT : Cap r T) (two : BinaryNames T)
    (plainT : ¬ IsProfile r allow T) (factor : P455Quotient.Factor U T) : ¬ Move r allow noMark U V := by
  rintro mv
  obtain ⟨l,k,rfl⟩ := factor
  exact plainT (binary_move_profile (mv.extend_of_cap l k capT) two)

theorem plain_good {r T U} (g : P455Quotient.Good (plain r) T U) : P455Quotient.Factor U T := by
  obtain ⟨v,p,h⟩ := g
  have eq : T=v := by
    induction p with
    | refl => rfl
    | snoc _ bad _ => exact False.elim bad
  exact eq ▸ h

/-- No source cap is assumed. Liveness provides the cap in the actual
    binary component and forces all assigned representatives to be honest
    factors, including units. -/
theorem plain_equal {r allow T} (capT : Cap r T) (two : BinaryNames T) (plainT : ¬ IsProfile r allow T)
    (f : Frame Nat) (l k : W) (x y : Nat) (hp : f.p = [x]) (hq : f.q = [y])
    (v : f.Valid r allow noMark) (val : Nat → P455Quotient.Q (plain r) T) :
    P455Quotient.eval (plain r) capT val (side f l k false) =
    P455Quotient.eval (plain r) capT val (side f l k true) := by
  classical
  let R := plain r
  let E := fun b => P455Quotient.eval R capT val (side f l k b)
  have one (b : Bool) (nz : E b ≠ P455Quotient.zero R T) : E b = E (!b) := by
    have rep (a) (h : a ∈ side f l k b) :=
      P455Quotient.nonzero_representative R _ (P455Quotient.live_inputs R capT val _ nz a h)
    let h a := if m : a ∈ side f l k b then (rep a m).choose else []
    have reps (a) (m : a ∈ side f l k b) : P455Quotient.ofWord R T (h a) = val a := by
      simpa only [h,dif_pos m] using (rep a m).choose_spec.2
    have eq := P455Quotient.eval_rep R capT val _ h reps
    change P455Quotient.eval R capT val (side f l k b) ≠ _ at nz
    have good := (P455Quotient.nonzero_iff R).mp (eq ▸ nz)
    have cap := P455Quotient.good_cap R capT good
    rcases equal_or_move f l k b x y hp hq v h (mark := noMark) (fun _ _ _ _ => ⟨id,id⟩) cap with raw|move
    · change P455Quotient.eval R capT val _ = P455Quotient.eval R capT val _
      rw [eq,raw,P455Quotient.eval_rep R capT val (side f l k (!b)) h
        (fun a m => reps a ((same_letters f l k b a).mpr m))]
    · exact False.elim (no_move_in_factor capT two plainT (plain_good good) move)
  by_cases zero : E false = P455Quotient.zero R T
  · by_cases z : E true = P455Quotient.zero R T
    · exact zero.trans z.symm
    · exact (one true z).symm
  · exact one false zero

end P455BinaryEquality
