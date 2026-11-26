import Problem455Finite
import Problem455DonorInterval



namespace P455Uncrossed
open P455Closure Problem455Finite
abbrev W := List Nat
abbrev Tags := List Bool → Prop
abbrev Marks := Nat → Nat → Prop

def side (f : Frame Nat) (l k : W) (bit : Bool) := l ++ f.core bit ++ k

def Unmarked (mark : Marks) (h : Nat → W) (x y : Nat) : Prop :=
  ∀ a ∈ h x, ∀ b ∈ h y, ¬ mark a b ∧ ¬ mark b a

private theorem nodup_of_counts (w : W) (h : ∀ a ∈ w, w.count a ≤ 1) : w.Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    apply List.nodup_cons.mpr
    have one := h a (by simp)
    simp only [List.count_cons_self] at one
    exact ⟨List.count_eq_zero.mp (by omega),
      ih fun b hb => by have hh := h b (by simp [hb]); simp [List.count_cons] at hh; omega⟩

private theorem core_mem {r A M} (f : Frame Nat) (valid : f.Valid r A M)
    (bit : Bool) (a : Nat) (mem : a ∈ f.p ∨ a ∈ f.q) : (f.core bit).count a = r := by
  have base := valid.2.2.2.2.2.2.2 a mem
  cases bit
  · exact base
  · exact (f.count_core a true).trans base

private def mappedFrame (f : Frame Nat) (h : Nat → W) (pHead : Nat) (pTail qInit : W)
    (qLast : Nat) : Frame Nat where
  pHead := pHead
  pTail := pTail
  qInit := qInit
  qLast := qLast
  tag := f.tag
  middle := f.middle.map (fun e => (e.1.flatMap h, e.2))
  beforeMutable := f.beforeMutable.flatMap h
  beforeFinalP := f.beforeFinalP.flatMap h
  beforeFinalQ := f.beforeFinalQ.flatMap h

private theorem mid_image (f : Frame Nat) (h : Nat → W) (phead : Nat) (pt qi : W) (qlast : Nat)
    (hp : f.p.flatMap h = phead :: pt) (hq : f.q.flatMap h = qi ++ [qlast]) :
    f.mid.flatMap h = (mappedFrame f h phead pt qi qlast).mid := by
  simp only [Frame.mid,mappedFrame,List.flatMap_assoc,List.flatMap_map]
  congr 1
  funext z
  obtain ⟨w,b⟩ := z
  cases b <;> simp only [Function.comp_apply, Bool.false_eq_true, if_false, if_true,
    List.flatMap_append, hp, hq] <;> rfl

private theorem core_image (f : Frame Nat) (h : Nat → W) (phead : Nat) (pt qi : W) (qlast : Nat)
    (hp : f.p.flatMap h = phead :: pt) (hq : f.q.flatMap h = qi ++ [qlast]) (bit : Bool) :
    (f.core bit).flatMap h = (mappedFrame f h phead pt qi qlast).core bit := by
  have mid := mid_image f h phead pt qi qlast hp hq
  cases bit <;> simp only [Frame.core,Frame.early,Frame.pair,Bool.false_eq_true,if_false,if_true,
    List.flatMap_append, mid, hp, hq] <;> rfl

theorem equal_or_move {r allow mark} (f : Frame Nat) (l k : W) (bit : Bool) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (h : Nat → W) (clear : Unmarked mark h x y)
    (cap : Cap r ((side f l k bit).flatMap h)) :
    (side f l k bit).flatMap h = (side f l k (!bit)).flatMap h ∨
    Move r allow mark ((side f l k bit).flatMap h) ((side f l k (!bit)).flatMap h) := by
  have xmap : f.p.flatMap h = h x := by simp [hp]
  have ymap : f.q.flatMap h = h y := by simp [hq]
  by_cases empty : h x = [] ∨ h y = []
  · left
    rcases empty with hx | hy <;> cases bit <;>
      simp [side,Frame.core,Frame.pair,List.flatMap_append,xmap,ymap, *]
  right
  have nonX : h x ≠ [] := fun e => empty (Or.inl e)
  have nonY : h y ≠ [] := fun e => empty (Or.inr e)
  obtain ⟨phead,pt,p⟩ : ∃ a t, h x = a :: t := by cases hv : h x <;> simp_all
  obtain ⟨qi,qlast,q⟩ : ∃ t a, h y = t ++ [a] := by
    cases hv : (h y).reverse with
    | nil => have e := congrArg List.reverse hv; simp_all
    | cons a t => exact ⟨t.reverse,a,by simpa using congrArg List.reverse hv⟩
  let g := mappedFrame f h phead pt qi qlast
  have gp : g.p = h x := p.symm
  have gq : g.q = h y := q.symm
  have eq (b : Bool) :
      (side f l k b).flatMap h = l.flatMap h ++ g.core b ++ k.flatMap h := by
    simp only [side,List.flatMap_append,core_image f h _ _ _ _ (xmap.trans p) (ymap.trans q),g]
  have capCore : Cap r ((f.core bit).flatMap h) := by
    intro a; have hh := cap a; simp only [side,List.flatMap_append,List.count_append] at hh; omega
  have xm : x ∈ f.p := by simp [hp]
  have ym : y ∈ f.q := by simp [hq]
  have ne : x ≠ y := fun e => valid.2.2.2.2.2.1 x xm (e ▸ ym)
  have hr : 0 < r := by have := valid.1; omega
  have cx := core_mem f valid bit x (.inl xm)
  have cy := core_mem f valid bit y (.inr ym)
  have usedY : y ∈ f.core bit := List.count_pos_iff.mp (cy.symm ▸ hr)
  have excl (a : Nat) (ha : a ∈ h x) :=
    P455DonorInterval.exclusive h (f.core bit) x a r hr cx ha (capCore a)
  have capImage := eq bit ▸ cap
  have gv : g.Valid r allow mark := by
    apply g.valid_of_capped_shape valid.1 valid.2.1 _ _ _ _ _ bit (l.flatMap h) (k.flatMap h) capImage
    · simpa [g,mappedFrame,List.map_map,Function.comp_def] using valid.2.2.1
    · rw [gp]; apply nodup_of_counts
      exact fun a ha => Nat.le_of_eq (excl a ha).1
    · rw [gq]; apply nodup_of_counts
      exact fun a ha => Nat.le_of_eq (P455DonorInterval.exclusive h (f.core bit) y a r hr cy ha (capCore a)).1
    · rw [gp,gq]; exact fun a ha => (excl a ha).2.1 y usedY ne.symm
    · simpa only [gp,gq] using clear
  exact ⟨g,bit,l.flatMap h,k.flatMap h,gv,eq bit,eq (!bit),cap⟩

private theorem words_from_good {r allow mark T} (capT : P455Quotient.Cap r T)
    (f : Frame Nat) (l k : W) (bit : Bool) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (h : Nat → W) (clear : Unmarked mark h x y)
    (good : P455Quotient.Good (rules r allow mark) T ((side f l k bit).flatMap h)) :
    P455Quotient.ofWord (rules r allow mark) T ((side f l k bit).flatMap h) =
      P455Quotient.ofWord (rules r allow mark) T ((side f l k (!bit)).flatMap h) := by
  let R := rules r allow mark
  have cap := P455Quotient.good_cap R capT good
  rcases equal_or_move f l k bit x y hp hq valid h clear cap with e | move
  · rw [e]
  · have path := P455Quotient.Walk.snoc (s := R.step) (.refl _) move
    have equiv := P455Quotient.good_context R capT path [] []
    simp only [List.nil_append,List.append_nil] at equiv
    exact (P455Quotient.same_nonzero_class R good).mpr ⟨equiv.mp good,path⟩

/-- Uncrossed literal representatives agree even if their product is zero.
    Any nonzero side supplies the cap on its evaluated factor. -/
theorem uncrossed_words {r allow mark T} (capT : P455Quotient.Cap r T)
    (f : Frame Nat) (l k : W) (bit : Bool) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (h : Nat → W) (clear : Unmarked mark h x y) :
    P455Quotient.ofWord (rules r allow mark) T ((side f l k bit).flatMap h) =
      P455Quotient.ofWord (rules r allow mark) T ((side f l k (!bit)).flatMap h) := by
  let R := rules r allow mark
  by_cases g : P455Quotient.Good R T ((side f l k bit).flatMap h)
  · exact words_from_good capT f l k bit x y hp hq valid h clear g
  by_cases g' : P455Quotient.Good R T ((side f l k (!bit)).flatMap h)
  · simpa using (words_from_good capT f l k (!bit) x y hp hq valid h clear g').symm
  have dead (w : W) (h : ¬ P455Quotient.Good R T w) :
      P455Quotient.ofWord R T w = P455Quotient.zero R T := by
    apply Classical.byContradiction
    intro nz; exact h ((P455Quotient.nonzero_iff R).mp nz)
  exact (dead _ g).trans (dead _ g').symm

theorem same_letters (f : Frame Nat) (l k : W) (bit : Bool) (a : Nat) :
    a ∈ side f l k bit ↔ a ∈ side f l k (!bit) := by
  have c := f.count_core a bit
  have perm : (side f l k bit).count a = (side f l k (!bit)).count a := by
    simp only [side,List.count_append,c]
  rw [←List.count_pos_iff,←List.count_pos_iff,perm]

/-- Arbitrarily chosen quotient representatives for all occurring variables
    are enough for a decision for a fixed evaluation. -/
theorem uncrossed_eval {r allow mark T} (capT : P455Quotient.Cap r T)
    (f : Frame Nat) (l k : W) (bit : Bool) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (val : Nat → P455Quotient.Q (rules r allow mark) T) (h : Nat → W)
    (reps : ∀ a ∈ side f l k bit, P455Quotient.ofWord (rules r allow mark) T (h a) = val a)
    (clear : Unmarked mark h x y) :
    P455Quotient.eval (rules r allow mark) capT val (side f l k bit) =
      P455Quotient.eval (rules r allow mark) capT val (side f l k (!bit)) := by
  rw [P455Quotient.eval_rep _ _ _ _ h reps,
      P455Quotient.eval_rep _ _ _ _ h (fun a ha => reps a ((same_letters f l k bit a).mpr ha))]
  exact uncrossed_words capT f l k bit x y hp hq valid h clear


/-- A distinguishing evaluation forces a cross-block mark in EVERY choice of
    representatives of its occurring variables. Both stored orientations count. -/
theorem difference_crosses {r allow mark T} (capT : P455Quotient.Cap r T)
    (f : Frame Nat) (l k : W) (bit : Bool) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (val : Nat → P455Quotient.Q (rules r allow mark) T) (h : Nat → W)
    (reps : ∀ a ∈ side f l k bit, P455Quotient.ofWord (rules r allow mark) T (h a) = val a)
    (diff : P455Quotient.eval (rules r allow mark) capT val (side f l k bit) ≠
      P455Quotient.eval (rules r allow mark) capT val (side f l k (!bit))) :
    ∃ a ∈ h x, ∃ b ∈ h y, mark a b ∨ mark b a := by
  apply Classical.byContradiction
  intro none
  apply diff
  apply uncrossed_eval capT f l k bit x y hp hq valid val h reps
  intro a ha b hb
  exact ⟨fun e => none ⟨a,ha,b,hb,Or.inl e⟩,fun e => none ⟨a,ha,b,hb,Or.inr e⟩⟩

/-- A distinguishing valuation has a live orientation and simultaneous arbitrary
    good-word representatives for its letters. Each such simultaneous choice
    occurs as a literal factor of a variant, including arbitrary proper factors. -/
theorem difference_live_representatives {r allow mark T} (capT : P455Quotient.Cap r T)
    (f : Frame Nat) (l k : W)
    (val : Nat → P455Quotient.Q (rules r allow mark) T)
    (diff : P455Quotient.eval (rules r allow mark) capT val (side f l k false) ≠
      P455Quotient.eval (rules r allow mark) capT val (side f l k true)) :
    ∃ bit : Bool,
      P455Quotient.eval (rules r allow mark) capT val (side f l k bit) ≠
        P455Quotient.zero (rules r allow mark) T ∧
      (∃ h : Nat → W, ∀ a ∈ side f l k bit,
        P455Quotient.Good (rules r allow mark) T (h a) ∧
        P455Quotient.ofWord (rules r allow mark) T (h a) = val a) ∧
      (∀ h : Nat → W, (∀ a ∈ side f l k bit,
        P455Quotient.ofWord (rules r allow mark) T (h a) = val a) →
        ∃ V left right, P455Quotient.Variant (rules r allow mark) T V ∧
          V = left ++ (side f l k bit).flatMap h ++ right) := by
  classical
  let R := rules r allow mark
  have live : ∃ bit, P455Quotient.eval R capT val (side f l k bit) ≠ P455Quotient.zero R T := by
    by_cases nz : P455Quotient.eval R capT val (side f l k false) ≠ P455Quotient.zero R T
    · exact ⟨false,nz⟩
    · exact ⟨true,fun z => diff ((Classical.not_not.mp nz).trans z.symm)⟩
  obtain ⟨bit,nz⟩ := live
  refine ⟨bit,nz,?_,?_⟩
  · have word (a) (ha : a ∈ side f l k bit) :=
      P455Quotient.nonzero_representative R (val a) (P455Quotient.live_inputs R capT val _ nz a ha)
    let h (a : Nat) := if ha : a ∈ side f l k bit then (word a ha).choose else []
    refine ⟨h,fun a ha => ?_⟩
    simpa only [h,dif_pos ha] using (word a ha).choose_spec
  · intro h reps
    exact (P455Quotient.arbitrary_representatives R capT val _ h reps).mp nz

end P455Uncrossed
