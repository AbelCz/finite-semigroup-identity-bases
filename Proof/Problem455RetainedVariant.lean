import Problem455SlotSaturation
import Problem455CompressedFrame

/- Retention is relative to the chosen marked component only through
   mark-independent contact observations. Both live orientations use
   exactly the same literal names and the same numerical gap naming. -/
namespace P455RetainedVariant
open P455Witness P455Paths P455CrossedSupport P455SlotSaturation P455Compression
open Problem455.Slots

theorem near_move {r allow mark u v} (mv : P455Closure.Move r allow noMark u v) (a t J : Nat) :
    Near r allow mark u a t J ↔ Near r allow mark v a t J := by
  constructor
  · rintro ⟨p,w,e,len⟩; exact ⟨p,pull_walk mv.symm _ _ w,e,len⟩
  · rintro ⟨p,w,e,len⟩; exact ⟨p,pull_walk mv _ _ w,e,len⟩

theorem needed_move {r allow mark u v} (mv : P455Closure.Move r allow noMark u v) (x y b : Nat) :
    Needed r allow mark u x y b ↔ Needed r allow mark v x y b := by
  have ball (t) : InBall r allow mark u x y t ↔ InBall r allow mark v x y t :=
    or_congr (near_move mv x t 6) (near_move mv y t 6)
  apply or_congr (ball b)
  constructor
  · rintro ⟨t,i,nb,sl,oc⟩; exact ⟨t,i,(ball t).mp nb,sl,(mv.slot_iff t i b sl).mp oc⟩
  · rintro ⟨t,i,nb,sl,oc⟩; exact ⟨t,i,(ball t).mpr nb,sl,(mv.slot_iff t i b sl).mpr oc⟩

theorem same_retained {r allow mark u v} (mv : P455Closure.Move r allow noMark u v) (x y : Nat) :
    (retained r allow mark u x y).Perm (retained r allow mark v x y) := by
  classical
  have perm : u.Perm v := List.perm_iff_count.mpr mv.count_eq
  unfold retained
  have pred : (fun b => decide (Needed r allow mark u x y b)) =
              (fun b => decide (Needed r allow mark v x y b)) := by
    funext b; simp [(needed_move mv x y b : Needed r allow mark u x y b ↔ _)]
  rw [pred]
  exact perm.filter _

theorem sum_perm {s t : W} (h : s.Perm t) : s.sum = t.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [List.sum_cons]; omega
  | trans _ _ ih jh => exact ih.trans jh

theorem pieces_perm (w : W) {s t : W} (perm : s.Perm t) : pieces s w = pieces t w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    by_cases h : a ∈ s
    · simp [pieces,h,perm.mem_iff.mp h,ih]
    · have ht : a ∉ t := fun m => h (perm.mem_iff.mpr m)
      simp [pieces,h,ht,ih]

theorem small_congr_names (w : W) {s t : W} (perm : s.Perm t) : small w s = small w t := by
  simp only [small,base,sum_perm perm,pieces_perm w perm]

theorem retained_remark {r allow mark mark' u x y} :
    retained r allow mark u x y = retained r allow mark' u x y := by
  classical
  have near (a b : Nat) (m m' : Marking) (h : Near r allow m u a b 6) : Near r allow m' u a b 6 := by
    obtain ⟨p,w,ep,len⟩ := h
    exact ⟨p,P455SourceFamilies.remark_walk a p w,ep,len⟩
  have ball (b : Nat) (m m' : Marking) (h : InBall r allow m u x y b) : InBall r allow m' u x y b :=
    h.imp (near _ _ _ _) (near _ _ _ _)
  have need (a : Nat) (m m' : Marking) (h : Needed r allow m u x y a) : Needed r allow m' u x y a := by
    rcases h with h|⟨t,i,h,hi,occ⟩
    · exact .inl (ball _ _ _ h)
    · exact .inr ⟨t,i,ball _ _ _ h,hi,occ⟩
  unfold retained
  apply List.filter_congr
  intro b _
  simp [show Needed r allow mark u x y b ↔ Needed r allow mark' u x y b from ⟨need _ _ _,need _ _ _⟩]

end P455RetainedVariant
