import Problem455EffectiveQReach


namespace P455EffectiveQ
open P455Quotient Problem455Finite
abbrev W := List Nat

def words (u : W) := wordsUpTo u u.length

theorem subword {u v : W} (s : u.Sublist v) : u ∈ words v := covered v v.length u s.length_le s.subset

def factorB (u v : W) := (words v).any (fun l => (words v).any (fun t => decide (v=l++u++t)))

theorem factor_iff (u v : W) : factorB u v=true ↔ Factor u v := by
  simp only [factorB,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨l,_,t,_,h⟩; exact ⟨l,t,h⟩
  · rintro ⟨l,t,rfl⟩
    exact ⟨l,subword ((List.sublist_append_left l u).trans (List.sublist_append_left _ t)),
      t,subword (List.sublist_append_right _ _),rfl⟩

def walkB (e : W → W → Bool) (u v : W) := P455EffectiveQReach.via e (words u) u v

theorem walk_iff (R : Rules Nat) (e : W → W → Bool) (ok : ∀ u v,e u v=true ↔ R.step u v)
    (u v : W) : walkB e u v=true ↔ Walk R.step u v := by
  constructor
  · exact P455EffectiveQReach.sound _ (fun x y => (ok x y).mp) _
  · intro path
    apply P455EffectiveQReach.complete _ (fun x y => (ok x y).mpr) _ _ path
    intro x reach
    have perm := List.perm_iff_count.mpr (count_walk R reach)
    exact covered _ _ _ (Nat.le_of_eq perm.length_eq.symm) (fun _ m => perm.mem_iff.mpr m)

def goodB (e : W → W → Bool) (T u : W) :=
  (words T).any fun v => walkB e T v && factorB u v

theorem good_iff (R : Rules Nat) (e : W → W → Bool) (ok : ∀ u v,e u v=true ↔ R.step u v)
    (T u : W) : goodB e T u=true ↔ Good R T u := by
  simp only [goodB,List.any_eq_true,Bool.and_eq_true,walk_iff R e ok,factor_iff]
  constructor
  · rintro ⟨v,_,p,f⟩; exact ⟨v,p,f⟩
  · rintro ⟨v,p,f⟩
    have pe := List.perm_iff_count.mpr (count_walk R p)
    exact ⟨v,covered _ _ _ (Nat.le_of_eq pe.length_eq.symm) (fun _ m => pe.mem_iff.mpr m),p,f⟩

def liveB (e : W → W → Bool) (T : W) : Raw Nat → Bool
  | none => false
  | some u => goodB e T u

def paired (e : W → W → Bool) (T : W) : Raw Nat → Raw Nat → Bool
  | some u,some v => goodB e T u && goodB e T v && walkB e u v
  | _,_ => false

def relB (e : W → W → Bool) (T : W) (a b : Raw Nat) :=
  ((!liveB e T a) && (!liveB e T b)) || paired e T a b

theorem rel_iff (R : Rules Nat) (e : W → W → Bool) (ok : ∀ u v,e u v=true ↔ R.step u v)
    (T : W) (a b : Raw Nat) : relB e T a b=true ↔ Rel R T a b := by
  have live (x : Raw Nat) : liveB e T x=true ↔ Live R T x := by
    cases x with
    | none => simp [liveB,Live]
    | some u => exact good_iff R e ok T u
  have no (x : Raw Nat) : (!liveB e T x)=true ↔ ¬Live R T x := by
    rw [←live]; cases liveB e T x <;> decide
  simp only [relB,Bool.or_eq_true,Bool.and_eq_true,no,Rel]
  apply or_congr_right
  cases a <;> cases b <;> simp [paired,good_iff R e ok,walk_iff R e ok,and_assoc,Option.some.injEq]
  constructor
  · intro h; exact ⟨_,rfl,_,rfl,h⟩
  · rintro ⟨u,hu,v,hv,h⟩; cases hu; cases hv; exact h

def eqB (R : Rules Nat) (e : W → W → Bool) (ok : ∀ u v,e u v=true ↔ R.step u v)
    (T : W) (x y : Q R T) : Bool :=
  Quotient.liftOn₂ x y (relB e T) (by
    intro a b c d ac bd
    apply Bool.eq_iff_iff.mpr
    rw [rel_iff R e ok,rel_iff R e ok]
    exact ⟨fun ab => rel_trans R (rel_symm R ac) (rel_trans R ab bd),
           fun cd => rel_trans R ac (rel_trans R cd (rel_symm R bd))⟩)

theorem eq_iff (R : Rules Nat) (e : W → W → Bool) (ok : ∀ u v,e u v=true ↔ R.step u v)
    (T : W) (x y : Q R T) : eqB R e ok T x y=true ↔ x=y := by
  induction x,y using Quotient.inductionOn₂ with | _ a b =>
    exact (rel_iff R e ok T a b).trans ⟨fun h => Quotient.sound (s := setoid R T) h,fun h => Quotient.exact h⟩

def decEq (R : Rules Nat) (e : W → W → Bool) (ok : ∀ u v,e u v=true ↔ R.step u v)
    (T : W) : DecidableEq (Q R T) :=
  fun x y => decidable_of_bool _ (eq_iff R e ok T x y)

end P455EffectiveQ
