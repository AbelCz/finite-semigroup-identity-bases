import Std




namespace P455Quotient

abbrev Word (α : Type) := List α

inductive Walk {α : Type} (s : α → α → Prop) : α → α → Prop
  | refl (a) : Walk s a a
  | snoc {a b c} : Walk s a b → s b c → Walk s a c

namespace Walk
theorem trans {s : α → α → Prop} (h : Walk s x y) (k : Walk s y z) : Walk s x z := by
  induction k with
  | refl => exact h
  | snoc _ step ih => exact .snoc ih step

theorem symm {s : α → α → Prop} (rev : ∀ {x y}, s x y → s y x) (h : Walk s x y) :
    Walk s y x := by
  induction h with
  | refl => exact .refl _
  | snoc _ step ih => exact (Walk.snoc (.refl _) (rev step)).trans ih

theorem transport {s : α → α → Prop} {P : α → Prop} (h : Walk s x y) (px : P x)
    (step : ∀ {u v}, s u v → P u → P v) : P y := by
  induction h with
  | refl => exact px
  | snoc _ move ih => exact step move ih
end Walk

section
variable {α : Type} [DecidableEq α]
local notation "W" => Word α
def Cap (r : Nat) (u : W) : Prop := ∀ a : α, u.count a ≤ r
structure Rules (α : Type) [DecidableEq α] where
  r : Nat
  step : Word α → Word α → Prop
  reverse : ∀ {u v}, step u v → step v u
  counts : ∀ {u v}, step u v → ∀ a, u.count a = v.count a
  extend : ∀ {u v}, step u v → ∀ l t, Cap r (l ++ u ++ t) →
    step (l ++ u ++ t) (l ++ v ++ t)

variable (R : Rules α)
abbrev Variant (T v : W) := Walk R.step T v
def Factor (u v : W) := ∃ l t : Word α, v = l ++ u ++ t
def Good (T u : W) := ∃ v, Variant R T v ∧ Factor u v

theorem count_walk {u v : W} (h : Walk R.step u v) (a : α) : u.count a = v.count a := by
  induction h with
  | refl => rfl
  | snoc _ step ih => exact ih.trans (R.counts step a)

theorem contextual_walk {u v : W} (h : Walk R.step u v) (l t : Word α)
    (hc : Cap R.r (l ++ u ++ t)) : Walk R.step (l ++ u ++ t) (l ++ v ++ t) := by
  induction h with
  | refl => exact .refl _
  | snoc pre mv ih =>
    apply Walk.snoc ih (R.extend mv l t ?_)
    intro a
    have eq := count_walk R pre a
    have bound := hc a
    simp only [List.count_append] at *
    omega

theorem good_context {T u v : W} (hc : Cap R.r T) (h : Walk R.step u v)
    (l t : Word α) : Good R T (l ++ u ++ t) ↔ Good R T (l ++ v ++ t) := by
  suffices f : ∀ {x y}, Walk R.step x y → Good R T (l ++ x ++ t) → Good R T (l ++ y ++ t) from
    ⟨f h, f (h.symm R.reverse)⟩
  intro x y path ⟨variant, reach, left, right, eq⟩
  subst variant
  have bound : Cap R.r ((left ++ l) ++ x ++ (t ++ right)) := by
    intro a
    have e := count_walk R reach a
    simp only [List.count_append] at *
    have := hc a
    omega
  have ext := contextual_walk R path (left ++ l) (t ++ right) bound
  simp only [List.append_assoc] at reach ext ⊢
  exact ⟨_, reach.trans ext, left, right, by simp [List.append_assoc]⟩

theorem good_cap {T u : W} (hc : Cap R.r T) (h : Good R T u) : Cap R.r u := by
  obtain ⟨_, reach, l, t, rfl⟩ := h
  intro a
  have e := count_walk R reach a
  have b := hc a
  simp only [List.count_append] at e
  omega

theorem factor_good {T u v : W} (g : Good R T v) (f : Factor u v) : Good R T u := by
  obtain ⟨w, path, l, t, hw⟩ := g
  obtain ⟨l', t', hv⟩ := f
  exact ⟨w, path, l ++ l', t' ++ t, by simp [hw, hv, List.append_assoc]⟩

def Raw (α : Type) := Option (Word α)
def mulRaw : Raw α → Raw α → Raw α
  | some u, some v => some (u ++ v)
  | _, _ => none

def Live (T : W) : Raw α → Prop
  | none => False
  | some u => Good R T u

def Rel (T : W) (x y : Raw α) : Prop :=
  (¬ Live R T x ∧ ¬ Live R T y) ∨
  ∃ u v : W, x = some u ∧ y = some v ∧ Good R T u ∧ Good R T v ∧ Walk R.step u v

theorem rel_refl (T : W) (x : Raw α) : Rel R T x x := by
  by_cases h : Live R T x
  · cases x with
    | none => exact h.elim
    | some u => exact Or.inr ⟨u,u,rfl,rfl,h,h,.refl _⟩
  · exact Or.inl ⟨h,h⟩

theorem rel_symm {T : W} {x y : Raw α} : Rel R T x y → Rel R T y x := by
  rintro (⟨a,b⟩ | ⟨u,v,rfl,rfl,gu,gv,h⟩)
  · exact Or.inl ⟨b,a⟩
  · exact Or.inr ⟨v,u,rfl,rfl,gv,gu,h.symm R.reverse⟩

theorem rel_trans {T : W} {x y z : Raw α} : Rel R T x y → Rel R T y z → Rel R T x z := by
  rintro (⟨a,b⟩ | ⟨u,v,rfl,rfl,gu,gv,h⟩) k
  · rcases k with ⟨_,c⟩ | ⟨v,w,rfl,rfl,gv,_,_⟩
    · exact Or.inl ⟨a,c⟩
    · exact (b gv).elim
  · rcases k with ⟨b,_⟩ | ⟨v',w,e,rfl,_,gw,h'⟩
    · exact (b gv).elim
    · cases e
      exact Or.inr ⟨u,w,rfl,rfl,gu,gw,h.trans h'⟩

def setoid (T : W) : Setoid (Raw α) where
  r := Rel R T
  iseqv := ⟨rel_refl R T, rel_symm R, rel_trans R⟩

abbrev Q (T : W) := Quotient (setoid R T)

def context (l t : Word α) : Raw α → Raw α
  | none => none
  | some u => some (l ++ u ++ t)

theorem dead_context {T : W} {x : Raw α} (d : ¬ Live R T x) (l t : Word α) :
    ¬ Live R T (context l t x) := by
  cases x with
  | none => exact id
  | some u => exact fun g => d (factor_good R g ⟨l,t,rfl⟩)

theorem rel_context {T : W} (hc : Cap R.r T) {x y : Raw α} (h : Rel R T x y)
    (l t : Word α) : Rel R T (context l t x) (context l t y) := by
  rcases h with ⟨a,b⟩ | ⟨u,v,rfl,rfl,_,_,path⟩
  · exact Or.inl ⟨dead_context R a l t,dead_context R b l t⟩
  · have equiv := good_context R hc path l t
    by_cases gu : Good R T (l ++ u ++ t)
    · exact Or.inr ⟨_,_,rfl,rfl,gu,equiv.mp gu,contextual_walk R path l t (good_cap R hc gu)⟩
    · exact Or.inl ⟨gu,fun gv => gu (equiv.mpr gv)⟩

theorem mul_compat {T : W} (hc : Cap R.r T) {x y z t : Raw α}
    (h : Rel R T x y) (k : Rel R T z t) : Rel R T (mulRaw x z) (mulRaw y t) := by
  apply rel_trans R (y := mulRaw y z)
  · cases z with
    | none => cases x <;> cases y <;> exact rel_refl R _ _
    | some w =>
      have e := rel_context R hc h [] w
      cases x <;> cases y <;> exact e
  · cases y with
    | none => exact rel_refl R _ _
    | some w =>
      have e := rel_context R hc k w []
      cases z <;> cases t <;> simpa [context, mulRaw] using e

def cls (T : W) (x : Raw α) : Q R T := Quotient.mk _ x

def mul {T : W} (hc : Cap R.r T) (x y : Q R T) : Q R T :=
  Quotient.liftOn₂ x y (fun a b => cls R T (mulRaw a b))
    (fun _ _ _ _ h k => Quotient.sound (mul_compat R hc h k))

def zero (T : W) : Q R T := cls R T none
def ofWord (T u : W) : Q R T := cls R T (some u)

theorem mul_assoc {T : W} (hc : Cap R.r T) (x y z : Q R T) :
    mul R hc (mul R hc x y) z = mul R hc x (mul R hc y z) := by
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      induction z using Quotient.inductionOn with | _ c =>
        change cls R T (mulRaw (mulRaw a b) c) = cls R T (mulRaw a (mulRaw b c))
        apply congrArg (cls R T)
        cases a <;> cases b <;> cases c <;> simp [mulRaw, List.append_assoc]

theorem unit_laws {T : W} (hc : Cap R.r T) (q : Q R T) :
    mul R hc (ofWord R T []) q = q ∧ mul R hc q (ofWord R T []) = q := by
  induction q using Quotient.inductionOn with | _ a =>
    change cls R T (mulRaw (some []) a) = cls R T a ∧ cls R T (mulRaw a (some [])) = cls R T a
    cases a <;> simp [mulRaw]

theorem absorbing {T : W} (hc : Cap R.r T) (q : Q R T) :
    mul R hc (zero R T) q = zero R T ∧ mul R hc q (zero R T) = zero R T := by
  induction q using Quotient.inductionOn with | _ a =>
    cases a <;> exact ⟨rfl,rfl⟩

theorem nonzero_iff {T u : W} : ofWord R T u ≠ zero R T ↔ Good R T u := by
  constructor
  · intro h
    by_cases good : Good R T u
    · exact good
    · exact (h (Quotient.sound (Or.inl ⟨good,id⟩ : Rel R T (some u) none))).elim
  · intro good eq
    have e : Rel R T (some u) none := Quotient.exact eq
    rcases e with ⟨bad,_⟩ | ⟨_,_,_,e,_,_,_⟩
    · exact bad good
    · contradiction

theorem good_empty (T : W) : Good R T [] :=
  ⟨T,.refl T,T,[],by simp⟩

theorem same_nonzero_class {T u v : W} (g : Good R T u) :
    ofWord R T u = ofWord R T v ↔ Good R T v ∧ Walk R.step u v := by
  constructor
  · intro e
    have h : Rel R T (some u) (some v) := Quotient.exact e
    rcases h with ⟨bad,_⟩ | ⟨_,_,ea,eb,_,gv,path⟩
    · exact (bad g).elim
    · cases ea
      cases eb
      exact ⟨gv,path⟩
  · rintro ⟨gv,path⟩
    exact Quotient.sound (Or.inr ⟨u,v,rfl,rfl,g,gv,path⟩ : Rel R T (some u) (some v))

theorem unit_rep_unique (T u : W) : ofWord R T u = ofWord R T [] ↔ u = [] := by
  constructor
  · intro eq
    have path := ((same_nonzero_class R (good_empty R T)).mp eq.symm).2
    exact (List.Perm.nil_eq (List.perm_iff_count.mpr (count_walk R path))).symm
  · rintro rfl; rfl

theorem nonzero_representative {T : W} (q : Q R T) (nz : q ≠ zero R T) :
    ∃ u, Good R T u ∧ ofWord R T u = q := by
  induction q using Quotient.inductionOn with | _ a =>
    cases a with
    | none => exact (nz rfl).elim
    | some u => exact ⟨u,(nonzero_iff R).mp nz,rfl⟩

def eval {T : W} (hc : Cap R.r T) (a : β → Q R T) : List β → Q R T
  | [] => ofWord R T []
  | x :: xs => mul R hc (a x) (eval hc a xs)

theorem eval_rep {T : W} (hc : Cap R.r T) (a : β → Q R T)
    (v : List β) (h : β → Word α) (reps : ∀ x ∈ v, ofWord R T (h x) = a x) :
    eval R hc a v = ofWord R T (v.flatMap h) := by
  induction v with
  | nil => rfl
  | cons x xs ih =>
    rw [eval, ← reps x (by simp), ih (fun y hy => reps y (by simp [hy]))]
    rfl

theorem arbitrary_representatives {T : W} (hc : Cap R.r T) (a : β → Q R T)
    (v : List β) (h : β → Word α) (reps : ∀ x ∈ v, ofWord R T (h x) = a x) :
    eval R hc a v ≠ zero R T ↔
    ∃ variant l t, Variant R T variant ∧ variant = l ++ v.flatMap h ++ t := by
  rw [eval_rep R hc a v h reps, nonzero_iff]
  constructor
  · rintro ⟨z,path,l,t,e⟩; exact ⟨z,l,t,path,e⟩
  · rintro ⟨z,l,t,path,e⟩; exact ⟨z,path,l,t,e⟩

theorem live_inputs {T : W} (hc : Cap R.r T) (a : β → Q R T)
    (v : List β) (nz : eval R hc a v ≠ zero R T) : ∀ x ∈ v, a x ≠ zero R T := by
  induction v with
  | nil => simp
  | cons y ys ih =>
    have yn : a y ≠ zero R T := fun h => nz (by rw [eval,h,(absorbing R hc _).1])
    have ns : eval R hc a ys ≠ zero R T := fun h => nz (by rw [eval,h,(absorbing R hc _).2])
    intro x hx
    rcases List.mem_cons.mp hx with e | hx
    · exact e ▸ yn
    · exact ih ns x hx

/-- For a fixed certificate, only preservation under ONE literal template move
    still has to be discharged. The certificate is read in the enclosing variant. -/
theorem designated {T : W} (hc : Cap R.r T) (a : β → Q R T) (v : List β)
    (h : β → Word α) (reps : ∀ x ∈ v, ofWord R T (h x) = a x)
    (nz : eval R hc a v ≠ zero R T) (P : Word α → Prop)
    (initial : P T) (one : ∀ {x y}, R.step x y → P x → P y) :
    ∃ variant l t, Variant R T variant ∧ variant = l ++ v.flatMap h ++ t ∧ P variant := by
  obtain ⟨z,l,t,path,eq⟩ := (arbitrary_representatives R hc a v h reps).mp nz
  exact ⟨z,l,t,path,eq,path.transport initial one⟩
end
end P455Quotient
