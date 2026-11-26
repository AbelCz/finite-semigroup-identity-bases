import Problem455PrefixNormalize
import Problem455ReductionBoundary



namespace P455Prefix
open P455FirstRewrite P455FirstTesters P455Quotient

def highNames (r : Nat) (u : Word) := (names u).filter (fun x => decide (r < u.count x))
def headPowers (r : Nat) (xs : Word) := xs.flatMap (List.replicate (r+1))
def residual (xs u : Word) := u.filter (fun a => decide (a ∉ xs))

@[simp] theorem mem_high (r x : Nat) (u : Word) : x ∈ highNames r u ↔ r < u.count x := by
  simp only [highNames,List.mem_filter,mem_names,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨List.count_pos_iff.mp (by omega),h⟩⟩

@[simp] theorem residual_count (xs u : Word) (a : Nat) :
    (residual xs u).count a = if a ∈ xs then 0 else u.count a := by
  by_cases h : a ∈ xs
  · rw [if_pos h]; exact List.count_eq_zero.mpr (fun m => by simp [residual,h] at m)
  · simp [residual,List.count_filter,h]

private theorem residual_step (x : Nat) (xs u : Word) :
    residual xs (dropName x u) = residual (x::xs) u := by
  simp only [residual,dropName,List.filter_filter]
  apply List.filter_congr
  intro a _
  by_cases e : a = x <;> by_cases m : a ∈ xs <;> simp [e,m]

private theorem handle_names {r allow ts} (xs u : Word) (dis : xs.Nodup)
    (many : ∀ x ∈ xs, r < u.count x) :
    Derives (Steps r allow ts) u (headPowers r xs ++ residual xs u) := by
  induction xs generalizing u with
  | nil =>
    have empty : residual [] u = u := List.filter_eq_self.mpr (by simp)
    simpa only [headPowers,List.flatMap_nil,List.nil_append,empty] using (Walk.refl (s := Step (Steps r allow ts)) u)
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp dis
    have p := gather_deduction (allow := allow) (ts := ts) u (many x List.mem_cons_self)
    have sat (a : Nat) (m : a ∈ xs) : r < (dropName x u).count a := by
      have ne : a ≠ x := fun e => fresh (e ▸ m)
      simpa only [drop_count,if_neg ne] using many a (List.mem_cons_of_mem _ m)
    have tailD := ih (dropName x u) tail sat
    have q := context_derives (List.replicate (r+1) x) [] tailD
    apply p.trans
    simpa only [headPowers,List.flatMap_cons,List.append_assoc,List.append_nil,residual_step,gather] using q

private theorem residual_instance (xs u : Word) :
    u.flatMap (fun a => if a ∈ xs then [] else [a]) = residual xs u := by
  induction u with
  | nil => rfl
  | cons a t ih => by_cases h : a ∈ xs <;> simp [residual,h,ih]

theorem residual_valid {A : Type} (M : Model A) (xs : Word) {u v : Word} (h : M.Valid u v) :
    M.Valid (residual xs u) (residual xs v) := by
  intro f
  rw [← residual_instance,← residual_instance,M.eval_instance,M.eval_instance]
  exact h _

/-- No input beyond validity of the original identity. The high names are
    explicitly computed on its left side and used in the same order on both. -/
theorem arbitrary_prefix {r allow ts} {u v : Word}
    (valid : (P455FullSingleton.model r allow ts).Valid u v) :
    let xs := highNames r u
    let p := headPowers r xs
    let a := residual xs u
    let b := residual xs v
    Derives (Steps r allow ts) u (p ++ a) ∧
    Derives (Steps r allow ts) v (p ++ b) ∧
    Cap r a ∧ Cap r b ∧ (P455FullSingleton.model r allow ts).Valid a b ∧
    (∀ z, a.count z = b.count z) ∧ (a = [] ↔ b = []) := by
  dsimp only
  have power := tester_rule (valid_left _ _ valid)
  let xs := highNames r u
  have high (x : Nat) : r < u.count x ↔ r < v.count x := by
    have := power.unary x; omega
  have distinct : xs.Nodup := (names_distinct u).filter _
  have cA : Cap r (residual xs u) := by
    intro a; rw [residual_count]; by_cases h : a ∈ xs
    · simp [h]
    · have lo : ¬ r < u.count a := fun n => h ((mem_high ..).mpr n)
      simp [h]; omega
  have cB : Cap r (residual xs v) := by
    intro a; rw [residual_count]; by_cases h : a ∈ xs
    · simp [h]
    · have lo : ¬ r < v.count a := fun n => h ((mem_high ..).mpr ((high a).mpr n))
      simp [h]; omega
  have h := residual_valid _ xs valid
  have categories := tester_rule (valid_left _ _ h)
  have count (a : Nat) : (residual xs u).count a = (residual xs v).count a := by
    have := categories.unary a; have := cA a; have := cB a; omega
  refine ⟨handle_names xs u distinct (fun a m => (mem_high ..).mp m),
    handle_names xs v distinct (fun a m => (high a).mp ((mem_high ..).mp m)),
    cA,cB,h,count,?_⟩
  exact ⟨fun e => (List.Perm.nil_eq (e ▸ List.perm_iff_count.mpr count)).symm,
    fun e => (List.Perm.nil_eq (e ▸ (List.perm_iff_count.mpr count).symm)).symm⟩

theorem lift_deduction {G H : Word → Word → Prop} (sub : ∀ a b, G a b → H a b)
    {u v : Word} (p : Derives G u v) : Derives H u v := by
  induction p with
  | refl => exact .refl _
  | snoc _ step ih =>
    obtain ⟨a,b,l,k,f,rule,an,bn,hn,left,right⟩ := step
    exact .snoc ih ⟨a,b,l,k,f,rule.imp (sub a b) (sub b a),an,bn,hn,left,right⟩

/-- Restore the common saturated prefix, inside an ordinary multiplication-only
    deduction, after any bounded derivation of the two capped suffixes. -/
theorem reassemble {r allow ts k} {u v : Word}
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (suffixes : Derives (fun a b => (P455FullSingleton.model r allow ts).Valid a b ∧ rank a b ≤ k)
      (residual (highNames r u) u) (residual (highNames r u) v)) :
    Derives (fun a b => (P455FullSingleton.model r allow ts).Valid a b ∧ rank a b ≤ max k (2*(r+2)+1)) u v := by
  obtain ⟨left,right,_⟩ := arbitrary_prefix valid
  let H : Word → Word → Prop := fun a b => (P455FullSingleton.model r allow ts).Valid a b ∧
    rank a b ≤ max k (2*(r+2)+1)
  have widen (a b) (h : Steps r allow ts a b) : H a b := ⟨h.1,Nat.le_trans h.2 (Nat.le_max_right ..)⟩
  have a := lift_deduction widen left
  have b := lift_deduction widen right
  have middle := context_derives (headPowers r (highNames r u)) []
    (lift_deduction (H := H) (fun _ _ h => ⟨h.1,Nat.le_trans h.2 (Nat.le_max_left ..)⟩) suffixes)
  have backwards := b.symm (fun step => P455ReductionBoundary.sym_step step)
  exact (a.trans (by simpa only [List.append_nil] using middle)).trans backwards

end P455Prefix
