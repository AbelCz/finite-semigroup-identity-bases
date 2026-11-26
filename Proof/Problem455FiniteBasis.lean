import Problem455FiniteModel
import Problem455PrefixBlocks

/- Conversion from bounded equational rank to a finite ordinary semigroup
   basis. Rule terms and every substitution term are nonempty. -/
namespace P455FiniteBasis
open P455FirstRewrite P455FiniteModel
abbrev W := List Nat
def Limited (k : Nat) (w : W) := ∀ x∈w, x<k
def Basis {S : Type} (M : Model S) (rules : List (W × W)) :=
  (∀ u v, (u,v)∈rules → u≠[] ∧ v≠[] ∧ M.Valid u v) ∧
  ∀ u v, u≠[] → v≠[] → M.Valid u v → Derives (fun u v => (u,v)∈rules) u v

private theorem agree {S : Type} (M : Model S) (w : W) (f g : Nat → S)
    (h : ∀ x∈w, f x=g x) : M.eval f w=M.eval g w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [Model.eval,h a List.mem_cons_self,ih (fun x m => h x (List.mem_cons_of_mem a m))]

def table {S : Type} (M : Model S) (k : Nat) (w : W) (v : Fin k → S) :=
  M.eval (fun x => if h : x<k then v ⟨x,h⟩ else M.unit) w

private theorem table_valid {S : Type} (M : Model S) {k u v}
    (lu : Limited k u) (lv : Limited k v) (eq : table M k u = table M k v) : M.Valid u v := by
  intro f
  let g (i : Fin k) := f i.val
  have read (w : W) (l : Limited k w) : table M k w g=M.eval f w :=
    agree _ _ _ _ (fun x m => by simp [l x m,g])
  exact (read u lu).symm.trans ((congrFun eq g).trans (read v lv))

private theorem representatives {S : Type} (M : Model S) (finite : Covered S) (k : Nat) :
    ∃ xs : List W, (∀ z∈xs, z≠[] ∧ Limited k z) ∧
      ∀ w, w≠[] → Limited k w → ∃ z∈xs, M.Valid w z := by
  classical
  have vals : Covered (Fin k → S) := pi (fin k) (fun _ => finite) (fun _ => M.unit)
  obtain ⟨ts,cover⟩ := pi vals (fun _ => finite) (fun _ => M.unit)
  let realized (t : (Fin k → S) → S) := ∃ w : W, w≠[] ∧ Limited k w ∧ table M k w=t
  let pick (t : (Fin k → S) → S) := if h : realized t then [Classical.choose h] else []
  refine ⟨ts.flatMap pick,?_,?_⟩
  · intro z m
    obtain ⟨t,_,hit⟩ := List.mem_flatMap.mp m
    by_cases h : realized t
    · obtain rfl : z=Classical.choose h := by simpa [pick,h] using hit
      exact ⟨(Classical.choose_spec h).1,(Classical.choose_spec h).2.1⟩
    · simp [pick,h] at hit
  · intro w ne lim
    let t := table M k w
    have h : realized t := ⟨w,ne,lim,rfl⟩
    obtain ⟨_,lz,ez⟩ := Classical.choose_spec h
    exact ⟨Classical.choose h,List.mem_flatMap.mpr ⟨t,cover t,by simp [pick,h]⟩,
      table_valid M lim lz ez.symm⟩

private theorem use_rule {rules : List (W×W)} {u v : W} (m : (u,v)∈rules) (a : u≠[]) (b : v≠[]) :
    Step (fun p q => (p,q)∈rules) u v :=
  ⟨u,v,[],[],fun i => [i],.inl m,a,b,by simp,by simp,by simp⟩

/-- A single finite list proves every valid identity on the first k names. -/
theorem finite_fragment {S : Type} (M : Model S) (finite : Covered S) (k : Nat) :
    ∃ rules : List (W×W), (∀ u v, (u,v)∈rules → u≠[] ∧ v≠[] ∧ M.Valid u v) ∧
      ∀ u v, u≠[] → v≠[] → Limited k u → Limited k v → M.Valid u v →
        Derives (fun a b => (a,b)∈rules) u v := by
  classical
  obtain ⟨reps,formed,rep⟩ := representatives M finite k
  let left := (List.range k).flatMap (fun x => ([]::reps).map (List.cons x))
  let raw := left.flatMap (fun w => reps.map (fun z => (w,z)))
  let rules := raw.filter (fun p => decide (p.1≠[] ∧ p.2≠[] ∧ M.Valid p.1 p.2))
  have ready (x : Nat) (lt : x<k) (q z : W) (part : q∈[]::reps) (inR : z∈reps)
      (idn : M.Valid (x::q) z) : Step (fun a b => (a,b)∈rules) (x::q) z := by
    have ne := (formed _ inR).1
    apply use_rule _ (by simp) ne
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨x::q,?_,List.mem_map.mpr ⟨z,inR,rfl⟩⟩,?_⟩
    · exact List.mem_flatMap.mpr ⟨x,List.mem_range.mpr lt,List.mem_map_of_mem part⟩
    · simpa using And.intro ne idn
  have norm (w : W) (ne : w≠[]) (lim : Limited k w) : ∀ z∈reps, M.Valid w z →
      Derives (fun a b => (a,b)∈rules) w z := by
    induction w with
    | nil => contradiction
    | cons x xs ih =>
      intro z inR idn
      have lt := lim _ List.mem_cons_self
      by_cases empty : xs=[]
      · subst xs; exact .snoc (.refl _) (ready _ lt [] z List.mem_cons_self inR idn)
      have tail : Limited k xs := fun j m => lim j (List.mem_cons_of_mem x m)
      obtain ⟨q,m,valid⟩ := rep xs empty tail
      have chain := P455Prefix.context_derives [x] [] (ih empty tail q m valid)
      have last : M.Valid (x::q) z := fun f =>
        (congrArg (M.op (f x)) (valid f).symm).trans (idn f)
      exact .snoc (by simpa using chain) (ready _ lt q z (List.mem_cons_of_mem _ m) inR last)
  refine ⟨rules,fun u v m => (of_decide_eq_true (List.mem_filter.mp m).2),?_⟩
  intro u v un vn lu lv idn
  obtain ⟨z,zr,correct⟩ := rep u un lu
  have U := norm u un lu z zr correct
  have V := norm v vn lv z zr (fun f => (idn f).symm.trans (correct f))
  exact U.trans (V.symm (fun step => P455ReductionBoundary.sym_step step))

private theorem map_eval {S : Type} (M : Model S) (d : Nat → Nat) (w : W) (f : Nat → S) :
    M.eval f (w.map d) = M.eval (fun a => f (d a)) w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [Model.eval,ih]

theorem finite_rank {S : Type} (M : Model S) (finite : Covered S) (k : Nat) :
    ∃ rules : List (W×W), (∀ u v, (u,v)∈rules → u≠[] ∧ v≠[] ∧ M.Valid u v) ∧
      ∀ u v, u≠[] → v≠[] → rank u v≤k → M.Valid u v →
        Derives (fun a b => (a,b)∈rules) u v := by
  obtain ⟨rules,ok,proof⟩ := finite_fragment M finite k
  refine ⟨rules,ok,?_⟩
  intro u v un vn rk idn
  let keep := names (u++v)
  have ku : ∀ x∈u, x∈keep := fun x h => by simp [keep,h]
  have kv : ∀ x∈v, x∈keep := fun x h => by simp [keep,h]
  have lim (w : W) (sur : ∀ x∈w,x∈keep) : Limited k (w.map keep.idxOf) := by
    intro z mz; obtain ⟨x,m,rfl⟩ := List.mem_map.mp mz
    exact Nat.lt_of_lt_of_le (List.idxOf_lt_length (sur x m)) rk
  have small := proof (u.map keep.idxOf) (v.map keep.idxOf) (by simpa using un) (by simpa using vn)
    (lim u ku) (lim v kv) (fun f => (map_eval M _ _ _).trans ((idn _).trans (map_eval M _ _ _).symm))
  let sub (i : Nat) := [P455DefectRename.decode keep i]
  have restored := P455Prefix.substitute_deduction sub (by simp [sub]) small
  have flat (w : W) : w.flatMap sub = w.map (P455DefectRename.decode keep) := by
    induction w with
    | nil => rfl
    | cons x w ih => simp [List.flatMap_cons,sub] at *; exact ih
  simpa only [flat,P455DefectRename.decode_map ku,P455DefectRename.decode_map kv] using restored

/-- A uniform bound on rank in ordinary semigroup deductions yields a
    finite basis; its converse is valid for every model. -/
theorem finite_of_uniform {S : Type} (M : Model S) (finite : Covered S) (k : Nat)
    (uniform : ∀ u v, u≠[] → v≠[] → M.Valid u v →
      Derives (fun a b => M.Valid a b ∧ rank a b≤k) u v) : ∃ rules, Basis M rules := by
  obtain ⟨rules,ok,all⟩ := finite_rank M finite k
  refine ⟨rules,ok,?_⟩
  intro u v un vn idn
  have path := uniform u v un vn idn
  induction path with
  | refl => exact .refl _
  | @snoc v w prev step ih =>
    obtain ⟨a,b,l,t,h,rule,an,bn,non,rfl,rfl⟩ := step
    have rule' : M.Valid a b ∧ rank a b≤k := by
      rcases rule with fw|rev
      · exact fw
      · exact ⟨fun f => (rev.1 f).symm,(rank_swap b a).symm ▸ rev.2⟩
    have localProof := all a b an bn rule'.2 rule'.1
    have localStep := P455Prefix.context_derives l t (P455Prefix.substitute_deduction h non localProof)
    have prior := M.derives_sound (fun a b (r : M.Valid a b ∧ rank a b≤k) => r.1) prev
    have startN : l++a.flatMap h++t≠[] := by
      intro e
      have flat : a.flatMap h=[] := by simpa using (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1).2
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ an
      exact non x ((List.flatMap_eq_nil_iff.mp flat) x hx)
    exact (ih startN prior).trans localStep

end P455FiniteBasis
