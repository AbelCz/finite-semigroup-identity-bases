import Problem455FirstRewrite
import Problem455Finite



namespace P455FirstTesters
open P455FirstRewrite P455Quotient

def plain (r : Nat) : Rules Nat where
  r := r
  step := fun _ _ => False
  reverse := False.elim
  counts := False.elim
  extend := False.elim

def power (r : Nat) : W := List.replicate r 0

def Binary (r : Nat) (T : W) := (∀ x ∈ T, x = 0 ∨ x = 1) ∧
  Cap r T ∧ 0 < T.count 0 ∧ 0 < T.count 1 ∧ (T.count 0 < r ∨ T.count 1 < r)

abbrev Index (r : Nat) := { T : W // T = power r ∨ Binary r T }
def Index.cap {r : Nat} (i : Index r) : Cap (plain r).r i.val := by
  rcases i.property with e | b
  · intro x; rw [e,power,List.count_replicate]; split <;> simp [plain]
  · exact b.2.1

private theorem binary_length {T : W} (letters : ∀ x ∈ T, x = 0 ∨ x = 1) :
    T.length = T.count 0 + T.count 1 := by
  induction T with
  | nil => rfl
  | cons x t ih =>
    have tail := ih (fun y m => letters y (List.mem_cons_of_mem _ m))
    rcases letters x List.mem_cons_self with rfl | rfl <;> simp [List.count_cons] <;> omega

theorem index_covered {r : Nat} (i : Index r) : i.val ∈ Problem455Finite.wordsUpTo [0, 1] (2*r) := by
  apply Problem455Finite.covered
  · rcases i.property with e | b
    · rw [e,power,List.length_replicate]; omega
    · have cnt := binary_length b.1
      have l := b.2.1 0
      have h := b.2.1 1
      omega
  · intro x m
    rcases i.property with e | b
    · rw [e] at m; have := List.eq_of_mem_replicate m; simp_all [power]
    · simpa using b.1 x m

abbrev Carrier (r : Nat) := (i : Index r) → Q (plain r) i.val

def product (r : Nat) : Model (Carrier r) where
  op := fun x y i => mul (plain r) i.cap (x i) (y i)
  unit := fun i => ofWord (plain r) i.val []
  assoc := fun x y z => funext (fun i => mul_assoc (plain r) i.cap (x i) (y i) (z i))
  oneL := fun x => funext (fun i => (unit_laws (plain r) i.cap (x i)).1)
  oneR := fun x => funext (fun i => (unit_laws (plain r) i.cap (x i)).2)

theorem observed {r u v} (h : (product r).Valid u v) (i : Index r) (f : Sub) :
    ofWord (plain r) i.val (u.flatMap f) = ofWord (plain r) i.val (v.flatMap f) := by
  let val : Nat → Carrier r := fun x j => ofWord (plain r) j.val (f x)
  have comp (w : W) : (product r).eval val w i = ofWord (plain r) i.val (w.flatMap f) := by
    induction w with
    | nil => rfl
    | cons x xs ih =>
      change mul (plain r) i.cap (ofWord (plain r) i.val (f x)) ((product r).eval val xs i) = _
      rw [ih]; rfl
  exact (comp u).symm.trans ((congrFun (h val) i).trans (comp v))

private theorem reflect {r : Nat} {T A B : W} (factor : Factor A T)
    (eq : ofWord (plain r) T A = ofWord (plain r) T B) : A = B := by
  have good : Good (plain r) T A := ⟨T,.refl T,factor⟩
  have path := ((same_nonzero_class (plain r) good).mp eq).2
  induction path with
  | refl => rfl
  | snoc _ f _ => exact False.elim f

def unaryImage (x z : Nat) : W := if z = x then [0] else []
private theorem unary_word (x : Nat) (w : W) :
    w.flatMap (unaryImage x) = power (w.count x) := by
  induction w with
  | nil => rfl
  | cons z t ih =>
    by_cases e : z = x <;> simp [List.flatMap_cons,unaryImage,e,List.count_cons,ih,power,
      List.replicate_succ]

private theorem small_count {r u v} (h : (product r).Valid u v) {x : Nat} (bd : u.count x ≤ r) :
    u.count x = v.count x := by
  let i : Index r := ⟨power r,Or.inl rfl⟩
  have eq := observed h i (unaryImage x)
  simp only [unary_word] at eq
  have fac : Factor (power (u.count x)) (power r) := by
    refine ⟨[], power (r-u.count x), ?_⟩
    simp only [List.nil_append,power,List.replicate_append_replicate]
    congr 1; omega
  simpa [power] using congrArg List.length (reflect fac eq)

def code (i j x : Nat) : W := if x = i then [0] else if x = j then [1] else []
private theorem code_letters (i j : Nat) (w : W) (x : Nat) (m : x ∈ w.flatMap (code i j)) :
    x = 0 ∨ x = 1 := by
  obtain ⟨y,_,m⟩ := List.mem_flatMap.mp m
  unfold code at m
  split at m
  · exact Or.inl (List.mem_singleton.mp m)
  · split at m
    · exact Or.inr (List.mem_singleton.mp m)
    · simp at m

private theorem code_counts (i j : Nat) (ne : i ≠ j) (w : W) :
    (w.flatMap (code i j)).count 0 = w.count i ∧ (w.flatMap (code i j)).count 1 = w.count j := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    by_cases xi : x=i <;> by_cases xj : x=j <;>
      simp_all [List.flatMap_cons,code,List.count_cons]

private theorem decode (i j : Nat) (w : W) :
    (w.flatMap (code i j)).map (fun z => if z = 0 then i else j) = proj i j w := by
  induction w with
  | nil => rfl
  | cons x t ih =>
    by_cases e : x=i <;> by_cases f : x=j <;> simp_all [List.flatMap_cons,code,proj]

private theorem only_one {i j : Nat} (u : W) (miss : j ∉ u) :
    proj i j u = List.replicate (u.count i) i := by
  induction u with
  | nil => rfl
  | cons x t ih =>
    have nx : x ≠ j := fun e => miss (e ▸ List.mem_cons_self)
    have tail := ih (fun m => miss (List.mem_cons_of_mem x m))
    by_cases xi : x=i <;> simp_all [proj,List.count_cons,List.replicate_succ]

private theorem proj_swap (i j : Nat) (w : W) : proj i j w = proj j i w := by
  simp only [proj,Or.comm]

private theorem identical_letter (i : Nat) (w : W) :
    proj i i w = List.replicate (w.count i) i := by
  induction w with
  | nil => rfl
  | cons z t ih => by_cases eq : z = i <;> simp_all [proj,List.count_cons,List.replicate_succ]

/-- Every identity in this fixed finite tester product satisfies the actual
clipped unary and binary restrictions used by the first-change proof. -/
theorem tester_rule {r u v} (h : (product r).Valid u v) : TesterRule r u v := by
  have clipped (x) : min (u.count x) (r+1) = min (v.count x) (r+1) := by
    by_cases a : u.count x ≤ r
    · rw [small_count h a]
    · by_cases b : v.count x ≤ r
      · rw [small_count (fun f => (h f).symm) b]
      · omega
  refine ⟨clipped,?_⟩
  intro cu cv i j diff
  have counts (x) : u.count x = v.count x := by have := clipped x; have := cu x; omega
  have ne : i ≠ j := by
    intro e; subst j; apply diff; rw [identical_letter, identical_letter, counts]
  have positive (a b) (d : proj a b u ≠ proj a b v) : 0 < u.count b := by
    apply Nat.pos_of_ne_zero; intro zero; apply d
    have zv : v.count b = 0 := (counts b).symm.trans zero
    rw [only_one u (List.count_eq_zero.mp zero),only_one v (List.count_eq_zero.mp zv),counts]
  have pj := positive i j diff
  have pi := positive j i (by simpa only [proj_swap j i] using diff)
  apply Classical.byContradiction
  intro fail
  have low : u.count i < r ∨ u.count j < r := by
    have := cu i; have := cu j; omega
  let T := u.flatMap (code i j)
  obtain ⟨c0,c1⟩ := code_counts i j ne u
  have letters := code_letters i j u
  have cap : Cap r T := by
    intro x
    by_cases mem : x ∈ T
    · rcases letters x mem with rfl | rfl
      · exact c0 ▸ cu i
      · exact c1 ▸ cu j
    · rw [List.count_eq_zero_of_not_mem mem]; omega
  let ix : Index r := ⟨T,Or.inr ⟨letters,cap,c0 ▸ pi,c1 ▸ pj,by simpa only [T,c0,c1] using low⟩⟩
  have eq := observed h ix (code i j)
  have fac : Factor T T := ⟨[],[],by simp⟩
  have ee := reflect fac eq
  dsimp [T] at ee
  apply diff
  rw [← decode i j u,← decode i j v,ee]

/-- Extra components of the final direct product are arbitrary. Including the
unmarked testers forces their consequences for every valid multiplication identity. -/
def combine {A B : Type} (M : Model A) (N : Model B) : Model (A × B) where
  op := fun x y => (M.op x.1 y.1,N.op x.2 y.2)
  unit := (M.unit,N.unit)
  assoc := fun _ _ _ => Prod.ext (M.assoc ..) (N.assoc ..)
  oneL := fun _ => Prod.ext (M.oneL _) (N.oneL _)
  oneR := fun _ => Prod.ext (M.oneR _) (N.oneR _)

theorem valid_left {A B : Type} (M : Model A) (N : Model B) {u v}
    (h : (combine M N).Valid u v) : M.Valid u v := by
  intro f
  let g := fun x => (f x,N.unit)
  have fst (w : W) : ((combine M N).eval g w).1 = M.eval f w := by
    induction w with
    | nil => rfl
    | cons x t ih => exact congrArg (M.op (f x)) ih
  exact (fst u).symm.trans ((congrArg Prod.fst (h g)).trans (fst v))

theorem first_change_no_finite_basis {A : Type} (N : Model A) (r : Nat) (hr : 0 < r)
    (witnesses : ∀ k, ∃ U V D, RankWitness (combine (product r) N) r U V D ∧ k < D.length)
    (G : List (W × W)) (valid : ∀ u v, (u,v) ∈ G → (combine (product r) N).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (combine (product r) N).Valid U V ∧
      ¬ Derives (fun u v => (u,v) ∈ G) U V :=
  no_finite_basis_of_witnesses _ r hr (fun _ _ h => tester_rule (valid_left _ _ h))
    witnesses G valid

end P455FirstTesters
