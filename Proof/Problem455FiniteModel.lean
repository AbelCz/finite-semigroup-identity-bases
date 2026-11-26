import Problem455FullSingleton





namespace P455FiniteModel
open P455FirstRewrite

def Covered (α : Type) := ∃ xs : List α, ∀ a, a ∈ xs

theorem from_codes {α β : Type} (f : α → β) (inj : ∀ a b, f a=f b → a=b)
    (xs : List β) (all : ∀ a, f a∈xs) : Covered α := by
  classical
  let pick (b : β) := if h : ∃ a, f a=b then [Classical.choose h] else []
  refine ⟨xs.flatMap pick,fun a => List.mem_flatMap.mpr ⟨f a,all a,?_⟩⟩
  have h : ∃ z, f z=f a := ⟨a,rfl⟩
  simp [pick,h,inj _ _ (Classical.choose_spec h)]

theorem fin (n : Nat) : Covered (Fin n) :=
  ⟨List.finRange n,fun a => by
    have h : a.val<(List.finRange n).length := by simp
    simpa using (List.getElem_mem (l := List.finRange n) h)⟩
theorem bool : Covered Bool := ⟨[false,true],fun b => by cases b <;> simp⟩

theorem sigma {ι : Type} {F : ι → Type} (base : Covered ι) (each : ∀ i, Covered (F i)) :
    Covered (Sigma F) := by
  obtain ⟨indices,all⟩ := base
  let vals (i) := Classical.choose (each i)
  refine ⟨indices.flatMap (fun i => (vals i).map (Sigma.mk i)),?_⟩
  rintro ⟨i,x⟩
  exact List.mem_flatMap.mpr ⟨i,all i,List.mem_map.mpr ⟨x,Classical.choose_spec (each i) x,rfl⟩⟩

theorem prod {α β : Type} (a : Covered α) (b : Covered β) : Covered (α×β) := by
  obtain ⟨xs,h⟩ := a; obtain ⟨ys,k⟩ := b
  exact ⟨xs.flatMap (fun x => ys.map (fun y => (x,y))),fun (x,y) =>
    List.mem_flatMap.mpr ⟨x,h x,List.mem_map.mpr ⟨y,k y,rfl⟩⟩⟩

theorem pi {ι : Type} {F : ι → Type} (base : Covered ι) (each : ∀ i, Covered (F i))
    (zero : ∀ i,F i) : Covered ((i : ι) → F i) := by
  classical
  obtain ⟨indices,all⟩ := base
  let set (f : (i : ι) → F i) (j : ι) (v : F j) := fun i : ι => if e : j=i then e ▸ v else f i
  have build (xs : List ι) : ∃ vs : List ((i : ι) → F i), ∀ f : (i : ι) → F i,
      ∃ g∈vs, ∀ i∈xs, g i=f i := by
    induction xs with
    | nil => exact ⟨[zero],fun _ => ⟨zero,by simp,by simp⟩⟩
    | cons j xs ih =>
      obtain ⟨gs,good⟩ := ih
      obtain ⟨ys,full⟩ := each j
      refine ⟨gs.flatMap (fun g => ys.map (set g j)),?_⟩
      intro f
      obtain ⟨g,mg,match'⟩ := good f
      refine ⟨set g j (f j),List.mem_flatMap.mpr ⟨g,mg,List.mem_map_of_mem (full _)⟩,?_⟩
      intro i mi
      by_cases e : j=i
      · subst i; simp [set]
      · simpa [set,e] using match' i ((List.mem_cons.mp mi).resolve_left (Ne.symm e))
  obtain ⟨gs,h⟩ := build indices
  refine ⟨gs,?_⟩; intro f
  obtain ⟨g,mg,agree⟩ := h f
  exact (funext (fun i => agree i (all i))) ▸ mg

theorem from_covered {α β : Type} (code : α → β) (inj : ∀ a b, code a=code b → a=b)
    (cov : Covered β) : Covered α := by
  obtain ⟨xs,h⟩ := cov
  exact from_codes code inj xs (fun _ => h _)

private theorem coordinate {ι : Type} (inds : Covered ι) (rs : ι → P455Quotient.Rules Nat)
    (ts : ι → List Nat) : Covered ((i : ι) → P455Quotient.Q (rs i) (ts i)) :=
  pi inds (fun i => ⟨_,Problem455Finite.carrier_complete (rs i) (ts i)⟩)
    (fun i => P455Quotient.zero (rs i) (ts i))

theorem primitive (r : Nat) : Covered (P455FirstTesters.Carrier r) :=
  coordinate (from_codes Subtype.val (fun _ _ => Subtype.ext) _ P455FirstTesters.index_covered) _ _

theorem binary (r allow) : Covered (P455BinaryProduct.Carrier r allow) := by
  apply coordinate (from_covered (fun i : P455BinaryProduct.Index r allow => (i.num,i.prof)) _ (prod (fin _) bool))
  intro i j; cases i; cases j; simp

theorem structural (r allow) : Covered (P455StructuralProduct.Carrier r allow) := by
  apply coordinate (from_covered (fun i : P455StructuralProduct.Index r allow => i.pos) _ (fin _))
  intro i j; cases i; cases j; simp

private abbrev GCode (r : Nat) := (k : Bool) ×
  (Fin (P455GuardProduct.words r k).length × Fin (P455GuardProduct.width k) × Fin (P455GuardProduct.width k))

theorem guard (r allow ts) : Covered (P455GuardProduct.Carrier r allow ts) := by
  let f (i : P455GuardProduct.Index r allow ts) : GCode r := ⟨i.kind,i.pos,i.a,i.b⟩
  apply coordinate (from_covered f _ (sigma bool (fun _ => prod (fin _) (prod (fin _) (fin _)))))
  intro i j eq
  cases i with
  | mk k i a b cp ok =>
    cases j with
    | mk m j c d cq oq =>
      obtain km : k=m := congrArg Sigma.fst eq
      subst m
      have e : (i,a,b)=(j,c,d) := eq_of_heq (Sigma.mk.inj eq).2
      simpa using e

theorem edge (r allow ts) : Covered (P455EdgeProduct.Carrier r allow ts) := by
  apply coordinate (from_covered
    (fun i : P455EdgeProduct.Index r allow ts => (i.num,i.a,i.b,i.c,i.d)) _
    (prod (fin _) (prod (fin _) (prod (fin _) (prod (fin _) (fin _))))))
  intro i j; cases i; cases j; simp

/-- An actual finite cover for the very type underlying the monoid used
    in both rank directions. No computability of a Prop-valued tile
    predicate is asserted by this classical cover. -/
theorem fixed_product (r allow ts) :
    Covered (P455FirstTesters.Carrier r ×
      ((P455GuardProduct.Carrier r allow ts × P455EdgeProduct.Carrier r allow ts) ×
       (P455BinaryProduct.Carrier r allow × P455StructuralProduct.Carrier r allow))) :=
  prod (primitive r) (prod (prod (guard ..) (edge ..)) (prod (binary ..) (structural ..)))

end P455FiniteModel
