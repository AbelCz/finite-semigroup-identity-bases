import Problem455NumericProduct

/- First-order assembly of all raw coordinate tables. The mathematical
   product retains one coordinate per original index. -/
namespace P455IndexedProduct
open P455Table P455NumericProduct P455FirstRewrite P455FirstTesters

theorem transport {A B : Type} {M : Model A} {N : Model B} {T : Matrix}
    (present : Represents T M) (f : A → B)
    (inj : ∀ x y, f x=f y → x=y) (surj : ∀ y, ∃ x, f x=y)
    (unit : f M.unit=N.unit) (mul : ∀ x y, f (M.op x y)=N.op (f x) (f y)) : Represents T N := by
  obtain ⟨X,rfl,⟨p⟩⟩ := present
  exact ⟨X,rfl,⟨⟨fun i => f (p.decode i),fun i j eq => p.inj i j (inj _ _ eq),by
    intro y; obtain ⟨x,rfl⟩ := surj y; obtain ⟨i,e⟩ := p.surj x; exact ⟨i,congrArg f e⟩,
    (congrArg f p.one_eq).trans unit,fun i j => (congrArg f (p.mul_eq i j)).trans (mul _ _)⟩⟩⟩

abbrev Sections {I : Type} (F : I → Type) (s : List I) := (i : I) → i∈s → F i

def restricted {I : Type} {F : I → Type} (models : (i:I) → Model (F i)) (s : List I) : Model (Sections F s) where
  op a b i h := (models i).op (a i h) (b i h)
  unit i _ := (models i).unit
  assoc _ _ _ := funext (fun i => funext fun _ => (models i).assoc ..)
  oneL _ := funext fun i => funext fun _ => (models i).oneL _
  oneR _ := funext fun i => funext fun _ => (models i).oneR _

def full {I : Type} {F : I → Type} (models : (i : I) → Model (F i)) : Model ((i : I) → F i) where
  op f g i := (models i).op (f i) (g i)
  unit i := (models i).unit
  assoc _ _ _ := funext fun i => (models i).assoc ..
  oneL _ := funext fun i => (models i).oneL _
  oneR _ := funext fun i => (models i).oneR _

def glue {I : Type} [DecidableEq I] {F : I → Type} (j : I) (s : List I) (v : F j × Sections F s) :
    Sections F (j::s) := fun i h =>
  if eq : j=i then eq ▸ v.1 else v.2 i ((List.mem_cons.mp h).resolve_left (Ne.symm eq))

private theorem glue_inj {I : Type} [DecidableEq I] {F : I → Type} (j : I) (s : List I) (fresh : j∉s)
    (u v : F j × Sections F s) (e : glue j s u=glue j s v) : u=v := by
  apply Prod.ext
  · simpa [glue] using congrArg (fun f : Sections F (j::s) => f j List.mem_cons_self) e
  · funext i h
    have diff : j≠i := fun eq => fresh (eq ▸ h)
    simpa [glue,diff] using congrArg (fun f : Sections F (j::s) => f i (List.mem_cons_of_mem _ h)) e

private theorem glue_surj {I : Type} [DecidableEq I] {F : I → Type} (j : I) (s : List I)
    (v : Sections F (j::s)) : ∃ u, glue j s u=v := by
  refine ⟨(v j List.mem_cons_self,fun i h => v i (List.mem_cons_of_mem _ h)),?_⟩
  funext i h
  by_cases eq : j=i
  · subst i; simp [glue]
  · simp [glue,eq]

theorem partial_product {I : Type} [DecidableEq I] {F : I → Type} (models : (i : I) → Model (F i))
    (raw : I → Matrix) (ok : ∀ i, Represents (raw i) (models i))
    (s : List I) (nd : s.Nodup) : Represents (assemble (s.map raw)) (restricted models s) := by
  induction s with
  | nil =>
    let send (_ : Unit) : Sections F [] := fun _ h => nomatch h
    apply transport (M:=unitModel) (f:=send) ⟨unitOps,rfl,⟨unitPresents⟩⟩
    · intro _ _ _; rfl
    · intro y; exact ⟨(),funext fun _ => funext fun h => nomatch h⟩
    · exact funext fun _ => funext fun h => nomatch h
    · intro _ _; exact funext fun _ => funext fun h => nomatch h
  | cons j s ih =>
    have info := List.nodup_cons.mp nd
    apply transport (represents_tensor (ok j) (ih info.2)) (glue j s)
      (glue_inj j s info.1) (glue_surj j s)
    · funext i h
      by_cases eq : j=i
      · subst i; simp [glue,combine,restricted]
      · simp [glue,eq,combine,restricted]
    · intro u v; funext i h
      by_cases eq : j=i
      · subst i; simp [glue,combine,restricted]
      · simp [glue,eq,combine,restricted]

theorem complete_product {I : Type} [DecidableEq I] {F : I → Type} (models : (i : I) → Model (F i))
    (raw : I → Matrix) (ok : ∀ i, Represents (raw i) (models i)) (s : List I)
    (nd : s.Nodup) (all : ∀ i, i∈s) :
    Represents (assemble (s.map raw)) (full models) := by
  apply transport (partial_product models raw ok s nd) (fun f i => f i (all i))
  · intro f g eq; exact funext fun i => funext fun _ => congrFun eq i
  · intro g; exact ⟨fun i _ => g i,rfl⟩
  · rfl
  · intro _ _; rfl

end P455IndexedProduct
