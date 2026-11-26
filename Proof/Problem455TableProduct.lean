import Problem455Table



namespace P455TableProduct
open P455Table P455FirstRewrite

def pair (L : Listing A) (K : Listing B) : Listing (A × B) := by
  letI := L.eq
  letI := K.eq
  exact ⟨inferInstance,L.items.flatMap (fun x => K.items.map (Prod.mk x)),
    fun (x,y) => List.mem_flatMap.mpr ⟨x,L.all x,List.mem_map.mpr ⟨y,K.all y,rfl⟩⟩⟩

def update {I : Type} [DecidableEq I] {F : I → Type} (f : (i : I) → F i) (i : I) (v : F i) :
    (j : I) → F j := fun j => if h : i=j then h ▸ v else f j

def tuples {I : Type} [DecidableEq I] {F : I → Type} (default : (i : I) → F i)
    (L : (i : I) → Listing (F i)) : List I → List ((i : I) → F i)
  | [] => [default]
  | i::xs => (tuples default L xs).flatMap fun f => (L i).items.map (update f i)

theorem tuples_cover {I : Type} [DecidableEq I] {F : I → Type} (default : (i : I) → F i)
    (L : (i : I) → Listing (F i)) (xs : List I) (f : (i : I) → F i) :
    ∃ g∈tuples default L xs, ∀ i∈xs, g i=f i := by
  induction xs with
  | nil => exact ⟨default,by simp [tuples],by simp⟩
  | cons j xs ih =>
    obtain ⟨g,hg,ag⟩ := ih
    refine ⟨update g j (f j),List.mem_flatMap.mpr ⟨g,hg,List.mem_map_of_mem ((L j).all _)⟩,?_⟩
    intro i mem
    by_cases eq : j=i
    · subst i; simp [update]
    · exact (dif_neg eq).trans (ag i ((List.mem_cons.mp mem).resolve_left (Ne.symm eq)))

def family {I : Type} {F : I → Type} (indices : Listing I) (L : (i : I) → Listing (F i))
    (default : (i : I) → F i) : Listing ((i : I) → F i) := by
  letI := indices.eq
  letI (i : I) : DecidableEq (F i) := (L i).eq
  let eq : DecidableEq ((i : I) → F i) := fun f g =>
    if h : ∀ i∈indices.items, f i=g i then
      isTrue (funext fun i => h i (indices.all i))
    else isFalse (fun e => h fun i _ => congrFun e i)
  refine ⟨eq,tuples default L indices.items,?_⟩
  intro f
  obtain ⟨g,mem,all⟩ := tuples_cover default L indices.items f
  exact (funext (fun i => all i (indices.all i))) ▸ mem

def quotientModel (R : P455Quotient.Rules Nat) (T : List Nat) (cap : P455Quotient.Cap R.r T) :
    Model (P455Quotient.Q R T) where
  op := P455Quotient.mul R cap
  unit := P455Quotient.ofWord R T []
  assoc := P455Quotient.mul_assoc R cap
  oneL x := (P455Quotient.unit_laws R cap x).1
  oneR x := (P455Quotient.unit_laws R cap x).2

def quotientListing (R : P455Quotient.Rules Nat) (T : List Nat) (eq : DecidableEq (P455Quotient.Q R T)) :
    Listing (P455Quotient.Q R T) :=
  ⟨eq,Problem455Finite.carrier R T,Problem455Finite.carrier_complete R T⟩

end P455TableProduct
