import Problem455BinaryTerms

/- Binary multiplication terms on every valid tabulated semigroup.
   The two definitions of finite basability have equivalent truth values. -/
namespace P455BinaryBasis
open P455BinaryTerms P455FirstRewrite P455Table P455TableSemantics

def eval (T : Matrix) (f : Nat → Nat) : Term → Nat
  | .var x => f x
  | .mul s t => entry T (eval T f s) (eval T f t)

def ValidTerm (T : Matrix) (s t : Term) :=
  ∀ f : Nat → Nat, (∀ x, f x<T.length) → eval T f s=eval T f t

def HasTermBasis (T : Matrix) := ∃ rules : List (Term × Term),
    (∀ s t, (s,t)∈rules → ValidTerm T s t) ∧
    ∀ s t, ValidTerm T s t → Proof (fun x y => (x,y)∈rules) s t

theorem entry_lt {T : Matrix} (good : SemigroupTable T) {i j : Nat}
    (hi : i<T.length) (hj : j<T.length) : entry T i j<T.length := by
  have row := good.2.1 T[i] (List.getElem_mem hi)
  have bound : j<T[i].length := row.1.symm ▸ hj
  have inr := row.2 T[i][j] (List.getElem_mem bound)
  simpa [entry,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem bound] using inr

theorem value_lt {T : Matrix} (good : SemigroupTable T) {f : Nat → Nat}
    (bounded : ∀ i, f i<T.length) (a : Nat) (w : W) : value T f a w<T.length := by
  induction w generalizing a with
  | nil => exact bounded a
  | cons b xs ih => exact entry_lt good (bounded a) (ih b)

theorem concatenate {T : Matrix} (good : SemigroupTable T) {f : Nat → Nat}
    (bounded : ∀ i, f i<T.length) (a : Nat) (A : W) (b : Nat) (B : W) :
    value T f a (A++b::B)=entry T (value T f a A) (value T f b B) := by
  induction A generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,value,ih]
    exact (good.2.2 _ _ _ (bounded a) (value_lt good bounded x xs) (value_lt good bounded b B)).symm

theorem eval_flat {T : Matrix} (good : SemigroupTable T) {f : Nat → Nat}
    (bounded : ∀ i, f i<T.length) (s : Term) : eval T f s=wordValue T f (flat s) := by
  induction s with
  | var x => rfl
  | mul s t ih ik =>
    simp only [eval,flat,ih,ik]
    obtain ⟨a,A,e⟩ := List.exists_cons_of_ne_nil (nonempty s)
    obtain ⟨b,B,h⟩ := List.exists_cons_of_ne_nil (nonempty t)
    rw [e,h]
    exact (concatenate good bounded a A b B).symm

theorem valid_flat {T : Matrix} (good : SemigroupTable T) (s t : Term) :
    ValidTerm T s t ↔ Valid T (flat s) (flat t) := by
  constructor <;> intro h f bounded
  · exact (eval_flat good bounded s).symm.trans ((h f bounded).trans (eval_flat good bounded t))
  · exact (eval_flat good bounded s).trans ((h f bounded).trans (eval_flat good bounded t).symm)

private theorem word_rule {rules : List (W×W)} {u v : W} (m : (u,v)∈rules) (un : u≠[]) (vn : v≠[]) :
    Derives (fun a b => (a,b)∈rules) u v :=
  .snoc (.refl u) ⟨u,v,[],[],fun i => [i],.inl m,un,vn,by simp,by simp,by simp⟩

theorem basis_iff_words {T : Matrix} (good : SemigroupTable T) :
    HasTermBasis T ↔ HasBasis T := by
  constructor
  · rintro ⟨terms,sound,complete⟩
    let words := terms.map (fun p => (flat p.1,flat p.2))
    refine ⟨words,?_,?_⟩
    · intro u v m
      obtain ⟨⟨s,t⟩,mem,e⟩ := List.mem_map.mp m
      cases e
      exact ⟨nonempty _,nonempty _,(valid_flat good _ _).mp (sound _ _ mem)⟩
    · intro u v un vn ok
      have valid : ValidTerm T (fromWord u) (fromWord v) :=
        (valid_flat good _ _).mpr (by simpa only [flat_from un,flat_from vn] using ok)
      have derive := terms_to_words (G:=fun x y => (x,y)∈words)
        (fun s t m => word_rule (List.mem_map_of_mem m) (nonempty s) (nonempty t))
        (complete _ _ valid)
      simpa only [flat_from un,flat_from vn] using derive
  · rintro ⟨words,sound,complete⟩
    let terms := words.map (fun p => (fromWord p.1,fromWord p.2))
    refine ⟨terms,?_,?_⟩
    · intro s t m
      obtain ⟨⟨u,v⟩,mem,e⟩ := List.mem_map.mp m
      cases e
      obtain ⟨un,vn,ok⟩ := sound _ _ mem
      apply (valid_flat good _ _).mpr
      simpa only [flat_from un,flat_from vn] using ok
    · intro s t ok
      have derive := complete _ _ (nonempty s) (nonempty t) ((valid_flat good _ _).mp ok)
      have path := words_to_terms (H:=fun x y => (x,y)∈terms)
        (fun _ _ m => Proof.gen (List.mem_map_of_mem m)) derive
      exact (norm _ s).trans (path.trans (norm _ t).symm)

end P455BinaryBasis
