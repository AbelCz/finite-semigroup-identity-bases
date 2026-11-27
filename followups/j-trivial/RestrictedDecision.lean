import FullProductJTrivial

namespace JTrivialFollowup

open P455Table P455TableSemantics P455MachineCleanup P455EffectiveMachine
open P455CertifiedReduction
open P455Undecidability (catalogue_ok)

def checkJ (T : Matrix) : Bool :=
  let ns := List.range T.length
  ns.all fun x => ns.all fun y => ns.all fun a => ns.all fun b =>
    ns.all fun c => ns.all fun d =>
      !(decide (x = entry T (entry T a y) b) && decide (y = entry T (entry T c x) d)) ||
      decide (x = y)

theorem checkJ_correct (T : Matrix) : checkJ T = true ↔ JTrivialTable T := by
  unfold checkJ JTrivialTable
  simp only [List.all_eq_true,List.mem_range]
  constructor
  · intro h x y hx hy
    rintro ⟨a,ha,b,hb,h₁⟩ ⟨c,hc,d,hd,h₂⟩
    have e₁ : decide (x = entry T (entry T a y) b) = true := decide_eq_true h₁
    have e₂ : decide (y = entry T (entry T c x) d) = true := decide_eq_true h₂
    have source := h x hx y hy a ha b hb c hc d hd
    rw [e₁,e₂] at source
    exact of_decide_eq_true source
  · intro h x hx y hy a ha b hb c hc d hd
    by_cases h₁ : x = entry T (entry T a y) b
    · by_cases h₂ : y = entry T (entry T c x) d
      · rw [decide_eq_true h₁,decide_eq_true h₂,
            decide_eq_true (h x y hx hy ⟨a,ha,b,hb,h₁⟩ ⟨c,hc,d,hd,h₂⟩)]
        rfl
      · rw [decide_eq_false h₂]
        simp
    · rw [decide_eq_false h₁]
      rfl

private theorem checkJ_primrec : Primrec checkJ := by
  unfold checkJ
  have n : Primrec fun T : Matrix => List.range T.length := Primrec.list_range.comp Primrec.list_length
  apply P455FramePrim.allB n
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp Primrec.fst)
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp (Primrec.fst.comp Primrec.fst))
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  apply Primrec₂.mk
  let E := ((((((Matrix × Nat) × Nat) × Nat) × Nat) × Nat) × Nat)
  have t : Primrec (fun z : E => z.1.1.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have x : Primrec (fun z : E => z.1.1.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have y : Primrec (fun z : E => z.1.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have a : Primrec (fun z : E => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have b : Primrec (fun z : E => z.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have c : Primrec (fun z : E => z.1.2) := Primrec.snd.comp Primrec.fst
  have d : Primrec (fun z : E => z.2) := Primrec.snd
  exact Primrec.or.comp (Primrec.not.comp (Primrec.and.comp
    (Primrec.eq.comp x (P455NumericProductPrim.entry' t (P455NumericProductPrim.entry' t a y) b))
    (Primrec.eq.comp y (P455NumericProductPrim.entry' t (P455NumericProductPrim.entry' t c x) d))))
    (Primrec.eq.comp x y)

def jSafe (T : Matrix) : Matrix := if checkJ T = true then T else [[0]]

theorem jSafe_trivial (T : Matrix) : JTrivialTable (jSafe T) := by
  unfold jSafe
  split
  next h => exact (checkJ_correct T).mp h
  next =>
    intro x y hx hy _ _
    change x < 1 at hx
    change y < 1 at hy
    omega

theorem jSafe_valid (T : Matrix) (valid : SemigroupTable T ∧ HasUnit T) :
    SemigroupTable (jSafe T) ∧ HasUnit (jSafe T) := by
  unfold jSafe
  split
  · exact valid
  · exact (P455TableValidate.correct _).mp (by decide)

theorem jSafe_primrec : Primrec jSafe :=
  Primrec.ite (Primrec.eq.comp checkJ_primrec (Primrec.const true)) Primrec.id (Primrec.const [[0]])

def tables (x : List Bool) := jSafe (selfTable P455WriterCatalogue.build x)

open P455TableBits P455EffectiveChain P455RelabeledChain P455BooleanReader

theorem basis_undecidable_j_trivial :
    ¬ ∃ p : Matrix →. Bool, Partrec p ∧ ∀ T, SemigroupTable T → HasUnit T →
      JTrivialTable T → ∃ b ∈ p T, (b=true ↔ P455PureSemigroup.Basis T) := by
  rintro ⟨p,hp,good⟩
  have hTab (x : List Bool) := jSafe_valid _ (finite_monoid P455WriterCatalogue.build (P455WriterProgram.fromBits x))
  have hJ (x : List Bool) := jSafe_trivial (selfTable P455WriterCatalogue.build x)
  have total (x : List Bool) : (p (tables x)).Dom := by
    obtain ⟨b,hb,_⟩ := good _ (hTab x).1 (hTab x).2 (hJ x)
    exact Part.dom_iff_mem.mpr ⟨_,hb⟩
  let f (x : List Bool) := (p (tables x)).get (total x)
  have hf : Computable f := (hp.comp (jSafe_primrec.comp (selfRec P455WriterCatalogue.buildRec)).to_comp).of_eq_tot
    (fun x => Part.get_mem (total x))
  have exact_result (x : List Bool) : f x = true ↔ P455PureSemigroup.Basis (tables x) := by
    obtain ⟨b,hb,claim⟩ := good _ (hTab x).1 (hTab x).2 (hJ x)
    have same : f x=b := Part.mem_unique (Part.get_mem (total x)) hb
    rw [same]; exact claim
  obtain ⟨_,_,D,A,ans,run⟩ := P455StandardDecision.bit_decider hf
  apply no_self_decider D A (fun q => !(ans q))
  intro g q M B
  let x := selfBits M B
  have jj := j_trivial_of_representation (self_presents catalogue_ok M B)
    (full_product_j_trivial _ _ _)
  have eq : tables x = selfTable P455WriterCatalogue.build x := by
    unfold tables jSafe
    rw [if_pos ((checkJ_correct _).mpr jj)]
  obtain ⟨t,stop,verdict⟩ := run x
  refine ⟨t,stop,?_⟩
  have basisOnCode : P455PureSemigroup.Basis (tables x) ↔ ¬ SelfHalt M B := by
    rw [eq]
    exact self_basis catalogue_ok M B
  have hs := (exact_result x).trans basisOnCode
  change (!(ans (follow D (inputConfig D A x) t).state))=true ↔ SelfHalt M B
  rw [verdict]
  classical
  cases e : f x <;> simp_all

/-- The promise is imposed on finite monoid multiplication tables, but the
    identities still use only multiplication and variables. -/
theorem finite_j_trivial_monoid_finite_basis_undecidable :
    ¬ ∃ p : Matrix →. Bool, Partrec p ∧ ∀ T (valid : SemigroupTable T),
      HasUnit T → JTrivialTable T →
      ∃ b ∈ p T, (b=true ↔ ∃ R : List (P455BinaryTerms.Term × P455BinaryTerms.Term), ∀ s t,
        (∀ a : Nat → Fin T.length, P455StatementAudit.val valid a s =
          P455StatementAudit.val valid a t) ↔
        P455SemanticConsequence.entails (fun u v => (u,v) ∈ R) s t) := by
  rintro ⟨p,hp,answers⟩
  apply basis_undecidable_j_trivial
  refine ⟨p,hp,?_⟩
  intro T valid unit jt
  obtain ⟨b,halt,spec⟩ := answers T valid unit jt
  exact ⟨b,halt,spec.trans (P455SemanticConsequence.public_basis valid).symm⟩

end JTrivialFollowup

#print axioms JTrivialFollowup.basis_undecidable_j_trivial

#print axioms JTrivialFollowup.finite_j_trivial_monoid_finite_basis_undecidable
