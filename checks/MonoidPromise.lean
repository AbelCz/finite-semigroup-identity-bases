import Problem455Undecidability




namespace P455LastReview
open P455Table P455TableSemantics P455BinaryTerms P455PureSemigroup
open P455SemanticConsequence P455StatementAudit

def rule (R : List (Term × Term)) (s t : Term) := (s,t) ∈ R

def semigroupEntails (R : List (Term × Term)) (s t : Term) : Prop :=
  ∀ (A : Type) (m : A → A → A), Nonempty A →
    (∀ x y z, m (m x y) z = m x (m y z)) →
    (∀ u v, rule R u v → satisfies m u v) → satisfies m s t

def finiteBasis {T : Matrix} (ok : SemigroupTable T) : Prop :=
  ∃ R : List (Term × Term), ∀ s t,
    (∀ f : Nat → Fin T.length, val ok f s = val ok f t) ↔ semigroupEntails R s t

theorem assocLaw (m : A → A → A) :
    satisfies m assocPair.1 assocPair.2 ↔ ∀ x y z, m (m x y) z = m x (m y z) := by
  constructor
  · intro h x y z
    exact h (fun i => if i = 0 then x else if i = 1 then y else z)
  · intro h f
    exact h (f 0) (f 1) (f 2)

theorem withAssoc (R : List (Term × Term)) (s t : Term) :
    entails (rule (assocPair :: R)) s t ↔ semigroupEntails R s t := by
  constructor
  · intro h A m _ assoc models
    apply h A m
    intro u v hr
    rcases List.mem_cons.mp hr with he | base
    · have eu : u = assocPair.1 := congrArg Prod.fst he
      have ev' : v = assocPair.2 := congrArg Prod.snd he
      rw [eu, ev']
      exact (assocLaw m).mpr assoc
    · exact models _ _ base
  · intro h A m models f
    have assoc := (assocLaw m).mp (models _ _ List.mem_cons_self)
    exact h A m ⟨f 0⟩ assoc (fun u v hu => models u v (List.mem_cons_of_mem _ hu)) f

theorem atTable {T : Matrix} (ok : SemigroupTable T) (f : Nat → Fin T.length) :
    val ok f assocPair.1 = val ok f assocPair.2 := by
  apply Fin.ext
  exact ok.2.2 _ _ _ (f 0).isLt (f 1).isLt (f 2).isLt

theorem finiteBasis_iff {T : Matrix} (ok : SemigroupTable T) : Basis T ↔ finiteBasis ok := by
  rw [public_basis ok]
  constructor
  · rintro ⟨R,hR⟩
    refine ⟨R,fun s t => ?_⟩
    have assoc := (hR assocPair.1 assocPair.2).mp (atTable ok)
    constructor
    · intro law A m _ _ models
      exact (hR s t).mp law A m models
    · intro law
      apply (hR s t).mpr
      intro A m models f
      exact law A m ⟨f 0⟩ ((assocLaw m).mp (assoc A m models)) models f
  · rintro ⟨R,hR⟩
    exact ⟨assocPair :: R,fun s t => (hR s t).trans (withAssoc R s t).symm⟩

open P455MachineCleanup P455EffectiveMachine P455CertifiedReduction
open P455EffectiveChain

/-- A numerical-table procedure need answer only for monoids. Its finite
    basis is interpreted among all nonempty semigroups in the single binary
    operation language. There is no distinguished identity constant. -/
theorem no_monoid_promise_decider :
    ¬ ∃ p : List (List Nat) →. Bool, Partrec p ∧
      ∀ T (ok : SemigroupTable T), HasUnit T → ∃ b ∈ p T, (b = true ↔ finiteBasis ok) := by
  rintro ⟨p,partialRec,answers⟩
  let tables := selfTable P455WriterCatalogue.build
  have lawful (x : List Bool) : SemigroupTable (tables x) ∧ HasUnit (tables x) := finite_monoid _ _
  have total (x : List Bool) : (p (tables x)).Dom := by
    obtain ⟨b,hb,_⟩ := answers _ (lawful x).1 (lawful x).2
    exact Part.dom_iff_mem.mpr ⟨b,hb⟩
  let f (x : List Bool) := (p (tables x)).get (total x)
  have computes : Computable f :=
    (partialRec.comp (selfRec P455WriterCatalogue.buildRec).to_comp).of_eq_tot
      (fun x => Part.get_mem (total x))
  obtain ⟨_,_,D,A,answer,run⟩ := P455StandardDecision.bit_decider computes
  apply no_self_decider D A (fun q => !(answer q))
  intro g q M B
  let x := selfBits M B
  obtain ⟨t,halt,outcome⟩ := run x
  obtain ⟨b,hb,yes⟩ := answers _ (lawful x).1 (lawful x).2
  have eq : f x = b := Part.mem_unique (Part.get_mem (total x)) hb
  have tag : (f x = true) ↔ ¬ SelfHalt M B := by
    rw [eq]
    exact yes.trans ((finiteBasis_iff _).symm.trans (self_basis P455Undecidability.catalogue_ok M B))
  refine ⟨t, halt, ?_⟩
  change (!(answer (follow D (inputConfig D A x) t).state)) = true ↔ SelfHalt M B
  rw [outcome]
  classical
  cases h : f x <;> simp_all

/-- The physical writer can be fixed for all direct machine-code inputs.
    The full tape and the head are specified by Delivers. -/
theorem direct_code_writer :
    ∃ (g q : Nat) (W : Ordinary g q) (A : Alphabet W),
      ∀ s : List Bool, Delivers W A s W A
        (P455TableBits.encode (P455Undecidability.multiplicationTable s)) :=
  P455ComputableWriter.realizes
    (P455NumericProductPrim.encode.comp P455Undecidability.table_primitive_recursive).to_comp

#print axioms finiteBasis_iff
#print axioms no_monoid_promise_decider
#print axioms direct_code_writer
#print axioms P455Undecidability.finite_semigroup_finite_basis_undecidable
end P455LastReview
