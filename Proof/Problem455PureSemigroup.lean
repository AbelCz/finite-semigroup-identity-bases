import Problem455BinaryBasis
import Problem455RawReduction

/- No background axiom is built into Equational. Associativity is added
   to the finite rule list by its single multiplication-only identity. -/
namespace P455PureSemigroup
open P455Table P455TableSemantics P455BinaryTerms P455BinaryBasis

inductive Equational (G : Term → Term → Prop) : Term → Term → Prop
  | refl (x) : Equational G x x
  | symm : Equational G x y → Equational G y x
  | trans : Equational G x y → Equational G y z → Equational G x z
  | gen : G x y → Equational G x y
  | mul : Equational G x y → Equational G z t → Equational G (.mul x z) (.mul y t)
  | subst (f) : Equational G x y → Equational G (inst f x) (inst f y)

def assocPair : Term × Term :=
  (.mul (.mul (.var 0) (.var 1)) (.var 2),.mul (.var 0) (.mul (.var 1) (.var 2)))

def Basis (T : Matrix) := ∃ rules : List (Term × Term),
  (∀ u v, (u,v)∈rules → ValidTerm T u v) ∧
  ∀ u v, ValidTerm T u v → Equational (fun x y => (x,y)∈rules) u v

theorem forget {G} {u v} (p : Equational G u v) : Proof G u v := by
  induction p with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih ik => exact .trans ih ik
  | gen m => exact .gen m
  | mul _ _ ih ik => exact .mul ih ik
  | subst f _ ih => exact .subst f ih

theorem explicit_assoc (rs : List (Term × Term)) {u v}
    (p : Proof (fun x y => (x,y)∈rs) u v) :
    Equational (fun x y => (x,y)∈assocPair::rs) u v := by
  induction p with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih ik => exact .trans ih ik
  | gen m => exact .gen (List.mem_cons_of_mem _ m)
  | mul _ _ ih ik => exact .mul ih ik
  | subst f _ ih => exact .subst f ih
  | assoc x y z =>
    let f (i : Nat) := if i=0 then x else if i=1 then y else z
    have law : Equational (fun s t => (s,t)∈assocPair::rs) assocPair.1 assocPair.2 := .gen List.mem_cons_self
    exact .subst f law

theorem basis_iff {T : Matrix} (good : SemigroupTable T) :
    Basis T ↔ P455TableSemantics.HasBasis T := by
  rw [←basis_iff_words good]
  constructor
  · rintro ⟨rs,s,all⟩; exact ⟨rs,s,fun u v h => forget (all u v h)⟩
  · rintro ⟨rs,s,all⟩
    refine ⟨assocPair::rs,?_,fun u v h => explicit_assoc rs (all u v h)⟩
    intro u v mem
    rcases List.mem_cons.mp mem with first|old
    · cases first
      intro f bounded
      exact good.2.2 (f 0) (f 1) (f 2) (bounded 0) (bounded 1) (bounded 2)
    · exact s _ _ old

theorem raw_basis (s : List Bool) :
    Basis (P455RawReduction.blankTable s) ↔
      ¬ P455RawReduction.realizesHalt (P455RawReduction.parseBlank s) :=
  (basis_iff (P455RawReduction.exact_blank s).2.1).trans (P455RawReduction.exact_blank s).2.2.2

end P455PureSemigroup
