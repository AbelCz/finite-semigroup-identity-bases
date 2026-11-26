import Problem455SameDonor
import Problem455Finite

/- The block implication actually used by the marked testers, in a proper
   factor representing an arbitrary nonzero evaluation. No donor is assigned
   to labels coming solely from a gap. -/
namespace P455DonorBridge
open P455Quotient
open Problem455Swap

theorem separated_donors {r : Nat} {allow mark} {T z : List Nat}
    {β : Type} [DecidableEq β] (u : List β) (h : β → List Nat) (i j : β)
    (a b : Nat) (hi : u.count i = r) (ha : a ∈ h i) (hb : b ∈ h j)
    (Tcap : P455Quotient.Cap r T)
    (path : Variant (Problem455Finite.rules r allow mark) T z)
    (factor : P455Quotient.Factor (u.flatMap h) z)
    (different : ¬ SameBlock r z a b) : i ≠ j := by
  rintro rfl
  have capZ : P455Quotient.Cap r z := fun s =>
    (count_walk _ path s) ▸ Tcap s
  have capF : P455Quotient.Cap r (u.flatMap h) :=
    good_cap (Problem455Finite.rules r allow mark) Tcap ⟨z,path,factor⟩
  apply different
  apply sameBlock_factor factor _ (Problem455SameDonor.sameDonor u h i hi capF a b ha hb)
  intro s
  rw [Problem455BlockBridge.occ_count]
  exact capZ s

end P455DonorBridge
