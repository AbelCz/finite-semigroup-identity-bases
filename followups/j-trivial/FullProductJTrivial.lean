import Problem455Undecidability
import QuotientJTrivial
import JTrivialCore

namespace JTrivialFollowup

open P455FirstRewrite P455Table P455TableSemantics P455NumericProduct
open P455PaddedTiles P455MachineCleanup P455EffectiveMachine P455Witness

theorem pair {α β : Type} {m : α → α → α} {n : β → β → β}
    (hm : MutuallyDivisibleTrivial m) (hn : MutuallyDivisibleTrivial n) :
    MutuallyDivisibleTrivial (fun x y : α × β => (m x.1 y.1, n x.2 y.2)) := by
  rintro x y ⟨a,b,hx⟩ ⟨c,d,hy⟩
  apply Prod.ext
  · exact hm _ _ ⟨a.1,b.1,congrArg Prod.fst hx⟩ ⟨c.1,d.1,congrArg Prod.fst hy⟩
  · exact hn _ _ ⟨a.2,b.2,congrArg Prod.snd hx⟩ ⟨c.2,d.2,congrArg Prod.snd hy⟩

theorem combine_preserves {α β : Type} (M : Model α) (N : Model β)
    (hm : MutuallyDivisibleTrivial M.op) (hn : MutuallyDivisibleTrivial N.op) :
    MutuallyDivisibleTrivial (P455FirstTesters.combine M N).op :=
  pair hm hn

theorem quotient_preserves {α : Type} [DecidableEq α] (R : P455Quotient.Rules α)
    {T : List α} (hT : P455Quotient.Cap R.r T) :
    MutuallyDivisibleTrivial (P455Quotient.mul R hT) :=
  P455Quotient.quotient_j_trivial R hT

theorem full_product_j_trivial (r : Nat) (allow : Tag → Prop)
    (ts : Tiles) :
    MutuallyDivisibleTrivial (P455FullSingleton.model r allow ts).op := by
  unfold P455FullSingleton.model P455MarkedRank.model
  apply combine_preserves
  · exact pi _ (fun i => quotient_preserves _ i.cap)
  apply combine_preserves
  · apply combine_preserves
    · exact pi _ (fun i => quotient_preserves _ i.cap)
    · exact pi _ (fun i => quotient_preserves _ i.cap)
  apply combine_preserves
  · exact pi _ (fun i => quotient_preserves _ i.bound)
  · exact pi _ (fun i => quotient_preserves _ i.cap)

def JTrivialTable (T : P455Table.Matrix) : Prop :=
  ∀ x y, x < T.length → y < T.length →
    (∃ a < T.length, ∃ b < T.length, x = entry T (entry T a y) b) →
    (∃ c < T.length, ∃ d < T.length, y = entry T (entry T c x) d) → x = y

theorem j_trivial_of_representation {α : Type} {M : Model α} {T : P455Table.Matrix}
    (p : Represents T M) (hm : MutuallyDivisibleTrivial M.op) : JTrivialTable T := by
  obtain ⟨X,rfl,⟨iso⟩⟩ := p
  intro x y hx hy
  rintro ⟨a,ha,b,hb,e⟩ ⟨c,hc,d,hd,e'⟩
  let i : Fin X.size := ⟨x,by simpa only [matrix_length] using hx⟩
  let j : Fin X.size := ⟨y,by simpa only [matrix_length] using hy⟩
  let a' : Fin X.size := ⟨a,by simpa only [matrix_length] using ha⟩
  let b' : Fin X.size := ⟨b,by simpa only [matrix_length] using hb⟩
  let c' : Fin X.size := ⟨c,by simpa only [matrix_length] using hc⟩
  let d' : Fin X.size := ⟨d,by simpa only [matrix_length] using hd⟩
  change i.val = entry (matrix X) (entry (matrix X) a' j) b' at e
  change j.val = entry (matrix X) (entry (matrix X) c' i) d' at e'
  simp only [matrix_entry] at e e'
  have h₁ := congrArg iso.decode (Fin.ext e : i = X.mul (X.mul a' j) b')
  have h₂ := congrArg iso.decode (Fin.ext e' : j = X.mul (X.mul c' i) d')
  simp only [iso.mul_eq] at h₁ h₂
  exact congrArg Fin.val (iso.inj i j (hm _ _ ⟨_,_,h₁⟩ ⟨_,_,h₂⟩))

-- Safe machine codes produce J-trivial finite multiplication tables.
theorem coded_machine_table_j_trivial {g q : Nat} (C : Code g q) (safe : C.Safe) :
    JTrivialTable (P455Undecidability.multiplicationTable C.bits) :=
  j_trivial_of_representation
    (P455Undecidability.presents_exact_model C safe)
    (full_product_j_trivial _ _ _)

end JTrivialFollowup

#print axioms JTrivialFollowup.coded_machine_table_j_trivial
