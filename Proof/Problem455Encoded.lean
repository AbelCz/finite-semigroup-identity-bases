import Problem455TableFactors
import Problem455TableBits
import Problem455EnumEdges
import Problem455EffectiveQTable
import Problem455EffectiveMachineCode



namespace P455Encoded
open P455Table P455TableFactors P455PaddedTiles P455FirstRewrite
open P455MachineCleanup P455MachineTable P455EffectiveMachine

def useCover {I : Type} [DecidableEq I] (c : P455Enum.Cover I) : Listing I :=
    ⟨inferInstance,c.list,c.mem⟩

def indices {n} (M : MachineTable n) : Catalogues (widthCode n+16) (allowed M) (system n) where
  primitive := useCover (P455Enum.primitive _)
  binary := useCover (P455Enum.binary _ M)
  structural := useCover (P455Enum.structural (by omega) M)
  guard := useCover (P455Enum.guard (by omega) M)
  edge := useCover (P455Enum.edge (by omega) M)

private def markEq {n} (M : MachineTable n) {mark : Nat → Nat → Prop}
    (d : DecidableRel mark) (r : Nat) (T : List Nat) :
    DecidableEq (P455Quotient.Q (Problem455Finite.rules r (allowed M) mark) T) :=
  P455EffectiveQMove.markedEq (fun _ => P455Enum.mem_tags (M := M))
    (marks := fun a b => @decide (mark a b) (d a b)) (fun a b => Iff.of_eq (@decide_eq_true_eq _ (d a b))) r T

def equalities {n} (M : MachineTable n) : EqualityTests (widthCode n+16) (allowed M) (system n) where
  plain := P455EffectiveQTable.plainEq _
  binary := fun i => by
    unfold P455BinaryProduct.Index.R
    split
    · exact markEq M (fun _ _ => .isFalse id) _ _
    · exact P455EffectiveQTable.plainEq _ _
  guard := fun _ => markEq M (fun _ _ => inferInstanceAs (Decidable (_=_ ∧ _=_))) _ _
  edge := fun i => markEq M (P455Enum.markD i.a i.b i.c i.d) _ _

def localOps {n} (M : MachineTable n) := finiteOps (listing (indices M) (equalities M)) (P455Global.monoid M)
def localPresents {n} (M : MachineTable n) : Presents (localOps M) (P455Global.monoid M) :=
  presentation ..

def ops (M : Ordinary g q) := localOps (compile (normalized M))

def presents (M : Ordinary g q) : Presents (ops M) (P455MachineReduction.model M) :=
  localPresents (compile (normalized M))

def output (M : Ordinary g q) := matrix (ops M)

theorem output_monoid (M : Ordinary g q) :
    P455TableSemantics.SemigroupTable (output M) ∧ P455TableSemantics.HasUnit (output M) :=
  P455TableSemantics.output_laws (presents M)

theorem finite_basis_iff (M : Ordinary g q) :
    P455TableSemantics.HasBasis (output M) ↔ ¬ ∃ t, stopped M t :=
  (P455TableSemantics.basis_iff (presents M)).trans (P455Decision.ordinary_equivalence M)

/-- The finite array input is validated. A rejected code returns none. -/
def fromCode (c : Code g q) : Option Matrix := c.decode.map output

theorem quoted_output (M : Ordinary g q) : fromCode (quote M)=some (output M) := by
  simp [fromCode,quote_decode]

theorem quoted_encoded (M : Ordinary g q) :
    P455TableBits.parse (P455TableBits.encode (output M))=some (output M) :=
  P455TableBits.matrix_roundtrip _

end P455Encoded
