import Problem455WriterCodePrim
import Problem455SerializePrim
import Problem455ComputableWriter
import Problem455TableValidate

namespace P455CertifiedReduction
open P455WriterTiles P455WriterProgram P455SerializePrim P455Table P455TableSemantics
open P455MachineCleanup P455MachineTable P455EffectiveMachine P455EffectiveWriter P455EffectiveChain
open P455NumericProduct P455PaddedTiles

abbrev Catalogue := MachineData → Data
def Correct (c : Catalogue) := ∀ {n} (M : MachineTable n) (d : MachineData), Models d M →
  asPayload (c d)=P455Packed.prepared M

def materialize (c : Catalogue) (d : MachineData) :=
  P455TableValidate.safe (P455Packed.serialize (asPayload (c d)))
def codeTable (c : Catalogue) (s : List Bool) := materialize c (fromCodeBits s)
def selfTable (c : Catalogue) (s : List Bool) := materialize c (fromBits s)

theorem buildRec {c : Catalogue} (hc : Primrec c) : Primrec (materialize c) :=
  P455TableValidate.safeRec.comp (P455SerializePrim.serialize.comp hc)
theorem codeRec {c : Catalogue} (hc : Primrec c) : Primrec (codeTable c) := (buildRec hc).comp Cert.fromCodeBits'
theorem selfRec {c : Catalogue} (hc : Primrec c) : Primrec (selfTable c) := (buildRec hc).comp Cert.fromBits'
theorem finite_monoid (c : Catalogue) (d : MachineData) :
    SemigroupTable (materialize c d) ∧ HasUnit (materialize c d) := P455TableValidate.monoid _

theorem builds {c : Catalogue} (hc : Correct c) (M : Ordinary ng nq) {d : MachineData}
    (h : Models d (compile (normalized M))) :
    Represents (materialize c d) (P455MachineReduction.model M) := by
  unfold materialize; rw [hc _ d h]
  obtain ⟨X,e,⟨iso⟩⟩ := P455PackedOutput.alternative_represents M
  change P455Packed.serialize _=matrix X at e
  exact ⟨X,by rw [e,P455TableValidate.identity (output_laws iso)],⟨iso⟩⟩

theorem code_presents {c : Catalogue} (hc : Correct c) (C : Code ng nq) (s : C.Safe) :
    Represents (codeTable c C.bits) (P455MachineReduction.model (C.machine s)) :=
  builds hc _ (fromCodeBits_spec C s)

theorem code_basis {c : Catalogue} (hc : Correct c) (C : Code ng nq) (s : C.Safe) :
    P455PureSemigroup.Basis (codeTable c C.bits) ↔ ¬ ∃ t, stopped (C.machine s) t := by
  obtain ⟨X,e,⟨iso⟩⟩ := code_presents hc C s
  rw [e,P455PureSemigroup.basis_iff (output_laws iso).1,P455TableSemantics.basis_iff iso]
  exact P455Decision.ordinary_equivalence _

theorem self_presents {c : Catalogue} (hc : Correct c) (P : Ordinary ng nq) (B : Alphabet P) :
    Represents (selfTable c (selfBits P B)) (P455MachineReduction.model (diagonalInput P B).2) :=
  builds hc _ (fromBits_self P B)

theorem self_basis {c : Catalogue} (hc : Correct c) (P : Ordinary ng nq) (B : Alphabet P) :
    P455PureSemigroup.Basis (selfTable c (selfBits P B)) ↔ ¬ SelfHalt P B := by
  obtain ⟨X,e,⟨iso⟩⟩ := self_presents hc P B
  rw [e,P455PureSemigroup.basis_iff (output_laws iso).1,P455TableSemantics.basis_iff iso]
  exact diagonal_basis P B

theorem presentation {c : Catalogue} (hc : Correct c) (rec : Primrec c) :
    P455TableDecision.PresentationWriterExists := by
  have hf := P455NumericProductPrim.encode.comp (selfRec rec)
  obtain ⟨g,q,W,A,run⟩ := P455ComputableWriter.realizes hf.to_comp
  refine ⟨g,q,W,A,A,?_⟩
  intro k s P B
  obtain ⟨X,e,iso⟩ := self_presents hc P B
  refine ⟨X,iso,?_⟩
  simpa only [Function.comp_apply,←e] using run (selfBits P B)

end P455CertifiedReduction
