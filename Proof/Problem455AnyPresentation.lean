import Problem455Operational




namespace P455AnyPresentation
open P455MachineCleanup P455MachineTable P455EffectiveMachine P455EffectiveChain
open P455RelabeledChain P455EffectiveWriter P455Table P455TableBits P455TableSemantics
open P455Operational

/-- The one finite writer may use any presentation of the model on each
    well-formed self input. No agreement with the ordering in `ops` is required. -/
def WritesPresentation (W : Ordinary g q) (A O : Alphabet W) :=
  ∀ {k s} (P : Ordinary k s) (B : Alphabet P),
    ∃ X : FiniteOps, Nonempty (Presents X (P455MachineReduction.model (diagonalInput P B).2)) ∧
      Delivers W A (selfBits P B) W O (encode (matrix X))

theorem exact_writer_suffices (W : Ordinary g q) (A O : Alphabet W)
    (writes : WritesSelf W A O) : WritesPresentation W A O := by
  intro k s P B
  refine ⟨P455Encoded.ops (diagonalInput P B).2,⟨P455Encoded.presents _⟩,?_⟩
  have output_eq : P455RawReduction.diagonalBits (selfBits P B)=
      encode (matrix (P455Encoded.ops (diagonalInput P B).2)) := by
    unfold P455RawReduction.diagonalBits P455RawReduction.diagonalTable
    rw [P455MachineParse.blankSource_self]
    rfl
  rw [←output_eq]
  exact writes P B

/-- Direct complement diagonal. The trap runs forever on a negative verdict.
    Its own halting is consequently equivalent to the positive verdict. -/
theorem no_table_decider (W : Ordinary g q) (A O : Alphabet W)
    (writes : WritesPresentation W A O) (D : Ordinary h r) (B : Alphabet D)
    (ans : Fin r → Bool) : ¬ DecidesTable D B ans := by
  intro reads
  let C := combined W O D B
  let I := inputs W A O D B
  let negate : Fin (q+r) → Bool := fun z => !(P455EffectiveChain.out q ans z)
  let P := trap C negate
  let J := P455EffectiveMachine.liftAlphabet C I negate
  let x := selfBits P J
  let c := inputConfig C I x
  obtain ⟨X,⟨pres⟩,delivers⟩ := writes P J
  obtain ⟨b,reading,spec⟩ := reads (matrix X) (output_laws pres).1
  obtain ⟨t,stop,outcome⟩ := answers_combined W A O D B ans delivers reading
  change instruction C (follow C c t)=none at stop
  change P455EffectiveChain.out q ans (follow C c t).state=b at outcome
  have self : SelfHalt P J ↔ b=true := by
    change HALT (trap C negate) c ↔ b=true
    rw [halt_trap_iff C negate c stop]
    change (!(P455EffectiveChain.out q ans (follow C c t).state))=false ↔ b=true
    rw [outcome]
    cases b <;> decide
  have flip : b=true ↔ ¬ SelfHalt P J :=
    spec.trans ((basis_iff pres).trans (diagonal_basis P J))
  have no : ¬ SelfHalt P J := fun v => flip.mp (self.mp v) v
  exact no (self.mpr (flip.mpr no))

end P455AnyPresentation
