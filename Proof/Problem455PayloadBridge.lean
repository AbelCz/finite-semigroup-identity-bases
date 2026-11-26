import Problem455SerializePrim
import Problem455PackedOutput
import Problem455PrimitivePrim

/- The first-order catalogue input to the actual bit writer. -/
namespace P455PayloadBridge
open P455PaddedTiles P455MachineCleanup P455MachineTable P455MachineParse

def selfPayload (s : List Bool) : Option P455SerializePrim.Data :=
  match blankSource s with
  | none => none
  | some ⟨_, _, M⟩ => some (P455SerializePrim.ofPayload (P455Packed.prepared (compile (normalized M))))

theorem primitive_field {n : Nat} (M : MachineTable n) :
    (P455Packed.prepared M).primitive = P455CataloguePrim.primitive (widthCode n + 16) := by
  simp only [P455Packed.prepared, P455Packed.names, P455Encoded.indices, P455Encoded.useCover,
    P455CataloguePrim.primitive]
  apply List.map_congr_left
  intro i _
  rfl

theorem selfOutput_computable (h : Computable selfPayload) :
    Computable P455PackedOutput.selfOutput := by
  let fallback := P455TableBits.encode [[0]]
  let serialize := fun d : P455SerializePrim.Data =>
    P455TableBits.encode (P455Packed.serialize (P455SerializePrim.asPayload d))
  have certified : Computable₂ (fun (_ : List Bool) d => serialize d) :=
    (P455SerializePrim.bits.to_comp.comp Computable.snd).to₂
  apply (Computable.option_casesOn h (Computable.const fallback) certified).of_eq
  intro s
  unfold selfPayload P455PackedOutput.selfOutput P455PackedOutput.selfTable
  cases blankSource s with
  | none => rfl
  | some source =>
    rcases source with ⟨g, q, M⟩
    simp only [serialize, P455SerializePrim.as_of, P455PackedOutput.alternative]

end P455PayloadBridge
