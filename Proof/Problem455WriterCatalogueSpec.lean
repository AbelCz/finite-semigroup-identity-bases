import Problem455WriterGuardSpec
import Problem455WriterEdgeTests
import Problem455WriterStructural
import Problem455WriterBinary
import Problem455PayloadBridge
/- The complete five-family catalogue from a finite numerical local table. -/
namespace P455WriterCatalogue
open P455PaddedTiles P455WriterTiles

def capSize (n : Nat) := widthCode n + 16
def build (D : MachineData) : P455SerializePrim.Data :=
  let n := size D
  let r := capSize n
  let ts := tags D
  (r, ts, P455CataloguePrim.primitive r, P455WriterGuard.family r n ts,
   P455WriterEdge.edges r n ts, P455WriterBinary.bin r ts, P455WriterStructural.structural r ts)

theorem build_correct {D : MachineData} {M : MachineTable n} (h : Models D M) :
    build D = P455SerializePrim.ofPayload (P455Packed.prepared M) := by
  have hr : 0 < capSize n := by unfold capSize; omega
  simp only [build,h.dim,tags_correct h]
  rw [P455WriterGuard.family_ok M hr,P455WriterEdge.edges_correct M hr,P455WriterBinary.bin_correct M,
    P455WriterStructural.structural_correct hr M]
  have p := P455PayloadBridge.primitive_field M
  unfold P455SerializePrim.ofPayload P455Packed.prepared
  dsimp only [P455Encoded.indices]
  simp only [capSize]
  rw [←p]
  simp only [P455Packed.prepared,P455Encoded.indices]

def table (D : MachineData) := P455Packed.serialize (P455SerializePrim.asPayload (build D))
def bits (D : MachineData) := P455TableBits.encode (table D)

theorem table_correct {D : MachineData} {M : MachineTable n} (h : Models D M) :
    table D = P455Packed.serialize (P455Packed.prepared M) := by
  unfold table
  rw [build_correct h,P455SerializePrim.as_of]

theorem table_represents {D : MachineData} {M : MachineTable n} (h : Models D M) :
    P455NumericProduct.Represents (table D) (P455Global.monoid M) := by
  rw [table_correct h]
  exact P455Packed.serialize_represents M

end P455WriterCatalogue
