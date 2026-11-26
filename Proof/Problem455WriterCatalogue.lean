import Problem455WriterCatalogueSpec
import Problem455WriterGuard
import Problem455WriterEdgeRec
namespace P455WriterCatalogue
open P455PaddedTiles P455WriterTiles

theorem capRec : Primrec capSize :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (.const 6)
    (Primrec.nat_mul.comp (.const 4) (Primrec.succ.comp Primrec.id))) (.const 16)

theorem buildRec : Primrec build := by
  have n : Primrec size := Primrec.fst
  have r := capRec.comp n
  have ts := P455WriterTiles.tagsRec
  exact r.pair (ts.pair ((P455CataloguePrim.primitive'.comp r).pair
    ((P455WriterGuard.familyRec r n ts).pair ((P455WriterEdge.edgesRec r n ts).pair
    ((P455WriterBinary.binRec r ts).pair (P455WriterStructural.structuralRec r ts))))))

theorem tableRec : Primrec table := P455SerializePrim.serialize.comp buildRec
theorem bitsRec : Primrec bits := P455SerializePrim.bits.comp buildRec

end P455WriterCatalogue
