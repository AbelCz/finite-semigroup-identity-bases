import Problem455WriterEdgeTypes

namespace P455WriterEdge
open P455Witness
variable {X : Type} [Primcodable X]

theorem certificatesRec {w : X → List Nat} {ts : X → List (List Bool)} (hw : Primrec w) (ht : Primrec ts) :
    Primrec (fun x => P455Enum.certificates (w x) (ts x)) := by
  have ns := poolRec hw ht
  apply Primrec.list_flatMap ns
  apply Primrec₂.mk
  apply Primrec.list_flatMap (ns.comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_flatMap ((ns.comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_flatMap (((ns.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_flatMap ((((ns.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_flatMap (((((ns.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_map ((((((ns.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  exact mkEdgeRec ((((((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) (((((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) ((((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) (((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) ((Primrec.snd.comp Primrec.fst).comp Primrec.fst) (Primrec.snd.comp Primrec.fst) Primrec.snd

theorem functionalitiesRec {w : X → List Nat} {ts : X → List (List Bool)} (hw : Primrec w) (ht : Primrec ts) :
    Primrec (fun x => P455Enum.functionalities (w x) (ts x)) := by
  have ns := poolRec hw ht
  apply Primrec.list_flatMap ns
  apply Primrec₂.mk
  apply Primrec.list_flatMap (Primrec.const [false,true])
  apply Primrec₂.mk
  apply Primrec.list_flatMap ((ns.comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_flatMap (((ns.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_flatMap (Primrec.const P455Enum.directions.list)
  apply Primrec₂.mk
  apply Primrec.list_map (Primrec.const [false,true])
  apply Primrec₂.mk
  exact mkFuncRec (((((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) ((((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) (((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) ((Primrec.snd.comp Primrec.fst).comp Primrec.fst) (Primrec.snd.comp Primrec.fst) Primrec.snd

end P455WriterEdge
