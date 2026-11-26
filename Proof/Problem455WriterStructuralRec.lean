import Problem455WriterStructuralTests
namespace P455WriterStructural
open P455WriterTiles P455WriterProfiles P455WriterObservations
open Problem455.Slots
variable {A : Type} [Primcodable A]

theorem recordRec {r : A → Nat} {ts : A → Tags} {w : A → W} {a b : A → Nat}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => recordB (r x) (ts x) (w x) (a x) (b x) := by
  apply Primrec.and.comp (PrimrecPred.not (Primrec.eq.comp ha hb))
  apply P455GraphPrim.anyB (choicesRec ht (.const [false,true]))
  apply Primrec₂.mk
  have t := Primrec.fst.comp (Primrec.snd (α := A) (β := List Bool × Bool))
  have v := Primrec.snd.comp (Primrec.snd (α := A) (β := List Bool × Bool))
  have k := Primrec.list_cons.comp ha (Primrec.list_cons.comp hb (.const []))
  exact PrimrecPred.and (Primrec.eq.comp (Primrec.nat_add.comp (Primrec.list_length.comp t) (.const 16)) (hr.comp Primrec.fst))
    (Primrec.eq.comp ((selectRec k hw).comp Primrec.fst) (profileRec (ha.comp Primrec.fst) (hb.comp Primrec.fst) t v))

theorem edgeRec {r : A → Nat} {ts : A → Tags} {w : A → W} {a b : A → Nat}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => edgeB (r x) (ts x) (w x) (a x) (b x) :=
  Primrec.or.comp (recordRec hr ht hw ha hb) (recordRec hr ht hw hb ha)

theorem widthRec {k : A → Nat} {w : A → W} (hk : Primrec k) (hw : Primrec w) :
    Primrec fun x => widthB (k x) (w x) := by
  apply P455GraphPrim.anyB (P455GraphPrim.wordsUpTo.comp hw hk)
  apply Primrec₂.mk
  apply P455FramePrim.allB (hw.comp Primrec.fst)
  exact (P455CataloguePrim.mem'.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂

theorem overlapRec {r : A → Nat} {ts : A → Tags} {w : A → W}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) :
    Primrec fun x => overlapB (r x) (ts x) (w x) := by
  apply P455GraphPrim.anyB (choicesRec hw (choicesRec hw hw))
  apply Primrec₂.mk
  have base := Primrec.fst (α := A) (β := Nat × Nat × Nat)
  have args := Primrec.snd (α := A) (β := Nat × Nat × Nat)
  have a := Primrec.fst.comp args
  have b := Primrec.fst.comp (Primrec.snd.comp args)
  have c := Primrec.snd.comp (Primrec.snd.comp args)
  have ab := PrimrecPred.not (Primrec.eq.comp a b)
  have ac := PrimrecPred.not (Primrec.eq.comp a c)
  have bc := PrimrecPred.not (Primrec.eq.comp b c)
  exact Primrec.and.comp (Primrec.and.comp (PrimrecPred.and ab (PrimrecPred.and ac bc))
    (edgeRec (hr.comp base) (ht.comp base) (hw.comp base) a b))
    (edgeRec (hr.comp base) (ht.comp base) (hw.comp base) a c)

theorem intrusionRec {r : A → Nat} {ts : A → Tags} {w : A → W}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) :
    Primrec fun x => intrusionB (r x) (ts x) (w x) := by
  apply P455GraphPrim.anyB (choicesRec hw (choicesRec hw (eventsRec.comp hw)))
  apply Primrec₂.mk
  have base := Primrec.fst (α := A) (β := Nat × Nat × Event)
  have args := Primrec.snd (α := A) (β := Nat × Nat × Event)
  have a := Primrec.fst.comp args
  have b := Primrec.fst.comp (Primrec.snd.comp args)
  have e := Primrec.snd.comp (Primrec.snd.comp args)
  have z := Primrec.fst.comp e
  have ab := PrimrecPred.not (Primrec.eq.comp a b)
  have za := PrimrecPred.not (Primrec.eq.comp z a)
  have zb := PrimrecPred.not (Primrec.eq.comp z b)
  have pattern := Primrec.list_cons.comp (Primrec.pair a (.const 0))
    (Primrec.list_cons.comp e (Primrec.list_cons.comp (Primrec.pair b (.const 2)) (.const [])))
  exact Primrec.and.comp (Primrec.and.comp (PrimrecPred.and ab (PrimrecPred.and za zb))
    (recordRec (hr.comp base) (ht.comp base) (hw.comp base) a b)) (seesRec (hw.comp base) pattern)

theorem compressedRec {r : A → Nat} {w : A → W} (hr : Primrec r) (hw : Primrec w) :
    Primrec fun x => compressedB (r x) (w x) := by
  apply P455FramePrim.allB (choicesRec hw hw)
  apply Primrec₂.mk
  exact PrimrecPred.not (Primrec.eq.comp
    (bigramRec (hw.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (hr.comp Primrec.fst))

end P455WriterStructural
