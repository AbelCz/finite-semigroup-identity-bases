import Problem455WriterGuardSpec
import Problem455WriterEdgePortsRec
namespace P455WriterGuard
open P455WriterTiles (choicesRec)
open P455PaddedTiles P455GuardProduct
open P455Witness (Tag)
variable {A : Type} [Primcodable A]

theorem widthRec : Primrec width := Primrec.ite (Primrec.eq.comp Primrec.id (.const true)) (.const 8) (.const 43)
theorem wordsRec {r : A → Nat} {k : A → Bool} (hr : Primrec r) (hk : Primrec k) :
    Primrec fun a => words (r a) (k a) := P455GraphPrim.wordsUpTo.comp (Primrec.list_range.comp (widthRec.comp hk))
      (Primrec.nat_mul.comp (widthRec.comp hk) hr)
theorem wordAtRec {r i : A → Nat} {k : A → Bool} (hr : Primrec r) (hk : Primrec k) (hi : Primrec i) :
    Primrec fun a => wordAt (r a) (k a) (i a) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (wordsRec hr hk) hi) (.const [])
theorem keysRec : Primrec keys := by
  apply Primrec.list_flatMap (.const [false,true])
  apply Primrec₂.mk
  have r := Primrec.fst (α := Nat) (β := Bool)
  have k := Primrec.snd (α := Nat) (β := Bool)
  have ws := Primrec.list_range.comp (widthRec.comp k)
  apply Primrec.list_map (choicesRec (Primrec.list_range.comp (Primrec.list_length.comp (wordsRec r k))) (choicesRec ws ws))
  exact (Primrec.pair (k.comp Primrec.fst) Primrec.snd).to₂

theorem checkerRec {r n a b : A → Nat} {ts : A → List Tag} {w : A → List Nat} {k : A → Bool}
    (hr : Primrec r) (hn : Primrec n) (ht : Primrec ts) (hw : Primrec w) (hk : Primrec k) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => checker (r x) (n x) (ts x) (w x) (k x) (a x) (b x) := by
  have mark := Primrec.list_cons.comp (ha.pair hb) (.const [])
  have e := hr.pair (ht.pair (mark.pair hw))
  exact Primrec.and.comp (P455FrameProof.capCheck hr hw) (Primrec.ite (Primrec.eq.comp hk (.const true))
    (P455WriterEdge.funcAcceptRec e hn ha hb) (P455WriterSlots.slotAcceptRec e ha hb))

theorem familyRec {r n : A → Nat} {ts : A → List Tag} (hr : Primrec r) (hn : Primrec n) (ht : Primrec ts) :
    Primrec fun a => family (r a) (n a) (ts a) := by
  have p := Primrec.snd (α := A) (β := Key)
  have src := Primrec.fst (α := A) (β := Key)
  have k := Primrec.fst.comp p
  have i := Primrec.fst.comp (Primrec.snd.comp p)
  have a := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp p))
  have b := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp p))
  have w := wordAtRec (hr.comp src) k i
  have pr : Primrec₂ (fun x (t : Key) => checker (r x) (n x) (ts x) (wordAt (r x) t.1 t.2.1) t.1 t.2.2.1 t.2.2.2) :=
    checkerRec (hr.comp src) (hn.comp src) (ht.comp src) w k a b
  have f := P455GraphPrim.filter (keysRec.comp hr) pr
  exact Primrec.list_map (P455CataloguePrim.distinct'.comp f)
    (w.pair (Primrec.option_some.comp (Primrec.list_cons.comp (a.pair b) (.const [])))).to₂
end P455WriterGuard
