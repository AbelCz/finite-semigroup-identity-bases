import Mathlib.Computability.Partrec
import Problem455Packed
import Problem455NumericProductPrim
import Problem455RowsPrim
import Problem455LiteralMovePrim

/- Certify the actual table serializer on arbitrary first-order records.
   This theorem takes the catalogue as input. -/
namespace P455SerializePrim
open P455Packed

abbrev Tags := List (List Bool)
abbrev Marks := List (Nat × Nat)
abbrev W := List Nat
abbrev Data := Nat × Tags × List Spec × List Spec × List Spec × List Spec × List Spec

def asPayload (x : Data) : Payload :=
  ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2⟩

def ofPayload (p : Payload) : Data :=
  (p.r, p.tags, p.primitive, p.guard, p.edge, p.binary, p.structural)

theorem as_of (p : Payload) : asPayload (ofPayload p) = p := rfl

variable {A : Type} [Primcodable A]

theorem move {r : A → Nat} {tags : A → Tags} {mark : A → Option Marks} {u v : A → W}
    (hr : Primrec r) (ht : Primrec tags) (hm : Primrec mark) (hu : Primrec u) (hv : Primrec v) :
    Primrec fun a => moves (r a) (tags a) (mark a) (u a) (v a) := by
  let h (a : A) (ps : Marks) :=
    P455EffectiveQMove.moveB (r a) (tags a) (fun x y => decide ((x,y) ∈ ps)) (u a) (v a)
  have m : Primrec₂ h := Primrec₂.mk (P455FrameProof.literalMove (hr.comp Primrec.fst)
    (ht.comp Primrec.fst) Primrec.snd (hu.comp Primrec.fst) (hv.comp Primrec.fst))
  exact (Primrec.option_casesOn hm (Primrec.const false) m).of_eq (fun a => by
    cases e : mark a <;> simp [moves,e,h])

theorem factor {r : A → Nat} {tags : A → Tags} {s : A → Spec}
    (hr : Primrec r) (ht : Primrec tags) (hs : Primrec s) :
    Primrec fun a => factorRows (r a) (tags a) (s a) := by
  apply P455RowsPrim.rowsRec (e := fun a => moves (r a) (tags a) (s a).2)
  · exact move (hr.comp Primrec.fst) (ht.comp Primrec.fst) ((Primrec.snd.comp hs).comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  · exact Primrec.fst.comp hs

theorem group {r : A → Nat} {tags : A → Tags} {s : A → List Spec}
    (hr : Primrec r) (ht : Primrec tags) (hs : Primrec s) :
    Primrec fun a => P455NumericProduct.assemble ((s a).map (factorRows (r a) (tags a))) :=
  P455NumericProductPrim.assemble'.comp (Primrec.list_map hs
    (Primrec₂.mk (factor (hr.comp Primrec.fst) (ht.comp Primrec.fst) Primrec.snd)))

theorem serialize : Primrec fun x : Data => P455Packed.serialize (asPayload x) := by
  have r : Primrec fun x : Data => x.1 := Primrec.fst
  have s := Primrec.snd (α := Nat) (β := Tags × List Spec × List Spec × List Spec × List Spec × List Spec)
  have tags := Primrec.fst.comp s
  have ss := Primrec.snd.comp s
  have gs := Primrec.snd.comp ss
  have es := Primrec.snd.comp gs
  have bs := Primrec.snd.comp es
  exact P455NumericProductPrim.tensor'.comp (group r tags (Primrec.fst.comp ss))
    (P455NumericProductPrim.tensor'.comp
      (P455NumericProductPrim.tensor'.comp (group r tags (Primrec.fst.comp gs)) (group r tags (Primrec.fst.comp es)))
      (P455NumericProductPrim.tensor'.comp (group r tags (Primrec.fst.comp bs)) (group r tags (Primrec.snd.comp bs))))

theorem bits : Primrec fun x : Data => P455TableBits.encode (P455Packed.serialize (asPayload x)) :=
  P455NumericProductPrim.encode.comp serialize

theorem bits_after_catalogue {p : A → Payload} (h : Computable (fun a => ofPayload (p a))) :
    Computable (fun a => P455TableBits.encode (P455Packed.serialize (p a))) :=
  by simpa only [Function.comp_def,as_of] using bits.to_comp.comp h

end P455SerializePrim
