import Problem455RealizerClass
import Problem455EffectiveQRaw
namespace P455RowsPrim
open P455EffectiveQ P455GraphPrim P455ClassPrim
open P455EffectiveQRaw (distinctRaw labels index rows)
variable {A B : Type} [Primcodable A] [Primcodable B]
theorem distinct {r : A → Raw → Raw → Bool}
    (hr : Primrec fun p : A×(Raw×Raw) => r p.1 p.2.1 p.2.2) {l : A → List Raw} (hl : Primrec l) :
    Primrec fun a => distinctRaw (r a) (l a) := by
  let h (a : A) (s : Raw × List Raw × List Raw) :=
    if s.2.1.any (r a s.1) then s.2.2 else s.1::s.2.2
  have hh : Primrec₂ h := by
    apply Primrec₂.mk
    apply Primrec.ite
    · change PrimrecPred (fun p : A×(Raw×List Raw×List Raw) => (p.2.2.1.any (r p.1 p.2.1))=true)
      have any := anyB (A := A × (Raw × List Raw × List Raw)) (B := Raw) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        ((hr.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))).to₂)
      exact Primrec.eq.comp any (.const true)
    · exact Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  apply (Primrec.list_rec hl (Primrec.const []) hh).of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons x xs ih =>
    change h a (x,xs,_) = _
    exact congrArg (fun acc => h a (x,xs,acc)) ih

theorem labelRec {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {t : A → W} (ht : Primrec t) : Primrec fun a => labels (e a) (t a) := by
  apply distinct (r := fun a => relB (e a) (t a))
  · exact relation (A := A×(Raw×Raw)) (e := fun p => e p.1)
      (he.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (ht.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  · exact Primrec.list_cons.comp (.const none)
      (Primrec.list_map (wordPool.comp ht) (Primrec.option_some.comp₂ Primrec₂.right))

theorem indexRec {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {t : A → W} {v : A → Raw} (ht : Primrec t) (hv : Primrec v) :
    Primrec fun a => index (e a) (t a) (v a) := by
  apply Primrec.list_findIdx (labelRec he ht)
  exact (relation (A := A×Raw) (e := fun p => e p.1)
      (he.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (ht.comp Primrec.fst) (hv.comp Primrec.fst) Primrec.snd).to₂

theorem rawMul : Primrec₂ (fun x y : Raw => (show Raw from @P455Quotient.mulRaw Nat x y)) := by
  let f (p : Raw × Raw) (u : W) := p.2.map (fun v => u++v)
  have rec : Primrec₂ f := Primrec₂.mk <|
    Primrec.option_map (Primrec.snd.comp Primrec.fst)
      ((Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  apply (Primrec.option_bind (Primrec.fst (α := Raw) (β := Raw)) rec).of_eq
  rintro ⟨x,y⟩
  cases x <;> cases y <;> rfl

theorem rowsRec {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {t : A → W} (ht : Primrec t) : Primrec fun a => rows (e a) (t a) := by
  apply Primrec.list_map (labelRec he ht)
  apply Primrec₂.mk
  apply Primrec.list_map ((labelRec he ht).comp Primrec.fst)
  apply Primrec₂.mk
  exact indexRec (A := (A×Raw)×Raw) (e := fun p => e p.1.1)
    (he.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
    (ht.comp (Primrec.fst.comp Primrec.fst))
    (rawMul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
end P455RowsPrim
