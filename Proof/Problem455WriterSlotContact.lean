import Problem455WriterSlotTypes
import Problem455WriterQueryLeaves
namespace P455WriterSlots
open P455Witness (Tag Holds Marking ContactChoice)
open P455WriterQueryLeaves P455WriterProfiles Problem455.Slots

def portTest (e : Env) (a b : Nat) (p : Fin 5) (rev : Bool) :=
  let i := 3+2*p.val
  let x := if rev then b else a
  let y := if rev then a else b
  decide (a≠b ∧ e.2.2.2.count a=e.1 ∧ e.2.2.2.count b=e.1) && earlyDisjoint e [a] [b] &&
    order e [(x,i),(y,i),(x,i+1),(y,i+1)]

def contact (e : Env) (a b : Nat) : ContactChoice → Bool
  | .record t v => if v then record e b a t else record e a b t
  | .port p v => portTest e a b p v

theorem contact_ok {e : Env} {r : Nat} {allow : Tag → Prop} {mark : Marking} {w : W}
    (h : ModelsEnv e r allow mark w) (a b c) :
    contact e a b c=true ↔ Holds r allow mark w (P455Witness.contact r a b c) := by
  cases c with
  | record t v => cases v <;> simp [contact,P455Witness.contact,record_ok h]
  | port p v =>
    simp [contact,portTest,P455Witness.contact,Bool.and_eq_true,earlyDisjoint_ok h,order_ok h,
      h.lim,h.word,P455Witness.allQ,Holds,and_assoc]

variable {A : Type} [Primcodable A]

theorem portRec {e : A → Env} {a b : A → Nat} {p : A → Fin 5} {v : A → Bool}
    (he : Primrec e) (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hv : Primrec v) :
    Primrec fun x => portTest (e x) (a x) (b x) (p x) (v x) := by
  have i := Primrec.nat_add.comp (.const 3) (Primrec.nat_mul.comp (.const 2) (Primrec.fin_val.comp hp))
  have cond := Primrec.eq.comp hv (.const true)
  have x := Primrec.ite cond hb ha
  have y := Primrec.ite cond ha hb
  let cons := @Primrec.list_cons Event _
  have pat := cons.comp (x.pair i) (cons.comp (y.pair i)
    (cons.comp (x.pair (Primrec.succ.comp i)) (cons.comp (y.pair (Primrec.succ.comp i)) (.const []))))
  exact Primrec.and.comp (Primrec.and.comp (PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp ha hb))
      (PrimrecPred.and (Primrec.eq.comp (P455CataloguePrim.count'.comp (wordRec he) ha) (limRec he))
        (Primrec.eq.comp (P455CataloguePrim.count'.comp (wordRec he) hb) (limRec he))))
    (earlyDisjointRec he (Primrec.list_cons.comp ha (.const [])) (Primrec.list_cons.comp hb (.const [])))) (orderRec he pat)

theorem contactRec {e : A → Env} {a b : A → Nat} {c : A → ContactChoice}
    (he : Primrec e) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec fun x => contact (e x) (a x) (b x) (c x) := by
  let f (x : A) (p : Tag × Bool) := if p.2 then record (e x) (b x) (a x) p.1 else record (e x) (a x) (b x) p.1
  have hf : Primrec₂ f := Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (.const true))
    (recordRec (he.comp Primrec.fst) (hb.comp Primrec.fst) (ha.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (recordRec (he.comp Primrec.fst) (ha.comp Primrec.fst) (hb.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  let g (x : A) (p : Fin 5 × Bool) := portTest (e x) (a x) (b x) p.1 p.2
  have hg : Primrec₂ g := portRec (he.comp Primrec.fst) (ha.comp Primrec.fst) (hb.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  apply (Primrec.sumCasesOn (contactCodeRec.comp hc) hf hg).of_eq
  intro x
  cases c x <;> rfl

end P455WriterSlots
