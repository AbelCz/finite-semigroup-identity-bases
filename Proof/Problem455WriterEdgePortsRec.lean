import Problem455WriterEdgePorts

set_option maxHeartbeats 30000
namespace P455WriterEdge
open P455Witness P455PaddedTiles P455WriterQueryLeaves
variable {A : Type} [Primcodable A]

theorem rolesRec : Primrec roles :=
  Primrec.list_cons.comp ownerRec (Primrec.list_cons.comp mateRec (.const []))

theorem order2Rec {e : A→Env} {a i b j : A→Nat} (he : Primrec e) (ha : Primrec a) (hi : Primrec i)
    (hb : Primrec b) (hj : Primrec j) : Primrec fun x => order2 (e x) (a x) (i x) (b x) (j x) :=
  orderRec he (Primrec.list_cons.comp (ha.pair hi) (Primrec.list_cons.comp (hb.pair hj) (.const [])))

theorem nodeRecordRec {e : A→Env} {a : A→Node} (he : Primrec e) (ha : Primrec a) :
    Primrec fun x => nodeRecord (e x) (a x) := recordRec he (ownerRec.comp ha) (mateRec.comp ha) (tagRec.comp ha)
theorem nodeMarkedRec {e : A→Env} {a : A→Node} {v : A→Bool} (he : Primrec e) (ha : Primrec a) (hv : Primrec v) :
    Primrec fun x => nodeMarked (e x) (a x) (v x) := markedRec he (ownerRec.comp ha) (mateRec.comp ha) (tagRec.comp ha) hv

theorem portRec {e : A→Env} {p : A→Nat} {a b : A→Node} (he : Primrec e) (hp : Primrec p) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => port (e x) (p x) (a x) (b x) := by
  have i := Primrec.nat_add.comp (.const 3) (Primrec.nat_mul.comp (.const 2) hp)
  have j := Primrec.nat_add.comp i (.const 1)
  have u := ownerRec.comp ha; have v := mateRec.comp ha; have y := ownerRec.comp hb; have z := mateRec.comp hb
  let cons := @Primrec.list_cons (Nat × Nat) _
  have upper := cons.comp (u.pair j) (cons.comp (v.pair j) (cons.comp (y.pair j) (cons.comp (z.pair j) (.const []))))
  have pat := cons.comp (u.pair i) (cons.comp (v.pair i) (cons.comp (y.pair i) (cons.comp (z.pair i) upper)))
  exact Primrec.and.comp (nodeRecordRec he ha) (Primrec.and.comp (nodeRecordRec he hb) (Primrec.and.comp
    (earlyDisjointRec he (rolesRec.comp ha) (rolesRec.comp hb)) (orderRec he pat)))

theorem flagRec (i : Nat) {a : A→Node} (ha : Primrec a) : Primrec fun x => (a x).tag[i]?.getD false :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (tagRec.comp ha) (.const i)) (.const false)

theorem rightRec {e : A→Env} {n : A→Nat} {a b : A→Node} (he : Primrec e) (hn : Primrec n) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => rightB (e x) (n x) (a x) (b x) := by
  have t := tagRec.comp ha
  have i := Primrec.nat_add.comp (.const 13) (Primrec.list_length.comp t)
  exact Primrec.and.comp (P455WriterTiles.horizontalRec hn t (tagRec.comp hb)) (Primrec.and.comp
    (portRec he (Primrec.ite (Primrec.eq.comp (flagRec 5 ha) (.const true)) (.const 1) (.const 0)) ha hb)
    (order2Rec he (ownerRec.comp ha) i (ownerRec.comp hb) i))

theorem downRec {e : A→Env} {n : A→Nat} {a b : A→Node} (he : Primrec e) (hn : Primrec n) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => downB (e x) (n x) (a x) (b x) := Primrec.and.comp
    (P455WriterTiles.verticalRec hn (tagRec.comp ha) (tagRec.comp hb))
    (portRec he (Primrec.ite (Primrec.eq.comp (flagRec 4 ha) (.const true)) (.const 3) (.const 2)) ha hb)

def selectDir (d : Dir) (rt lt dn up : Bool) :=
  bif (dirCode d).1 then (bif (dirCode d).2 then up else dn) else (bif (dirCode d).2 then lt else rt)

theorem chosenDir (e : Env) (n : Nat) (a b : Node) (d : Dir) :
    selectDir d (rightB e n a b) (rightB e n b a) (downB e n a b) (downB e n b a)=neighborB e n a b d := by
  cases d <;> simp only [selectDir,dirCode,Equiv.coe_fn_mk,cond_true,cond_false,neighborB]

theorem neighborRec {e : A→Env} {n : A→Nat} {a b : A→Node} {d : A→Dir}
    (he : Primrec e) (hn : Primrec n) (ha : Primrec a) (hb : Primrec b) (hd : Primrec d) :
    Primrec fun x => neighborB (e x) (n x) (a x) (b x) (d x) := by
  have pair := dirCodeRec.comp hd
  have test : Primrec (fun x => selectDir (d x) (rightB (e x) (n x) (a x) (b x)) (rightB (e x) (n x) (b x) (a x))
       (downB (e x) (n x) (a x) (b x)) (downB (e x) (n x) (b x) (a x))) :=
    Primrec.cond (Primrec.fst.comp pair)
      (Primrec.cond (Primrec.snd.comp pair) (downRec he hn hb ha) (downRec he hn ha hb))
      (Primrec.cond (Primrec.snd.comp pair) (rightRec he hn hb ha) (rightRec he hn ha hb))
  exact test.of_eq (fun x => chosenDir (e x) (n x) (a x) (b x) (d x))

theorem roleRec {b : A→Bool} {a : A→Node} (hb : Primrec b) (ha : Primrec a) :
    Primrec fun x => role (b x) (a x) := Primrec.ite (Primrec.eq.comp hb (.const true)) (mateRec.comp ha) (ownerRec.comp ha)

theorem funcRec {e : A→Env} {n : A→Nat} {f : A→FunctionalityCertificate} (he : Primrec e) (hn : Primrec n) (hf : Primrec f) :
    Primrec fun x => funcB (e x) (n x) (f x) := by
  have a := funcAnchorRec.comp hf; have b := funcBRec.comp hf; have c := funcCRec.comp hf
  have d := funcDirRec.comp hf; have v := funcDistinguishMateRec.comp hf
  exact Primrec.and.comp (nodeMarkedRec he a (funcBitRec.comp hf)) (Primrec.and.comp (neighborRec he hn a b d)
    (Primrec.and.comp (neighborRec he hn a c d) (separateRec he (roleRec v b) (roleRec v c))))

theorem funcAcceptRec {e : A→Env} {n a b : A→Nat} (he : Primrec e) (hn : Primrec n) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => funcAccept (e x) (n x) (a x) (b x) := by
  have F := Primrec.snd (α:=A) (β:=FunctionalityCertificate)
  have anc := funcAnchorRec.comp F
  exact P455GraphPrim.anyB (functionalitiesRec (wordRec he) (tagsRec he)) (Primrec.and.comp
    ((Primrec.eq.comp (ownerRec.comp anc) (ha.comp Primrec.fst)).and (Primrec.eq.comp (mateRec.comp anc) (hb.comp Primrec.fst)))
    (funcRec (he.comp Primrec.fst) (hn.comp Primrec.fst) F)).to₂

end P455WriterEdge
