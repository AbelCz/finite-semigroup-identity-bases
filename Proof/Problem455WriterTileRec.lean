import Problem455WriterTiles

namespace P455WriterTiles
open P455PaddedTiles
variable {A : Type} [Primcodable A]

theorem replicateRec {B : Type} [Primcodable B] {n : A → Nat} {v : A → B}
    (hn : Primrec n) (hv : Primrec v) : Primrec fun a => List.replicate (n a) (v a) :=
  (Primrec.list_map (Primrec.list_range.comp hn) (hv.comp Primrec.fst).to₂).of_eq
    (fun a => by simp [List.map_const'])

theorem tokenRec {n k : A → Nat} (hn : Primrec n) (hk : Primrec k) :
    Primrec fun a => tokenN (n a) (k a) :=
  Primrec.list_append.comp (replicateRec hk (.const true))
    (replicateRec (Primrec.nat_sub.comp (Primrec.succ.comp hn) hk) (.const false))

theorem rawCodeRec : Primrec₂ rawCode := by
  let A := Nat × TileData
  have n : Primrec fun a : A => a.1 := Primrec.fst
  have t := Primrec.snd (α := Nat) (β := TileData)
  have t1 := Primrec.snd.comp t
  have t2 := Primrec.snd.comp t1
  have t3 := Primrec.snd.comp t2
  have t4 := Primrec.snd.comp t3
  have t5 := Primrec.snd.comp t4
  have t6 := Primrec.snd.comp t5
  have t7 := Primrec.snd.comp t6
  have t8 := Primrec.snd.comp t7
  apply Primrec₂.mk
  apply Primrec.list_cons.comp (Primrec.fst.comp t)
  apply Primrec.list_cons.comp (Primrec.fst.comp t1)
  apply Primrec.list_cons.comp (Primrec.fst.comp t2)
  apply Primrec.list_cons.comp (Primrec.fst.comp t3)
  apply Primrec.list_cons.comp (Primrec.fst.comp t4)
  apply Primrec.list_cons.comp (Primrec.fst.comp t5)
  exact Primrec.list_append.comp (tokenRec n (Primrec.fst.comp t6))
    (Primrec.list_append.comp (tokenRec n (Primrec.succ.comp (Primrec.fst.comp t7)))
      (Primrec.list_append.comp (tokenRec n (Primrec.fst.comp t8)) (tokenRec n (Primrec.succ.comp (Primrec.snd.comp t8)))))

theorem impliesRec {p q : A → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a => p a → q a := by
  apply (PrimrecPred.or (PrimrecPred.not hp) hq).of_eq
  intro a
  simp [imp_iff_not_or]

theorem eligibleRec : Primrec₂ (fun d t => decide (eligible d t)) := by
  let A := MachineData × TileData
  have d := Primrec.fst (α := MachineData) (β := TileData)
  have v := Primrec.snd.comp d
  have v2 := Primrec.snd.comp v
  have v3 := Primrec.snd.comp v2
  have v4 := Primrec.snd.comp v3
  have n := Primrec.fst.comp d
  have t := Primrec.snd (α := MachineData) (β := TileData)
  have t1 := Primrec.snd.comp t
  have t2 := Primrec.snd.comp t1
  have t3 := Primrec.snd.comp t2
  have t4 := Primrec.snd.comp t3
  have t5 := Primrec.snd.comp t4
  have t6 := Primrec.snd.comp t5
  have t7 := Primrec.snd.comp t6
  have t8 := Primrec.snd.comp t7
  have leftFlag := Primrec.fst.comp t
  have rightFlag := Primrec.fst.comp t1
  have top := Primrec.fst.comp t2
  have bottom := Primrec.fst.comp t3
  have row := Primrec.fst.comp t4
  have col := Primrec.fst.comp t5
  have l := Primrec.fst.comp t6
  have c := Primrec.fst.comp t7
  have r := Primrec.fst.comp t8
  have b := Primrec.snd.comp t8
  let L (x : A) := x.2.1 = true
  have hl : PrimrecPred L := Primrec.eq.comp leftFlag (.const true)
  have init := Primrec.ite hl (Primrec.fst.comp v3) (Primrec.fst.comp v2)
  have ix := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp l n) c)
    (Primrec.succ.comp n)) r
  have next := Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp v4) ix) (.const none)
  have mark := Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp v) c) (.const false)
  apply Primrec₂.mk
  unfold eligible
  exact PrimrecPred.and (Primrec.eq.comp next (Primrec.option_some.comp b)) <|
    PrimrecPred.and (Primrec.eq.comp leftFlag (Primrec.eq.comp l (.const 0))) <|
    PrimrecPred.and (Primrec.eq.comp rightFlag (Primrec.eq.comp r (.const 0))) <|
    PrimrecPred.and (Primrec.eq.comp mark leftFlag) <|
    PrimrecPred.and (impliesRec hl (Primrec.eq.comp col (.const false))) <|
    PrimrecPred.and (impliesRec (Primrec.eq.comp top (.const true))
      (PrimrecPred.and (Primrec.eq.comp row (.const false)) (Primrec.eq.comp c init)))
      (impliesRec (Primrec.eq.comp bottom (.const true)) (impliesRec hl (Primrec.eq.comp c (Primrec.fst.comp v4))))

theorem tagsRec : Primrec tags :=
  Primrec.list_map (P455GraphPrim.filter (poolRec.comp Primrec.fst) eligibleRec)
    (rawCodeRec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

end P455WriterTiles
