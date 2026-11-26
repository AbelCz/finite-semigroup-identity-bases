import Problem455WriterEdgeTests
import Problem455WriterEdgePortsRec

set_option maxHeartbeats 30000
namespace P455WriterEdge
open P455Witness P455PaddedTiles P455WriterQueryLeaves
variable {A : Type} [Primcodable A]

theorem whenRec {b p : A→Bool} (hb : Primrec b) (hp : Primrec p) : Primrec fun x => whenB (b x) (p x) :=
  Primrec.ite (Primrec.eq.comp hb (.const true)) hp (.const true)

theorem localRec {v : A→Env} {n : A→Nat} {f : A→EdgeCertificate} (hv : Primrec v) (hn : Primrec n) (hf : Primrec f) :
    Primrec fun x => localB (v x) (n x) (f x) := by
  have a := edgeARec.comp hf; have rt := edgeRightRec.comp hf; have dn := edgeDownRec.comp hf; have di := edgeDiagonalRec.comp hf
  have rightActive := Primrec.not.comp (flagRec 1 a); have bottom := Primrec.not.comp (flagRec 3 a)
  exact Primrec.and.comp (whenRec rightActive (rightRec hv hn a rt)) <|
    Primrec.and.comp (whenRec (Primrec.not.comp (flagRec 0 a)) (rightRec hv hn (edgeLeftRec.comp hf) a)) <|
    Primrec.and.comp (whenRec bottom (downRec hv hn a dn)) <|
    Primrec.and.comp (whenRec (Primrec.not.comp (flagRec 2 a)) (downRec hv hn (edgeUpRec.comp hf) a))
    (whenRec (Primrec.and.comp rightActive bottom) (Primrec.and.comp (downRec hv hn rt di) (rightRec hv hn dn di)))

theorem chosenRec {v : A→Env} {n : A→Nat} {f : A→EdgeCertificate} (hv : Primrec v) (_hn : Primrec n) (hf : Primrec f) :
    Primrec fun x => chosenB (v x) (n x) (f x) := by
  have a := edgeARec.comp hf; have b := edgeBRec.comp hf
  have odd := Primrec.eq.comp (flagRec 4 a) (.const true)
  have last := Primrec.ite odd (flagRec 0 a) (flagRec 1 a)
  have next := Primrec.ite (Primrec.eq.comp last (.const true)) (edgeDownRec.comp hf) (Primrec.ite odd (edgeLeftRec.comp hf) (edgeRightRec.comp hf))
  have corner := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (flagRec 2 b) (flagRec 0 b))
    (Primrec.not.comp (flagRec 4 b))) (Primrec.not.comp (flagRec 5 b))
  exact Primrec.ite (Primrec.eq.comp (Primrec.and.comp last (flagRec 3 a)) (.const true))
    (Primrec.and.comp corner (Primrec.and.comp (Primrec.or.comp (portRec hv (.const 4) a b) (portRec hv (.const 4) b a))
      (order2Rec hv (ownerRec.comp b) (.const 0) (ownerRec.comp a) (.const 0))))
    (Primrec.and.comp (Primrec.eq.comp next b) (order2Rec hv (ownerRec.comp a) (.const 0) (ownerRec.comp b) (.const 0)))

theorem queryRec {v : A→Env} {n : A→Nat} {f : A→EdgeCertificate} (hv : Primrec v) (hn : Primrec n) (hf : Primrec f) :
    Primrec fun x => queryB (v x) (n x) (f x) :=
  Primrec.and.comp (nodeMarkedRec hv (edgeARec.comp hf) (.const true)) (Primrec.and.comp
    (nodeMarkedRec hv (edgeBRec.comp hf) (.const false)) (Primrec.and.comp (localRec hv hn hf) (chosenRec hv hn hf)))

theorem namesRec {n : A→Nat} {f : A→EdgeCertificate} (_hn : Primrec n) (hf : Primrec f) :
    Primrec fun x => P455EdgeProjection.names (system (n x)) (f x) := by
  have a := edgeARec.comp hf; have b := edgeBRec.comp hf
  have rightActive := Primrec.not.comp (flagRec 1 a); have bottom := Primrec.not.comp (flagRec 3 a)
  let cons := @Primrec.list_cons (Node × Bool) _
  have fin := cons.comp ((edgeDiagonalRec.comp hf).pair (Primrec.and.comp rightActive bottom)) (.const [])
  have up := cons.comp ((edgeUpRec.comp hf).pair (Primrec.not.comp (flagRec 2 a))) fin
  have down := cons.comp ((edgeDownRec.comp hf).pair bottom) up
  have leftList := cons.comp ((edgeLeftRec.comp hf).pair (Primrec.not.comp (flagRec 0 a))) down
  have rest := cons.comp ((edgeRightRec.comp hf).pair rightActive) leftList
  have candidates := cons.comp (a.pair (.const true)) (cons.comp (b.pair (.const true)) rest)
  have active := P455GraphPrim.filter candidates (Primrec.snd.comp Primrec.snd).to₂
  have nodes := Primrec.list_map active (Primrec.fst.comp Primrec.snd).to₂
  exact Primrec.list_flatMap nodes (rolesRec.comp Primrec.snd).to₂

theorem sameRec {s t : A→List Nat} (hs : Primrec s) (ht : Primrec t) : Primrec fun x => sameNames (s x) (t x) :=
  Primrec.and.comp (P455FramePrim.allB hs (memRec Primrec.snd (ht.comp Primrec.fst)).to₂)
    (P455FramePrim.allB ht (memRec Primrec.snd (hs.comp Primrec.fst)).to₂)

theorem envRec {r : A→Nat} {ts : A→List (List Bool)} {w : A→List Nat} {k : A→Quad}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) (hk : Primrec k) :
    Primrec fun x => env (r x) (ts x) (w x) (k x) := by
  have z := Primrec.snd.comp hk
  exact hr.pair (ht.pair ((Primrec.list_cons.comp ((Primrec.fst.comp hk).pair (Primrec.fst.comp z))
    (Primrec.list_cons.comp (Primrec.snd.comp z) (.const []))).pair hw))

theorem testsRec {r n : A→Nat} {ts : A→List (List Bool)} {w : A→List Nat} {k : A→Quad}
    (hr : Primrec r) (hn : Primrec n) (ht : Primrec ts) (hw : Primrec w) (hk : Primrec k) :
    Primrec fun x => tests (r x) (n x) (ts x) (w x) (k x) := by
  have p := Primrec.fst (α:=A) (β:=EdgeCertificate)
  have f := Primrec.snd (α:=A) (β:=EdgeCertificate)
  have a := edgeARec.comp f; have b := edgeBRec.comp f; have k := hk.comp p
  have z := Primrec.snd.comp k; have t := Primrec.snd.comp z
  have eqB := (Primrec.eq.comp (ownerRec.comp a) (Primrec.fst.comp k)).and <|
    (Primrec.eq.comp (mateRec.comp a) (Primrec.fst.comp z)).and <|
    (Primrec.eq.comp (ownerRec.comp b) (Primrec.fst.comp t)).and (Primrec.eq.comp (mateRec.comp b) (Primrec.snd.comp t))
  exact Primrec.and.comp (P455FrameProof.capCheck hr hw) (P455GraphPrim.anyB (certificatesRec hw ht) (Primrec.and.comp eqB
    (Primrec.and.comp (sameRec (hw.comp p) (namesRec (hn.comp p) f)) (queryRec ((envRec hr ht hw hk).comp p) (hn.comp p) f))).to₂)

theorem edgesRec {r n : A→Nat} {ts : A→List (List Bool)} (hr : Primrec r) (hn : Primrec n) (ht : Primrec ts) :
    Primrec fun x => edges (r x) (n x) (ts x) := by
  apply familyRec hr
  have p := Primrec.fst.comp (Primrec.fst (α:=A × List Nat) (β:=Quad))
  exact testsRec (hr.comp p) (hn.comp p) (ht.comp p) (Primrec.snd.comp Primrec.fst) Primrec.snd

end P455WriterEdge
