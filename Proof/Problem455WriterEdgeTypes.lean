import Problem455WriterTiles

namespace P455WriterEdge
open P455Witness
variable {X : Type} [Primcodable X]

def nodeCode : Node ≃ Nat × Nat × List Bool where
  toFun x := (x.owner,x.mate,x.tag)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by rintro ⟨owner,mate,tag⟩; rfl
instance : Primcodable Node := Primcodable.ofEquiv _ nodeCode
theorem nodeCodeRec : Primrec nodeCode := Primrec.of_equiv
theorem ownerRec : Primrec Node.owner := (Primrec.fst.comp nodeCodeRec)
theorem mateRec : Primrec Node.mate := (Primrec.fst.comp (Primrec.snd.comp nodeCodeRec))
theorem tagRec : Primrec Node.tag := (Primrec.snd.comp (Primrec.snd.comp nodeCodeRec))
theorem mkNodeRec {x0 : X → Nat} {x1 : X → Nat} {x2 : X → List Bool}
    (h0 : Primrec x0) (h1 : Primrec x1) (h2 : Primrec x2) :
    Primrec (fun u => Node.mk (x0 u) (x1 u) (x2 u)) :=
  (Primrec.of_equiv_symm (e:=nodeCode)).comp (h0.pair (h1.pair h2))

def dirCode : Dir ≃ Bool × Bool where
  toFun | .right => (false,false) | .left => (false,true) | .down => (true,false) | .up => (true,true)
  invFun | (false,false) => .right | (false,true) => .left | (true,false) => .down | (true,true) => .up
  left_inv := by intro d; cases d <;> rfl
  right_inv := by rintro ⟨a,b⟩; cases a <;> cases b <;> rfl
instance : Primcodable Dir := Primcodable.ofEquiv _ dirCode
theorem dirCodeRec : Primrec dirCode := Primrec.of_equiv

def funcCode : FunctionalityCertificate ≃ Node × Bool × Node × Node × Dir × Bool where
  toFun x := (x.anchor,x.bit,x.b,x.c,x.dir,x.distinguishMate)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by rintro ⟨anchor,bit,b,c,dir,distinguishMate⟩; rfl
instance : Primcodable FunctionalityCertificate := Primcodable.ofEquiv _ funcCode
theorem funcCodeRec : Primrec funcCode := Primrec.of_equiv
theorem funcAnchorRec : Primrec FunctionalityCertificate.anchor := (Primrec.fst.comp funcCodeRec)
theorem funcBitRec : Primrec FunctionalityCertificate.bit := (Primrec.fst.comp (Primrec.snd.comp funcCodeRec))
theorem funcBRec : Primrec FunctionalityCertificate.b := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp funcCodeRec)))
theorem funcCRec : Primrec FunctionalityCertificate.c := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp funcCodeRec))))
theorem funcDirRec : Primrec FunctionalityCertificate.dir := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp funcCodeRec)))))
theorem funcDistinguishMateRec : Primrec FunctionalityCertificate.distinguishMate := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp funcCodeRec)))))
theorem mkFuncRec {x0 : X → Node} {x1 : X → Bool} {x2 : X → Node} {x3 : X → Node} {x4 : X → Dir} {x5 : X → Bool}
    (h0 : Primrec x0) (h1 : Primrec x1) (h2 : Primrec x2) (h3 : Primrec x3) (h4 : Primrec x4) (h5 : Primrec x5) :
    Primrec (fun u => FunctionalityCertificate.mk (x0 u) (x1 u) (x2 u) (x3 u) (x4 u) (x5 u)) :=
  (Primrec.of_equiv_symm (e:=funcCode)).comp (h0.pair (h1.pair (h2.pair (h3.pair (h4.pair h5)))))

def edgeCode : EdgeCertificate ≃ Node × Node × Node × Node × Node × Node × Node where
  toFun x := (x.a,x.b,x.right,x.left,x.down,x.up,x.diagonal)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by rintro ⟨a,b,right,left,down,up,diagonal⟩; rfl
instance : Primcodable EdgeCertificate := Primcodable.ofEquiv _ edgeCode
theorem edgeCodeRec : Primrec edgeCode := Primrec.of_equiv
theorem edgeARec : Primrec EdgeCertificate.a := (Primrec.fst.comp edgeCodeRec)
theorem edgeBRec : Primrec EdgeCertificate.b := (Primrec.fst.comp (Primrec.snd.comp edgeCodeRec))
theorem edgeRightRec : Primrec EdgeCertificate.right := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp edgeCodeRec)))
theorem edgeLeftRec : Primrec EdgeCertificate.left := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp edgeCodeRec))))
theorem edgeDownRec : Primrec EdgeCertificate.down := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp edgeCodeRec)))))
theorem edgeUpRec : Primrec EdgeCertificate.up := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp edgeCodeRec))))))
theorem edgeDiagonalRec : Primrec EdgeCertificate.diagonal := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp edgeCodeRec))))))
theorem mkEdgeRec {x0 : X → Node} {x1 : X → Node} {x2 : X → Node} {x3 : X → Node} {x4 : X → Node} {x5 : X → Node} {x6 : X → Node}
    (h0 : Primrec x0) (h1 : Primrec x1) (h2 : Primrec x2) (h3 : Primrec x3) (h4 : Primrec x4) (h5 : Primrec x5) (h6 : Primrec x6) :
    Primrec (fun u => EdgeCertificate.mk (x0 u) (x1 u) (x2 u) (x3 u) (x4 u) (x5 u) (x6 u)) :=
  (Primrec.of_equiv_symm (e:=edgeCode)).comp (h0.pair (h1.pair (h2.pair (h3.pair (h4.pair (h5.pair h6))))))

theorem poolRec {w : X → List Nat} {ts : X → List (List Bool)} (hw : Primrec w) (ht : Primrec ts) :
    Primrec (fun x => P455CatalogueBounds.pool (w x) (ts x)) := by
  apply Primrec.list_flatMap hw
  apply Primrec₂.mk
  apply Primrec.list_flatMap (hw.comp Primrec.fst)
  apply Primrec₂.mk
  apply Primrec.list_map (ht.comp (Primrec.fst.comp Primrec.fst))
  exact (mkNodeRec (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

end P455WriterEdge
