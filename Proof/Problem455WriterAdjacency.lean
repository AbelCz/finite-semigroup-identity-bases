import Problem455WriterTileRec

namespace P455WriterTiles
open P455PaddedTiles

namespace RawTile
def left (p : TileData) := p.1
def right (p : TileData) := p.2.1
def top (p : TileData) := p.2.2.1
def bottom (p : TileData) := p.2.2.2.1
def oddRow (p : TileData) := p.2.2.2.2.1
def oddColumn (p : TileData) := p.2.2.2.2.2.1
def l (p : TileData) := p.2.2.2.2.2.2.1
def c (p : TileData) := p.2.2.2.2.2.2.2.1
def r (p : TileData) := p.2.2.2.2.2.2.2.2.1
def b (p : TileData) := p.2.2.2.2.2.2.2.2.2
theorem leftRec : Primrec left := Primrec.fst
theorem rightRec : Primrec right := (Primrec.fst).comp Primrec.snd
theorem topRec : Primrec top := ((Primrec.fst).comp Primrec.snd).comp Primrec.snd
theorem bottomRec : Primrec bottom := (((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
theorem oddRowRec : Primrec oddRow := ((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
theorem oddColumnRec : Primrec oddColumn := (((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
theorem lRec : Primrec l := ((((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
theorem cRec : Primrec c := (((((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
theorem rRec : Primrec r := ((((((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
theorem bRec : Primrec b := ((((((((Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
end RawTile

def across (p q : TileData) : Prop :=
  RawTile.right p=false ∧ RawTile.left q=false ∧ RawTile.top p=RawTile.top q ∧ RawTile.bottom p=RawTile.bottom q ∧
  RawTile.oddRow p=RawTile.oddRow q ∧ RawTile.oddColumn p≠RawTile.oddColumn q ∧
  RawTile.l q=RawTile.c p+1 ∧ RawTile.r p=RawTile.c q+1

def down (p q : TileData) : Prop :=
  RawTile.bottom p=false ∧ RawTile.top q=false ∧ RawTile.left p=RawTile.left q ∧ RawTile.right p=RawTile.right q ∧
  RawTile.oddColumn p=RawTile.oddColumn q ∧ RawTile.oddRow p≠RawTile.oddRow q ∧ RawTile.b p=RawTile.c q

instance acrossDec (p q : TileData) : Decidable (across p q) := by unfold across; infer_instance
instance downDec (p q : TileData) : Decidable (down p q) := by unfold down; infer_instance

private theorem asSome (u : Option (Fin n)) (v : Fin n) : letter u = v.val+1 ↔ u=some v := by
  cases u <;> simp [letter,Fin.ext_iff]

theorem across_correct (p q : Tile n) : across (raw p) (raw q) ↔ Horizontal p q := by
  simp only [across,Horizontal,raw,RawTile.right,RawTile.left,RawTile.top,RawTile.bottom,RawTile.oddRow,
    RawTile.oddColumn,RawTile.l,RawTile.c,RawTile.r,asSome]

theorem down_correct (p q : Tile n) : down (raw p) (raw q) ↔ Vertical p q := by
  simp only [down,Vertical,raw,RawTile.left,RawTile.right,RawTile.top,RawTile.bottom,RawTile.oddRow,
    RawTile.oddColumn,RawTile.b,RawTile.c,Fin.ext_iff]

def pairTest (R : TileData → TileData → Bool) (n : Nat) (s t : List Bool) :=
  (pool n).any fun p => (pool n).any fun q => decide (rawCode n p=s) && decide (rawCode n q=t) && R p q

theorem pairTest_correct (R : TileData → TileData → Bool) (X : Tile n → Tile n → Prop)
    (correct : ∀ p q, R (raw p) (raw q)=true ↔ X p q) (s t) :
    pairTest R n s t = true ↔ ∃ p q, code p=s ∧ code q=t ∧ X p q := by
  simp only [pairTest,←map_raw,List.any_eq_true,List.mem_map,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨_,⟨p,_,rfl⟩,_,⟨q,_,rfl⟩,⟨ps,qt⟩,h⟩
    exact ⟨p,q,ps,qt,(correct p q).mp h⟩
  · rintro ⟨p,q,ps,qt,h⟩
    exact ⟨_,⟨p,(P455Enum.tiles n).mem p,rfl⟩,_,⟨q,(P455Enum.tiles n).mem q,rfl⟩,⟨ps,qt⟩,(correct p q).mpr h⟩

def horizontal (n : Nat) (s t : List Bool) := pairTest (fun p q => decide (across p q)) n s t
def vertical (n : Nat) (s t : List Bool) := pairTest (fun p q => decide (down p q)) n s t

theorem horizontal_correct (n s t) : horizontal n s t=true ↔ (system n).horizontal s t :=
  pairTest_correct _ _ (fun p q=>by simpa using across_correct p q) s t
theorem vertical_correct (n s t) : vertical n s t=true ↔ (system n).vertical s t :=
  pairTest_correct _ _ (fun p q=>by simpa using down_correct p q) s t


open RawTile in
theorem acrossRec : Primrec₂ (fun p q => decide (across p q)) := by
  exact PrimrecPred.and (Primrec.eq.comp (rightRec.comp Primrec.fst) (.const false)) <|
      PrimrecPred.and (Primrec.eq.comp (leftRec.comp Primrec.snd) (.const false)) <|
      PrimrecPred.and (Primrec.eq.comp (topRec.comp Primrec.fst) (topRec.comp Primrec.snd)) <|
      PrimrecPred.and (Primrec.eq.comp (bottomRec.comp Primrec.fst) (bottomRec.comp Primrec.snd)) <|
      PrimrecPred.and (Primrec.eq.comp (oddRowRec.comp Primrec.fst) (oddRowRec.comp Primrec.snd)) <|
      PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp (oddColumnRec.comp Primrec.fst) (oddColumnRec.comp Primrec.snd))) <|
      PrimrecPred.and (Primrec.eq.comp (lRec.comp Primrec.snd) (Primrec.succ.comp (cRec.comp Primrec.fst)))
        (Primrec.eq.comp (rRec.comp Primrec.fst) (Primrec.succ.comp (cRec.comp Primrec.snd)))

open RawTile in
theorem downRec : Primrec₂ (fun p q => decide (down p q)) := by
  exact PrimrecPred.and (Primrec.eq.comp (bottomRec.comp Primrec.fst) (.const false)) <|
      PrimrecPred.and (Primrec.eq.comp (topRec.comp Primrec.snd) (.const false)) <|
      PrimrecPred.and (Primrec.eq.comp (leftRec.comp Primrec.fst) (leftRec.comp Primrec.snd)) <|
      PrimrecPred.and (Primrec.eq.comp (rightRec.comp Primrec.fst) (rightRec.comp Primrec.snd)) <|
      PrimrecPred.and (Primrec.eq.comp (oddColumnRec.comp Primrec.fst) (oddColumnRec.comp Primrec.snd)) <|
      PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp (oddRowRec.comp Primrec.fst) (oddRowRec.comp Primrec.snd))) <|
      Primrec.eq.comp (bRec.comp Primrec.fst) (cRec.comp Primrec.snd)

theorem pairTestRec {A : Type} [Primcodable A] {R : TileData → TileData → Bool} (rel : Primrec₂ R)
    {n : A → Nat} {s t : A → List Bool} (hn : Primrec n) (hs : Primrec s) (ht : Primrec t) :
    Primrec fun a => pairTest R (n a) (s a) (t a) := by
  apply P455GraphPrim.anyB (poolRec.comp hn)
  apply Primrec₂.mk
  apply P455GraphPrim.anyB (poolRec.comp (hn.comp Primrec.fst))
  apply Primrec₂.mk
  have g := Primrec.fst (α := A) (β := TileData) |>.comp (Primrec.fst (β := TileData))
  have p : Primrec fun a : (A×TileData)×TileData => a.1.2 := Primrec.snd.comp Primrec.fst
  have q : Primrec fun a : (A×TileData)×TileData => a.2 := Primrec.snd
  exact Primrec.and.comp (Primrec.and.comp
    (Primrec.eq.comp (rawCodeRec.comp (hn.comp g) p) (hs.comp g))
    (Primrec.eq.comp (rawCodeRec.comp (hn.comp g) q) (ht.comp g))) (rel.comp p q)

theorem horizontalRec {A : Type} [Primcodable A] {n : A → Nat} {s t : A → List Bool}
    (hn : Primrec n) (hs : Primrec s) (ht : Primrec t) :
    Primrec fun a => horizontal (n a) (s a) (t a) := pairTestRec acrossRec hn hs ht

theorem verticalRec {A : Type} [Primcodable A] {n : A → Nat} {s t : A → List Bool}
    (hn : Primrec n) (hs : Primrec s) (ht : Primrec t) :
    Primrec fun a => vertical (n a) (s a) (t a) := pairTestRec downRec hn hs ht

end P455WriterTiles
