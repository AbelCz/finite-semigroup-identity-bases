import Problem455WriterProfiles

namespace P455WriterBinary
open P455PaddedTiles P455WriterTiles P455WriterProfiles
abbrev Key := Nat × Bool

def words (r : Nat) : List (List Nat) := Problem455Finite.wordsUpTo [0,1] (2*r)
def atKey (r i : Nat) := (words r)[i]?.getD []
def key (i : P455BinaryProduct.Index r allow) : Key := (i.num.val,i.prof)

theorem key_inj : Function.Injective (@key r allow) := by
  rintro ⟨a,b,_,_⟩ ⟨c,d,_,_⟩ e
  change (a.val,b)=(c.val,d) at e
  obtain ⟨h,rfl⟩ := Prod.mk.inj e
  cases Fin.ext h
  rfl

def tests (r : Nat) (ts : Tags) (w : W) (prof : Bool) :=
  P455EffectiveQMove.capB r w &&
    decide (w=P455FirstTesters.power r ∨ 0<w.count 0 ∧ 0<w.count 1) &&
    decide (prof = isProfile r ts w)

def filtered (r : Nat) (ts : Tags) : List Key :=
  (choices (List.range (words r).length) [false,true]).filter (fun k => tests r ts (atKey r k.1) k.2)

def spec (r : Nat) (k : Key) : P455Packed.Spec :=
  (atKey r k.1, if k.2 then some [] else none)

def bin (r : Nat) (ts : Tags) := (P455Table.distinct (filtered r ts)).map (spec r)

theorem getAt (r : Nat) (i : Fin (words r).length) : atKey r i.val = (words r).get i := by
  simp [atKey,i.isLt]

theorem valid (M : MachineTable n) (r ts) (tEq : ts = P455Enum.tags M) (w : W) (b : Bool) :
    tests r ts w b=true ↔ P455Closure.Cap r w ∧
      (w=P455FirstTesters.power r ∨ 0<w.count 0 ∧ 0<w.count 1) ∧
      (b=true ↔ P455BinaryEquality.IsProfile r (allowed M) w) := by
  subst ts
  simp only [tests,Bool.and_eq_true,decide_eq_true_eq,P455EffectiveQMove.cap_iff,
    ←P455WriterProfiles.correct M r w,and_assoc]
  cases b <;> cases isProfile r (P455Enum.tags M) w <;> simp

private theorem attachKeys {n : Nat} (xs : List (Fin n × Bool)) :
    xs.attach.map (fun x => (x.val.1.val,x.val.2)) = xs.map (fun x => (x.1.val,x.2)) :=
  @List.attach_map_val (Fin n × Bool) Key xs (fun x => (x.1.val,x.2))

theorem raw_keys {n} (M : MachineTable n) (r : Nat) :
    (P455Enum.binary r M).list.map key = filtered r (P455Enum.tags M) := by
  let X := Fin (words r).length × Bool
  let K : X → Key := fun x => (x.1.val,x.2)
  let xs := choices (P455Enum.fins (words r).length).list P455Enum.bools.list
  have order : xs.map K = choices (List.range (words r).length) [false,true] := by
    unfold xs K
    rw [←List.map_coe_finRange]
    simp only [choices,P455Enum.fins,P455Enum.bools,List.map_flatMap,List.map_map,List.flatMap_map,Function.comp_def]
  unfold filtered
  rw [←order,List.filter_map]
  unfold P455Enum.binary
  simp only [P455Enum.Cover.map,P455Enum.coverSub,P455Enum.selectSub,List.map_map,Function.comp_def,key]
  rw [attachKeys]
  apply congrArg (List.map K)
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [valid M r _ rfl]
  simp only [K,getAt,words]

theorem bin_correct (M : MachineTable n) (r : Nat) :
    bin r (P455Enum.tags M) = P455Packed.names (P455Encoded.useCover (P455Enum.binary r M)) P455Packed.binSpec := by
  unfold bin
  rw [←raw_keys,←P455CataloguePrim.map_distinct key key_inj,List.map_map]
  unfold P455Packed.names P455Encoded.useCover
  apply List.map_congr_left
  intro i _
  change (atKey r i.num.val,_) = _
  rw [getAt]
  rfl

variable {A : Type} [Primcodable A]

theorem wordsRec : Primrec words :=
  P455GraphPrim.wordsUpTo.comp (.const [0,1]) (Primrec.nat_mul.comp (.const 2) Primrec.id)

theorem atKeyRec : Primrec₂ atKey :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (wordsRec.comp Primrec.fst) Primrec.snd) (.const [])

theorem testsRec {r : A → Nat} {ts : A → Tags} {w : A → W} {b : A → Bool}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) (hb : Primrec b) :
    Primrec fun a => tests (r a) (ts a) (w a) (b a) := by
  exact Primrec.and.comp (Primrec.and.comp (P455FrameProof.capCheck hr hw)
    (PrimrecPred.or (Primrec.eq.comp hw (replicateRec hr (.const 0)))
      (PrimrecPred.and (Primrec.nat_lt.comp (.const 0) (P455CataloguePrim.count'.comp hw (.const 0)))
        (Primrec.nat_lt.comp (.const 0) (P455CataloguePrim.count'.comp hw (.const 1))))))
    (Primrec.eq.comp hb (isProfileRec hr ht hw))

theorem binRec {r : A → Nat} {ts : A → Tags} (hr : Primrec r) (ht : Primrec ts) :
    Primrec fun a => bin (r a) (ts a) := by
  have hg := choicesRec (Primrec.list_range.comp (Primrec.list_length.comp (wordsRec.comp hr))) (.const [false,true])
  have k := Primrec.snd (α := A) (β := Key)
  have ha := Primrec.fst (α := A) (β := Key)
  have w := atKeyRec.comp (hr.comp ha) (Primrec.fst.comp k)
  have b := Primrec.snd.comp k
  have ft : Primrec₂ (fun a (k : Key) => tests (r a) (ts a) (atKey (r a) k.1) k.2) :=
    testsRec (hr.comp ha) (ht.comp ha) w b
  have f : Primrec (fun a => filtered (r a) (ts a)) := P455GraphPrim.filter hg ft
  exact Primrec.list_map (P455CataloguePrim.distinct'.comp f)
    (Primrec.pair w (Primrec.ite (Primrec.eq.comp b (.const true)) (.const (some [])) (.const none))).to₂

end P455WriterBinary
