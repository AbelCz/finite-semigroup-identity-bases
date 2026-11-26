import Problem455WriterStructuralRec
namespace P455WriterStructural
open P455WriterTiles P455WriterProfiles P455PaddedTiles P455StructuralProduct

def wordAt (r i : Nat) := (templates r)[i]?.getD []

def test (r : Nat) (ts : Tags) (w : W) :=
  P455EffectiveQMove.capB r w && compressedB r w &&
    ((widthB 4 w && overlapB r ts w) || (widthB 3 w && intrusionB r ts w))

theorem test_correct {r : Nat} (pos : 0<r) (M : MachineTable n) (w : W) :
    test r (P455Enum.tags M) w=true ↔ P455Closure.Cap r w ∧ P455SourceFamilies.Compressed r w ∧
      P455Structural.Structural w r (allowed M) := by
  simp only [test,Bool.and_eq_true,Bool.or_eq_true,P455EffectiveQMove.cap_iff,compressed_correct pos,
    width_correct,overlap_correct,intrusion_correct,P455Structural.Structural,and_assoc]

def indexKey (i : Index r allow) := i.pos.val

theorem key_injective : Function.Injective (@indexKey r allow) := by
  rintro ⟨i,_,_,_⟩ ⟨j,_,_,_⟩ h
  change i.val=j.val at h
  cases Fin.ext h
  rfl

def indices (r : Nat) (ts : Tags) :=
  (List.range (templates r).length).filter fun i => test r ts (wordAt r i)

theorem getWord (r : Nat) (i : Fin (templates r).length) : wordAt r i.val=(templates r).get i := by
  simp [wordAt,i.isLt]

private theorem attachIndices {n : Nat} (xs : List (Fin n)) :
    xs.attach.map (fun x => x.val.val) = xs.map Fin.val :=
  @List.attach_map_val (Fin n) Nat xs Fin.val

theorem indices_correct {r : Nat} (pos : 0<r) (M : MachineTable n) :
    (P455Enum.structural pos M).list.map indexKey = indices r (P455Enum.tags M) := by
  unfold indices
  rw [←List.map_coe_finRange,List.filter_map]
  unfold P455Enum.structural
  simp only [P455Enum.Cover.map,P455Enum.coverSub,P455Enum.selectSub,List.map_map,Function.comp_def,indexKey]
  rw [attachIndices]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,getWord,test_correct pos]

def structural (r : Nat) (ts : Tags) : List P455Packed.Spec :=
  (P455Table.distinct (indices r ts)).map fun i => (wordAt r i,none)

theorem structural_correct {r : Nat} (pos : 0<r) (M : MachineTable n) :
    structural r (P455Enum.tags M) =
      P455Packed.names (P455Encoded.useCover (P455Enum.structural pos M)) P455Packed.structSpec := by
  unfold structural
  rw [←indices_correct pos,←P455CataloguePrim.map_distinct indexKey key_injective,List.map_map]
  unfold P455Packed.names P455Encoded.useCover
  apply List.map_congr_left
  intro i _
  change (wordAt r i.pos.val,none) = _
  rw [getWord]
  rfl

variable {A : Type} [Primcodable A]

theorem templatesRec : Primrec templates :=
  P455GraphPrim.wordsUpTo.comp (.const (List.range 4)) (Primrec.nat_mul.comp (.const 4) Primrec.id)

theorem wordAtRec : Primrec₂ wordAt :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (templatesRec.comp Primrec.fst) Primrec.snd) (.const [])

theorem testRec {r : A → Nat} {ts : A → Tags} {w : A → W}
    (hr : Primrec r) (ht : Primrec ts) (hw : Primrec w) :
    Primrec fun a => test (r a) (ts a) (w a) :=
  Primrec.and.comp (Primrec.and.comp (P455FrameProof.capCheck hr hw) (compressedRec hr hw))
    (Primrec.or.comp (Primrec.and.comp (widthRec (.const 4) hw) (overlapRec hr ht hw))
                    (Primrec.and.comp (widthRec (.const 3) hw) (intrusionRec hr ht hw)))

theorem structuralRec {r : A → Nat} {ts : A → Tags} (hr : Primrec r) (ht : Primrec ts) :
    Primrec fun a => structural (r a) (ts a) := by
  have ids := Primrec.list_range.comp (Primrec.list_length.comp (templatesRec.comp hr))
  have w := wordAtRec.comp (hr.comp (Primrec.fst (β := Nat))) Primrec.snd
  have valid : Primrec₂ (fun a i => test (r a) (ts a) (wordAt (r a) i)) :=
    testRec (hr.comp Primrec.fst) (ht.comp Primrec.fst) w
  have idx := P455GraphPrim.filter ids valid
  exact Primrec.list_map (P455CataloguePrim.distinct'.comp idx) (Primrec.pair w (.const none)).to₂

end P455WriterStructural
