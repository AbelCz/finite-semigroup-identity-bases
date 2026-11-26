import Problem455RealizerFrameOps

/- Primitive recursive literal-move search on standard natural-number
   encodings, uniformly in the cap, tags and finitely stored mark relation. -/
namespace P455FrameProof
set_option maxHeartbeats 450000
open P455Closure P455EffectiveQ P455GraphPrim P455FramePrim
open P455EffectiveQMove (capB frames entries validB moveB)
variable {A B : Type} [Primcodable A] [Primcodable B]

private theorem same_decision {p : Prop} (a b : Decidable p) : @decide p a = @decide p b := by
  rw [Subsingleton.elim a b]

theorem forNames {l : A → List B} {pr : A → B → Prop} [d : ∀ a, DecidablePred (pr a)]
    (hl : Primrec l) (hp : Primrec₂ fun a b => decide (pr a b)) : PrimrecPred fun a => ∀ b∈l a,pr a b := by
  apply (allB hl hp).of_eq
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,decide_eq_true_eq]

theorem capCheck {r : A → Nat} {w : A → W} (hr : Primrec r) (hw : Primrec w) :
    Primrec fun a => capB (r a) (w a) := by
  apply allB hw
  exact (Primrec.nat_le.comp (countN Primrec.snd (hw.comp Primrec.fst)) (hr.comp Primrec.fst)).to₂

theorem validity {r : A → Nat} {tags : A → List Tag} {marks : A → Marks} {f : A → Frame Nat}
    (hr : Primrec r) (ht : Primrec tags) (hm : Primrec marks) (hf : Primrec f) :
    Primrec fun a => validB (r a) (tags a) (fun x y => decide ((x,y)∈marks a)) (f a) := by
  change PrimrecPred _
  let Fp := P455FramePrim.p.comp hf
  let Fq := P455FramePrim.q.comp hf
  let Ft := P455FramePrim.tag.comp hf
  let Fm := P455FramePrim.middle.comp hf
  have apart : PrimrecPred (fun a => ∀ x∈(f a).p, x∉(f a).q) := by
    apply forNames Fp
    exact (PrimrecPred.not (contains Primrec.snd (Fq.comp Primrec.fst))).to₂
  have marksOK : PrimrecPred (fun a => ∀ x∈(f a).p, ∀ y∈(f a).q,
      decide ((x,y)∈marks a)=false ∧ decide ((y,x)∈marks a)=false) := by
    apply forNames Fp
    apply Primrec₂.mk
    apply forNames (Fq.comp Primrec.fst)
    apply Primrec₂.mk
    have old : Primrec (fun s : (A×Nat)×Nat => marks s.1.1) := (hm.comp Primrec.fst).comp Primrec.fst
    have xy : Primrec (fun s : (A×Nat)×Nat => decide ((s.1.2,s.2)∈marks s.1.1)) :=
      (contains (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd) old).of_eq (fun _ => same_decision _ _)
    have yx : Primrec (fun s : (A×Nat)×Nat => decide ((s.2,s.1.2)∈marks s.1.1)) :=
      (contains (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)) old).of_eq (fun _ => same_decision _ _)
    exact PrimrecPred.and (Primrec.eq.comp xy (.const false)) (Primrec.eq.comp yx (.const false))
  have saturated : PrimrecPred (fun a => ∀ x∈(f a).p++(f a).q, ((f a).core false).count x = r a) := by
    apply forNames (Primrec.list_append.comp Fp Fq)
    exact (Primrec.eq.comp (countN Primrec.snd ((P455FramePrim.core.comp hf (.const false)).comp Primrec.fst))
      (hr.comp Primrec.fst)).to₂
  apply PrimrecPred.and (Primrec.eq.comp hr (Primrec.nat_add.comp (.const 16) (Primrec.list_length.comp Ft)))
  have member : Primrec (fun a => decide ((f a).tag ∈ tags a)) := (contains Ft ht).of_eq (fun _ => same_decision _ _)
  apply PrimrecPred.and member
  apply PrimrecPred.and (Primrec.eq.comp (Primrec.list_map Fm (Primrec.snd.comp₂ Primrec₂.right)) (phases.comp Ft))
  apply PrimrecPred.and (nodup Fp)
  apply PrimrecPred.and (nodup Fq)
  apply PrimrecPred.and apart
  apply PrimrecPred.and marksOK
  exact saturated

theorem entriesRec {w : A → W} (hw : Primrec w) : Primrec fun a => entries (w a) := by
  apply Primrec.list_flatMap (wordPool.comp hw)
  apply Primrec₂.mk
  exact Primrec.list_cons.comp (Primrec.pair Primrec.snd (.const false))
    (singleton (Primrec.pair Primrec.snd (.const true)))

private def choices {X Y : Type} (xs : List X) (ys : List Y) : List (X × Y) :=
  xs.flatMap fun x => ys.map fun y => (x,y)

private theorem map_choices {X Y Z : Type} (xs : List X) (ys : List Y) (f : X × Y → Z) :
    (choices xs ys).map f = xs.flatMap fun x => ys.map fun y => f (x,y) := by
  simp only [choices, List.map_flatMap, List.map_map, Function.comp_def]

private theorem choices_rec {X Y : Type} [Primcodable X] [Primcodable Y]
    {xs : A → List X} {ys : A → List Y} (hx : Primrec xs) (hy : Primrec ys) :
    Primrec fun a => choices (xs a) (ys a) := by
  apply Primrec.list_flatMap hx
  apply Primrec₂.mk
  apply Primrec.list_map (hy.comp Primrec.fst)
  exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private abbrev Body := Nat × W × W × Nat × PairList × W × W × W

private def insertTag (t : Tag) (b : Body) : FrameData :=
  (b.1,b.2.1,b.2.2.1,b.2.2.2.1,t,b.2.2.2.2)

private theorem insert_rec : Primrec₂ insertTag := by
  apply Primrec₂.mk
  have tail1 : Primrec (fun s : Tag × Body => s.2.2) := Primrec.snd.comp Primrec.snd
  have tail2 := Primrec.snd.comp tail1
  have tail3 := Primrec.snd.comp tail2
  have tail4 := Primrec.snd.comp tail3
  exact Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.pair (Primrec.fst.comp tail1)
    (Primrec.pair (Primrec.fst.comp tail2) (Primrec.pair (Primrec.fst.comp tail3)
    (Primrec.pair Primrec.fst tail4))))

theorem frameList {tags : A → List Tag} {w : A → W} (ht : Primrec tags) (hw : Primrec w) :
    Primrec fun a => frames (tags a) (w a) := by
  apply Primrec.list_flatMap ht
  apply Primrec₂.mk
  let U : (A × Tag) → W := fun s => w s.1
  let S : (A × Tag) → List W := fun s => P455EffectiveQ.words (U s)
  let E : (A × Tag) → List PairList := fun s =>
    Problem455Finite.wordsUpTo (entries (U s)) (fixedPhases s.2).length
  have hU : Primrec U := hw.comp Primrec.fst
  have hS : Primrec S := wordPool.comp hU
  have hE : Primrec E := wordsUpTo.comp (entriesRec hU) (Primrec.list_length.comp (phases.comp Primrec.snd))
  have bodies := choices_rec hU (choices_rec hS (choices_rec hS (choices_rec hU
    (choices_rec hE (choices_rec hS (choices_rec hS hS))))))
  have attach : Primrec₂ (fun (s : A × Tag) (b : Body) => packing.symm (insertTag s.2 b)) :=
    unpack.comp₂ (insert_rec.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
  apply (Primrec.list_map bodies attach).of_eq
  intro s
  simp only [map_choices, insertTag, packing]
  rfl

theorem literalMove {r : A → Nat} {tags : A → List Tag} {marks : A → Marks} {u v : A → W}
    (hr : Primrec r) (ht : Primrec tags) (hm : Primrec marks) (hu : Primrec u) (hv : Primrec v) :
    Primrec fun a => moveB (r a) (tags a) (fun x y => decide ((x,y)∈marks a)) (u a) (v a) := by
  apply Primrec.and.comp (Primrec.and.comp (Primrec.nat_le.comp hr (Primrec.list_length.comp hu)) (capCheck hr hu))
  apply anyB (frameList ht hu)
  apply Primrec₂.mk
  apply Primrec.and.comp (validity (hr.comp Primrec.fst) (ht.comp Primrec.fst) (hm.comp Primrec.fst) Primrec.snd)
  apply anyB (Primrec.const [false,true])
  apply Primrec₂.mk
  apply anyB (wordPool.comp ((hu.comp Primrec.fst).comp Primrec.fst))
  apply Primrec₂.mk
  apply anyB (wordPool.comp (((hu.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst))
  apply Primrec₂.mk
  let C := ((((A × Frame Nat) × Bool) × W) × W)
  have f : Primrec (fun x : C => x.1.1.1.2) := (((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst)
  have b : Primrec (fun x : C => x.1.1.2) := ((Primrec.snd.comp Primrec.fst).comp Primrec.fst)
  have l : Primrec (fun x : C => x.1.2) := (Primrec.snd.comp Primrec.fst)
  have t : Primrec (fun x : C => x.2) := Primrec.snd
  exact PrimrecPred.and
    (Primrec.eq.comp ((((hu.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) (Primrec.list_append.comp (Primrec.list_append.comp l (P455FramePrim.core.comp f b)) t))
    (Primrec.eq.comp ((((hv.comp Primrec.fst).comp Primrec.fst).comp Primrec.fst).comp Primrec.fst) (Primrec.list_append.comp (Primrec.list_append.comp l (P455FramePrim.core.comp f (Primrec.not.comp b))) t))

end P455FrameProof
