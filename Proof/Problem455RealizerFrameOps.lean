import Problem455RealizerPrim
import Problem455EffectiveQMove
namespace P455FramePrim
open P455Closure P455EffectiveQ P455GraphPrim

abbrev Tag := List Bool
abbrev Marks := List (Nat×Nat)
abbrev PairList := List (List Nat×Bool)
abbrev FrameData := Nat × W × W × Nat × Tag × PairList × W × W × W

def packing : Frame Nat ≃ FrameData where
  toFun f := (f.pHead,f.pTail,f.qInit,f.qLast,f.tag,f.middle,f.beforeMutable,f.beforeFinalP,f.beforeFinalQ)
  invFun d := ⟨d.1,d.2.1,d.2.2.1,d.2.2.2.1,d.2.2.2.2.1,d.2.2.2.2.2.1,d.2.2.2.2.2.2.1,
    d.2.2.2.2.2.2.2.1,d.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance framePrimcodable : Primcodable (Frame Nat) := Primcodable.ofEquiv _ packing

theorem pack : Primrec packing := Primrec.of_equiv
theorem unpack : Primrec packing.symm := Primrec.of_equiv_symm

variable {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]

theorem allB {l : A → List B} {p : A → B → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec fun a => (l a).all (p a) := by
  apply (Primrec.not.comp (anyB hl (Primrec.not.comp₂ hp))).of_eq
  intro a; simp only [List.not_any_eq_all_not,Bool.not_not]

theorem countN {z : A → Nat} {l : A → W} (hz : Primrec z) (hl : Primrec l) :
    Primrec fun a => (l a).count (z a) := by
  apply (Primrec.list_length.comp (P455GraphPrim.filter hl
    ((Primrec.beq.comp Primrec.snd (hz.comp Primrec.fst)).to₂))).of_eq
  intro a
  simp [List.count_eq_countP,List.countP_eq_length_filter,BEq.comm]

theorem nodup {l : A → W} (hl : Primrec l) : Primrec fun a => decide (l a).Nodup := by
  apply (allB hl ((Primrec.eq.comp (countN Primrec.snd (hl.comp Primrec.fst)) (.const 1)).to₂)).of_eq
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,decide_eq_true_eq,List.nodup_iff_count_eq_one]

theorem singleton {v : A → B} (hv : Primrec v) : Primrec fun a => [v a] := Primrec.list_cons.comp hv (.const [])

theorem pairs : Primrec phasePair :=
  Primrec.list_cons.comp Primrec.id (singleton Primrec.not)

theorem phases : Primrec fixedPhases :=
  Primrec.list_append.comp (Primrec.list_append.comp (.const _) (Primrec.list_flatMap Primrec.id (pairs.comp₂ .right))) (.const _)

theorem pHead : Primrec (@Frame.pHead Nat) := (Primrec.fst.comp pack)
theorem pTail : Primrec (@Frame.pTail Nat) := (Primrec.fst.comp (Primrec.snd.comp pack))
theorem qInit : Primrec (@Frame.qInit Nat) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp pack)))
theorem qLast : Primrec (@Frame.qLast Nat) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pack))))
theorem tag : Primrec (@Frame.tag Nat) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pack)))))
theorem middle : Primrec (@Frame.middle Nat) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pack))))))
theorem beforeMutable : Primrec (@Frame.beforeMutable Nat) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pack)))))))
theorem beforeFinalP : Primrec (@Frame.beforeFinalP Nat) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pack))))))))
theorem beforeFinalQ : Primrec (@Frame.beforeFinalQ Nat) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pack))))))))

theorem p : Primrec (@Frame.p Nat) := Primrec.list_cons.comp pHead pTail
theorem q : Primrec (@Frame.q Nat) := Primrec.list_append.comp qInit (singleton qLast)
theorem early : Primrec (@Frame.early Nat) :=
  Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp p p) q) p) q) q
theorem mid : Primrec (@Frame.mid Nat) := Primrec.list_flatMap middle <| Primrec₂.mk <|
  Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (.const true))
       (q.comp Primrec.fst) (p.comp Primrec.fst))

theorem pairCore : Primrec₂ (@Frame.pair Nat) := Primrec₂.mk <|
  Primrec.ite (Primrec.eq.comp Primrec.snd (.const true))
    (Primrec.list_append.comp (q.comp Primrec.fst) (p.comp Primrec.fst))
    (Primrec.list_append.comp (p.comp Primrec.fst) (q.comp Primrec.fst))
theorem core : Primrec₂ (@Frame.core Nat) := Primrec₂.mk <|
  (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (early.comp Primrec.fst) (mid.comp Primrec.fst)) (beforeMutable.comp Primrec.fst)) (pairCore.comp Primrec.fst Primrec.snd)) (beforeFinalP.comp Primrec.fst)) (p.comp Primrec.fst)) (beforeFinalQ.comp Primrec.fst)) (q.comp Primrec.fst))

end P455FramePrim
