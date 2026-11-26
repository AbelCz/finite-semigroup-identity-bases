import Mathlib.Computability.Primrec
import Problem455RealizerGraph
/- Encoded first-order subroutines for the #455 computation. -/
namespace P455GraphPrim
open P455EffectiveQ P455RealizerGraph
variable {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]

theorem filter {l : A → List B} {p : A → B → Bool}
    (hl : Primrec l) (hp : Primrec₂ p) : Primrec fun a => (l a).filter (p a) := by
  have k : Primrec₂ (fun a (x : B) => if p a x then some x else none) :=
    (Primrec.ite (show PrimrecPred (fun z : A×B => p z.1 z.2=true) by
      simpa [PrimrecPred] using hp) (Primrec.option_some.comp Primrec.snd) (.const none)).to₂
  apply (Primrec.listFilterMap hl k).of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih => cases h : p a b <;> simp [h,ih]

theorem join [DecidableEq B] : Primrec₂ (@joinAt B _) := by
  apply Primrec₂.mk
  apply Primrec.list_append.comp Primrec.snd
  apply Primrec.list_flatMap Primrec.snd
  apply Primrec₂.mk
  apply Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
  · apply Primrec.listFilterMap (Primrec.snd.comp Primrec.fst)
    apply Primrec₂.mk
    apply Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    · exact Primrec.option_some.comp (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
    · exact .const none
  · exact .const []

theorem graphFold [DecidableEq B] {p : A → List B} {s : A → List (B×B)}
    (hp : Primrec p) (hs : Primrec s) : Primrec fun a => (p a).foldr joinAt (s a) := by
  exact Primrec.list_foldr (h := fun _ (ks : B × List (B×B)) => joinAt ks.1 ks.2) hp hs
    (((join.comp Primrec.fst Primrec.snd).comp Primrec.snd).to₂)

theorem wordsUpTo : Primrec₂ (@Problem455Finite.wordsUpTo B) := by
  let step (l : List B) (x : Nat × List (List B)) :=
    [] :: l.flatMap (fun a => x.2.map (List.cons a))
  have steprec : Primrec₂ step := by
    apply Primrec₂.mk
    apply Primrec.list_cons.comp (.const [])
    apply Primrec.list_flatMap Primrec.fst
    apply Primrec₂.mk
    apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  apply (Primrec.nat_rec (Primrec.const [[]]) steprec).of_eq
  intro l n
  induction n with
  | zero => rfl
  | succ n ih => simp [Problem455Finite.wordsUpTo,step,ih]

theorem wordPool : Primrec words := (wordsUpTo.comp Primrec.id Primrec.list_length)

theorem initialized [DecidableEq B] {e : A → B → B → Bool}
    (he : Primrec (fun x : A×(B×B) => e x.1 x.2.1 x.2.2))
    {d : A → List B} (hd : Primrec d) :
    Primrec fun a => initial (d a) (e a) := by
  apply Primrec.list_flatMap hd
  apply Primrec₂.mk
  apply Primrec.list_map
  · apply filter (hd.comp Primrec.fst)
    apply Primrec₂.mk
    apply Primrec.or.comp
    · exact Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    · exact he.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  · exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

theorem contains [DecidableEq B] {v : A → B} {xs : A → List B}
    (hv : Primrec v) (hx : Primrec xs) : Primrec fun a => decide (v a∈xs a) := by
  apply (Primrec.nat_lt.comp (Primrec.list_idxOf.comp hv hx) (Primrec.list_length.comp hx)).of_eq
  intro a; simp [List.idxOf_lt_length_iff]

theorem reachable {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {u v : A → W} (hu : Primrec u) (hv : Primrec v) :
    Primrec fun a => walkB (e a) (u a) (v a) := by
  have piv := wordPool.comp hu
  have dom := Primrec.list_cons.comp hu (Primrec.list_cons.comp hv piv)
  exact (contains (hu.pair hv) (graphFold piv (initialized he dom))).of_eq (fun a => by
    rw [←walk_eq (e a) (u a) (v a)]
    apply Bool.eq_iff_iff.mpr
    simp only [walk,decide_eq_true_eq])
theorem anyB {l : A → List B} {p : A → B → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec fun a => (l a).any (p a) := by
  apply (Primrec.list_foldr hl (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
       (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih => simp [ih]

theorem factor {u v : A → W} (hu : Primrec u) (hv : Primrec v) : Primrec fun a => factorB (u a) (v a) := by
  apply anyB (wordPool.comp hv)
  apply Primrec₂.mk
  apply anyB (wordPool.comp (hv.comp Primrec.fst))
  apply Primrec₂.mk
  exact Primrec.eq.comp (hv.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      (hu.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)

theorem good {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {t u : A → W} (ht : Primrec t) (hu : Primrec u) :
    Primrec fun a => goodB (e a) (t a) (u a) := by
  apply anyB (wordPool.comp ht)
  apply Primrec₂.mk
  exact Primrec.and.comp
    (reachable (A := A × W) (e := fun p => e p.1) (he.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (ht.comp Primrec.fst) Primrec.snd)
    (factor (hu.comp Primrec.fst) Primrec.snd)

end P455GraphPrim
