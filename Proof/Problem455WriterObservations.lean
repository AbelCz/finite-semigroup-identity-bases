import Problem455WriterProfiles

namespace P455WriterObservations
open Problem455.Slots P455WriterProfiles

variable {A X : Type} [Primcodable A] [Primcodable X]

theorem selectRec {k w : A → List Nat} (hk : Primrec k) (hw : Primrec w) :
    Primrec fun a => select (k a) (w a) :=
  P455GraphPrim.filter hw ((P455CataloguePrim.mem'.comp Primrec.snd (hk.comp Primrec.fst)).to₂)

def bump (a : Nat) (p : Event) : Event := (p.1, p.2 + if p.1=a then 1 else 0)

theorem stamp_add (n f : Nat → Nat) (w : W) :
    stamp (fun i => n i + f i) w = (stamp n w).map (fun p => (p.1,p.2+f p.1)) := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih =>
    simp only [stamp,List.map_cons,List.cons.injEq,true_and]
    have eq : advance (fun i => n i+f i) [a] = fun i => advance n [a] i+f i := by
      funext i
      change (n i+f i)+[a].count i=(n i+[a].count i)+f i
      omega
    rw [eq,ih]

theorem events_cons (a : Nat) (w : W) : events (a::w) = (a,0)::(events w).map (bump a) := by
  unfold events
  simp only [stamp,List.cons.injEq,true_and]
  have eq : advance (fun _ => 0) [a] = fun i : Nat => 0+(if i=a then 1 else 0) := by
    funext i
    by_cases h : i=a <;> simp [advance,h,Ne.symm,BEq.comm]
  rw [eq,stamp_add]
  rfl

theorem eventsRec : Primrec events := by
  let h (_ : W) (p : Nat × List Event) := (p.1,0)::p.2.map (bump p.1)
  have hh : Primrec₂ h := by
    apply Primrec₂.mk
    apply Primrec.list_cons.comp (Primrec.pair (Primrec.fst.comp Primrec.snd) (.const 0))
    apply Primrec.list_map (Primrec.snd.comp Primrec.snd)
    apply Primrec₂.mk
    have letter := Primrec.fst.comp (Primrec.snd (α := (W×(Nat×List Event))) (β := Event))
    exact Primrec.pair letter (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp letter (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (.const 1) (.const 0)))
  apply (Primrec.list_foldr (h:=h) (Primrec.id (α:=W)) (Primrec.const ([] : List Event)) hh).of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [events_cons]
    exact congrArg (fun tail => (a,0)::tail.map (bump a)) ih

def subsequences (l : List X) :=
  l.foldr (fun x s => s ++ s.map (List.cons x)) [[]]

theorem mem_subsequences {α : Type} (s t : List α) : s∈subsequences t ↔ s.Sublist t := by
  induction t generalizing s with
  | nil => simp [subsequences]
  | cons a l ih =>
    change s∈subsequences l ++ (subsequences l).map (List.cons a) ↔ _
    simp only [List.mem_append,List.mem_map,ih,List.sublist_cons_iff]
    tauto

theorem subsequencesRec : Primrec (@subsequences X) := by
  let h (_ : List X) (p : X×List (List X)) := p.2 ++ p.2.map (List.cons p.1)
  apply Primrec.list_foldr (h:=h) (Primrec.id (α:=List X)) (Primrec.const [[]])
  apply Primrec₂.mk
  exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
    (Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂)

theorem seesRec {w : A → W} {t : A → List Event} (hw : Primrec w) (ht : Primrec t) :
    PrimrecPred fun x => sees (w x) (t x) := by
  have v := P455GraphPrim.anyB (subsequencesRec.comp (eventsRec.comp hw))
    ((Primrec.eq.comp (ht.comp (Primrec.fst (β := List Event))) Primrec.snd).to₂)
  apply Primrec.of_eq v
  intro a
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,sees,mem_subsequences]


theorem bigramRec {w : A → W} {x y : A → Nat} (hw : Primrec w) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun a => Problem455Swap.bigram (x a) (y a) (w a) := by
  let h (a : A) (p : Nat×W×Nat) :=
    Problem455Swap.hit (x a) (y a) (some p.1) p.2.1.head? + p.2.2
  have hh : Primrec₂ h := by
    apply Primrec₂.mk
    apply Primrec.nat_add.comp _ (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    apply Primrec.ite _ (.const 1) (.const 0)
    exact PrimrecPred.and
      (Primrec.eq.comp (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.option_some.comp (hx.comp Primrec.fst)))
      (Primrec.eq.comp (Primrec.list_head?.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) (Primrec.option_some.comp (hy.comp Primrec.fst)))
  apply (Primrec.list_rec hw (.const 0) hh).of_eq
  intro a
  induction w a with
  | nil => rfl
  | cons b t ih => exact congrArg (fun acc => h a (b,t,acc)) ih

end P455WriterObservations
