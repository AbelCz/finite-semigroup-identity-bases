import Problem455WriterSlotTypes
import Problem455WriterQueryLeaves

namespace P455WriterSlots
open P455Witness (Tag Holds Query Marking SlotDefect)
open P455WriterQueryLeaves P455WriterObservations P455WriterProfiles
open Problem455.Slots

def slot (e : Env) (o i a : Nat) :=
  decide (slotStart i) && (events e.2.2.2).any (fun p => decide (sees e.2.2.2 [(o,i),(a,p.2),(o,i+1)]))

def different (e : Env) : W → Bool
  | [] => true
  | a::t => t.all (separate e a) && different e t

def holes (e : Env) (o i : Nat) (xs : W) :=
  decide (xs.length=5) && different e (o::xs) &&
    xs.all (fun a => decide (e.2.2.2.count a=e.1) && slot e o i a)

def terminal (e : Env) (o i : Nat) (defect : SlotDefect) : Bool :=
  match defect with
  | .deficient a => slot e o i a && decide (e.2.2.2.count a < e.1)
  | .overflow xs => holes e o i xs

variable {e : Env} {r : Nat} {allow : Tag → Prop} {mark : Marking} {w : W}

theorem slot_ok (h : ModelsEnv e r allow mark w) (o i a : Nat) :
    slot e o i a=true ↔ Holds r allow mark w (.slot o i a) := by
  simp only [slot,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,h.word,Holds,occupies]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨p,_,s⟩; exact ⟨p.2,s⟩
  · rintro ⟨j,s⟩; exact ⟨(a,j),s.subset (by simp),s⟩

theorem different_ok (h : ModelsEnv e r allow mark w) (xs : W) :
    different e xs=true ↔ Holds r allow mark w (P455Witness.differentBlocks xs) := by
  induction xs with
  | nil => simp [different,P455Witness.differentBlocks,Holds]
  | cons a xs ih =>
    simp [different,P455Witness.differentBlocks,Holds,P455PortReflection.holds_all,List.all_eq_true,ih,separate_ok h]

theorem terminal_ok (h : ModelsEnv e r allow mark w) (o i d) :
    terminal e o i d=true ↔ Holds r allow mark w (P455Witness.terminalSlot r o i d) := by
  cases d with
  | deficient a => simp only [terminal,Bool.and_eq_true,slot_ok h,decide_eq_true_eq,h.word,h.lim,P455Witness.terminalSlot,Holds]
  | overflow xs =>
    simp [terminal,holes,Bool.and_eq_true,slot_ok h,decide_eq_true_eq,h.word,h.lim,different_ok h,List.all_eq_true,
      P455Witness.terminalSlot,P455PortReflection.holds_all,Holds,and_assoc]

variable {A : Type} [Primcodable A]

theorem slotRec {e : A → Env} {o i a : A → Nat} (he : Primrec e) (ho : Primrec o) (hi : Primrec i) (ha : Primrec a) :
    Primrec fun x => slot (e x) (o x) (i x) (a x) := by
  have fixed : Primrec fun x => decide (slotStart (i x)) := by
    have hit := memRec hi (Primrec.const [0,1,3,5,7,9,11])
    apply Primrec.of_eq hit
    intro x
    apply Bool.eq_iff_iff.mpr
    simp [slotStart]
  apply Primrec.and.comp fixed
  apply P455GraphPrim.anyB (eventsRec.comp (wordRec he))
  apply Primrec₂.mk
  let cons := @Primrec.list_cons Event _
  have o' := ho.comp (Primrec.fst (β := Event))
  have i' := hi.comp (Primrec.fst (β := Event))
  exact seesRec ((wordRec he).comp Primrec.fst) (cons.comp (o'.pair i') (cons.comp
    (Primrec.pair (ha.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (cons.comp (o'.pair (Primrec.succ.comp i')) (.const []))))

theorem differentRec {e : A → Env} {l : A → W} (he : Primrec e) (hl : Primrec l) :
    Primrec fun x => different (e x) (l x) := by
  let h (x : A) (p : Nat×W×Bool) := p.2.1.all (separate (e x) p.1) && p.2.2
  have hh : Primrec₂ h := by
    apply Primrec₂.mk
    apply Primrec.and.comp _ (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    apply P455FramePrim.allB (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact (separateRec ((he.comp Primrec.fst).comp Primrec.fst) ((Primrec.fst.comp Primrec.snd).comp Primrec.fst) Primrec.snd).to₂
  apply (Primrec.list_rec hl (.const true) hh).of_eq
  intro x
  induction l x with
  | nil => rfl
  | cons a xs ih => exact congrArg (fun b => h x (a,xs,b)) ih

theorem holesRec {e : A → Env} {o i : A → Nat} {xs : A → W} (he : Primrec e) (ho : Primrec o)
    (hi : Primrec i) (hl : Primrec xs) : Primrec fun x => holes (e x) (o x) (i x) (xs x) := by
  apply Primrec.and.comp (Primrec.and.comp (Primrec.eq.comp (Primrec.list_length.comp hl) (.const 5))
    (differentRec he (Primrec.list_cons.comp ho hl)))
  apply P455FramePrim.allB hl
  exact (Primrec.and.comp (Primrec.eq.comp (P455CataloguePrim.count'.comp ((wordRec he).comp Primrec.fst) Primrec.snd)
    ((limRec he).comp Primrec.fst)) (slotRec (he.comp Primrec.fst) (ho.comp Primrec.fst) (hi.comp Primrec.fst) Primrec.snd)).to₂

theorem terminalRec {e : A → Env} {o i : A → Nat} {d : A → SlotDefect}
    (he : Primrec e) (ho : Primrec o) (hi : Primrec i) (hd : Primrec d) :
    Primrec fun x => terminal (e x) (o x) (i x) (d x) := by
  let a (x : A) (z : Nat) := slot (e x) (o x) (i x) z && decide ((e x).2.2.2.count z < (e x).1)
  have ha : Primrec₂ a := Primrec.and.comp
    (slotRec (he.comp Primrec.fst) (ho.comp Primrec.fst) (hi.comp Primrec.fst) Primrec.snd)
    (Primrec.nat_lt.comp (P455CataloguePrim.count'.comp ((wordRec he).comp Primrec.fst) Primrec.snd) ((limRec he).comp Primrec.fst))
  let b (x : A) (xs : W) := holes (e x) (o x) (i x) xs
  have hb : Primrec₂ b := holesRec (he.comp Primrec.fst) (ho.comp Primrec.fst) (hi.comp Primrec.fst) Primrec.snd
  apply (Primrec.sumCasesOn (defectCodeRec.comp hd) ha hb).of_eq
  intro x
  cases d x <;> rfl

end P455WriterSlots
