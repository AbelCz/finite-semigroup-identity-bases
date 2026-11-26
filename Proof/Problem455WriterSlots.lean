import Problem455WriterSlotsTerminal
import Problem455WriterSlotContact
namespace P455WriterSlots
open P455Witness (Tag Holds Marking ContactChoice SlotCertificate)
open P455WriterQueryLeaves P455WriterProfiles P455WriterEdge

abbrev Step := Nat × ContactChoice
def visit (e : Env) (s : Nat×Bool) (b : Step) := (b.1, s.2 && contact e s.1 b.1 b.2)
def walk (e : Env) (s : Nat×Bool) (bs : List Step) := bs.foldl (visit e) s

def sat (e : Env) (s : SlotCertificate) :=
  let start := if s.startAtMate then s.anchor.mate else s.anchor.owner
  let last := walk e (start,true) s.steps
  marked e s.anchor.owner s.anchor.mate s.anchor.tag s.bit && decide (s.steps.length≤6) &&
    last.2 && terminal e last.1 s.terminalIndex s.defect

variable {e : Env} {r : Nat} {allow : Tag → Prop} {mark : Marking} {w : W}

theorem walk_ok (h : ModelsEnv e r allow mark w) (s : Nat × Bool) (bs : List Step) (i d) :
    ((walk e s bs).2=true ∧ terminal e (walk e s bs).1 i d=true) ↔
      s.2=true ∧ Holds r allow mark w (P455Witness.route r s.1 bs (fun a => P455Witness.terminalSlot r a i d)) := by
  induction bs generalizing s with
  | nil => simp only [walk,List.foldl_nil,P455Witness.route,terminal_ok h]
  | cons b bs ih =>
    change (_ ∧ _) ↔ s.2=true ∧ Holds r allow mark w (.both _ _)
    rw [show walk e s (b::bs) = walk e (visit e s b) bs by rfl,ih]
    simp only [visit,Holds,Bool.and_eq_true,contact_ok h,and_assoc]

theorem sat_ok (h : ModelsEnv e r allow mark w) (s : SlotCertificate) :
    sat e s=true ↔ Holds r allow mark w (s.query r) := by
  simp only [sat,Bool.and_eq_true,and_assoc,walk_ok h,true_and,marked_ok h,decide_eq_true_eq,
    P455Witness.SlotCertificate.query,P455Witness.allQ,Holds,P455Witness.markedNode,and_true]

variable {A : Type} [Primcodable A]

theorem walkRec {e : A → Env} {s : A → Nat×Bool} {bs : A → List Step}
    (he : Primrec e) (hs : Primrec s) (hb : Primrec bs) : Primrec fun a => walk (e a) (s a) (bs a) := by
  let step (a : A) (p : (Nat×Bool)×Step) := visit (e a) p.1 p.2
  apply Primrec.list_foldl (h:=step) hb hs
  apply Primrec₂.mk
  have p := Primrec.snd (α := A) (β := (Nat×Bool) × Step)
  have i := Primrec.fst.comp (Primrec.fst.comp p)
  have yes := Primrec.snd.comp (Primrec.fst.comp p)
  have j := Primrec.fst.comp (Primrec.snd.comp p)
  have c := Primrec.snd.comp (Primrec.snd.comp p)
  exact j.pair (Primrec.and.comp yes (contactRec (he.comp Primrec.fst) i j c))

theorem satRec {e : A → Env} {s : A → SlotCertificate} (he : Primrec e) (hs : Primrec s) :
    Primrec fun a => sat (e a) (s a) := by
  have z := slotCodeRec.comp hs
  have node := Primrec.fst.comp z
  have a := ownerRec.comp node
  have b := mateRec.comp node
  have tag := tagRec.comp node
  have tail1 := Primrec.snd.comp z
  have bit := Primrec.fst.comp tail1
  have tail2 := Primrec.snd.comp tail1
  have atMate := Primrec.fst.comp tail2
  have tail3 := Primrec.snd.comp tail2
  have steps := Primrec.fst.comp tail3
  have tail4 := Primrec.snd.comp tail3
  have i := Primrec.fst.comp tail4
  have d := Primrec.snd.comp tail4
  have start := Primrec.ite (Primrec.eq.comp atMate (.const true)) b a
  have last := walkRec he (start.pair (.const true)) steps
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (markedRec he a b tag bit)
    (Primrec.nat_le.comp (Primrec.list_length.comp steps) (.const 6))) (Primrec.snd.comp last))
    (terminalRec he (Primrec.fst.comp last) i d)

def slotAccept (e : Env) (a b : Nat) :=
  (P455Enum.slots e.2.2.2 e.2.1).any fun s =>
    decide (s.anchor.owner=a ∧ s.anchor.mate=b) && sat e s

theorem slotAcceptRec {e : A → Env} {a b : A → Nat} (he : Primrec e) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => slotAccept (e x) (a x) (b x) := by
  apply P455GraphPrim.anyB (slotsRec (wordRec he) (tagsRec he))
  apply Primrec₂.mk
  have s := Primrec.snd (α := A) (β := SlotCertificate)
  have node := Primrec.fst.comp (slotCodeRec.comp s)
  exact Primrec.and.comp (PrimrecPred.and (Primrec.eq.comp (ownerRec.comp node) (ha.comp Primrec.fst))
    (Primrec.eq.comp (mateRec.comp node) (hb.comp Primrec.fst))) (satRec (he.comp Primrec.fst) s)

theorem slotAccept_ok (M : P455PaddedTiles.MachineTable n) {e : Env} {r : Nat} {mark : Marking} {w : W}
    (h : ModelsEnv e r (P455PaddedTiles.allowed M) mark w) (ht : e.2.1=P455Enum.tags M) (a b) :
    slotAccept e a b=true ↔ ∃ s : SlotCertificate, s.anchor.owner=a ∧ s.anchor.mate=b ∧
      Holds r (P455PaddedTiles.allowed M) mark w (s.query r) := by
  simp only [slotAccept,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,sat_ok h,h.word,ht]
  constructor
  · rintro ⟨s,_,⟨ha,hb⟩,ok⟩; exact ⟨s,ha,hb,ok⟩
  · rintro ⟨s,ha,hb,ok⟩; exact ⟨s,P455Enum.slot_mem M s ok,⟨ha,hb⟩,ok⟩

end P455WriterSlots
