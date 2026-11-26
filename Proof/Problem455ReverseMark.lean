import Problem455OutsideFactor



namespace Problem455ReverseMark
open P455Witness
open P455OutsideFactor
open Problem455.Slots

def reverseOnly (a b : Nat) : Prop := a = 1 ∧ b = 0

theorem reverseOnly_mark : ¬ reverseOnly 0 1 ∧ reverseOnly 1 0 := by simp [reverseOnly]

/-- The actual r=16 slot tester with mark {(1,0)}, stored once. This proof
    cannot pass if the certificate requires the ordered atom Mark 0 1. -/
theorem reversed_slot_captured : Holds 16 allow reverseOnly template (cert.query 16) := by
  have occ : occupies template 0 0 2 := ⟨0,by unfold sees; decide⟩
  have df : template.count 2 < 16 := by decide
  have pr : select [0,1] template = profile 0 1 [] false := by decide
  simp [SlotCertificate.query, cert, allQ, route, terminalSlot, markedNode, Holds,
        reverseOnly, allow, pr, occ, df, slotStart]

/-- Reversing EVERY stored pair leaves every observation on every word
    unchanged, including arbitrary compiled certificates of all three kinds. -/
theorem reverse_storage (q : Query) (r : Nat) (allow : Tag → Prop)
    (mark : Marking) (w : W) :
    Holds r allow mark w q ↔ Holds r allow (fun a b => mark b a) w q := by
  induction q with
  | fixed | count | deficient | record | order | slot | separate => rfl
  | markedBit => simp only [Holds]; rw [or_comm]
  | both _ _ hx hy => exact and_congr hx hy
  | either _ _ hx hy => exact or_congr hx hy

end Problem455ReverseMark
