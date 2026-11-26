import Problem455Witness



namespace P455OutsideFactor
open Problem455.Slots
open P455Witness

def template : W := 0 :: 2 :: (profile 0 1 [] false).tail
def allow (t : Tag) : Prop := t = []
def mark (a b : Nat) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
def cert : SlotCertificate :=
  { anchor := ⟨0, 1, []⟩
    bit := false
    startAtMate := false
    steps := []
    terminalIndex := 0
    defect := .deficient 2 }

theorem capped : P455Quotient.Cap 16 template := by
  intro a
  by_cases h0 : a = 0
  · subst a; decide
  by_cases h1 : a = 1
  · subst a; decide
  by_cases h2 : a = 2
  · subst a; decide
  have h : a ∉ template := by
    simp [template, profile, profilePrefix, pair, List.replicate_succ, h0, h1, h2]
  rw [List.count_eq_zero.mpr h]
  decide

theorem defect_in_template : Holds 16 allow mark template (cert.query 16) := by
  have occ : occupies template 0 0 2 := ⟨0,by unfold sees; decide⟩
  have df : template.count 2 < 16 := by decide
  have pr : select [0,1] template = profile 0 1 [] false := by decide
  simp [SlotCertificate.query, cert, allQ, route, terminalSlot, markedNode, Holds,
        mark, allow, pr, occ, df, slotStart]

theorem defect_absent_in_empty : ¬ Holds 16 allow mark [] (cert.query 16) := by
  have h : select [0,1] ([] : W) ≠ profile 0 1 [] false := by decide
  simp [SlotCertificate.query, cert, allQ, route, terminalSlot, markedNode, Holds, h]

abbrev R := rules 16 allow mark

theorem all_unit_proper_factor (v : List Nat) :
    P455Quotient.eval R capped (fun _ : Nat => P455Quotient.ofWord R template []) v ≠
      P455Quotient.zero R template ∧
    v.flatMap (fun _ => ([] : W)) = [] ∧ template ≠ [] ∧
    Holds 16 allow mark template (cert.query 16) ∧
    ¬ Holds 16 allow mark [] (cert.query 16) := by
  have nz := (P455Quotient.nonzero_iff R).mpr (P455Quotient.good_empty R template)
  have eq := P455Quotient.eval_rep R capped (fun _ : Nat => P455Quotient.ofWord R template [])
    v (fun _ => ([] : W)) (fun _ _ => rfl)
  have e : v.flatMap (fun _ => ([] : W)) = [] := by simp
  rw [eq,e]
  exact ⟨nz,rfl,by decide,defect_in_template,defect_absent_in_empty⟩

end P455OutsideFactor
