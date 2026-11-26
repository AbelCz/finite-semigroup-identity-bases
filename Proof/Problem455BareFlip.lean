import Problem455SlotSaturation



namespace P455BareFlip
open P455Witness Problem455.Slots P455CrossedSupport P455SlotSaturation

def f : P455Closure.Frame Nat := {
  pHead := 0, pTail := [], qInit := [], qLast := 1, tag := []
  middle := ([],false) :: ([2],true) ::
    ((P455Closure.fixedPhases []).drop 2).map (fun bit => ([],bit))
  beforeMutable := [], beforeFinalP := [], beforeFinalQ := [] }

def word (bit : Bool) := f.core bit
def allow (t : Tag) := t = []
theorem capped (b : Bool) : P455Closure.Cap 16 (word b) := by
  intro a
  by_cases mem : a ∈ word b
  · have ns : ∀ x ∈ word b, x < 3 := by cases b <;> decide
    have tab : ∀ i : Fin 3, (word b).count i.val ≤ 16 := by cases b <;> decide
    exact tab ⟨a,ns a mem⟩
  · rw [List.count_eq_zero.mpr mem]; omega

theorem literal (b : Bool) : ClosedFlip 16 allow (word b) 0 1 := by
  have ok : f.Valid 16 allow noMark := f.valid_of_capped_shape rfl rfl (by decide)
    (by decide) (by decide) (by decide) (fun _ _ _ _ => ⟨id,id⟩) b [] [] (by simpa using capped b)
  exact ⟨f,b,[],[],rfl,rfl,ok,by simp [word]⟩

theorem bare_flip_fails (b : Bool) : (word b).length = 33 ∧ ClosedFlip 16 allow (word b) 0 1 ∧
    select [0,1] (word b) ≠ select [0,1] (word (!b)) ∧
    ¬ UniformSlots 16 allow noMark (word b) 0 1 ∧
    ¬ P455SlotProduct.Identity 16 allow (word b) (word (!b)) := by
  have diff : select [0,1] (word b) ≠ select [0,1] (word (!b)) := by cases b <;> decide
  have occ : occupies (word b) 0 3 2 := ⟨0,by cases b <;> unfold sees <;> decide⟩
  have fail : ¬ UniformSlots 16 allow noMark (word b) 0 1 := by
    intro uni
    have c := uni 0 (.inl (P455Paths.near_self 0 6)) 3 (by simp [slotStart]) 2 occ
    have deficit : (word b).count 2 = 1 := by cases b <;> decide
    omega
  exact ⟨by cases b <;> decide,literal b,diff,fail,fun iden =>
    fail (uniform_of_identity (capped b) iden (literal b) diff)⟩

end P455BareFlip
