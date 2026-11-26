import Problem455ContactLift

/- Proper-factor test of the quantified path-transfer theorem. In the
   enclosing profile a,c,b are distinct letters. The two exterior letters
   are singletons, and x -> ab, y -> c. -/
namespace P455FoldedWalk
open Problem455.Slots P455Witness P455Paths P455ContactLift
def src : W := profile 0 1 [] false
def h (x : Nat) : W := if x = 0 then [2,3] else if x = 1 then [4] else []
def z : W := [5] ++ src.flatMap h ++ [6]
def allow (tag : Tag) : Prop := tag = []
def mark (a b : Nat) : Prop := a = 2 ∧ b = 4

def outSteps : List Step := [(4,.record [] false),(3,.record [] true)]
def srcSteps : List Step := [(1,.record [] false),(0,.record [] true)]

theorem cap : P455Closure.Cap 16 z := by
  intro a
  have alphabet : ∀ j ∈ z, j ∈ [2,3,4,5,6] := by decide
  by_cases occur : a ∈ z
  · have := alphabet a occur
    simp only [List.mem_cons,List.not_mem_nil,or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [List.count_eq_zero.mpr occur]; decide

private theorem sup0 : Supplies src h 16 0 2 := ⟨by decide,by decide⟩
private theorem sup0' : Supplies src h 16 0 3 := ⟨by decide,by decide⟩
private theorem sup1 : Supplies src h 16 1 4 := ⟨by decide,by decide⟩

theorem proper : z.length = (src.flatMap h).length + 2 := by simp [z]
theorem output_walk : Walk 16 allow mark z 2 outSteps := by
  have a : Holds 16 allow mark z (typedNode ⟨2,4,[]⟩) :=
    ⟨by decide,rfl,rfl,false,by decide⟩
  have b : Holds 16 allow mark z (typedNode ⟨3,4,[]⟩) :=
    ⟨by decide,rfl,rfl,false,by decide⟩
  exact ⟨a,b,True.intro⟩

/-- The kernel verifies that the output vertex list is simple and that
   the source path returned by lift_walk revisits the first donor. -/
theorem proper_factor_folded_walk :
    [2,4,3].Nodup ∧ ¬ [0,1,0].Nodup ∧
    z.length = (src.flatMap h).length + 2 ∧
    relabel (donor src h 16) outSteps = srcSteps ∧ Walk 16 allow mark src 0 srcSteps := by
  have zcap : P455Closure.Cap 16 ([5] ++ src.flatMap h ++ [6]) := cap
  have nc := factor_cap zcap
  have d3 := donor_eq (by decide : 0 < 16) nc sup0'
  have d4 := donor_eq (by decide : 0 < 16) nc sup1
  have rel : relabel (donor src h 16) outSteps = srcSteps := by simp [outSteps,srcSteps,relabel,d3,d4]
  have uni : ∀ a ∈ src, src.count a = 16 := by decide
  have lifted := lift_walk (by decide : 0 < 16) zcap sup0
    (guard_uniform (allow := allow) (mark := mark) (seed := 0) (J := 2) uni)
    outSteps (by decide) output_walk
  exact ⟨by decide,by decide,proper,rel,rel ▸ lifted.1⟩

theorem evaluation_live :
    P455Quotient.eval (rules 16 allow mark) cap (fun a => P455Quotient.ofWord (rules 16 allow mark) z (h a)) src
      ≠ P455Quotient.zero (rules 16 allow mark) z := by
  rw [P455Quotient.eval_rep (rules 16 allow mark) cap _ src h (fun _ _ => rfl)]
  apply (P455Quotient.nonzero_iff _).mpr
  exact ⟨z,.refl _,[5],[6],rfl⟩

end P455FoldedWalk
