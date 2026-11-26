import Problem455NumericProductPrim
import Problem455LiteralMovePrim
import Problem455TableDecision

/- Validate a numeric output on all strings, including malformed machine codes.
   The test looks only at the finite square array and has primitive recursive bounds. -/
namespace P455TableValidate
open P455Table P455TableSemantics

def rows (T : Matrix) := T.all fun row => decide (row.length=T.length) && row.all fun x => decide (x<T.length)
def assocB (T : Matrix) := (List.range T.length).all fun i => (List.range T.length).all fun j =>
  (List.range T.length).all fun k => decide (entry T (entry T i j) k=entry T i (entry T j k))
def unitB (T : Matrix) := (List.range T.length).any fun i => (List.range T.length).all fun j =>
  decide (entry T i j=j) && decide (entry T j i=j)
def valid (T : Matrix) := decide (0<T.length) && rows T && assocB T && unitB T
def safe (T : Matrix) : Matrix := if valid T then T else [[0]]

theorem correct (T : Matrix) : valid T=true ↔ SemigroupTable T ∧ HasUnit T := by
  simp only [valid,SemigroupTable,HasUnit,rows,assocB,unitB,Bool.and_eq_true,decide_eq_true_eq,
    List.all_eq_true,List.any_eq_true,List.mem_range]
  constructor
  · rintro ⟨⟨⟨ne,r⟩,assoc⟩,u⟩; exact ⟨⟨ne,r,fun i j k hi hj hk => assoc i hi j hj k hk⟩,u⟩
  · rintro ⟨⟨ne,r,assoc⟩,u⟩; exact ⟨⟨⟨ne,r⟩,fun i hi j hj k hk => assoc i j k hi hj hk⟩,u⟩

theorem identity {T} (good : SemigroupTable T ∧ HasUnit T) : safe T=T := by simp [safe,(correct _).mpr good]

theorem monoid (T) : SemigroupTable (safe T) ∧ HasUnit (safe T) := by
  unfold safe; split
  next h => exact (correct _).mp h
  next => exact (correct _).mp (by decide)

theorem rowsRec : Primrec rows := by
  unfold rows
  apply P455FramePrim.allB Primrec.id
  apply Primrec₂.mk
  apply Primrec.and.comp (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
    (Primrec.list_length.comp Primrec.fst))
  apply P455FramePrim.allB Primrec.snd
  apply Primrec₂.mk
  exact Primrec.nat_lt.comp Primrec.snd (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))

theorem assocRec : Primrec assocB := by
  unfold assocB
  have n : Primrec fun T : Matrix => List.range T.length := Primrec.list_range.comp Primrec.list_length
  apply P455FramePrim.allB n
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp Primrec.fst)
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp (Primrec.fst.comp Primrec.fst))
  apply Primrec₂.mk
  apply Primrec.eq.comp
  · apply P455NumericProductPrim.entry' ((Primrec.fst.comp Primrec.fst).comp Primrec.fst) _ Primrec.snd
    exact P455NumericProductPrim.entry' ((Primrec.fst.comp Primrec.fst).comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  · apply P455NumericProductPrim.entry' ((Primrec.fst.comp Primrec.fst).comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).comp Primrec.fst)
    exact P455NumericProductPrim.entry' ((Primrec.fst.comp Primrec.fst).comp Primrec.fst) (Primrec.snd.comp Primrec.fst) Primrec.snd

theorem unitRec : Primrec unitB := by
  unfold unitB
  have n : Primrec fun T : Matrix => List.range T.length := Primrec.list_range.comp Primrec.list_length
  apply P455GraphPrim.anyB n
  apply Primrec₂.mk
  apply P455FramePrim.allB (n.comp Primrec.fst)
  apply Primrec₂.mk
  exact Primrec.and.comp (Primrec.eq.comp (P455NumericProductPrim.entry' (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst) Primrec.snd) Primrec.snd) (Primrec.eq.comp
    (P455NumericProductPrim.entry' (Primrec.fst.comp Primrec.fst) Primrec.snd (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem validRec : Primrec valid :=
  Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.nat_lt.comp (Primrec.const 0) Primrec.list_length) rowsRec) assocRec) unitRec

theorem safeRec : Primrec safe :=
  Primrec.ite (Primrec.eq.comp validRec (Primrec.const true)) Primrec.id (Primrec.const [[0]])

end P455TableValidate
