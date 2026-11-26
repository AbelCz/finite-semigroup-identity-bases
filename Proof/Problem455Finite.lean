import Problem455Closure
import Problem455Quotient



namespace Problem455Finite

def rules (r : Nat) (allow : List Bool → Prop) (mark : Nat → Nat → Prop) :
    P455Quotient.Rules Nat where
  r := r
  step := P455Closure.Move r allow mark
  reverse := P455Closure.Move.symm
  counts := P455Closure.Move.count_eq
  extend h l t := P455Closure.Move.extend_of_cap h l t

open P455Quotient

/-- Enumerate all words of length at most n on the input list alphabet.
    Duplicates in the alphabet are harmless. -/
def wordsUpTo (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => [] :: alphabet.flatMap (fun a => (wordsUpTo alphabet n).map (List.cons a))

theorem covered (a : List α) (n : Nat) (w : List α) (len : w.length ≤ n)
    (names : ∀ x ∈ w, x ∈ a) : w ∈ wordsUpTo a n := by
  induction n generalizing w with
  | zero =>
    cases w <;> simp_all [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons x w =>
      have hx := names x (by simp)
      have hl : w.length ≤ n := by simpa using len
      have hw := ih w hl (fun z hz => names z (by simp [hz]))
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      exact ⟨x,hx,List.mem_map.mpr ⟨w,hw,rfl⟩⟩

theorem good_bound [DecidableEq α] (R : Rules α) (T w : Word α)
    (good : Good R T w) : w.length ≤ T.length ∧ ∀ x ∈ w, x ∈ T := by
  obtain ⟨v,path,l,t,hv⟩ := good
  have perm := List.perm_iff_count.mpr (count_walk R path)
  have len := perm.length_eq
  refine ⟨?_,?_⟩
  · simp only [hv,List.length_append] at len
    omega
  · intro x hx
    apply perm.mem_iff.mpr
    simp [hv,hx]

/-- A list of every quotient element, possibly with repeated entries.
    This enumerates the explicit zero even for an empty template. -/
def carrier [DecidableEq α] (R : Rules α) (T : Word α) : List (Q R T) :=
  zero R T :: (wordsUpTo T T.length).map (ofWord R T)

theorem carrier_complete [DecidableEq α] (R : Rules α) (T : Word α) (q : Q R T) :
    q ∈ carrier R T := by
  by_cases dead : q = zero R T
  · simp [carrier,dead]
  · obtain ⟨w,good,e⟩ := nonzero_representative R q dead
    obtain ⟨len,names⟩ := good_bound R T w good
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, covered T T.length w len names, e⟩)

end Problem455Finite
