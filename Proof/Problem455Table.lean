import Problem455Decision



namespace P455Table
open P455FirstRewrite

structure FiniteOps where
  size : Nat
  one : Fin size
  mul : Fin size → Fin size → Fin size

structure Presents {A : Type} (X : FiniteOps) (M : Model A) where
  decode : Fin X.size → A
  inj : ∀ i j, decode i=decode j → i=j
  surj : ∀ a, ∃ i, decode i=a
  one_eq : decode X.one=M.unit
  mul_eq : ∀ i j, decode (X.mul i j)=M.op (decode i) (decode j)

/-- An executable list cover and equality test. Neither is obtained by choice. -/
structure Listing (A : Type) where
  eq : DecidableEq A
  items : List A
  all : ∀ x, x∈items

def distinct [DecidableEq A] : List A → List A
  | [] => []
  | x::xs => if x∈xs then distinct xs else x::distinct xs

theorem mem_distinct [DecidableEq A] (a : A) (xs : List A) : a∈distinct xs ↔ a∈xs := by
  induction xs with
  | nil => simp [distinct]
  | cons x xs ih =>
    by_cases h : x∈xs
    · simp only [distinct,if_pos h,ih,List.mem_cons]
      exact ⟨Or.inr,fun v => v.elim (fun e => e ▸ h) id⟩
    · simp [distinct,h,ih]

theorem nodup_distinct [DecidableEq A] (xs : List A) : (distinct xs).Nodup := by
  induction xs with
  | nil => simp [distinct]
  | cons x xs ih =>
    by_cases h : x∈xs
    · simpa [distinct,h] using ih
    · simpa [distinct,h,List.nodup_cons,mem_distinct] using ih

def number [DecidableEq A] (a : A) : (xs : List A) → a∈xs → Fin xs.length
  | [], h => nomatch h
  | x::xs, h => if e : a=x then ⟨0,by simp⟩ else
      (number a xs ((List.mem_cons.mp h).resolve_left e)).succ

theorem number_get [DecidableEq A] (a : A) (xs : List A) (h : a∈xs) :
    xs.get (number a xs h) = a := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    by_cases e : a=x
    · subst a; simp [number]
    · simp only [number,dif_neg e]
      exact ih _

def finiteOps {A : Type} (L : Listing A) (M : Model A) : FiniteOps := by
  letI := L.eq
  let xs := distinct L.items
  have all (a : A) : a∈xs := (mem_distinct a L.items).mpr (L.all a)
  exact ⟨xs.length,number _ xs (all M.unit),fun i j => number _ xs (all (M.op (xs.get i) (xs.get j)))⟩

def presentation {A : Type} (L : Listing A) (M : Model A) : Presents (finiteOps L M) M := by
  letI := L.eq
  let xs := distinct L.items
  have all (a : A) : a∈xs := (mem_distinct a L.items).mpr (L.all a)
  refine ⟨xs.get,?_,fun a => ⟨number a xs (all a),number_get ..⟩,number_get ..,fun i j => number_get ..⟩
  intro i j e
  apply Fin.ext
  apply List.getElem?_inj (xs := xs) i.isLt (nodup_distinct _)
  have left : xs[i.val]?=some (xs.get i) := List.getElem?_eq_getElem (by exact i.isLt)
  have right : xs[j.val]?=some (xs.get j) := List.getElem?_eq_getElem (by exact j.isLt)
  exact left.trans ((congrArg some e).trans right.symm)

abbrev Matrix := List (List Nat)

/-- The output contains only multiplication. Numeric names range from zero
    to the number of rows minus one. -/
def matrix (X : FiniteOps) : Matrix :=
  (List.finRange X.size).map fun i => (List.finRange X.size).map fun j => (X.mul i j).val

def entry (T : Matrix) (i j : Nat) := (T[i]?.getD [])[j]?.getD 0

@[simp] theorem matrix_length (X : FiniteOps) : (matrix X).length=X.size := by simp [matrix]

theorem matrix_entry (X : FiniteOps) (i j : Fin X.size) : entry (matrix X) i j=(X.mul i j).val := by
  simp [entry,matrix,List.getElem?_eq_getElem,i.isLt,j.isLt]

theorem square (X : FiniteOps) : ∀ row∈matrix X, row.length=X.size ∧ ∀ a∈row, a<X.size := by
  intro row mem
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
  refine ⟨by simp,?_⟩
  intro a m; obtain ⟨j,_,rfl⟩ := List.mem_map.mp m
  exact (X.mul i j).isLt

end P455Table
