import Std

namespace JTrivialFollowup

def MutuallyDivisibleTrivial (mul : α → α → α) : Prop :=
  ∀ x y, (∃ a b, x = mul (mul a y) b) →
    (∃ c d, y = mul (mul c x) d) → x = y

/-- A length detects nontrivial multiplication in the nonzero part. -/
theorem of_length (mul : α → α → α) (z e : α) (length : α → Nat)
    (zeroL : ∀ a, mul z a = z) (zeroR : ∀ a, mul a z = z)
    (oneL : ∀ a, mul e a = a) (oneR : ∀ a, mul a e = a)
    (add : ∀ a b, mul a b ≠ z → length (mul a b) = length a + length b)
    (empty : ∀ a, a ≠ z → length a = 0 → a = e) :
    MutuallyDivisibleTrivial mul := by
  rintro x y ⟨a,b,hx⟩ ⟨c,d,hy⟩
  by_cases xz : x = z
  · simpa [xz,zeroL,zeroR] using hy.symm
  by_cases yz : y = z
  · simpa [yz,zeroL,zeroR] using hx
  have step {u v s t : α} (nz : u ≠ z) (h : u = mul (mul s v) t) :
      length u = length s + length v + length t := by
    have h₁ : mul (mul s v) t ≠ z := by simpa [← h] using nz
    have h₂ : mul s v ≠ z := by
      intro es
      exact h₁ (by rw [es,zeroL])
    rw [h, add _ _ h₁, add _ _ h₂]
  have ax := step xz hx
  have ay := step yz hy
  have az : a ≠ z := by
    intro h
    exact xz (by simpa [h,zeroL] using hx)
  have bz : b ≠ z := by
    intro h
    exact xz (by simpa [h,zeroR] using hx)
  have ae := empty a az (by omega)
  have be := empty b bz (by omega)
  simpa [ae,be,oneL,oneR] using hx

theorem pi {ι : Type} {α : ι → Type} (mul : (i : ι) → α i → α i → α i)
    (h : ∀ i, MutuallyDivisibleTrivial (mul i)) :
    MutuallyDivisibleTrivial (fun x y i => mul i (x i) (y i)) := by
  rintro x y ⟨a,b,hx⟩ ⟨c,d,hy⟩
  funext i
  exact h i (x i) (y i)
    ⟨a i,b i,congrFun hx i⟩ ⟨c i,d i,congrFun hy i⟩

end JTrivialFollowup

#print axioms JTrivialFollowup.of_length
#print axioms JTrivialFollowup.pi
