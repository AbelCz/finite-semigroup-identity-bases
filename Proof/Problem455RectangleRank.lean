import Problem455FirstTesters




namespace P455RectangleRank
open P455FirstRewrite
def owner (i : Nat) := 2*i
def mate (i : Nat) := 2*i+1
def privateCell (i : Nat) : W := [owner i,owner i,mate i,owner i,mate i,mate i]
def mutableCell (bit : Nat → Bool) (i : Nat) : W :=
  if bit i then [mate i,owner i] else [owner i,mate i]

def word (t : Nat) (middle tail : W) (bit : Nat → Bool) :=
  (List.range t).flatMap privateCell ++ middle ++ (List.range t).flatMap (mutableCell bit) ++ tail

def constant (b : Bool) : Nat → Bool := fun _ => b

private theorem within {t i : Nat} (m : i ∈ List.range t) {x : Nat}
    (member : x = owner i ∨ x = mate i) : x < 2*t := by
  have := List.mem_range.mp m
  unfold owner mate at member
  omega

theorem word_names {t : Nat} {middle tail : W} (bit : Nat → Bool)
    (small : ∀ x ∈ middle ++ tail, x < 2*t) (x) (hx : x ∈ word t middle tail bit) : x < 2*t := by
  simp only [word,List.mem_append,List.mem_flatMap] at hx
  rcases hx with ((⟨i,mi,m⟩|m)|⟨i,mi,m⟩)|m
  · apply within mi
    simp only [privateCell,List.mem_cons,List.mem_nil_iff,or_false] at m
    rcases m with h|h|h|h|h|h <;> simp [h]
  · exact small x (List.mem_append_left _ m)
  · apply within mi
    unfold mutableCell at m
    split at m <;> simp_all [Or.comm]
  · exact small x (List.mem_append_right _ m)

private theorem private_factor {t i : Nat} (ix : i < t) (middle tail : W) (bit : Nat → Bool) :
    P455Quotient.Factor (privateCell i) (word t middle tail bit) := by
  obtain ⟨l,r,e⟩ := List.append_of_mem (List.mem_range.mpr ix)
  refine ⟨l.flatMap privateCell,r.flatMap privateCell ++ middle ++
    (List.range t).flatMap (mutableCell bit) ++ tail,?_⟩
  unfold word
  conv => lhs; arg 1; arg 1; arg 1; rw [e]
  simp [List.flatMap_cons,List.append_assoc]

private theorem positive_factor {a b : Nat} {f u : W} (factor : P455Quotient.Factor f u)
    (pos : 0 < Problem455Swap.bigram a b f) : 0 < Problem455Swap.bigram a b u := by
  obtain ⟨p,q,rfl⟩ := factor
  rw [Problem455Swap.bigram_append,Problem455Swap.bigram_append]
  omega




theorem no_links {r t : Nat} (hr : 0 < r) {middle tail : W} (bit : Nat → Bool)
    (small : ∀ x ∈ middle ++ tail, x < 2*t)
    (cap : P455Quotient.Cap r (word t middle tail bit)) :
    P455SourceFamilies.Compressed r (word t middle tail bit) := by
  let U := word t middle tail bit
  intro x y link
  change Problem455Swap.bigram x y U = r at link
  have bound := Problem455Swap.out_bound x y (y+1) (by omega) U
  rw [Problem455BlockBridge.occ_count] at bound
  have mem : x ∈ U := List.count_pos_iff.mp (by omega)
  have smallX := word_names bit small x mem
  let i := x/2
  have ix : i < t := by dsimp [i]; omega
  have either : x = owner i ∨ x = mate i := by simp only [owner,mate,i]; omega
  have ne : owner i ≠ mate i := by simp [owner,mate]
  have fac := private_factor ix middle tail bit
  have aPos : 0 < Problem455Swap.bigram x (owner i) U := by
    apply positive_factor fac
    rcases either with e|e <;> conv => rhs; arg 1; rw [e]
    all_goals simp [privateCell,Problem455Swap.bigram,Problem455Swap.hit,ne,Ne.symm ne] <;> omega
  have bPos : 0 < Problem455Swap.bigram x (mate i) U := by
    apply positive_factor fac
    rcases either with e|e <;> conv => rhs; arg 1; rw [e]
    all_goals simp [privateCell,Problem455Swap.bigram,Problem455Swap.hit,ne,Ne.symm ne] <;> omega
  obtain ⟨z,ny,pz⟩ : ∃ z, y ≠ z ∧ 0 < Problem455Swap.bigram x z U := by
    by_cases e : y = owner i
    · exact ⟨mate i,e ▸ ne,bPos⟩
    · exact ⟨owner i,e,aPos⟩
  have upper := Problem455Swap.out_bound x y z ny U
  rw [Problem455BlockBridge.occ_count] at upper
  have cx : U.count x ≤ r := cap x
  omega

private theorem project_mutable (cells : W) (nd : cells.Nodup) (bit : Nat → Bool) (i : Nat) :
    proj (owner i) (mate i) (cells.flatMap (mutableCell bit)) =
      (if i ∈ cells then mutableCell bit i else []) := by
  induction cells with
  | nil => rfl
  | cons j t ih =>
    have tail := ih (List.nodup_cons.mp nd).2
    by_cases e : i=j
    · subst j
      have out := (List.nodup_cons.mp nd).1
      have one : proj (owner i) (mate i) (mutableCell bit i) = mutableCell bit i := by
        cases hb : bit i <;> simp [proj,mutableCell,hb]
      simp only [List.flatMap_cons,proj,List.filter_append] at tail one ⊢
      rw [one,tail]
      simp [out]
    · have eqs : owner j ≠ owner i ∧ owner j ≠ mate i ∧ mate j ≠ owner i ∧ mate j ≠ mate i := by
        unfold owner mate; omega
      have no : proj (owner i) (mate i) (mutableCell bit j) = [] := by
        cases b : bit j <;> simp [proj,mutableCell,b,eqs.1,eqs.2.1,eqs.2.2.1,eqs.2.2.2]
      simp only [List.flatMap_cons,proj,List.filter_append] at tail no ⊢
      rw [no,tail]
      simp [e]

theorem participants {t : Nat} (middle tail : W) :
    ∀ x ∈ List.range (2*t), ∃ y,
      proj x y (word t middle tail (constant false)) ≠ proj x y (word t middle tail (constant true)) := by
  intro x m
  have lt := List.mem_range.mp m
  let i := x/2
  have mi : i ∈ List.range t := List.mem_range.mpr (by dsimp [i]; omega)
  have pairDiff : proj (owner i) (mate i) (word t middle tail (constant false)) ≠
      proj (owner i) (mate i) (word t middle tail (constant true)) := by
    intro eq
    simp only [word,proj,List.filter_append,List.append_cancel_right_eq,List.append_cancel_left_eq] at eq
    change proj (owner i) (mate i) ((List.range t).flatMap (mutableCell (constant false))) =
      proj (owner i) (mate i) ((List.range t).flatMap (mutableCell (constant true))) at eq
    rw [project_mutable _ List.nodup_range,project_mutable _ List.nodup_range] at eq
    simp [mi,mutableCell,constant,owner,mate] at eq
  have either : x = owner i ∨ x = mate i := by simp only [owner,mate,i]; omega
  rcases either with e|e
  · exact ⟨mate i,e ▸ pairDiff⟩
  · refine ⟨owner i,?_⟩
    rw [e]
    simpa only [proj,Or.comm] using pairDiff

/-- Local inequalities along the numbered snake and its wrap force a
constant bit on all cells. There is no assumption on bits outside the array. -/
theorem cycle_constant {t : Nat} (bit : Nat → Bool) (next : ∀ i, i+1 < t →
      bit i = true → bit (i+1) = true) (wrap : 0 < t → bit (t-1) = true → bit 0 = true) :
    ∃ b, ∀ i < t, bit i = b := by
  have onward (i j : Nat) (le : i ≤ j) (lt : j < t) (yes : bit i = true) : bit j = true := by
    induction j with
    | zero => have := Nat.eq_zero_of_le_zero le; simpa [this] using yes
    | succ j ih =>
      by_cases e : i=j+1
      · exact e ▸ yes
      · exact next j lt (ih (by omega) (by omega))
  by_cases existsTrue : ∃ i < t, bit i = true
  · obtain ⟨i,lt,active⟩ := existsTrue
    have first := wrap (by omega) (onward i (t-1) (by omega) (by omega) active)
    exact ⟨true,fun j lj => onward 0 j (by omega) lj first⟩
  · exact ⟨false,fun i li => by cases eq : bit i <;> simp_all⟩

theorem word_constant {t : Nat} (middle tail : W) (bit : Nat → Bool) (b : Bool)
    (all : ∀ i < t, bit i = b) : word t middle tail bit = word t middle tail (constant b) := by
  have m : (List.range t).flatMap (mutableCell bit) = (List.range t).flatMap (mutableCell (constant b)) := by
    have go (xs : W) (small : ∀ i ∈ xs, i < t) : xs.flatMap (mutableCell bit) = xs.flatMap (mutableCell (constant b)) := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        have tailEq := ih (fun i hi => small i (List.mem_cons_of_mem _ hi))
        simp [List.flatMap_cons,tailEq,mutableCell,constant,all x (small x List.mem_cons_self)]
    exact go _ (fun _ => List.mem_range.mp)
  simp only [word,m]

/-- The remaining semantic inputs are the constant identity, representation
of every identical word by cell bits, and detection of each descending
snake (including wrap) edge. The two-word class is proved from these. -/
theorem witness {A : Type} {M : Model A} {r t : Nat} (hr : 0 < r) (ht : 0 < t) (middle tail : W)
    (small : ∀ x ∈ middle ++ tail, x < 2*t)
    (cap : P455Quotient.Cap r (word t middle tail (constant false)))
    (identity : M.Valid (word t middle tail (constant false)) (word t middle tail (constant true)))
    (represent : ∀ w, M.Valid (word t middle tail (constant false)) w →
      ∃ bit, w = word t middle tail bit)
    (edge : ∀ bit, M.Valid (word t middle tail (constant false)) (word t middle tail bit) →
      (∀ i, i+1 < t → bit i = true → bit (i+1) = true) ∧
      (0 < t → bit (t-1) = true → bit 0 = true)) :
    RankWitness M r (word t middle tail (constant false)) (word t middle tail (constant true))
      (List.range (2*t)) := by
  have m0 : 0 ∈ List.range (2*t) := List.mem_range.mpr (by omega)
  obtain ⟨y,change0⟩ := participants middle tail 0 m0
  have ne : word t middle tail (constant false) ≠ word t middle tail (constant true) :=
    fun e => change0 (congrArg (proj 0 y) e)
  have nonempty (bit : Nat → Bool) : word t middle tail bit ≠ [] := by
    obtain ⟨p,q,eq⟩ := private_factor (i:=0) ht middle tail bit
    rw [eq]; simp [privateCell]
  refine ⟨⟨nonempty _,nonempty _⟩,ne,identity,?_,cap,no_links hr _ small cap,
    List.nodup_range,participants middle tail⟩
  intro w valid
  obtain ⟨bit,rfl⟩ := represent w valid
  obtain ⟨nx,wrap⟩ := edge bit valid
  obtain ⟨b,all⟩ := cycle_constant bit nx wrap
  cases b with
  | false => exact Or.inl (word_constant middle tail bit false all)
  | true => exact Or.inr (word_constant middle tail bit true all)

end P455RectangleRank
