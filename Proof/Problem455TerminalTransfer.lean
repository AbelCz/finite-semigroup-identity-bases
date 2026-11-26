import Problem455Witness
import Problem455SlotOrigin
import Problem455SameDonor



namespace P455TerminalTransfer
open Problem455.Slots P455Witness

/-- In the overflow branch the assignment is specified only on the five
    selected labels. Different source names are enough for the slot bound. -/
def Lift (v : Word) (h : Nat → Word) (x i r : Nat) : SlotDefect → Prop
  | .deficient _ => False
  | .overflow xs => ∃ assign : Nat → Nat, xs.length = 5 ∧ (x :: xs.map assign).Nodup ∧
      ∀ a ∈ xs, occupies v x i (assign a) ∧ a ∈ h (assign a) ∧ v.count (assign a) = r

theorem holds_all {r allow mark z} (qs : List Query) :
    Holds r allow mark z (allQ qs) ↔ ∀ q ∈ qs, Holds r allow mark z q := by
  induction qs with
  | nil => simp [allQ,Holds]
  | cons q qs ih => simp [allQ,Holds,ih]

theorem block_separation {r allow mark z} (xs : List Nat) :
    Holds r allow mark z (differentBlocks xs) ↔
      xs.Pairwise (fun a b => ¬ Problem455Swap.SameBlock r z a b) := by
  induction xs with
  | nil => simp [differentBlocks,Holds]
  | cons a xs ih =>
    simp [differentBlocks,Holds,holds_all,ih,List.pairwise_cons]

theorem terminal (v : Word) (h : Nat → Word) (l k : Word) (x s i r : Nat)
    (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (hx : v.count x = r)
    (hs : s ∈ h x) (guard : ∀ y, occupies v x i y → v.count y = r) {allow mark}
    (d : SlotDefect)
    (obs : Holds r allow mark (l ++ v.flatMap h ++ k) (terminalSlot r s i d)) :
    Lift v h x i r d := by
  let z := l ++ v.flatMap h ++ k
  have capF : ∀ j, (v.flatMap h).count j ≤ r := by
    intro a
    have c := cap a
    simp only [List.count_append] at c
    omega
  have satZ (a y : Nat) (hy : v.count y = r) (ha : a ∈ h y) : z.count a = r := by
    have full := (P455DonorInterval.exclusive h v y a r hr hy ha (capF a)).2.2
    have c := cap a
    simp only [z,List.count_append] at *
    omega
  have common (y a b : Nat) (hy : v.count y = r) (ha : a ∈ h y) (hb : b ∈ h y) :
      Problem455Swap.SameBlock r z a b := by
    have capZ : Problem455Swap.cap r z := by
      intro c
      rw [Problem455BlockBridge.occ_count]
      exact cap c
    exact Problem455Swap.sameBlock_factor ⟨l,k,rfl⟩ capZ
      (Problem455SameDonor.sameDonor v h y hy capF a b ha hb)
  cases d with
  | deficient a =>
    obtain ⟨⟨_,occ⟩,bad⟩ := obs
    change z.count a < r at bad
    rcases P455SlotOrigin.supplier_or_boundary v h l k x s a i r hr cap hx hs occ guard with
        bnd | ⟨y,_,ay,hy,_⟩
    · have := satZ a x hx bnd
      omega
    · have := satZ a y hy ay
      omega
  | overflow xs =>
    change Holds r allow mark z (allQ _) at obs
    have ob := (holds_all _).mp obs
    have len : xs.length = 5 := ob (.fixed _) (by simp)
    have sep := (block_separation (s::xs)).mp (ob _ (by simp))
    obtain ⟨ownerSep,tailSep⟩ := List.pairwise_cons.mp sep
    have rest : ∀ a ∈ xs, occupies z s i a := by
      intro a ha
      have htest : Holds r allow mark z
          (allQ (xs.map fun a => .both (.count a r) (.slot s i a))) := ob _ (by simp)
      have hin := (holds_all _).mp htest (.both (.count a r) (.slot s i a)) (List.mem_map.mpr ⟨a,ha,rfl⟩)
      exact hin.2.2
    classical
    have supply (a : Nat) (ha : a ∈ xs) :
        ∃ y, occupies v x i y ∧ a ∈ h y ∧ v.count y = r ∧ x ≠ y :=
      P455SlotOrigin.supplier v h l k x s a i r hr cap hx hs
        (fun shared => ownerSep a ha (common x s a hx hs shared)) (rest a ha) guard
    let assign := fun a => if ha : a ∈ xs then (supply a ha).choose else x
    have spec (a : Nat) (ha : a ∈ xs) :
        occupies v x i (assign a) ∧ a ∈ h (assign a) ∧ v.count (assign a) = r ∧ x ≠ assign a := by
      simpa [assign,ha] using (supply a ha).choose_spec
    have nodup : (xs.map assign).Nodup := by
      apply List.pairwise_map.mpr
      apply tailSep.imp_of_mem
      intro a b ha hb distinct e
      have A := spec a ha
      have B := spec b hb
      exact distinct (common (assign a) a b A.2.2.1 A.2.1 (e ▸ B.2.1))
    refine ⟨assign,len,List.nodup_cons.mpr ⟨?_,nodup⟩,?_⟩
    · rintro member
      obtain ⟨a,ha,e⟩ := List.mem_map.mp member
      exact (spec a ha).2.2.2 e.symm
    · intro a ha
      have e := spec a ha
      exact ⟨e.1,e.2.1,e.2.2.1⟩

end P455TerminalTransfer
