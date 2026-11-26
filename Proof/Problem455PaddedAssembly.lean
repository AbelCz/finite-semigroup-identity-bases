import Problem455PaddedReadback
import Problem455GridAssembly



namespace P455PaddedTiles
open P455Witness
variable {n : Nat} {M : MachineTable n}

private theorem neg_of_ne {a b : Bool} (h : a≠b) : b= !a := by
  cases a <;> cases b <;> simp_all

theorem system_laws (n : Nat) : P455GridRows.Laws (system n) where
  horiz := by
    rintro _ _ ⟨p,q,rfl,rfl,ok⟩
    exact ⟨ok.1,ok.2.1,ok.2.2.1,ok.2.2.2.1,ok.2.2.2.2.1,neg_of_ne ok.2.2.2.2.2.1⟩
  vert := by
    rintro _ _ ⟨p,q,rfl,rfl,ok⟩
    exact ⟨ok.1,ok.2.1,ok.2.2.1.symm,ok.2.2.2.1.symm,ok.2.2.2.2.1.symm,neg_of_ne ok.2.2.2.2.2.1⟩

private theorem odd_next (i : Nat) : odd (i+1)= !odd i := by
  by_cases p : i%2=1
  · simp [odd,p,show (i+1)%2≠1 by omega]
  · simp [odd,p,show (i+1)%2=1 by omega]

private theorem flag_eq {b : Bool} {p : Prop} [Decidable p] (h : b=true ↔ p) : b=decide p := by
  cases b <;> by_cases hp : p <;> simp_all

def from_assembly (A : P455GridAssembly.Rectangle (allowed M) (system n)) :
    Rectangle M (A.width+1) (A.height+1) where
  positiveW := by omega
  positiveH := by omega
  tag := A.tile
  eligible := fun _ iy _ jx => A.allowed _ _ (by omega) (by omega)
  right := fun _ iy _ jx => A.horiz _ _ (by omega) (by omega)
  down := fun _ iy _ jx => A.vert _ _ (by omega) (by omega)
  flags := by
    intro y iy x jx
    have hy : y≤A.height := by omega
    have hx : x≤A.width := by omega
    have tops := A.top y x hy hx
    have lefts := A.left y x hy hx
    refine ⟨flag_eq lefts,flag_eq ((A.right y x hy hx).trans (by omega)),flag_eq tops,
      flag_eq ((A.bottom y x hy hx).trans (by omega)),?_,?_⟩
    · clear tops lefts iy
      induction y with
      | zero =>
        obtain ⟨p,eq,ok⟩ := A.allowed 0 x (by omega) hx
        have top := (A.top 0 x (by omega) hx).mpr rfl
        rw [←eq] at top ⊢
        exact (ok.2.2.2.2.2.1 top).1
      | succ y ih =>
        have pr := (system_laws n).vert _ _ (A.vert y x (by omega) hx)
        rw [pr.2.2.2.2.2,ih (by omega),odd_next]
    · clear tops lefts jx
      induction x with
      | zero =>
        obtain ⟨p,eq,ok⟩ := A.allowed y 0 hy (by omega)
        have left := (A.left y 0 hy (by omega)).mpr rfl
        rw [←eq] at left ⊢
        exact ok.2.2.2.2.1 left
      | succ x ih =>
        have pr := (system_laws n).horiz _ _ (A.horiz y x hy (by omega))
        rw [pr.2.2.2.2.2,ih (by omega),odd_next]

/-- Last row s is the accepting configuration. The trace uses width+1
cells, including when the last column is zero. -/
noncomputable def assembly_trace (A : P455GridAssembly.Rectangle (allowed M) (system n)) :
    AcceptingTrace M (A.width+1) A.height := by
  simpa using read_trace (from_assembly A)

/-- Infinite continuation of literal source-word arrows now yields
a finite accepting trace of the specified transition table. -/
theorem accepts_of_arrows {r : Nat} {mark : Marking} {w : List Nat} (c : Nat → EdgeCertificate)
    (edges : ∀ i, P455GridRows.Arrow r (allowed M) mark w (system n) (c i))
    (cont : ∀ i, (c i).b = (c (i+1)).a)
    (functional : ∀ i, P455GridRows.Functional r (allowed M) mark w (system n) (c i).a) :
    ∃ width s, Nonempty (AcceptingTrace M width s) := by
  obtain ⟨R⟩ := P455GridAssembly.rectangle_of_trace (system_laws n) c edges cont functional
  exact ⟨R.width+1,R.height,⟨assembly_trace R⟩⟩

end P455PaddedTiles
