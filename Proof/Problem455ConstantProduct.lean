import Problem455ConstantLayout
import Problem455ReductionBoundary

/- The checked geometric constant-layout implication at the same monoid
   as the finite-basis rank bounds. The mixed bit assignments need no
   assumption of validity, goodness, or membership in a two-word class. -/
namespace P455ConstantProduct
open P455Witness P455FirstRewrite P455Uncrossed P455FirstTesters P455MarkedRank
open P455ConstantLayout
abbrev W := List Nat

private theorem ordinary_chain {A : Type} (M : Model A) {r allow used U V}
    (each : ∀ (f : P455Closure.Frame Nat) (l k : W) (x y : Nat), f.p=[x] → f.q=[y] →
      f.Valid r allow (fun _ _ => False) → M.Valid (side f l k false) (side f l k true))
    (p : Chain r allow used U V) : M.Valid U V := by
  induction p with
  | refl => intro _; rfl
  | snoc _ flip ih =>
    obtain ⟨x,y,f,b,l,k,_,hp,hq,valid,rfl,rfl⟩ := flip
    intro val
    have eq := each f l k x y hp hq valid val
    cases b
    · exact (ih val).trans eq
    · exact (ih val).trans eq.symm

theorem identity {r allow ts} (endWord : Bool → W) (layout : Layout r allow ts endWord) :
    (P455FullSingleton.model r allow ts).Valid (endWord false) (endWord true) := by
  refine (valid_pair ..).mpr ⟨ordinary_chain _ P455FullSingleton.primitive_identity layout.path,
    (valid_pair ..).mpr ⟨(valid_pair ..).mpr ⟨?_,?_⟩,
      (valid_pair ..).mpr ⟨ordinary_chain _ P455BinaryProduct.identity layout.path,
        ordinary_chain _ P455StructuralProduct.identity layout.path⟩⟩⟩
  · intro val; funext i
    obtain ⟨c,only,obs⟩ := P455LocalIdentity.guard_coordinate i
    rw [P455LocalIdentity.coordinate_eval,P455LocalIdentity.coordinate_eval]
    exact marked_equal i.cap endWord layout c only obs _
  · intro val; funext i
    obtain ⟨c,only,obs⟩ := edge_coordinate i
    rw [edge_eval,edge_eval]; exact marked_equal i.cap endWord layout c only obs _

theorem rectangle_no_basis {r allow ts} (hr : 0 < r)
    (padding : ∀ k : Nat, ∃ (t : Nat) (middle tail : W), k < 2*t ∧
      (∀ x ∈ middle ++ tail, x < 2*t) ∧
      Nonempty (Layout r allow ts (fun b => P455RectangleRank.word t middle tail (P455RectangleRank.constant b))) ∧
      (∀ w, (P455FullSingleton.model r allow ts).Valid (P455RectangleRank.word t middle tail (P455RectangleRank.constant false)) w →
        ∃ b, w = P455RectangleRank.word t middle tail b) ∧
      (∀ b, (P455FullSingleton.model r allow ts).Valid (P455RectangleRank.word t middle tail (P455RectangleRank.constant false))
        (P455RectangleRank.word t middle tail b) →
        (∀ i, i+1<t → b i=true → b (i+1)=true) ∧ (0<t → b (t-1)=true → b 0=true)))
    (basis : List (W × W)) (sound : ∀ u v, (u,v) ∈ basis → (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (P455FullSingleton.model r allow ts).Valid U V ∧
      ¬ Derives (fun u v => (u,v) ∈ basis) U V := by
  apply P455ReductionBoundary.rectangle_family_no_basis hr _ basis sound
  intro k
  obtain ⟨t,m,z,large,bounded,⟨layout⟩,represent,edges⟩ := padding k
  have cap : P455Quotient.Cap r (P455RectangleRank.word t m z (P455RectangleRank.constant false)) := by
    intro a; by_cases mem : a ∈ P455RectangleRank.word t m z (P455RectangleRank.constant false)
    · exact Nat.le_of_eq (layout.uniform false a mem)
    · simp [List.count_eq_zero.mpr mem]
  exact ⟨t,m,z,large,bounded,cap,identity _ layout,represent,edges⟩

end P455ConstantProduct
