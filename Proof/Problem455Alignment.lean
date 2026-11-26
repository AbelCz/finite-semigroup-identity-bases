import Problem455CellClassBinary
import Problem455ContactReflection

/- A matching of inverted comparisons of indexed positions forces literal
   adjacent transpositions. This argument works directly on arbitrary
   permutations, without choosing a pre-existing cell layout. -/
namespace P455Alignment
open P455Witness P455Paths P455ContactReflection Problem455.Slots

def Inverted {α : Type} (u v : List α) (a b : α) := [a,b].Sublist u ∧ [b,a].Sublist v

inductive Blocks {α : Type} (mates : α → α → Prop) : List α → List α → Prop where
  | nil : Blocks mates [] []
  | fixed (x) {u v} : Blocks mates u v → Blocks mates (x::u) (x::v)
  | pair (x y) {u v} : mates x y → Blocks mates u v → Blocks mates (x::y::u) (y::x::v)

private theorem prep {α : Type} (a : α) {b : α} {w : List α} (inW : b ∈ w) :
    [a,b].Sublist (a::w) := (List.singleton_sublist.mpr inW).cons₂ a

private theorem second {α : Type} [DecidableEq α] {a b : α} {u v : List α}
    (neq : a≠b) (distinct : (a::u).Nodup) (same : (a::u).Perm (b::v))
    (M : α → α → Prop) (sym : ∀ {x y}, M x y → M y x) (unique : ∀ {x y z}, M x y → M x z → y=z)
    (cross : ∀ x y, Inverted (a::u) (b::v) x y → M x y) : ∃ t, u=b::t := by
  have bu := (List.mem_cons.mp (same.mem_iff.mpr (List.mem_cons_self : b ∈ b::v))).resolve_left (Ne.symm neq)
  have av := (List.mem_cons.mp (same.mem_iff.mp (List.mem_cons_self : a ∈ a::u))).resolve_left neq
  have ba := sym (cross _ _ ⟨prep _ bu,prep _ av⟩)
  cases u with
  | nil => contradiction
  | cons c t =>
    by_cases e : c=b
    · exact ⟨t,by rw [e]⟩
    have bt := (List.mem_cons.mp bu).resolve_left (Ne.symm e)
    have cv := (List.mem_cons.mp (same.mem_iff.mp (show c∈a::c::t by simp))).resolve_left e
    have bc := sym (cross _ _ ⟨(prep c bt).cons a,prep b cv⟩)
    have ca := unique bc ba
    exact False.elim ((List.nodup_cons.mp distinct).1 (ca ▸ List.mem_cons_self))

/-- If each inverted pair is an edge of a matching, the original words
    split into the same sequence of singles and disjoint transposed pairs. -/
theorem align {α : Type} [DecidableEq α] (M : α → α → Prop)
    (sym : ∀ {x y}, M x y → M y x) (unique : ∀ {x y z}, M x y → M x z → y=z)
    (u v : List α) (distinct : u.Nodup) (same : u.Perm v)
    (cross : ∀ x y, Inverted u v x y → M x y) : Blocks M u v := by
  cases u with
  | nil => obtain rfl := same.nil_eq; exact .nil
  | cons a u =>
    cases v with
    | nil => cases same.length_eq
    | cons b v =>
      by_cases eq : a=b
      · subst b
        exact .fixed a (align M sym unique u v (List.nodup_cons.mp distinct).2
          ((List.perm_cons _).mp same) (fun x y e => cross x y ⟨e.1.cons a,e.2.cons a⟩))
      · obtain ⟨u',rfl⟩ := second eq distinct same M sym unique cross
        obtain ⟨v',rfl⟩ := second (Ne.symm eq) (same.nodup_iff.mp distinct) same.symm M sym unique
          (fun x y h => sym (cross y x ⟨h.2,h.1⟩))
        have aligned : (a::b::u').Perm (a::b::v') := same.trans (.swap _ _ _)
        have common := (List.perm_cons _).mp ((List.perm_cons _).mp aligned)
        have pair := cross a b ⟨prep _ List.mem_cons_self,prep _ List.mem_cons_self⟩
        exact .pair a b pair (align M sym unique u' v' ((List.nodup_cons.mp
          (List.nodup_cons.mp distinct).2).2) common (fun x y e =>
            cross x y ⟨(e.1.cons b).cons a,(e.2.cons a).cons b⟩))
termination_by u.length

end P455Alignment
