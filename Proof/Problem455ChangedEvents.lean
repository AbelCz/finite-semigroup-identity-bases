import Problem455Alignment

/- From a genuine capped identity to the order of its indexed positions.
   Only matching of the changed *names* is needed by the final lemma. -/
namespace P455ChangedEvents
open P455Witness P455Paths P455Alignment P455ContactReflection Problem455.Slots
abbrev W := List Nat

theorem stamped_perm {u v : W} (p : u.Perm v) (n : Nat → Nat) : (stamp n u).Perm (stamp n v) := by
  induction p generalizing n with
  | nil => exact .nil
  | cons a _ ih => exact .cons _ (ih _)
  | trans _ _ ih jh => exact (ih n).trans (jh n)
  | swap a b t =>
    by_cases eq : a=b
    · subst b; exact .refl _
    have oa : advance n [b] a=n a := by simp [advance,eq,Ne.symm eq]
    have ob : advance n [a] b=n b := by simp [advance,eq,Ne.symm eq]
    have tail : advance (advance n [a]) [b]=advance (advance n [b]) [a] := by
      funext z; simp only [advance]; omega
    simp only [stamp,oa,ob,tail]
    exact .swap _ _ _

private theorem earlier_idx {α : Type} [DecidableEq α] (x y : α) (w : List α) (nd : w.Nodup)
    (pat : [x,y].Sublist w) : w.idxOf x < w.idxOf y := by
  induction w with
  | nil => cases pat
  | cons b w ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    cases pat with
    | cons _ h =>
      have bx : b≠x := fun e => fresh (e ▸ h.subset (by simp))
      have by' : b≠y := fun e => fresh (e ▸ h.subset (by simp))
      simpa only [List.idxOf_cons,cond_eq_if,beq_iff_eq,if_neg bx,if_neg by',
        if_neg (Ne.symm bx),if_neg (Ne.symm by'),Nat.add_lt_add_iff_right] using ih rest h
    | cons₂ _ h =>
      have xy : x≠y := fun e => fresh (e ▸ h.subset List.mem_cons_self)
      simp [List.idxOf_cons,cond_eq_if,beq_iff_eq,xy,Ne.symm xy]

private theorem impossible {w : W} {x y : Event} (h : sees w [x,y]) (g : sees w [y,x]) : False :=
  Nat.lt_asymm (earlier_idx _ _ _ (stamp_unique _ _) h) (earlier_idx _ _ _ (stamp_unique _ _) g)

private theorem count_tag {a b z : Nat} (ne : a≠b) (which : z=a ∨ z=b) (tag : Tag) :
    (tag.flatMap (pair a b)).count z=tag.length := by
  induction tag with
  | nil => simp
  | cons bit t ih =>
    cases bit <;> rcases which with rfl|rfl <;>
      simp [pair,List.flatMap_cons,List.count_cons,ih,ne,Ne.symm ne,Nat.add_comm]

private theorem prefix_count {a b z : Nat} (ne : a≠b) (which : z=a ∨ z=b) (tag : Tag) :
    (profilePrefix a b tag).count z=14+tag.length := by
  have tt := count_tag ne which tag
  rcases which with rfl|rfl <;>
    simp [profilePrefix,List.replicate_succ,List.count_cons,ne,Ne.symm ne,tt] <;> omega

private def profileMove {a b : Nat} (ne : a≠b) (tag : Tag) : Move (14+tag.length) where
  pre := profilePrefix a b tag
  p := [a]
  q := [b]
  post := [a,b]
  dp := by simp
  dq := by simp
  disjoint := by simpa using ne
  indexP := by intro z hz; exact prefix_count ne (.inl (List.mem_singleton.mp hz)) tag
  indexQ := by intro z hz; exact prefix_count ne (.inr (List.mem_singleton.mp hz)) tag

private theorem same_if_missing {a b : Nat} (ne : a≠b) (tag : Tag) (bit : Bool) (pat : List Event)
    (missing : (a,14+tag.length) ∉ pat ∨ (b,14+tag.length) ∉ pat) :
    sees (profile a b tag bit) pat ↔ sees (profile a b tag (!bit)) pat := by
  let m := profileMove ne tag
  have flat : sees (before m) pat ↔ sees (after m) pat :=
    sees_invariant m pat (by simpa [m,profileMove] using missing)
  cases bit
  · exact flat
  · exact flat.symm

private theorem one_name {u : W} (a : Nat) : select [a,a] u=List.replicate (u.count a) a := by
  induction u with
  | nil => rfl
  | cons b t ih =>
    by_cases e : a=b
    · subst b; simpa [select,List.count_cons,List.replicate_succ] using congrArg (List.cons a) ih
    · simpa [select,List.count_cons,e,Ne.symm e,beq_iff_eq] using ih

def ChangedPair (u v : W) (x y : Nat) := select [x,y] u ≠ select [x,y] v

/-- Every inverted comparison in arbitrary capped endpoints is precisely a
    comparison of the two mutable indexed copies in a changed binary profile. -/
theorem inverted_indices {r allow ts u v} (cap : P455Closure.Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (x y : Event)
    (cross : Inverted (events u) (events v) x y) :
    x.1 ≠ y.1 ∧ ChangedPair u v x.1 y.1 ∧ x.2=r-2 ∧ y.2=r-2 := by
  let ks := [x.1,y.1]
  have obs := sees_select ks u [x,y] (by simp [ks]) cross.1
  have rev := sees_select ks v [y,x] (by simp [ks]) cross.2
  have diff : select ks u ≠ select ks v := by
    intro eq; exact impossible (eq ▸ obs) rev
  have names : x.1≠y.1 := by
    intro eq
    have e : select [x.1,y.1] u = select [x.1,y.1] v := by
      rw [← eq,one_name,one_name,P455CellClassBinary.exact_counts cap valid]
    exact diff e
  obtain ⟨a,b,tag,bit,roles,len,_,U,V⟩ := P455CellClassBinary.changed cap valid names diff
  have ab : a≠b := by rcases roles with ⟨h,j⟩|⟨h,j⟩ <;> rw [h,j] <;> first | exact names | exact Ne.symm names
  change sees (select [x.1,y.1] u) [x,y] at obs
  change sees (select [x.1,y.1] v) [y,x] at rev
  rw [U] at obs; rw [V] at rev
  have necessary : (a,14+tag.length) ∈ [x,y] ∧ (b,14+tag.length) ∈ [x,y] := by
    constructor <;> apply Classical.byContradiction <;> intro missing
    · exact impossible ((same_if_missing ab tag bit _ (.inl missing)).mp obs) rev
    · exact impossible ((same_if_missing ab tag bit _ (.inr missing)).mp obs) rev
  obtain ⟨ax,bx⟩ := necessary
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ax bx
  refine ⟨names,diff,?_⟩
  rcases ax with e|e <;> rcases bx with f|f
  · exact False.elim (ab (congrArg Prod.fst (e.trans f.symm)))
  · rw [← e,← f]; simp only; omega
  · rw [← f,← e]; simp only; omega
  · exact False.elim (ab (congrArg Prod.fst (e.trans f.symm)))

def Mates (u v : W) (r : Nat) (x y : Event) := ChangedPair u v x.1 y.1 ∧ x.2=r-2 ∧ y.2=r-2

theorem blocks_of_matching {r allow ts u v} (cap : P455Closure.Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (matching : ∀ a b c, ChangedPair u v a b → ChangedPair u v a c → b=c) :
    Blocks (Mates u v r) (events u) (events v) := by
  have cnt := P455CellClassBinary.exact_counts cap valid
  refine align (Mates u v r) ?_ ?_ (events u) (events v) (stamp_unique _ _) (stamped_perm (List.perm_iff_count.mpr cnt) _) ?_
  · intro x y h
    refine ⟨?_,h.2.2,h.2.1⟩
    unfold ChangedPair at *
    simpa only [select_pair_symm x.1 y.1] using h.1
  · intro x y z h k
    exact Prod.ext (matching _ _ _ h.1 k.1) (h.2.2.trans k.2.2.symm)
  · intro x y i; exact (inverted_indices cap valid x y i).2

end P455ChangedEvents
