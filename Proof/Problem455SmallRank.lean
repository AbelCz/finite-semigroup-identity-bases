import Problem455CompressedFrame
import Problem455FirstRewrite



namespace P455SmallRank
open P455Closure P455Compression P455Uncrossed
open P455FirstRewrite (names rank size_le mem_names names_distinct Step Model)

private def lits : List Piece → W
  | [] => []
  | .literal a :: t => a :: lits t
  | .gap _ :: t => lits t

private def gaps (n : Nat) : List Piece → W
  | [] => []
  | .literal _ :: t => gaps (n+1) t
  | .gap _ :: t => n :: gaps (n+1) t

private theorem gap_bound (n : Nat) : ∀ (cs : List Piece), noTouch cs →
    (gaps n cs).length ≤ (lits cs).length + 1
  | [],_ => by simp [gaps,lits]
  | .literal _ :: cs,ok => by
    have := gap_bound (n+1) cs ok
    simpa [gaps,lits] using Nat.le_step this
  | [.gap _],_ => by simp [gaps,lits]
  | .gap _ :: .literal _ :: cs,ok => by
    have h := gap_bound (n+1+1) cs ok
    simp only [gaps,lits,List.length_cons]
    omega
  | .gap _ :: .gap _ :: _,ok => False.elim ok

private theorem lit_subset (cs : List Piece) : (lits cs).Sublist (cs.flatMap body) := by
  induction cs with
  | nil => exact .slnil
  | cons p cs ih =>
    cases p with
    | literal a => exact ih.cons₂ a
    | gap w => exact ih.trans (List.sublist_append_right _ _)

private theorem cover (keep : W) (n : Nat) (cs : List Piece)
    (all : ∀ c ∈ cs,good keep c) (a : Nat) (ha : a ∈ code n cs) :
    a ∈ keep ∨ a ∈ gaps n cs := by
  induction cs generalizing n with
  | nil => cases ha
  | cons c cs ih =>
    have tail (p) (hp : p ∈ cs) := all p (List.mem_cons_of_mem _ hp)
    cases c with
    | literal x =>
      rcases List.mem_cons.mp ha with e|m
      · exact .inl (e ▸ all (.literal x) List.mem_cons_self)
      · exact ih (n+1) tail m
    | gap w =>
      rcases List.mem_cons.mp ha with e|m
      · exact .inr (List.mem_cons.mpr (.inl e))
      · exact (ih (n+1) tail m).imp_right (List.mem_cons_of_mem _)

private theorem lit_mem {keep : W} (cs : List Piece) (all : ∀ c ∈ cs,good keep c) :
    ∀ a ∈ lits cs, a ∈ keep := by
  induction cs with
  | nil => simp [lits]
  | cons c cs ih =>
    have tail (p) (hp : p ∈ cs) := all p (List.mem_cons_of_mem _ hp)
    cases c with
    | literal x =>
      intro a m; rcases List.mem_cons.mp m with e|h
      · exact e ▸ all (.literal x) List.mem_cons_self
      · exact ih tail a h
    | gap _ => exact ih tail

private theorem count_away (a : Nat) (w : W) :
    w.length = w.count a + (w.filter (· != a)).length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases e : b = a <;> simp [e,List.count_cons] <;> omega

private theorem length_bound (r : Nat) (C w : W) (cap : Cap r w)
    (covered : ∀ a ∈ w, a ∈ C) : w.length ≤ r*C.length := by
  induction C generalizing w with
  | nil =>
    cases w with
    | nil => simp
    | cons a t => exact (List.not_mem_nil (covered a List.mem_cons_self)).elim
  | cons a C ih =>
    let t := w.filter (· != a)
    have subset : t.Sublist w := List.filter_sublist
    have ht : Cap r t := fun b => Nat.le_trans (subset.count_le b) (cap b)
    have tc (b) (hb : b ∈ t) : b ∈ C := by
      obtain ⟨bw,ba⟩ := List.mem_filter.mp hb
      exact (List.mem_cons.mp (covered b bw)).resolve_left (by simpa using ba)
    have h := ih t ht tc
    have split := count_away a w
    have c := cap a
    simp only [List.length_cons,Nat.mul_succ]
    dsimp [t] at h; omega

private theorem literal_bound {r : Nat} (u keep : W) (cap : Cap r u) :
    (lits (pieces keep u)).length ≤ r*(names keep).length := by
  have sub := lit_subset (pieces keep u)
  rw [decoded] at sub
  apply length_bound
  · exact fun a => Nat.le_trans (sub.count_le a) (cap a)
  · exact fun a h => (mem_names a keep).mpr (lit_mem _ (pieces_good keep u) a h)

private theorem code_length (n : Nat) (cs : List Piece) :
    (code n cs).length = (lits cs).length + (gaps n cs).length := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [code,lits,gaps,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem small_length {r : Nat} (u keep : W) (cap : Cap r u) :
    (small u keep).length ≤ 2*(r*(names keep).length)+1 := by
  have l := literal_bound u keep cap
  have g := gap_bound (base u keep) (pieces keep u) (maximal keep u)
  unfold small; rw [code_length]; omega

/-- Covers the joint rank of both sides when they have identical support,
    counting each kept name only once even when the given list contains repeats. -/
theorem joint_rank {r : Nat} (u keep v : W) (cap : Cap r u)
    (same : ∀ a ∈ v, a ∈ small u keep) :
    rank (small u keep) v ≤ (names keep).length + r*(names keep).length + 1 := by
  let cs := pieces keep u
  let n := base u keep
  have l := literal_bound u keep cap
  have g := gap_bound n cs (maximal keep u)
  have le : rank (small u keep) v ≤ ((names keep) ++ gaps n cs).length := by
    apply size_le (names_distinct _)
    intro a ha
    have ma := (List.mem_append.mp ((mem_names _ _).mp ha)).elim id (same a)
    have mem := cover keep n cs (pieces_good keep u) a ma
    exact List.mem_append.mpr (mem.imp_left (mem_names a keep).mpr)
  simp only [List.length_append] at le
  dsimp only [cs] at g; dsimp only [cs] at le; omega

private theorem lookup_nonempty (keep : W) (cs : List Piece) (all : ∀ c ∈ cs,good keep c)
    (n a : Nat) : lookup n cs a ≠ [] := by
  induction cs generalizing n with
  | nil => simp [lookup]
  | cons c cs ih =>
    have tail (p) (hp : p ∈ cs) := all p (List.mem_cons_of_mem _ hp)
    cases c with
    | literal x => exact ih tail (n+1)
    | gap w =>
      by_cases e : a=n
      · simpa only [lookup,if_pos e] using (all (.gap w) List.mem_cons_self).1
      · simpa only [lookup,if_neg e] using ih tail (n+1)

theorem expansion_nonempty (u keep : W) (a : Nat) : expand u keep a ≠ [] :=
  lookup_nonempty keep _ (pieces_good keep u) _ a

/-- The literal source flip is one step using a semantically valid identity on
    at most N + r*N + 1 variables. All substitution images, even for unused
    variables, are nonempty semigroup words. -/
theorem bounded_step {A : Type} (M : Model A) {r allowed} (f : Frame Nat)
    (l k keep : W) {x y : Nat} (hx : x ∈ keep) (hy : y ∈ keep)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allowed (fun _ _ => False))
    (b : Bool) (cap : Cap r (side f l k b))
    (semantic : M.Valid (small (side f l k b) keep) (small (side f l k (!b)) keep)) :
    let N := (names keep).length
    Step (fun u v => M.Valid u v ∧ rank u v ≤ N+r*N+1)
      (side f l k b) (side f l k (!b)) := by
  dsimp only
  obtain ⟨g,left,right,gp,_,_,eq,expanded⟩ :=
    P455CompressedFrame.canonical_pair f l k keep hx hy hp hq valid b cap
  have letters (a) (ha : a ∈ small (side f l k (!b)) keep) : a ∈ small (side f l k b) keep := by
    rw [eq] at ha ⊢
    exact (P455Uncrossed.same_letters g left right b a).mpr ha
  have nonempty (c : Bool) : small (side f l k c) keep ≠ [] := by
    rw [eq]; obtain ⟨t,e⟩ := g.core_starts c
    simp [side,e]
  refine ⟨_,_,[],[],expand (side f l k b) keep,.inl ⟨semantic,joint_rank _ _ _ cap letters⟩,
    nonempty b,nonempty (!b),expansion_nonempty _ _,?_,?_⟩
  all_goals simp only [List.nil_append,List.append_nil,eq,expanded]

end P455SmallRank
