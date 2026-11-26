import Problem455PrefixValidity



namespace P455Prefix
open P455FirstRewrite P455Compression P455Quotient

def gather (r x : Nat) (u : Word) := List.replicate (r+1) x ++ dropName x u
def Steps (r : Nat) (allow : P455Witness.Tag → Prop) (ts : P455Witness.Tiles) (u v : Word) :=
  (P455FullSingleton.model r allow ts).Valid u v ∧ rank u v ≤ 2*(r+2)+1

@[simp] theorem drop_mem (a x : Nat) (u : Word) : a ∈ dropName x u ↔ a ∈ u ∧ a ≠ x := by
  simp [dropName]

@[simp] theorem drop_count (a x : Nat) (u : Word) :
    (dropName x u).count a = if a = x then 0 else u.count a := by
  by_cases h : a = x
  · rw [if_pos h]; exact List.count_eq_zero.mpr (fun m => ((drop_mem ..).mp m).2 h)
  · simp [dropName,List.count_filter,h]

@[simp] theorem gather_drop (r x : Nat) (u : Word) :
    dropName x (gather r x u) = dropName x u := by
  simp [gather,dropName,List.filter_append,List.filter_filter]

@[simp] theorem gather_count (r x : Nat) (u : Word) : (gather r x u).count x = r+1 := by
  simp [gather]

private theorem code_len (n : Nat) (cs : List Piece) : (code n cs).length = cs.length := by
  induction cs generalizing n with
  | nil => rfl
  | cons p cs ih => cases p <;> simp [code,ih]

private theorem compact_length (x : Nat) :
    ∀ cs : List Piece, noTouch cs → (∀ p ∈ cs, good [x] p) →
      cs.length ≤ 2*(cs.flatMap body).count x+1
  | [],_,_ => by simp
  | .literal b :: cs,ok,g => by
    have bx : b = x := List.mem_singleton.mp (g _ List.mem_cons_self)
    have tail := compact_length x cs ok (fun p h => g _ (List.mem_cons_of_mem _ h))
    subst b
    simp [body,List.count_cons]; omega
  | [.gap a],_,_ => by simp [body]
  | .gap a :: .literal b :: cs,ok,g => by
    have bx : b = x := List.mem_singleton.mp (g (.literal b) (by simp))
    have tail := compact_length x cs ok (fun p h => g _ (by simp [h]))
    subst b
    simp [body,List.count_cons]; omega
  | .gap _ :: .gap _ :: _,ok,_ => False.elim ok

private theorem small_len (u : Word) (x : Nat) : (small u [x]).length ≤ 2*u.count x+1 := by
  have h := compact_length x (pieces [x] u) (maximal [x] u) (pieces_good [x] u)
  rw [decoded] at h
  simpa only [small,code_len] using h

private theorem expand_drop {s : Word} {e : Nat → Word} {x : Nat}
    (exp : P455Retained.Expansion s e (fun a => a ∈ [x])) :
    ∀ (t : Word), (∀ a ∈ t, a ∈ s) → (dropName x t).flatMap e = dropName x (t.flatMap e) := by
  intro t sub
  induction t with
  | nil => rfl
  | cons a t ih =>
    have inc (b) (h : b ∈ t) := sub b (List.mem_cons_of_mem _ h)
    have eq := ih inc
    have m := sub a List.mem_cons_self
    by_cases same : a = x
    · subst a
      simpa [dropName,List.filter_append,exp.literal x m (by simp)] using eq
    · have gap := exp.gaps a m (by simpa using same)
      have all : (e a).filter (· != x) = e a := List.filter_eq_self.mpr (fun b hb => by
        simpa using gap.2.2 b hb)
      simpa [dropName,List.filter_append,same,all] using congrArg (List.append (e a)) eq

private theorem map_reps (k x : Nat) (e : Nat → Word) (fixed : e x = [x]) :
    (List.replicate k x).flatMap e = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,fixed,ih]

/-- If at most r+2 copies are present, the entire collection and truncation
    of this name takes a single rule instance with at most 2(r+2)+1 names,
    regardless of the length or multiplicities of the intervening gaps. -/
theorem gather_step {r allow ts x} (u : Word) (lo : r < u.count x) (hi : u.count x ≤ r+2) :
    Step (Steps r allow ts) u (gather r x u) := by
  let s := small u [x]
  let e := expand u [x]
  have cnt : s.count x = u.count x := counts_retained u [x] x (by simp)
  have xs : x ∈ s := List.count_pos_iff.mp (by omega)
  have expanded : s.flatMap e = u := recover u [x]
  have exp := canonical u [x]
  have fixed : e x = [x] := exp.literal x xs (by simp)
  have right : (gather r x s).flatMap e = gather r x u := by
    rw [gather,List.flatMap_append,map_reps _ _ _ fixed, expand_drop exp s (fun _ m => m),expanded]
    rfl
  have covers (a : Nat) (h : a ∈ gather r x s) : a ∈ s := by
    rcases List.mem_append.mp h with h|h
    · exact (List.eq_of_mem_replicate h) ▸ xs
    · exact ((drop_mem ..).mp h).1
  have rankBound : rank s (gather r x s) ≤ s.length := by
    apply size_le (names_distinct _)
    intro a ha
    exact (List.mem_append.mp ((mem_names ..).mp ha)).elim id (covers a)
  have short := small_len u x
  change s.length ≤ _ at short
  have valid := overflow_valid (allow := allow) (ts := ts) (x := x) (u := s) (w := gather r x s)
    (by omega : r < s.count x) (by simp) (gather_drop r x s).symm
  refine ⟨s,gather r x s,[],[],e,.inl ⟨valid,by omega⟩,fun h => ?_,?_,
    P455SmallRank.expansion_nonempty u [x],by simpa using expanded.symm,by simpa using right.symm⟩
  · simp [h] at xs
  · simp [gather,List.replicate_succ]

theorem context_step {G : Word → Word → Prop} {u v : Word} (p q : Word) (s : Step G u v) :
    Step G (p ++ u ++ q) (p ++ v ++ q) := by
  obtain ⟨a,b,l,t,h,rule,an,bn,hn,rfl,rfl⟩ := s
  exact ⟨a,b,p++l,t++q,h,rule,an,bn,hn,by simp [List.append_assoc],by simp [List.append_assoc]⟩

theorem context_derives {G : Word → Word → Prop} {u v : Word} (p q : Word) (s : Derives G u v) :
    Derives G (p ++ u ++ q) (p ++ v ++ q) := by
  induction s with
  | refl => exact .refl _
  | snoc _ step ih => exact .snoc ih (context_step p q step)

/-- All high multiplicities, including arbitrarily large ones. -/
theorem gather_deduction {r allow ts x} (u : Word) (sat : r < u.count x) :
    Derives (Steps r allow ts) u (gather r x u) := by
  induction u with
  | nil => simp at sat
  | cons a t ih =>
    by_cases tail : r < t.count x
    · have path := context_derives [a] [] (ih tail)
      have low : r < (a :: gather r x t).count x := by simp [List.count_cons]; omega
      have high : (a :: gather r x t).count x ≤ r+2 := by simp [List.count_cons]; split <;> omega
      have step := gather_step (allow := allow) (ts := ts) _ low high
      have eq : gather r x (a::gather r x t) = gather r x (a::t) := by
        by_cases same : a=x <;> simp [gather,dropName,List.filter_append,List.filter_filter,same]
      exact (show Derives (Steps r allow ts) (a::t) (a::gather r x t) by simpa using path).snoc (eq ▸ step)
    · have high : (a :: t).count x ≤ r+2 := by simp only [List.count_cons]; split <;> omega
      exact .snoc (.refl _) (gather_step _ sat high)

end P455Prefix
