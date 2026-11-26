import Problem455PrefixLinkInvariance



namespace P455Prefix
open P455Quotient P455FirstRewrite P455Witness Problem455.Slots
open Problem455Swap (bigram Link hit)

def beforePair (a b z : Nat) : Word := if z=b then [a,b] else [z]

theorem recover_link_left {r a b} {w : Word} (hr : 0 < r) (cap : Cap r w) (l : Link r w a b) :
    (dropName a w).flatMap (beforePair a b) = w := by
  have ne : a ≠ b := fun e => not_self hr cap (e ▸ l)
  have restore (t : Word) (fresh : b ∉ t) : (dropName a (t.flatMap (openPair a b))).flatMap
      (beforePair a b) = t.flatMap (openPair a b) := by
    induction t with
    | nil => rfl
    | cons x t ih =>
      have xb : x ≠ b := fun e => fresh (e ▸ List.mem_cons_self)
      have tail := ih (fun h => fresh (List.mem_cons_of_mem _ h))
      simp only [List.flatMap_cons,dropName,List.filter_append,List.flatMap_append] at tail ⊢
      rw [tail]
      by_cases xa : x=a <;> simp [openPair,beforePair,xa,xb,ne,Ne.symm ne]
  have h := restore (dropName b w) (by simp)
  rwa [recover_link cap l] at h

/-- Every b,c boundary of the input appears between the last symbol of the
    b-image and first symbol of the c-image. Further occurrences only help. -/
theorem boundary_count (g : Nat → Word) (b c X Y : Nat) (last : (g b).getLast? = some X)
    (first : (g c).head? = some Y) (w : Word) :
    bigram b c w ≤ bigram X Y (w.flatMap g) := by
  induction w with
  | nil => simp [bigram]
  | cons j t ih =>
    rw [List.flatMap_cons,Problem455Swap.bigram_append]
    change hit b c (some j) t.head? + bigram b c t ≤ _
    by_cases h : j=b ∧ t.head?=some c
    · obtain ⟨rfl,p⟩ := h
      have head : (t.flatMap g).head? = some Y := by
        cases t with
        | nil => simp at p
        | cons x s =>
          have xc : x=c := Option.some.inj p
          subst x
          cases e : g c with
          | nil => simp [e] at first
          | cons k ks => simpa [e] using first
      simp [hit,p,last,head]; omega
    · simp [hit,h]; omega

private theorem computed_link {r b c X Y} {w v : Word} (cap : Cap r v) (g : Nat → Word)
    (recover : w.flatMap g = v) (edge : Link r w b c)
    (last : (g b).getLast? = some X) (first : (g c).head? = some Y) : Link r v X Y := by
  have low := boundary_count g b c X Y last first w
  rw [recover,show bigram b c w=r from edge] at low
  have top := Problem455Swap.out_bound X Y (Y+1) (by omega) v
  rw [Problem455BlockBridge.occ_count] at top
  have := cap X
  change bigram X Y v=r; omega

/-- If deleting z repairs b→c and z itself is attached to some saturated
    name by a repeated directed link, it must occupy precisely b|c at every
    occurrence. No claim is made about any unattached outsider. -/
theorem inserted_between {r b c z} {w : Word} (hr : 0 < r) (cap : Cap r w)
    (after : Link r (dropName z w) b c) (split : ¬ Link r w b c)
    (anchored : ∃ p, Link r w p z ∨ Link r w z p) : Link r w b z ∧ Link r w z c := by
  obtain ⟨p,incoming|outgoing⟩ := anchored
  · have recover := recover_link cap incoming
    have head : ((openPair p z) c).head? = some c := by by_cases h : c=p <;> simp [openPair,h]
    have bp : b=p := by
      apply Classical.byContradiction; intro n
      exact split (computed_link cap _ recover after (by simp [openPair,n]) head)
    subst p
    exact ⟨incoming,computed_link cap _ recover after (by simp [openPair]) head⟩
  · have recover := recover_link_left hr cap outgoing
    have last : ((beforePair z p) b).getLast? = some b := by by_cases h : b=p <;> simp [beforePair,h]
    have cp : c=p := by
      apply Classical.byContradiction; intro n
      exact split (computed_link cap _ recover after last (by simp [beforePair,n]))
    subst p
    exact ⟨computed_link cap _ recover after last (by simp [beforePair]),outgoing⟩

/-- Order of the first retained copies is invariant under deleting other names. -/
theorem first_select (k w : Word) {a b : Nat} (ha : a ∈ k) (hb : b ∈ k) :
    (select k w).idxOf a < (select k w).idxOf b ↔ w.idxOf a < w.idxOf b := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases xa : x=a <;> by_cases xb : x=b <;> by_cases keep : x ∈ k <;>
      simp_all [select,List.idxOf_cons,cond_eq_if,beq_iff_eq,Ne.symm]

theorem link_first {r a b} {w : Word} (hr : 0 < r) (cap : Cap r w) (l : Link r w a b) :
    w.idxOf a < w.idxOf b := by
  let k := [a,b]
  have ab : a≠b := fun e => not_self hr cap (e ▸ l)
  obtain ⟨ca,_⟩ := link_counts cap l
  have keep : a ∈ k := by simp [k]
  have inW : a ∈ select k w := List.mem_filter.mpr ⟨List.count_pos_iff.mp (ca ▸ hr),by simpa using keep⟩
  have link := link_project cap l k keep (by simp [k])
  have cp := P455DefectProjection.select_cap k cap
  apply (first_select k w keep (by simp [k])).mp
  cases e : select k w with
  | nil => simp [e] at inW
  | cons x t =>
    have m : x ∈ k := by
      have mem : x ∈ select k w := e ▸ List.mem_cons_self
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp mem).2
    have nb : x≠b := by
      intro eq; subst x
      rw [e] at link cp
      have inc := Problem455Swap.in_bound a (a+1) b (by omega) (b::t)
      rw [Problem455BlockBridge.occ_count] at inc
      have total := (link_counts cp link).2
      change bigram a b (b::t)=r at link
      simp [List.count_cons] at inc total; omega
    have xa : x=a := by simpa [k,nb] using m
    subst x; simp [List.idxOf_cons,cond_eq_if,beq_iff_eq,ab,Ne.symm ab]

end P455Prefix
