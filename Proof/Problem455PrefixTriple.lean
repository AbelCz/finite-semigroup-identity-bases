import Problem455PrefixBlocks



namespace P455Prefix
open P455FirstRewrite P455Quotient P455Witness P455BlockSeparators
open Problem455.Slots
open Problem455Swap (Link)
open P455DefectProjection (select_count select_cap)

theorem next_after_link {r a b : Nat} {w t : Word} (cap : Cap r w)
    (link : Link r w a b) (m : t ∈ rows a w) : t.tail.head? = some b := by
  rw [link_rows cap link] at m
  obtain ⟨row,mem,rfl⟩ := List.mem_map.mp m
  exact row_head mem

theorem link_project {r a b : Nat} {w : Word} (cap : Cap r w) (link : Link r w a b)
    (keep : Word) (ha : a ∈ keep) (hb : b ∈ keep) : Link r (select keep w) a b := by
  have ct := (link_counts cap link).1
  apply (all_next a b ?_).trans ((select_count keep w a ha).trans ct)
  intro t m
  rw [project_rows keep ha] at m
  obtain ⟨s,hm,et⟩ := List.mem_map.mp m
  rw [← et]
  have one := row_head hm
  have two := next_after_link cap link hm
  cases s with
  | nil => simp at one
  | cons x s =>
    obtain rfl : x = a := Option.some.inj one
    cases s with
    | nil => simp at two
    | cons y s =>
      obtain rfl : y = b := Option.some.inj two
      simp [select,ha,hb]

/-- A literal successor condition can be reconstructed from every triple
    projection by retaining the actual next name, even when it is an outsider. -/
theorem link_of_triples {r a b : Nat} {w : Word} (cap : Cap r w) (ca : w.count a = r)
    (triples : ∀ z, Link r (select [a,b,z] w) a b) : Link r w a b := by
  apply (all_next a b ?_).trans ca
  intro t m
  have first := row_head m
  have each (z : Nat) : (select [a,b,z] t).tail.head? = some b := by
    apply next_after_link (select_cap _ cap) (triples z)
    rw [project_rows _ (by simp : a ∈ [a,b,z])]
    exact List.mem_map.mpr ⟨t,m,rfl⟩
  cases t with
  | nil => simp at first
  | cons x t =>
    have eq : x = a := Option.some.inj first
    subst x
    cases t with
    | nil => simpa [select] using each a
    | cons z s => simpa [select] using each z

private theorem one_witness {r a b : Nat} {u v : Word} (cu : Cap r u) (cv : Cap r v)
    (counts : u.count a = v.count a) (left : Link r u a b) (right : ¬ Link r v a b) :
    ∃ z, Link r (select [a,b,z] u) a b ∧ ¬ Link r (select [a,b,z] v) a b := by
  classical
  have miss : ∃ z, ¬ Link r (select [a,b,z] v) a b := by
    apply Classical.byContradiction; intro fail
    exact right (link_of_triples cv (counts.symm.trans (link_counts cu left).1)
      (fun z => Classical.byContradiction (fun bad => fail ⟨z,bad⟩)))
  obtain ⟨z,m⟩ := miss
  exact ⟨z,link_project cu left _ (by simp) (by simp),m⟩

/-- Any obstruction returned by contraction is already seen in opposite
    projections to at most three input names. The order and direction of
    the repeated bigram are the same in these comparisons. -/
theorem asymmetric_triple {r allow ts} {u v : Word} (cu : Cap r u) (cv : Cap r v)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (asym : Asymmetric r u v) :
    ∃ a b z, (Link r (select [a,b,z] u) a b ∧ ¬ Link r (select [a,b,z] v) a b) ∨
      (Link r (select [a,b,z] v) a b ∧ ¬ Link r (select [a,b,z] u) a b) := by
  have rule := P455FirstTesters.tester_rule (P455FirstTesters.valid_left _ _ valid)
  have c (a) : u.count a = v.count a := by
    have := rule.unary a; have := cu a; have := cv a; omega
  obtain ⟨a,b,e⟩ := asym
  rcases e with ⟨l,j⟩|⟨l,j⟩
  · obtain ⟨z,h⟩ := one_witness cu cv (c a) l j; exact ⟨a,b,z,.inl h⟩
  · obtain ⟨z,h⟩ := one_witness cv cu (c a).symm l j; exact ⟨a,b,z,.inr h⟩

end P455Prefix
