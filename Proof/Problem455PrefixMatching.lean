import Problem455PrefixInsertion



namespace P455Prefix
open P455Quotient P455FirstRewrite P455Witness P455Structural Problem455.Slots
open P455DefectProjection (select_cap select_sub)
open Problem455Swap (Link)

def Changed (u v : Word) (a b : Nat) := select [a,b] u ≠ select [a,b] v

theorem changed_symm {u v a b} : Changed u v a b ↔ Changed u v b a := by
  unfold Changed; rw [select_swap a b u,select_swap a b v]

theorem subpair (keep w : Word) {a b : Nat} (ha : a ∈ keep) (hb : b ∈ keep) :
    select [a,b] (select keep w) = select [a,b] w :=
  select_sub _ _ _ (by simpa using And.intro ha hb)

theorem selected_change (keep : Word) {u v a b} (ha : a ∈ keep) (hb : b ∈ keep) :
    Changed (select keep u) (select keep v) a b ↔ Changed u v a b := by
  simp only [Changed,subpair keep _ ha hb]

theorem selected_edge (keep : Word) {r allow w a b} (ab : a ≠ b) (ha : a ∈ keep) (hb : b ∈ keep) :
    Edge (select keep w) r allow a b ↔ Edge w r allow a b := by
  rw [edge_iff ab,edge_iff ab,subpair keep _ ha hb]

private theorem overlapping_projection {r allow ts u v a b c} (hr : 0 < r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (keep : Word) (small : keep.length ≤ 4) (ha : a∈keep) (hb : b∈keep) (hc : c∈keep)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (edit : Changed u v a b) (ec : Edge u r allow a c) :
    ∃ i j, Link r (select keep u) i j := by
  classical
  have eb := (changed_edges cap valid ab edit).1
  have overlap : Structural (select keep u) r allow := .inl ⟨⟨keep,small,
    fun _ m => by simpa only [decide_eq_true_eq] using (List.mem_filter.mp m).2⟩,
    a,b,c,ab,ac,bc,(selected_edge keep ab ha hb).mpr eb,(selected_edge keep ac ha hc).mpr ec⟩
  apply Classical.byContradiction; intro empty
  have cmp : P455SourceFamilies.Compressed r (select keep u) := fun i j l => empty ⟨i,j,l⟩
  have eq := P455StructuralReflection.literal_projection hr cap valid keep small overlap cmp
  have diff := (selected_change keep ha hb).mpr edit
  exact diff (congrArg (select [a,b]) eq)

private theorem link_names {r w i j} (hr : 0 < r) (cap : Cap r w) (l : Link r w i j) : i∈w ∧ j∈w := by
  obtain ⟨x,y⟩ := link_counts cap l
  exact ⟨List.count_pos_iff.mp (x ▸ hr),List.count_pos_iff.mp (y ▸ hr)⟩

theorem neighbors_link {r allow ts u v a b c} (hr : 0 < r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (edit : Changed u v a b) (ec : Edge u r allow a c) :
    Link r (select [a,b,c] u) b c ∨ Link r (select [a,b,c] u) c b := by
  let k := [a,b,c]
  have cp := select_cap k cap
  obtain ⟨i,j,l⟩ := overlapping_projection hr cap valid k (by simp [k]) (by simp [k]) (by simp [k])
    (by simp [k]) ab ac bc edit ec
  have m := link_names hr cp l
  have hi : i ∈ k := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp m.1).2
  have hj : j ∈ k := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp m.2).2
  have p := edge_no_links cp ab ((selected_edge k ab (by simp [k]) (by simp [k])).mpr
    (changed_edges cap valid ab edit).1)
  have q := edge_no_links cp ac ((selected_edge k ac (by simp [k]) (by simp [k])).mpr ec)
  simp only [k,List.mem_cons,List.not_mem_nil,or_false] at hi hj
  rcases hi with hi|hi|hi <;> rcases hj with hj|hj|hj <;> subst i <;> subst j <;>
    first | exact (not_self hr cp l).elim | exact (p.1 l).elim | exact (p.2 l).elim |
      exact (q.1 l).elim | exact (q.2 l).elim | exact .inl l | exact .inr l

private theorem split_four {r u a b c} (cap : Cap r u) (cmp : P455SourceFamilies.Compressed r u)
    (l : Link r (select [a,b,c] u) b c) :
    ∃ z, z ∉ [a,b,c] ∧ ¬ Link r (select [a,b,c,z] u) b c := by
  classical
  have count : u.count b = r := by
    have x := (link_counts (select_cap _ cap) l).1
    rwa [P455DefectProjection.select_count _ _ _ (by simp)] at x
  have miss : ∃ z, ¬ Link r (select [a,b,c,z] u) b c := by
    apply Classical.byContradiction; intro none
    apply cmp b c (link_of_triples cap count ?_)
    intro z
    have four : Link r (select [a,b,c,z] u) b c := Classical.byContradiction (fun f => none ⟨z,f⟩)
    have tri := link_project (select_cap _ cap) four [b,c,z] (by simp) (by simp)
    rwa [select_sub _ _ _ (by simp)] at tri
  obtain ⟨z,f⟩ := miss
  refine ⟨z,?_,f⟩
  intro old
  have eq : select [a,b,c,z] u = select [a,b,c] u := by
    unfold select; apply List.filter_congr; intro t _
    by_cases e : t=z
    · subst t; simp at old; simp [old]
    · simp [e]
  exact f (eq ▸ l)

private theorem drop_four {a b c z} (fresh : z ∉ [a,b,c]) (w : Word) :
    dropName z (select [a,b,c,z] w) = select [a,b,c] w := by
  simp only [dropName,select,List.filter_filter]
  apply List.filter_congr; intro t _
  by_cases e : t=z
  · subst t; simp at fresh; simp [fresh]
  · simp [e]

/-- Any two changed neighbors ordered by first occurrence contain another
    changed neighbor strictly between them. The same actual four-name link
    is used on both sides via identity_link. -/
theorem intermediate_neighbor {r allow ts u v a b c} (hr : 0 < r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (cmp : P455SourceFamilies.Compressed r u)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (eb : Changed u v a b) (ec : Changed u v a c)
    (order : u.idxOf b < u.idxOf c) :
    ∃ z, a≠z ∧ b≠z ∧ c≠z ∧ Changed u v a z ∧ u.idxOf b < u.idxOf z ∧ u.idxOf z < u.idxOf c := by
  let k := [a,b,c]
  have ecR := (changed_edges cap valid ac ec).1
  have base : Link r (select k u) b c := by
    rcases neighbors_link hr cap valid ab ac bc eb ecR with l|l
    · exact l
    · have rev := (first_select k u (by simp [k] : c∈k) (by simp [k] : b∈k)).mp
        (link_first hr (select_cap k cap) l)
      omega
  obtain ⟨z,fresh,bad⟩ := split_four cap cmp base
  let four := [a,b,c,z]
  let U := select four u
  let V := select four v
  have zne : z≠a ∧ z≠b ∧ z≠c := by simpa using fresh
  have ma : a∈four := by simp [four]
  have mb : b∈four := by simp [four]
  have mc : c∈four := by simp [four]
  have mz : z∈four := by simp [four]
  have cp : Cap r U := select_cap _ cap
  have id4 := select_valid _ four valid
  have vcap : Cap r V := fun t => P455CellClassBinary.exact_counts cp id4 t ▸ cp t
  have reverse : ¬ Link r U c b := by
    intro l
    have to3 := link_project cp l k (by simp [k]) (by simp [k])
    have eq : select k U = select k u := select_sub _ _ _ (by simp [k,four])
    exact no_opposite hr (select_cap k cap) base (eq ▸ to3)
  have forb := edge_no_links cp ab ((selected_edge four ab ma mb).mpr (changed_edges cap valid ab eb).1)
  have forc := edge_no_links cp ac ((selected_edge four ac ma mc).mpr ecR)
  obtain ⟨i,j,l⟩ := overlapping_projection hr cap valid four (by simp [four]) ma mb mc ab ac bc eb ecR
  have anchor : ∃ p, Link r U p z ∨ Link r U z p := by
    obtain ⟨pi,pj⟩ := link_names hr cp l
    have hi : i∈four := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp pi).2
    have hj : j∈four := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp pj).2
    simp only [four,List.mem_cons,List.not_mem_nil,or_false] at hi hj
    rcases hi with hi|hi|hi|hi <;> rcases hj with hj|hj|hj|hj <;> subst i <;> subst j <;>
      first | exact (not_self hr cp l).elim | exact (forb.1 l).elim | exact (forb.2 l).elim |
        exact (forc.1 l).elim | exact (forc.2 l).elim | exact (bad l).elim | exact (reverse l).elim |
        exact ⟨_,.inl l⟩ | exact ⟨_,.inr l⟩
  have dropped : dropName z U = select k u := drop_four fresh u
  obtain ⟨bz,zc⟩ := inserted_between hr cp (dropped ▸ base) bad anchor
  have bv := (identity_link hr cp id4 b z).mp bz
  have du := linked_shadow cp bz zne.2.1.symm ab.symm zne.1
  have dv := linked_shadow vcap bv zne.2.1.symm ab.symm zne.1
  have ch : Changed U V a z := by
    intro equal
    have e := congrArg (List.map (exchange b z)) ((select_swap z a U).trans (equal.trans (select_swap a z V)))
    rw [du,dv] at e
    exact (selected_change four ma mb).mpr eb ((select_swap a b U).trans (e.trans (select_swap b a V)))
  exact ⟨z,zne.1.symm,zne.2.1.symm,zne.2.2.symm,(selected_change four ma mz).mp ch,
    (first_select four u mb mz).mp (link_first hr cp bz),(first_select four u mz mc).mp (link_first hr cp zc)⟩

theorem disjoint_changes {r allow ts u v a b c} (hr : 0 < r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (cmp : P455SourceFamilies.Compressed r u)
    (ab : a≠b) (ac : a≠c) (eb : Changed u v a b) (ec : Changed u v a c) : b=c := by
  classical
  by_cases bc : b=c
  · exact bc
  have no (d : Nat) : ∀ i j, u.idxOf j-u.idxOf i=d → a≠i → a≠j → i≠j →
      Changed u v a i → Changed u v a j → u.idxOf i < u.idxOf j → False := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro i j length ai aj ij ei ej order
      obtain ⟨z,az,iz,_,ez,lower,upper⟩ := intermediate_neighbor hr cap valid cmp ai aj ij ei ej order
      exact ih (u.idxOf z-u.idxOf i) (by omega) i z rfl ai az iz ei ez lower
  rcases neighbors_link hr cap valid ab ac bc eb (changed_edges cap valid ac ec).1 with l|l
  · have lt := (first_select [a,b,c] u (by simp : b∈[a,b,c]) (by simp : c∈[a,b,c])).mp
      (link_first hr (select_cap _ cap) l)
    exact (no _ b c rfl ab ac bc eb ec lt).elim
  · have lt := (first_select [a,b,c] u (by simp : c∈[a,b,c]) (by simp : b∈[a,b,c])).mp
      (link_first hr (select_cap _ cap) l)
    exact (no _ c b rfl ac ab (Ne.symm bc) ec eb lt).elim

end P455Prefix
