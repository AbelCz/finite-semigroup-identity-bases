import Problem455PrefixTriple
import Problem455CellClassBinary

 
namespace P455Prefix
open P455FirstRewrite P455Quotient P455Witness P455Structural Problem455.Slots
open Problem455Swap (Link)
open P455DefectProjection (select_count select_cap)

theorem select_swap (a b : Nat) (w : Word) : select [a,b] w = select [b,a] w := by
  unfold select; apply List.filter_congr; intro x _; simp [Or.comm]

def PairProfile (r : Nat) (allow : Tag → Prop) (a b : Nat) (T : Word) :=
  ∃ tag bit, tag.length+16=r ∧ allow tag ∧
    (T=profile a b tag bit ∨ T=profile b a tag bit)

theorem edge_iff {r allow a b w} (ab : a ≠ b) :
    Edge w r allow a b ↔ PairProfile r allow a b (select [a,b] w) := by
  constructor
  · rintro (⟨t,_,len,ok,bit,h⟩|⟨t,_,len,ok,bit,h⟩)
    · exact ⟨t,bit,len,ok,.inl h⟩
    · exact ⟨t,bit,len,ok,.inr ((select_swap a b w).trans h)⟩
  · rintro ⟨t,bit,len,ok,h|h⟩
    · exact .inl ⟨t,ab,len,ok,bit,h⟩
    · exact .inr ⟨t,ab.symm,len,ok,bit,(select_swap b a w).trans h⟩

theorem changed_edges {r allow ts u v a b} (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (ab : a ≠ b)
    (diff : select [a,b] u ≠ select [a,b] v) : Edge u r allow a b ∧ Edge v r allow a b := by
  obtain ⟨x,y,t,bit,orient,len,ok,hu,hv⟩ := P455CellClassBinary.changed cap valid ab diff
  rw [edge_iff ab,edge_iff ab]
  rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨⟨t,bit,len,ok,.inl hu⟩,⟨t,!bit,len,ok,.inl hv⟩⟩
  · exact ⟨⟨t,bit,len,ok,.inr hu⟩,⟨t,!bit,len,ok,.inr hv⟩⟩

theorem edge_persists {r allow ts u v a b} (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (ab : a ≠ b)
    (e : Edge u r allow a b) : Edge v r allow a b := by
  by_cases same : select [a,b] u = select [a,b] v
  · rw [edge_iff ab,← same]; exact (edge_iff ab).mp e
  · exact (changed_edges cap valid ab same).2

private theorem head_not_target {r a b z t} (cap : Cap r (z::t)) (l : Link r (z::t) a b) : z ≠ b := by
  intro eq; subst z
  have h := Problem455Swap.in_bound a (a+1) b (by omega) (b::t)
  rw [Problem455BlockBridge.occ_count] at h
  have c := (link_counts cap l).2
  change Problem455Swap.bigram a b (b::t) = r at l
  simp [List.count_cons] at h c; omega

private theorem double_not_link {r a b c t} (cap : Cap r (c::c::t)) (one : c=a ∨ c=b) :
    ¬ Link r (c::c::t) a b := by
  intro l
  have nb := head_not_target cap l
  rcases one with e|e
  · subst c
    have n := next_after_link cap l (t := a::a::t) (by simp [P455BlockSeparators.rows])
    exact nb (Option.some.inj n)
  · exact nb e

theorem profile_not_link {r allow a b T} (cap : Cap r T)
    (p : PairProfile r allow a b T) : ¬ Link r T a b ∧ ¬ Link r T b a := by
  obtain ⟨t,bit,_,_,e|e⟩ := p <;> subst T
  · exact ⟨double_not_link cap (.inl rfl),double_not_link cap (.inr rfl)⟩
  · exact ⟨double_not_link cap (.inr rfl),double_not_link cap (.inl rfl)⟩

theorem link_fixes_binary {r allow ts a b u v} (cap : Cap r u) (ab : a ≠ b) (l : Link r u a b)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) : select [a,b] u = select [a,b] v := by
  apply Classical.byContradiction; intro bad
  have profile := (edge_iff ab).mp (changed_edges cap valid ab bad).1
  exact (profile_not_link (select_cap _ cap) profile).1 (link_project cap l _ (by simp) (by simp))

theorem not_self {r a} {u : Word} (hr : 0 < r) (cap : Cap r u) : ¬ Link r u a a := by
  intro l
  have rows := P455BlockSeparators.link_rows cap l
  have ct := P455BlockSeparators.rows_length a u
  have pos := (link_counts cap l).1
  cases e : P455BlockSeparators.rows a u with
  | nil => simp [e] at ct; omega
  | cons z s =>
    rw [e] at rows
    have len := congrArg List.length (List.cons.inj rows).1
    simp at len

theorem no_opposite {r a b} {u : Word} (hr : 0 < r) (cap : Cap r u) (l : Link r u a b) :
    ¬ Link r u b a := by
  intro back
  let rows := P455BlockSeparators.rows
  have forward := P455BlockSeparators.link_rows cap l
  have backward := P455BlockSeparators.link_rows cap back
  rw [backward,List.map_map] at forward
  have ct := P455BlockSeparators.rows_length a u
  have pos := (link_counts cap l).1
  cases e : rows a u with
  | nil => change P455BlockSeparators.rows a u = [] at e; simp [e] at ct; omega
  | cons z s =>
    change P455BlockSeparators.rows a u = z::s at e
    rw [e] at forward
    have len := congrArg List.length (List.cons.inj forward).1
    simp at len; omega

def exchange (a b z : Nat) := if z=a then b else if z=b then a else z

private theorem shadow {a b z} (ab : a ≠ b) (az : a ≠ z) (bz : b ≠ z)
    (t : Word) (out : b ∉ t) :
    (select [a,z] (t.flatMap (openPair a b))).map (exchange a b) =
      select [b,z] (t.flatMap (openPair a b)) := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    have cb : c ≠ b := fun e => out (e ▸ List.mem_cons_self)
    have eq := ih (fun h => out (List.mem_cons_of_mem _ h))
    simp only [List.flatMap_cons,select_append,List.map_append,eq]
    by_cases ca : c=a <;> by_cases cz : c=z <;>
      simp_all [openPair,select,exchange,Ne.symm]

private theorem map_prof {r allow a b T} (d : Nat → Nat) (p : PairProfile r allow a b T) :
    PairProfile r allow (d a) (d b) (T.map d) := by
  obtain ⟨t,bit,len,ok,h|h⟩ := p <;> subst T
  · exact ⟨t,bit,len,ok,.inl (P455ContactReflection.map_profile ..)⟩
  · exact ⟨t,bit,len,ok,.inr (P455ContactReflection.map_profile ..)⟩

theorem twin_edges {r allow a b z u} (cap : Cap r u) (l : Link r u a b)
    (ab : a ≠ b) (az : a ≠ z) (bz : b ≠ z) : Edge u r allow a z ↔ Edge u r allow b z := by
  rw [edge_iff az,edge_iff bz]
  let d := exchange a b
  have swap : (select [a,z] u).map d = select [b,z] u := by
    have sh := shadow ab az bz (dropName b u) (by simp)
    rwa [recover_link cap l] at sh
  have back : (select [b,z] u).map d = select [a,z] u := by
    rw [← swap,List.map_map]
    have dd : d ∘ d = id := by
      funext c; by_cases ca : c=a <;> by_cases cb : c=b <;> simp_all [d,exchange,Function.comp_def,Ne.symm]
    simp [dd]
  constructor
  · intro p; have q := map_prof d p
    simpa [d,exchange,ab,Ne.symm az,Ne.symm bz,← swap] using q
  · intro p; have q := map_prof d p
    simpa [d,exchange,Ne.symm ab,Ne.symm az,Ne.symm bz,← back] using q

/-- A linked pair has identical binary comparisons, up to an exchange of
    its two names, against every distinct third name. -/
theorem linked_shadow {r a b z u} (cap : Cap r u) (l : Link r u a b)
    (ab : a ≠ b) (az : a ≠ z) (bz : b ≠ z) :
    (select [b,z] u).map (exchange a b) = select [a,z] u := by
  have sh := shadow ab az bz (dropName b u) (by simp)
  rw [recover_link cap l] at sh
  rw [← sh,List.map_map]
  have ex : exchange a b ∘ exchange a b = id := by
    funext c; by_cases ca : c=a <;> by_cases cb : c=b <;> simp_all [exchange,Function.comp_def,Ne.symm]
  simp [ex]

end P455Prefix
