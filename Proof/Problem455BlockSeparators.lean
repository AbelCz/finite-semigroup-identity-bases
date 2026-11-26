import Problem455DefectProjection

 
namespace P455BlockSeparators
open P455Witness Problem455.Slots Problem455Swap

/-- A directed path of the literal repeated bigrams. -/
inductive Directed (e : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (a) : Directed e a a
  | snoc {a b c} : Directed e a b → e b c → Directed e a c

theorem prepend {e a b c} (h : e a b) (p : Directed e b c) : Directed e a c := by
  induction p with
  | refl => exact .snoc (.refl _) h
  | snoc _ last ih => exact .snoc ih last

theorem split_first {e a b} (p : Directed e a b) :
    a = b ∨ ∃ c, e a c ∧ Directed e c b := by
  induction p with
  | refl => exact .inl rfl
  | @snoc y z _ last ih =>
    rcases ih with eq|⟨c,first,rest⟩
    · exact .inr ⟨z, eq ▸ last,.refl z⟩
    · exact .inr ⟨c,first,.snoc rest last⟩

theorem orient {e a b} (outgoing : ∀ {x y z}, e x y → e x z → y = z)
    (incoming : ∀ {x y z}, e y x → e z x → y = z) (p : Joined e a b) :
    Directed e a b ∨ Directed e b a := by
  induction p with
  | refl => exact .inl (.refl _)
  | @extend y z prev h ih =>
    rcases ih with f|b
    · rcases h with f'|b'
      · exact .inl (.snoc f f')
      · cases f with
        | refl => exact .inr (.snoc (.refl _) b')
        | snoc rest last => exact .inl (incoming last b' ▸ rest)
    · rcases h with f'|b'
      · rcases split_first b with eq|⟨c,first,rest⟩
        · exact .inl (eq ▸ Directed.snoc (.refl _) f')
        · exact .inr (outgoing first f' ▸ rest)
      · exact .inr (prepend b' b)

theorem directed_of_same {r w a b} (hr : 0 < r) (cap : P455Closure.Cap r w)
    (same : SameBlock r w a b) : Directed (Link r w) a b ∨ Directed (Link r w) b a := by
  apply orient _ _ same.2.2
  · intro x y z xy xz
    apply Classical.byContradiction; intro ne
    have h := out_bound x y z ne w
    rw [show bigram x y w = r from xy,show bigram x z w = r from xz,Problem455BlockBridge.occ_count] at h
    have hx := cap x; omega
  · intro x y z yx zx
    apply Classical.byContradiction; intro ne
    have h := Nat.le_trans (in_bound y z x ne w) (tail_occ_le x w)
    rw [show bigram y x w = r from yx,show bigram z x w = r from zx,Problem455BlockBridge.occ_count] at h
    have hx := cap x; omega

/-- Suffixes starting at each occurrence, listed in word order. -/
def rows (a : Nat) : W → List W
  | [] => []
  | b :: w => if a = b then (b :: w) :: rows a w else rows a w

theorem rows_length (a : Nat) (w : W) : (rows a w).length = w.count a := by
  induction w with
  | nil => rfl
  | cons b w ih => by_cases eq : a = b <;> simp_all [rows,List.count_cons,beq_iff_eq,Ne.symm]

/-- Each row can be shifted exactly one position across a repeated
link. This includes equality of the entire remaining suffix, rather
than a numerical comparison of positions. -/
private def edgeRows (a b : Nat) : W → List W
  | [] => []
  | c :: w => if c = a ∧ w.head? = some b then w :: edgeRows a b w else edgeRows a b w

private theorem edgeRows_length (a b : Nat) (w : W) : (edgeRows a b w).length = bigram a b w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    by_cases test : c = a ∧ w.head? = some b <;> simp [edgeRows,bigram,hit,test,ih,Nat.add_comm]

private theorem edge_sub_left (a b : Nat) (w : W) :
    ((edgeRows a b w).map (List.cons a)).Sublist (rows a w) := by
  induction w with
  | nil => exact .slnil
  | cons c w ih =>
    by_cases k : c = a
    · subst c
      by_cases h : w.head? = some b
      · simpa [edgeRows,rows,h] using ih.cons₂ (a::w)
      · simpa [edgeRows,rows,h] using ih.cons (a::w)
    · simpa [rows,edgeRows,k,Ne.symm k] using ih

private theorem edge_sub_right (a b : Nat) (w : W) :
    (edgeRows a b w).Sublist (rows b w.tail) := by
  induction w with
  | nil => exact .slnil
  | cons c w ih =>
    cases w with
    | nil => simp [rows,edgeRows]
    | cons x t =>
      by_cases mem : x = b
      · subst x
        by_cases yes : c = a
        · simpa [rows,edgeRows,yes] using ih.cons₂ (b::t)
        · simpa [rows,edgeRows,yes] using ih.cons (b::t)
      · simpa [rows,edgeRows,mem,Ne.symm mem] using ih

theorem link_rows {r a b w} (cap : P455Closure.Cap r w) (link : Link r w a b) :
    rows a w = (rows b w).map (List.cons a) := by
  have l := edge_sub_left a b w
  have f := edge_sub_right a b w
  have s : (rows b w.tail).Sublist (rows b w) := by
    cases w with
    | nil => exact .slnil
    | cons x t =>
      by_cases eq : b=x
      · simp [rows,eq]
      · simp [rows,eq]
  have t := f.trans s
  have len : (edgeRows a b w).length = r := (edgeRows_length ..).trans link
  have e := t.eq_of_length_le (by rw [rows_length,len]; exact cap b)
  have g := l.eq_of_length_le (by rw [List.length_map,rows_length,len]; exact cap a)
  rw [← g,e]

theorem directed_prefix {r w a b} (cap : P455Closure.Cap r w) (p : Directed (Link r w) a b) :
    ∃ pre : W, rows a w = (rows b w).map (pre ++ ·) := by
  induction p with
  | refl => exact ⟨[],by simp⟩
  | @snoc y z prev edge ih =>
    obtain ⟨pre,h⟩ := ih
    refine ⟨pre ++ [y],?_⟩
    rw [h,link_rows cap edge,List.map_map]
    apply List.map_congr_left
    intro row _; simp


theorem row_head {a : Nat} {w row : W} (h : row ∈ rows a w) : row.head? = some a := by
  induction w with
  | nil => contradiction
  | cons x w ih =>
    by_cases eq : a=x
    · subst x; rcases (show row = a::w ∨ row ∈ rows a w by simpa [rows] using h) with rfl|old
      · rfl
      · exact ih old
    · exact ih (by simpa [rows,eq] using h)

theorem all_next {w : W} (a b : Nat)
    (h : ∀ z ∈ rows a w, z.tail.head? = some b) : bigram a b w = w.count a := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases eq : x=a
    · subst x
      have next := h (a::w) (by simp [rows])
      have rec := ih (fun z hz => h z (by simp [rows,hz]))
      simp [bigram,hit,show w.head? = some b from next,rec,Nat.add_comm]
    · have rec := ih (fun z hz => h z (by simp [rows,Ne.symm eq,hz]))
      simp [bigram,hit,eq,rec,List.count_cons,beq_iff_eq]

theorem directed_of_prefix {r w b} (hr : 0 < r) (cap : P455Closure.Cap r w)
    (cb : w.count b = r) (pre : W) (a : Nat)
    (eq : rows a w = (rows b w).map (pre ++ ·)) : Directed (Link r w) a b := by
  have non : rows b w ≠ [] := by
    intro z; have h := rows_length b w; rw [z,cb] at h; simp at h; omega
  obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ non
  induction pre generalizing a with
  | nil =>
    have e : rows a w = rows b w := by simpa using eq
    have ma := row_head (e ▸ hz : z ∈ rows a w)
    exact (show a=b by simpa [row_head hz] using ma.symm) ▸ Directed.refl _
  | cons c p ih =>
    have ma := row_head (w := w) (a := a) (row := (c::p)++z)
      (eq ▸ List.mem_map_of_mem hz)
    have ac : c=a := by simpa using ma
    subst c
    let next := p.head?.getD b
    have all (v) (hv : v ∈ rows b w) : (p ++ v).head? = some next := by
      cases p with
      | nil => simpa [next] using row_head hv
      | cons x xs => rfl
    have ct : w.count a = r := by simpa [rows_length,cb] using congrArg List.length eq
    have li : Link r w a next := by
      apply Eq.trans _ ct; apply all_next
      intro t ht
      rw [eq] at ht
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
      exact all v hv
    apply prepend li
    apply ih
    have strip := congrArg (List.map List.tail) ((link_rows cap li).symm.trans eq)
    simpa [List.map_map,Function.comp_def] using strip

theorem directed_joined {e a b} (p : Directed e a b) : Joined e a b := by
  induction p with
  | refl => exact .refl _
  | snoc _ last ih => exact .extend ih (.inl last)

theorem reversed_joined {e a b} (p : Directed e a b) : Joined e b a := by
  induction p with
  | refl => exact .refl _
  | snoc _ last ih =>
    have cat {x y z} (p : Joined e x y) (q : Joined e y z) : Joined e x z := by
      induction q with
      | refl => exact p
      | extend _ t j => exact .extend j t
    exact cat (.extend (.refl _) (.inr last)) ih

theorem project_rows (keep : W) {a : Nat} (ha : a ∈ keep) (w : W) :
    rows a (select keep w) = (rows a w).map (select keep) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases eq : a=b
    · subst b; simp [rows,select,ha,ih] at *
    · by_cases hb : b ∈ keep <;> simp [rows,select,ha,hb,eq,ih] at *


theorem pair_ext {w v : W} (pairs : ∀ c d : Nat, select [c,d] w = select [c,d] v) : w = v := by
  induction w generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons b v => simpa [select] using pairs b b
  | cons a w ih =>
    cases v with
    | nil => simpa [select] using pairs a a
    | cons b v =>
      have eq : a = b := by simpa [select] using congrArg List.head? (pairs a b)
      subst b
      apply congrArg (List.cons a)
      apply ih
      intro c d
      by_cases ac : a = c <;> by_cases ad : a = d <;> simpa [select,ac,ad] using pairs c d

theorem rowmaps_ext {as bs : List W} (pairs : ∀ c d : Nat,
    as.map (select [c,d]) = bs.map (select [c,d])) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs with
           | nil => rfl
           | cons b bs => simpa using pairs 0 0
  | cons a as ih =>
    cases bs with
    | nil => simpa using pairs 0 0
    | cons b bs =>
      have h (c d) := List.cons.inj (show select [c,d] a :: as.map (select [c,d]) =
        select [c,d] b :: bs.map (select [c,d]) from pairs c d)
      exact List.cons.injEq _ _ _ _ |>.mpr ⟨pair_ext fun c d => (h c d).1,ih fun c d => (h c d).2⟩

theorem row_suffix {a : Nat} {w row : W} (m : row ∈ rows a w) : row <:+ w := by
  induction w with
  | nil => contradiction
  | cons x w ih =>
    by_cases eq : a=x
    · subst x; rcases (show row = a::w ∨ row ∈ rows a w by simpa [rows] using m) with rfl|old
      · exact List.suffix_refl _
      · exact (ih old).trans (List.suffix_cons _ _)
    · exact (ih (by simpa [rows,eq] using m)).trans (List.suffix_cons _ _)

theorem project_prefix (keep : W) (pre : W) (bs : List W) :
    (bs.map (pre ++ ·)).map (select keep) =
    (bs.map (select keep)).map (select keep pre ++ ·) := by
  simp [List.map_map, Function.comp_def, select, List.filter_append]

/-- A putative merger in every extension of some two extra names
    recovers an actual directed repeated block in the original word.
    The orientation is fixed by the first rows in the original word. -/
private theorem reconstruct {r w a b} (hr : 0 < r) (cp : P455Closure.Cap r w)
    (cb : w.count b = r) (ne : a ≠ b) (A B : W) (As Bs : List W)
    (aa : rows a w = A::As) (bb : rows b w = B::Bs) (pre : W) (first : A = pre ++ B)
    (merges : ∀ c d : Nat, ∃ keep : W, a ∈ keep ∧ b ∈ keep ∧ c ∈ keep ∧ d ∈ keep ∧
        SameBlock r (select keep w) a b) : Directed (Link r w) a b := by
  have ma : A ∈ rows a w := by simp [aa]
  have mb : B ∈ rows b w := by simp [bb]
  have headA := row_head ma
  have headB := row_head mb
  have pre_head : pre.head? = some a := by
    cases pre with
    | nil => simp_all
    | cons x p => simpa [first] using headA
  apply directed_of_prefix hr cp cb pre
  apply rowmaps_ext
  intro c d
  obtain ⟨keep,ha,hb,hc,hd,sm⟩ := merges c d
  have not_empty : select keep pre ≠ [] := by
    cases pre with
    | nil => contradiction
    | cons x p =>
      have eq : x=a := by simpa using pre_head
      simp [select,eq,ha]
  have rx := project_rows keep ha w
  have ry := project_rows keep hb w
  have capK := P455DefectProjection.select_cap keep cp
  have hdir := directed_of_same hr capK sm
  have orient' : ∃ k : W, rows a (select keep w) = (rows b (select keep w)).map (k ++ ·) := by
    rcases hdir with f|g
    · exact directed_prefix capK f
    · obtain ⟨k,h⟩ := directed_prefix capK g
      rw [rx,ry,aa,bb] at h
      have eq := (List.cons.inj h).1
      have len := congrArg List.length eq
      simp only [first,select_append,List.length_append] at len
      have pos := List.length_pos_iff.mpr not_empty
      omega
  obtain ⟨k,h⟩ := orient'
  rw [rx,ry] at h
  have fst := h
  rw [aa,bb] at fst
  have eq := (List.cons.inj fst).1
  change select keep A = k ++ select keep B at eq
  rw [first,select_append] at eq
  have := List.append_cancel_right eq
  subst k
  rw [← project_prefix] at h
  let f := select [c,d]
  have nested : ∀ z : W, f (select keep z) = f z := fun z =>
    P455DefectProjection.select_sub keep [c,d] z (by simpa using And.intro hc hd)
  have proj := congrArg (List.map f) h
  simpa only [List.map_map, Function.comp_def,nested] using proj

theorem robust_separators {r w a b} (hr : 0 < r) (cp : P455Closure.Cap r w)
    (ca : w.count a = r) (cb : w.count b = r) (apart : ¬ SameBlock r w a b) :
    ∃ c d : Nat, ∀ keep : W, a ∈ keep → b ∈ keep → c ∈ keep → d ∈ keep →
      ¬ SameBlock r (select keep w) a b := by
  classical
  apply Classical.byContradiction
  intro contra
  have merges : ∀ c d : Nat, ∃ keep : W, a ∈ keep ∧ b ∈ keep ∧ c ∈ keep ∧ d ∈ keep ∧
        SameBlock r (select keep w) a b := by
    intro c d
    apply Classical.byContradiction; intro miss
    apply contra; refine ⟨c,d,?_⟩
    intro keep ha hb hc hd hm
    exact miss ⟨keep,ha,hb,hc,hd,hm⟩
  have oba : occ a w = r := (Problem455BlockBridge.occ_count ..).trans ca
  have obb : occ b w = r := (Problem455BlockBridge.occ_count ..).trans cb
  have ne : a ≠ b := by rintro rfl; exact apart ⟨oba,obb,.refl _⟩
  apply apart
  refine ⟨oba,obb,?_⟩
  have split (z : Nat) (cz : w.count z = r) : ∃ h t, rows z w = h::t := by
    cases eq : rows z w with
    | nil => have := rows_length z w; rw [eq,cz] at this; simp at this; omega
    | cons h t => exact ⟨h,t,rfl⟩
  obtain ⟨A,As,aa⟩ := split a ca
  obtain ⟨B,Bs,bb⟩ := split b cb
  rcases List.suffix_or_suffix_of_suffix (row_suffix (a := b) (by simp [bb] : B ∈ rows b w))
    (row_suffix (a := a) (by simp [aa] : A ∈ rows a w)) with ⟨pre,h⟩|⟨pre,h⟩
  · exact directed_joined (reconstruct hr cp cb ne A B As Bs aa bb pre h.symm merges)
  · apply reversed_joined (reconstruct hr cp ca ne.symm B A Bs As bb aa pre h.symm ?_)
    intro c d
    obtain ⟨keep,ha,hb,hc,hd,m⟩ := merges c d
    refine ⟨keep,hb,ha,hc,hd,m.2.1,m.1,?_⟩
    rcases directed_of_same hr (P455DefectProjection.select_cap keep cp) m with f|g
    · exact reversed_joined f
    · exact directed_joined g

end P455BlockSeparators
