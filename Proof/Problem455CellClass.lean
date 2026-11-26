import Problem455CellClassBinary

/- Reconstruct every word identical to the zero-bit word from its binary
   projections. The only final-phase assumption is a literal projection
   of the given tail; it holds for the canonical final phase. -/
namespace P455CellClass
open P455RectangleRank P455FirstRewrite P455Witness P455Structural Problem455.Slots
abbrev W := List Nat
def samePair (x y i : Nat) : Prop :=
  (x = owner i ∧ y = mate i) ∨ (x = mate i ∧ y = owner i)

private theorem roles (x : Nat) : x = owner (x/2) ∨ x = mate (x/2) := by
  unfold owner mate; omega

theorem private_closed {t i} (ix : i < t) (middle tail : W) (bit : Nat → Bool) :
    Closed (word t middle tail bit) (owner i) (mate i) := by
  let lower := (List.range i).flatMap privateCell
  let higher := ((List.range (t-(i+1))).map (fun x => i+1+x)).flatMap privateCell
  have eq : List.range t = (List.range i ++ [i]) ++
      (List.range (t-(i+1))).map (fun x => i+1+x) := by
    conv => lhs; arg 1; rw [show t=(i+1)+(t-(i+1)) by omega]
    rw [List.range_add,List.range_succ]
  have pre (x : Nat) (inside : x=owner i ∨ x=mate i) : x ∉ lower := by
    intro m
    obtain ⟨j,mj,h⟩ := List.mem_flatMap.mp m
    have lt := List.mem_range.mp mj
    have rr : x=owner j ∨ x=mate j := by simpa [privateCell,or_assoc,or_left_comm,or_comm] using h
    unfold owner mate at *; omega
  refine ⟨by simp [owner,mate],lower,higher ++ middle ++ (List.range t).flatMap (mutableCell bit) ++ tail,?_,
    pre _ (.inl rfl),pre _ (.inr rfl)⟩
  unfold word
  conv => lhs; arg 1; arg 1; arg 1; rw [eq]
  simp [lower,higher,early,privateCell,List.append_assoc,List.flatMap_append]

theorem only_cell {r allow ts t middle tail V} (small : ∀ x ∈ middle ++ tail, x < 2*t)
    (cap : P455Quotient.Cap r (word t middle tail (constant false)))
    (ident : (P455FullSingleton.model r allow ts).Valid (word t middle tail (constant false)) V)
    {x y} (ne : x ≠ y)
    (diff : select [x,y] (word t middle tail (constant false)) ≠ select [x,y] V) :
    ∃ i < t, samePair x y i := by
  let U := word t middle tail (constant false)
  obtain ⟨a,b,tag,bit,order,len,allowT,src,_⟩ := P455CellClassBinary.changed cap ident ne diff
  have edge : Edge U r allow x y := by
    rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact .inl ⟨tag,ne,len,allowT,bit,src⟩
    · exact .inr ⟨tag,Ne.symm ne,len,allowT,bit,(select_pair_symm _ _ _).trans src⟩
  have xproj : x ∈ select [x,y] (word t middle tail (constant false)) := by
    rw [src]; rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [profile,profilePrefix]
  have xlt := word_names _ small x (List.mem_filter.mp xproj).1
  have lt : x/2 < t := by omega
  have xc := roles x
  have yc : y=owner (x/2) ∨ y=mate (x/2) := by
    apply Classical.byContradiction; intro bad
    exact (no_external_record (private_closed lt middle tail _) xc
      ⟨fun h => bad (.inl h),fun h => bad (.inr h)⟩) edge
  exact ⟨x/2,lt,by unfold samePair; omega⟩

private theorem mutable_own (cells : List Nat) (nd : cells.Nodup) (bit : Nat → Bool) (i : Nat) :
    select [owner i,mate i] (cells.flatMap (mutableCell bit)) =
      (if i ∈ cells then mutableCell bit i else []) := by
  induction cells with
  | nil => simp [select]
  | cons j cells ih =>
    rw [List.flatMap_cons,select_append,ih (List.nodup_cons.mp nd).2]
    by_cases eq : i=j
    · subst j
      have fresh := (List.nodup_cons.mp nd).1
      cases b : bit i <;> simp [mutableCell,b,fresh,select]
    · have no : select [owner i,mate i] (mutableCell bit j) = [] := by
        apply select_nil
        intro z m
        have either : z=owner j ∨ z=mate j := by
          cases b : bit j <;> simpa [mutableCell,b,or_comm] using m
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        unfold owner mate at *; omega
      simp [no,eq]

private def stem (t : Nat) (middle : W) :=
  (List.range t).flatMap privateCell ++ middle

private theorem own {t i} (ix : i<t) (middle tail : W) (bit : Nat → Bool)
    (finalPair : select [owner i,mate i] tail = [owner i,mate i]) :
    select [owner i,mate i] (word t middle tail bit) =
      select [owner i,mate i] (stem t middle) ++
        (mutableCell bit i ++ [owner i,mate i]) := by
  unfold word stem
  rw [select_append,select_append,mutable_own _ List.nodup_range,if_pos (List.mem_range.mpr ix),finalPair,
    List.append_assoc]

private theorem kept_other (x y i : Nat) (outside : ¬ samePair x y i) (bit : Nat → Bool) :
    select [x,y] (mutableCell bit i) = select [x,y] (mutableCell (constant false) i) := by
  by_cases b : bit i
  · have emptySide : (∀ a ∈ [owner i], a ∉ [x,y]) ∨ (∀ a ∈ [mate i], a ∉ [x,y]) := by
      simp only [List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false,forall_eq]
      unfold samePair owner mate at *; omega
    have sw := selected_swap [x,y] [] [owner i] [mate i] [] emptySide
    simpa [mutableCell,constant,b] using sw.symm
  · simp [mutableCell,constant,b]

private theorem other {t x y} (middle tail : W) (bit : Nat → Bool)
    (none : ∀ i<t, ¬samePair x y i) :
    select [x,y] (word t middle tail bit) = select [x,y] (word t middle tail (constant false)) := by
  have go (cells : List Nat) (all : ∀ i ∈ cells, ¬ samePair x y i) :
      select [x,y] (cells.flatMap (mutableCell bit)) =
        select [x,y] (cells.flatMap (mutableCell (constant false))) := by
    induction cells with
    | nil => rfl
    | cons i cells ih =>
      simp only [List.flatMap_cons, select_append]
      rw [kept_other x y i (all i List.mem_cons_self) bit,
        ih (fun j hj => all j (List.mem_cons_of_mem _ hj))]
  unfold word
  simp only [select_append,go _ (fun i m => none i (List.mem_range.mp m))]

private theorem reverse_names (w : W) (x y : Nat) : select [x,y] w = select [y,x] w := by
  exact select_pair_symm _ _ _

private theorem mono (w : W) (x : Nat) : select [x,x] w = List.replicate (w.count x) x := by
  induction w with
  | nil => simp [select]
  | cons z w ih => by_cases eq : z=x <;> simp_all [select,List.count_cons,List.replicate_succ]

/-- No restriction is imposed on the comparison word. The middle may
    contain arbitrary occurrences on the prescribed cell names. -/
theorem represent {r allow ts t middle tail V} (small : ∀ x ∈ middle ++ tail, x < 2*t)
    (cap : P455Quotient.Cap r (word t middle tail (constant false)))
    (finalPair : ∀ i < t, select [owner i,mate i] tail = [owner i,mate i])
    (valid : (P455FullSingleton.model r allow ts).Valid (word t middle tail (constant false)) V) :
    ∃ bit, V = word t middle tail bit := by
  classical
  let U := word t middle tail (constant false)
  let bit := fun i => decide (select [owner i,mate i] U ≠ select [owner i,mate i] V)
  have sameCell (i : Nat) (ix : i<t) :
      select [owner i,mate i] V = select [owner i,mate i] (word t middle tail bit) := by
    let x := owner i
    let y := mate i
    let K := select [x,y] (stem t middle)
    have ne : x ≠ y := by simp [x,y,owner,mate]
    have source : select [x,y] U = K ++ [x,y,x,y] := by
      simpa [K,U,x,y,mutableCell,constant] using own ix middle tail (constant false) (finalPair i ix)
    by_cases eq : select [x,y] U = select [x,y] V
    · have hb : bit i=false := by
        change decide (select [x,y] U ≠ select [x,y] V) = false
        simp [eq]
      rw [own ix middle tail bit (finalPair i ix)]
      exact eq.symm.trans (by simpa [mutableCell,hb] using source)
    · have hb : bit i=true := by exact decide_eq_true eq
      obtain ⟨a,b,tag,c,order,_,_,orig,comp⟩ := P455CellClassBinary.changed cap valid ne eq
      have e : K ++ [x,y,x,y] = profilePrefix a b tag ++ (pair a b c ++ [a,b]) :=
        source.symm.trans orig
      have len := congrArg List.length e
      have kl : K.length = (profilePrefix a b tag).length := by
        cases c <;> simp only [pair,if_true,if_false,List.length_append,List.length_cons,
          List.length_nil,Bool.false_eq_true] at len <;> omega
      obtain ⟨ke,rest⟩ := List.append_inj e kl
      have ab : a=x ∧ b=y ∧ c=false := by
        cases c <;> simp [pair] at rest ⊢ <;> omega
      obtain ⟨rfl,rfl,rfl⟩ := ab
      rw [own ix middle tail bit (finalPair i ix)]
      simpa [profile,pair,mutableCell,hb,K,x,y] using comp.trans (by
        change profile x y tag true = K ++ [y,x,x,y]
        rw [ke]; rfl)
  refine ⟨bit,P455BlockSeparators.pair_ext (fun x y => ?_)⟩
  by_cases used : ∃ i<t, samePair x y i
  · obtain ⟨i,ix,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := used
    · exact sameCell i ix
    · exact (reverse_names _ _ _).trans ((sameCell i ix).trans (reverse_names _ _ _))
  · have notUsed : ∀ i<t, ¬ samePair x y i := fun i ix yes => used ⟨i,ix,yes⟩
    rw [other middle tail bit notUsed]
    by_cases eq : x=y
    · subst y; rw [mono,mono,P455CellClassBinary.exact_counts cap valid x]
    · apply Classical.byContradiction; intro diff
      exact used (only_cell small cap valid eq (Ne.symm diff))

theorem canonical_final (t i : Nat) (ix : i < t) :
    select [owner i,mate i] ((List.range t).flatMap (mutableCell (constant false))) = [owner i,mate i] := by
  rw [mutable_own _ List.nodup_range,if_pos (List.mem_range.mpr ix)]; rfl

theorem bit_change {t i : Nat} (ix : i<t) (middle tail : W) (bit : Nat → Bool)
    (yes : bit i=true) (finalPair : select [owner i,mate i] tail=[owner i,mate i]) :
    select [owner i,mate i] (word t middle tail bit) ≠
      select [owner i,mate i] (word t middle tail (constant false)) := by
  rw [own ix middle tail bit finalPair,own ix middle tail (constant false) finalPair]
  simp [mutableCell,constant,yes,owner,mate]

/-- An admitted type read at the cell has exactly the bit used in its
    displayed mutable pair. The tag itself may be supplied by a tester. -/
theorem read_bit {t i : Nat} (ix : i<t) (middle tail : W) (bit : Nat → Bool)
    (endPair : select [owner i,mate i] tail=[owner i,mate i]) (tag : Tag)
    (record : typed (word t middle tail bit) (owner i) (mate i) tag) :
    select [owner i,mate i] (word t middle tail bit) = profile (owner i) (mate i) tag (bit i) := by
  obtain ⟨value,eq⟩ := record
  have ne : owner i ≠ mate i := by simp [owner,mate]
  have parts := (own ix middle tail bit endPair).symm.trans eq
  unfold profile at parts
  have len := congrArg List.length parts
  have ends := List.append_inj_right parts (by
    cases bi : bit i <;> cases value <;> simp [mutableCell,bi,pair] at len <;> omega)
  have matchBit : value=bit i := by
    cases bi : bit i <;> cases value <;> simp_all [mutableCell,pair]
  exact matchBit ▸ eq

end P455CellClass
