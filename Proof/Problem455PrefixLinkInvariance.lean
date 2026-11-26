import Problem455PrefixRecordLinks
import Problem455StructuralReflection



namespace P455Prefix
open P455FirstRewrite P455Quotient P455Witness P455Structural Problem455.Slots
open Problem455Swap (Link)
open P455DefectProjection (select_cap)

theorem select_valid {A : Type} (M : Model A) (keep : Word) {u v : Word} (valid : M.Valid u v) :
    M.Valid (select keep u) (select keep v) := by
  let f (x : Nat) : Word := if x ∈ keep then [x] else []
  have eq (w : Word) : w.flatMap f = select keep w := by
    induction w with
    | nil => rfl
    | cons c t ih => by_cases k : c ∈ keep <;> simp [f,select,k,ih]
  intro val; rw [← eq,← eq,M.eval_instance,M.eval_instance]; exact valid _

private theorem selected_self (k w : Word) (sup : ∀ t ∈ w, t ∈ k) : select k w = w :=
  List.filter_eq_self.mpr (fun t m => by simpa using sup t m)

private theorem three_ext {a b z : Nat} {u v : Word}
    (su : ∀ t ∈ u, t ∈ [a,b,z]) (sv : ∀ t ∈ v, t ∈ [a,b,z]) (count : ∀ t, u.count t = v.count t)
    (xy : select [a,b] u = select [a,b] v) (xz : select [a,z] u = select [a,z] v)
    (yz : select [b,z] u = select [b,z] v) : u = v := by
  let g (c : Nat) : Word := if c ∈ [a,b,z] then [c] else []
  have dec (w : Word) (sup : ∀ t ∈ w, t ∈ [a,b,z]) : w.flatMap g = w := by
    induction w with
    | nil => rfl
    | cons c t ih =>
      have m := sup c List.mem_cons_self
      simpa only [List.flatMap_cons,g,if_pos m,List.singleton_append] using congrArg (List.cons c) (ih (fun d hd => sup d (List.mem_cons_of_mem _ hd)))
  rw [← dec u su,← dec v sv]
  apply trace g count
  intro i j bad
  have hi : i ∈ [a,b,z] := by
    apply Classical.byContradiction; intro h; exact bad (by simp only [g,if_neg h,List.nil_append,List.append_nil])
  have hj : j ∈ [a,b,z] := by
    apply Classical.byContradiction; intro h; exact bad (by simp only [g,if_neg h,List.nil_append,List.append_nil])
  have ne : i ≠ j := fun e => bad (by rw [e])
  have rev {c d : Nat} (eq : select [c,d] u = select [c,d] v) : select [d,c] u = select [d,c] v := by
    rw [select_swap d c u,select_swap d c v,eq]
  have cvt (x y : Nat) (w : Word) : proj x y w = select [x,y] w := by simp [proj,select]
  rw [cvt,cvt]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi hj
  rcases hi with ha|hb|hz <;> rcases hj with ka|kb|kz <;> subst i <;> subst j <;>
    first | contradiction | exact xy | exact xz | exact yz | exact rev xy | exact rev xz | exact rev yz

theorem edge_no_links {r allow a z} {v : Word} (cv : Cap r v) (az : a ≠ z) (e : Edge v r allow a z) :
    ¬ Link r v a z ∧ ¬ Link r v z a := by
  have p := profile_not_link (select_cap [a,z] cv) ((edge_iff az).mp e)
  exact ⟨fun l => p.1 (link_project cv l _ (by simp) (by simp)),
    fun l => p.2 (link_project cv l _ (by simp) (by simp))⟩

/-- All hypotheses here are local: validity, the cap, and a three-name support.
    The tester is constructed from the endpoint where the directed link splits. -/
theorem triple_invariant {r allow ts a b z} {u v : Word} (hr : 0 < r) (cu : Cap r u) (cv : Cap r v)
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (su : ∀ t ∈ u, t ∈ [a,b,z]) (sv : ∀ t ∈ v, t ∈ [a,b,z]) (left : Link r u a b) : Link r v a b := by
  classical
  apply Classical.byContradiction; intro failed
  have neq : u ≠ v := fun eq => failed (eq ▸ left)
  have ab : a ≠ b := fun eq => not_self hr cu (eq ▸ left)
  have fixed := link_fixes_binary cu ab left valid
  have third : z ≠ a ∧ z ≠ b := by
    have separate (hz : z ∈ [a,b]) : False := by
      have cut (w : Word) (sw : ∀ t ∈ w, t ∈ [a,b,z]) : select [a,b] w = w := by
        apply selected_self; intro t ht
        have mem := sw t ht
        simp only [List.mem_cons,List.not_mem_nil,or_false] at mem hz ⊢
        rcases mem with h|h|h
        · exact .inl h
        · exact .inr h
        · exact h ▸ hz
      exact neq ((cut u su).symm.trans (fixed.trans (cut v sv)))
    exact ⟨fun e => separate (by simp [e]),fun e => separate (by simp [e])⟩
  have az := third.1.symm
  have bz := third.2.symm
  have twins := twin_edges (allow := allow) cu left ab az bz
  have counts := P455CellClassBinary.exact_counts cu valid
  have eA : Edge u r allow a z := by
    by_cases eq : select [a,z] u = select [a,z] v
    · have other : select [b,z] u ≠ select [b,z] v := fun s => neq (three_ext su sv counts fixed eq s)
      exact twins.mpr (changed_edges cu valid bz other).1
    · exact (changed_edges cu valid az eq).1
  have va := edge_persists cu valid az eA
  have vb := edge_persists cu valid bz (twins.mp eA)
  have ea := edge_no_links cv az va
  have eb := edge_no_links cv bz vb
  have rev : ¬ Link r v b a := by
    intro l
    have h := link_project cv l [a,b] (by simp) (by simp)
    rw [← fixed] at h
    exact no_opposite hr (select_cap _ cu) (link_project cu left _ (by simp) (by simp)) h
  have cmp : P455SourceFamilies.Compressed r v := by
    intro i j link
    obtain ⟨ci,cj⟩ := link_counts cv link
    have mi := sv i (List.count_pos_iff.mp (ci ▸ hr))
    have mj := sv j (List.count_pos_iff.mp (cj ▸ hr))
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mi mj
    rcases mi with hi|hi|hi <;> rcases mj with hj|hj|hj <;> subst i <;> subst j <;>
      first | exact not_self hr cv link | exact failed link | exact rev link |
        exact ea.1 link | exact ea.2 link | exact eb.1 link | exact eb.2 link
  have structural : Structural v r allow :=
    .inl ⟨⟨[a,b,z],by simp,sv⟩,z,a,b,third.1,third.2,ab,
      va.elim Or.inr Or.inl,vb.elim Or.inr Or.inl⟩
  have fixedV := selected_self [a,b,z] v sv
  have eq := P455StructuralReflection.literal_projection hr cv (fun f => (valid f).symm)
    [a,b,z] (by simp) (by simpa only [fixedV] using structural) (by simpa only [fixedV] using cmp)
  exact neq (by simpa only [fixedV,selected_self [a,b,z] u su] using eq.symm)

/-- The directed repeated links of the two sides of any capped valid
    identity in the full tester product agree. -/
theorem identity_link {r allow ts} (hr : 0 < r) {u v : Word} (cu : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (a b : Nat) :
    Link r u a b ↔ Link r v a b := by
  have counts := P455CellClassBinary.exact_counts cu valid
  have cv : Cap r v := fun i => counts i ▸ cu i
  have go {U V : Word} (cU : Cap r U) (cV : Cap r V)
      (ct : U.count a = V.count a) (idUV : (P455FullSingleton.model r allow ts).Valid U V)
      (l : Link r U a b) : Link r V a b := by
    apply link_of_triples cV (ct.symm.trans (link_counts cU l).1)
    intro z
    let k := [a,b,z]
    have cover (w : Word) (t : Nat) (h : t ∈ select k w) : t ∈ k := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp h).2
    exact triple_invariant hr (select_cap _ cU) (select_cap _ cV) (select_valid _ k idUV)
      (cover U) (cover V) (link_project cU l k (by simp [k]) (by simp [k]))
  exact ⟨go cu cv (counts a) valid,go cv cu (counts a).symm (fun f => (valid f).symm)⟩

/-- Any capped valid identity is a single shared nonempty substitution of
   a capped, compressed valid identity; no link-preservation hypothesis. -/
theorem compressed_instance {r allow ts} (hr : 0 < r) (u v : Word) (cu : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ A B : Word, ∃ h : Nat → Word, (∀ z, h z ≠ []) ∧ A.flatMap h = u ∧ B.flatMap h = v ∧
      Cap r A ∧ Cap r B ∧ (P455FullSingleton.model r allow ts).Valid A B ∧
      P455SourceFamilies.Compressed r A ∧ P455SourceFamilies.Compressed r B := by
  have cv : Cap r v := fun i => P455CellClassBinary.exact_counts cu valid i ▸ cu i
  obtain ⟨A,B,h,n,e,f,ca,cb,ok,_,outcome⟩ := contract_common hr u v cu cv valid
  refine ⟨A,B,h,n,e,f,ca,cb,ok,?_⟩
  rcases outcome with done|⟨a,b,⟨l,miss⟩|⟨l,miss⟩⟩
  · exact done
  · exact (miss ((identity_link hr ca ok a b).mp l)).elim
  · exact (miss ((identity_link hr ca ok a b).mpr l)).elim

end P455Prefix
