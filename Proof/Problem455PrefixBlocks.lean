import Problem455PrefixCommon



namespace P455Prefix
open P455FirstRewrite P455Quotient
open Problem455Swap (Link bigram hit)

def openPair (a b z : Nat) : Word := if z = a then [a,b] else [z]

private theorem out_le (a b : Nat) (w : Word) : bigram a b w ≤ w.count a := by
  have h := Problem455Swap.out_bound a b (b+1) (by omega) w
  rw [Problem455BlockBridge.occ_count] at h; omega

private theorem in_le (a b : Nat) (w : Word) : bigram a b w ≤ w.tail.count b := by
  have h := Problem455Swap.in_bound a (a+1) b (by omega) w
  rw [Problem455BlockBridge.occ_count] at h; omega

theorem link_counts {r a b} {w : Word} (c : Cap r w) (l : Link r w a b) :
    w.count a = r ∧ w.count b = r := by
  have h := out_le a b w
  have j := in_le a b w
  have t := Problem455Swap.tail_occ_le b w
  simp only [Problem455BlockBridge.occ_count] at t
  have ca := c a; have cb := c b
  change bigram a b w = r at l
  omega

private theorem parse {a b : Nat} (w : Word)
    (ca : bigram a b w = w.count a) (cb : bigram a b w = w.count b) :
    (dropName b w).flatMap (openPair a b) = w := by
  cases w with
  | nil => rfl
  | cons z t =>
    have nb : z ≠ b := by
      rintro rfl
      have h := in_le a z (z::t)
      simp [List.count_cons] at cb h; omega
    by_cases za : z = a
    · subst z
      cases t with
      | nil => simp [bigram,hit,List.count_cons] at ca
      | cons c s =>
        have next : c = b := by
          apply Classical.byContradiction; intro h
          have lower := out_le a b (c::s)
          simp [bigram,hit,h,List.count_cons] at ca
          simp [bigram,hit,List.count_cons] at lower
          omega
        subst c
        have size : bigram a b (a::b::s) = 1+bigram a b s := by simp [bigram,hit,Ne.symm nb]
        rw [size] at ca cb
        simp [List.count_cons,nb,Ne.symm nb] at ca cb
        have eq := parse s (by omega : bigram a b s = s.count a) (by omega : bigram a b s = s.count b)
        simpa [dropName,openPair,nb] using congrArg (List.cons a ∘ List.cons b) eq
    · have same : bigram a b (z::t) = bigram a b t := by simp [bigram,hit,za]
      rw [same] at ca cb
      simp [List.count_cons,za,nb] at ca cb
      simpa [dropName,openPair,za,nb] using congrArg (List.cons z) (parse t ca cb)
termination_by w.length

theorem recover_link {r a b} {w : Word} (cap : Cap r w) (l : Link r w a b) :
    (dropName b w).flatMap (openPair a b) = w := by
  obtain ⟨p,q⟩ := link_counts cap l
  exact parse w (l.trans p.symm) (l.trans q.symm)

private theorem drop_length (b : Nat) (w : Word) :
    (dropName b w).length + w.count b = w.length := by
  induction w with
  | nil => rfl
  | cons a t ih => by_cases e : a=b <;> simp_all [dropName,List.count_cons] <;> omega

private theorem drop_cap {r} (b : Nat) {w : Word} (cap : Cap r w) : Cap r (dropName b w) := by
  intro a; rw [drop_count]; split
  · omega
  · exact cap a

private theorem drop_valid {A : Type} (M : Model A) (b : Nat) {u v : Word} (h : M.Valid u v) :
    M.Valid (dropName b u) (dropName b v) := by
  have eq (z : Word) : residual [b] z = dropName b z := by
    unfold residual dropName; apply List.filter_congr; intro a _; by_cases e : a=b <;> simp [e]
  simpa only [eq] using residual_valid M [b] h

private theorem nonempty_composition {f g : Nat → Word} (hf : ∀ z, f z ≠ []) (hg : ∀ z, g z ≠ [])
    (z : Nat) : (f z).flatMap g ≠ [] := by
  obtain ⟨a,m⟩ := List.exists_mem_of_ne_nil _ (hf z)
  exact fun nil => hg a ((List.flatMap_eq_nil_iff.mp nil) a m)

def Asymmetric (r : Nat) (u v : Word) : Prop := ∃ a b,
    (Link r u a b ∧ ¬ Link r v a b) ∨ (Link r v a b ∧ ¬ Link r u a b)

/-- During contraction new projected links need not be predicted in advance.
    Recompute common links, decrease length, and compose their nonempty inverses. -/
theorem contract_common {r allow ts} (hr : 0 < r) (u v : Word) (cu : Cap r u) (cv : Cap r v)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ A B : Word, ∃ h : Nat → Word, (∀ x, h x ≠ []) ∧ A.flatMap h = u ∧ B.flatMap h = v ∧
      Cap r A ∧ Cap r B ∧ (P455FullSingleton.model r allow ts).Valid A B ∧
      (∀ a b, ¬ (Link r A a b ∧ Link r B a b)) ∧
      ((P455SourceFamilies.Compressed r A ∧ P455SourceFamilies.Compressed r B) ∨ Asymmetric r A B) := by
  classical
  by_cases common : ∃ a b, Link r u a b ∧ Link r v a b
  · obtain ⟨a,b,ul,vl⟩ := common
    have hlt : (dropName b u).length < u.length := by
      have c := (link_counts cu ul).2; have l := drop_length b u; omega
    obtain ⟨A,B,h,non,hu,hv,ca,cb,hvld,last,done⟩ := contract_common hr (dropName b u) (dropName b v)
      (drop_cap b cu) (drop_cap b cv) (drop_valid _ b valid)
    have op (z) : openPair a b z ≠ [] := by by_cases e : z=a <;> simp [openPair,e]
    refine ⟨A,B,fun z => (h z).flatMap (openPair a b),nonempty_composition non op,?_,?_,ca,cb,hvld,last,done⟩
    · rw [← List.flatMap_assoc,hu,recover_link cu ul]
    · rw [← List.flatMap_assoc,hv,recover_link cv vl]
  · have no (a b : Nat) := fun both => common ⟨a,b,both⟩
    refine ⟨u,v,fun a => [a],by simp,by simp,by simp,cu,cv,valid,no,?_⟩
    by_cases all : P455SourceFamilies.Compressed r u ∧ P455SourceFamilies.Compressed r v
    · exact .inl all
    · right
      by_cases one : ∃ a b, Link r u a b
      · obtain ⟨a,b,l⟩ := one; exact ⟨a,b,.inl ⟨l,fun j => no a b ⟨l,j⟩⟩⟩
      · by_cases two : ∃ a b, Link r v a b
        · obtain ⟨a,b,l⟩ := two; exact ⟨a,b,.inr ⟨l,fun j => no a b ⟨j,l⟩⟩⟩
        · exact (all ⟨fun a b l => one ⟨a,b,l⟩,fun a b l => two ⟨a,b,l⟩⟩).elim
termination_by u.length

/-- Apply an inverse block expansion throughout a semigroup derivation even
    when its rule substitutions already have multi-letter images. -/
theorem substitute_deduction {G : Word → Word → Prop} (h : Nat → Word) (non : ∀ x, h x ≠ [])
    {A B : Word} (d : Derives G A B) : Derives G (A.flatMap h) (B.flatMap h) := by
  induction d with
  | refl => exact .refl _
  | snoc _ step ih =>
    obtain ⟨a,b,l,k,f,rule,an,bn,fn,rfl,rfl⟩ := step
    exact .snoc ih ⟨a,b,l.flatMap h,k.flatMap h,fun z => (f z).flatMap h,rule,an,bn,
      nonempty_composition fn non,by simp [List.flatMap_assoc],by simp [List.flatMap_assoc]⟩

end P455Prefix
