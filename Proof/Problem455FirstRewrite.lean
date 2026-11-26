import Problem455SourceFamilies




namespace P455FirstRewrite
abbrev W := List Nat
abbrev Sub := Nat → W
def Step (G : W → W → Prop) (A B : W) : Prop :=
  ∃ (u v p q : W) (h : Sub), (G u v ∨ G v u) ∧ u ≠ [] ∧ v ≠ [] ∧
    (∀ x, h x ≠ []) ∧ A = p ++ u.flatMap h ++ q ∧ B = p ++ v.flatMap h ++ q
abbrev Derives (G : W → W → Prop) := P455Quotient.Walk (Step G)

/-- A deduction entirely in a two-word class contains an actual one-step
instance from the initial to the other word. Self steps may occur anywhere. -/
theorem first_change {G : W → W → Prop} {A B : W} (ne : A ≠ B)
    (two : ∀ w, Derives G A w → w = A ∨ w = B) (path : Derives G A B) : Step G A B := by
  suffices go : ∀ w, Derives G A w → w = A ∨ Step G A B by
    exact (go B path).resolve_left ne.symm
  intro w walk
  induction walk with
  | refl => exact Or.inl rfl
  | @snoc v w prev step ih =>
    rcases ih with h | done
    · rcases two w (.snoc prev step) with f | f
      · exact Or.inl f
      · exact Or.inr (h ▸ f ▸ step)
    · exact Or.inr done

def proj (a b : Nat) (w : W) : W := w.filter (fun x => decide (x = a ∨ x = b))
private theorem proj_append (a b : Nat) (p q : W) :
    proj a b (p ++ q) = proj a b p ++ proj a b q := List.filter_append p q
private theorem filter_erase (f : Nat → Bool) (a : Nat) (w : W) :
    (w.erase a).filter f = (w.filter f).erase a := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x = a
    · subst x
      by_cases h : f a = true
      · simp [h]
      · have n : a ∉ xs.filter f := by simp [h]
        simp [h, List.erase_of_not_mem n]
    · by_cases h : f x = true <;> simp [List.erase_cons, e, h, ih]
private theorem first_split {a : Nat} {v : W} (mem : a ∈ v) :
    ∃ L R : W, v = L ++ a :: R ∧ a ∉ L := by
  induction v with
  | nil => simp at mem
  | cons z zs ih =>
    by_cases e : z = a
    · subst z; exact ⟨[],zs,rfl,by simp⟩
    · obtain ⟨l,r,f,n⟩ := ih ((List.mem_cons.mp mem).resolve_left (Ne.symm e))
      exact ⟨z::l,r,by simp [f],by simp [Ne.symm e,n]⟩

private theorem prefix_head {a z : Nat} {L : W} (n : a ∉ L) (m : z ∈ L) :
    ∃ t, proj a z L = z :: t := by
  induction L with
  | nil => simp at m
  | cons c L ih =>
    have ca : c ≠ a := fun e => n (e ▸ List.mem_cons_self)
    by_cases cz : c = z
    · subst c; exact ⟨proj a z L,by simp [proj]⟩
    · have mz := (List.mem_cons.mp m).resolve_left (Ne.symm cz)
      obtain ⟨t,e⟩ := ih (fun h => n (List.mem_cons_of_mem c h)) mz
      exact ⟨t, by simpa [proj,ca,cz] using e⟩

private theorem flatten_commute (g : Sub) (a : Nat) (L : W)
    (ok : ∀ z ∈ L, g a ++ g z = g z ++ g a) :
    g a ++ L.flatMap g = L.flatMap g ++ g a := by
  induction L with
  | nil => simp
  | cons z L ih =>
    have tail := ih (fun x h => ok x (List.mem_cons_of_mem z h))
    have head := ok z (List.mem_cons_self)
    simp only [List.flatMap_cons]
    calc
      _ = (g a ++ g z) ++ L.flatMap g := (List.append_assoc ..).symm
      _ = (g z ++ g a) ++ L.flatMap g := by rw [head]
      _ = _ := by simp only [List.append_assoc,tail]

/-- Multiplicities and two-letter projections of all pairs with noncommuting
images determine the whole substituted word, even for erasing substitutions. -/
theorem trace {u v : W} (g : Sub) (counts : ∀ x, u.count x = v.count x)
    (pairs : ∀ i j, g i ++ g j ≠ g j ++ g i → proj i j u = proj i j v) :
    u.flatMap g = v.flatMap g := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons b t => simpa using counts b
  | cons a u ih =>
    have m : a ∈ v := List.count_pos_iff.mp (by rw [← counts]; simp)
    obtain ⟨L,R,rfl,n⟩ := first_split m
    have cross (z) (mz : z ∈ L) : g a ++ g z = g z ++ g a := by
      apply Classical.byContradiction
      intro bad
      have pair := pairs a z bad
      obtain ⟨t,eq⟩ := prefix_head n mz
      rw [proj_append,eq] at pair
      have az : a = z := by simpa [proj] using congrArg List.head? pair
      exact n (az ▸ mz)
    have er : (L ++ a :: R).erase a = L ++ R := by
      rw [List.erase_append_right _ n, List.erase_cons_head]
    have cnt (x) : u.count x = (L ++ R).count x := by
      have orig := counts x
      simp only [List.count_append,List.count_cons] at orig ⊢
      omega
    have rest (i j) (bad : g i ++ g j ≠ g j ++ g i) : proj i j u = proj i j (L ++ R) := by
      have eq := congrArg (fun w : W => w.erase a) (pairs i j bad)
      dsimp only at eq
      unfold proj at eq
      rw [← filter_erase, ← filter_erase, List.erase_cons_head, er] at eq
      exact eq
    have sub := ih cnt rest
    simp only [List.flatMap_cons,List.flatMap_append] at sub ⊢
    calc
      _ = g a ++ (L.flatMap g ++ R.flatMap g) := by rw [sub]
      _ = _ := by rw [← List.append_assoc, flatten_commute g a L cross, List.append_assoc]
/-- The two tester consequences required of a rule in the chosen orientation.
Clipping at r+1 records the overflow class. -/
structure TesterRule (r : Nat) (u v : W) : Prop where
  unary : ∀ x, min (u.count x) (r+1) = min (v.count x) (r+1)
  binary : P455Quotient.Cap r u → P455Quotient.Cap r v →
    ∀ i j, proj i j u ≠ proj i j v → u.count i = r ∧ u.count j = r

private theorem cap_rule {r : Nat} {p q u : W} {h : Sub} (ne : ∀ x, h x ≠ [])
    (cap : P455Quotient.Cap r (p ++ u.flatMap h ++ q)) : P455Quotient.Cap r u := by
  intro x
  obtain ⟨a,hm⟩ : ∃ a, a ∈ h x := by
    cases e : h x with
    | nil => exact False.elim (ne x e)
    | cons a t => exact ⟨a,List.mem_cons_self⟩
  have pos := List.count_pos_iff.mpr hm
  have mul := Nat.mul_le_mul_left (u.count x) pos
  have ct := P455DonorInterval.split_contributions h u x a
  have bound := cap a
  simp only [List.count_append] at bound
  simp only [Nat.mul_one] at mul
  omega

private theorem counted_edge (h : Sub) (x a b : Nat)
    (pos : 0 < Problem455Swap.bigram a b (h x)) (u : W) :
    u.count x ≤ Problem455Swap.bigram a b (u.flatMap h) := by
  induction u with
  | nil => simp [Problem455Swap.bigram]
  | cons z u ih =>
    simp only [List.flatMap_cons,Problem455Swap.bigram_append]
    by_cases e : z = x
    · subst z; simp [List.count_cons]; omega
    · simp [List.count_cons,e]; omega

private theorem singleton {r : Nat} {p q u : W} {h : Sub}
    (ne : ∀ x, h x ≠ []) (cap : P455Quotient.Cap r (p ++ u.flatMap h ++ q))
    (compressed : P455SourceFamilies.Compressed r (p ++ u.flatMap h ++ q))
    {x : Nat} (sat : u.count x = r) : ∃ a, h x = [a] := by
  cases e : h x with
  | nil => exact False.elim (ne x e)
  | cons a t =>
    cases t with
    | nil => exact ⟨a,rfl⟩
    | cons b tail =>
      have edge : 0 < Problem455Swap.bigram a b (h x) := by
        rw [e]; simp [Problem455Swap.bigram,Problem455Swap.hit]; omega
      have lo := counted_edge h x a b edge u
      let U := p ++ u.flatMap h ++ q
      have lower : r ≤ Problem455Swap.bigram a b U := by
        dsimp [U]; rw [Problem455Swap.bigram_append,Problem455Swap.bigram_append]; omega
      have upper := Problem455Swap.out_bound a b (b+1) (by omega) U
      rw [Problem455BlockBridge.occ_count] at upper
      have hc : U.count a ≤ r := cap a
      exact False.elim (compressed a b (by change Problem455Swap.bigram a b U = r; omega))

private theorem project_images (a b : Nat) (u : W) (h : Sub) :
    proj a b (u.flatMap h) = u.flatMap (fun x => proj a b (h x)) := by
  induction u with
  | nil => rfl
  | cons x u ih => simp only [List.flatMap_cons,proj_append,ih]

private theorem projected_commutes_without (a b c d : Nat) (ca : c ≠ a) (da : d ≠ a) :
    proj a b [c] ++ proj a b [d] = proj a b [d] ++ proj a b [c] := by
  by_cases cb : c = b <;> by_cases db : d = b <;> simp_all [proj]

/-- Every literal name in a changed binary projection is the singleton image
of an actual matched-side rule variable. This uses no occurrence indexing. -/
theorem changed_name {r : Nat} (hr : 0 < r) {p q u v : W} {h : Sub}
    (ne : ∀ x, h x ≠ []) (cap : P455Quotient.Cap r (p ++ u.flatMap h ++ q))
    (compressed : P455SourceFamilies.Compressed r (p ++ u.flatMap h ++ q))
    (rule : TesterRule r u v) (a b : Nat)
    (changed : proj a b (p ++ u.flatMap h ++ q) ≠ proj a b (p ++ v.flatMap h ++ q)) :
    ∃ x ∈ u, h x = [a] := by
  have cu := cap_rule ne cap
  have counts (x) : u.count x = v.count x := by
    have eq := rule.unary x
    have bound := cu x
    omega
  have cv : P455Quotient.Cap r v := fun x => counts x ▸ cu x
  let g : Sub := fun x => proj a b (h x)
  apply Classical.byContradiction
  intro absent
  apply changed
  simp only [proj_append,project_images]
  have pair (i j) (bad : g i ++ g j ≠ g j ++ g i) : proj i j u = proj i j v := by
    apply Classical.byContradiction
    intro diff
    obtain ⟨ci,cj⟩ := rule.binary cu cv i j diff
    obtain ⟨c,ec⟩ := singleton ne cap compressed ci
    obtain ⟨d,ed⟩ := singleton ne cap compressed cj
    have mi : i ∈ u := List.count_pos_iff.mp (ci ▸ hr)
    have mj : j ∈ u := List.count_pos_iff.mp (cj ▸ hr)
    have ca : c ≠ a := fun e => absent ⟨i,mi,ec.trans (e ▸ rfl)⟩
    have da : d ≠ a := fun e => absent ⟨j,mj,ed.trans (e ▸ rfl)⟩
    apply bad
    simpa [g,ec,ed] using projected_commutes_without a b c d ca da
  rw [show u.flatMap (fun x => proj a b (h x)) = v.flatMap (fun x => proj a b (h x))
      from trace g counts pair]

/-- A list of distinct names included in an arbitrary covering list gives a
numeric lower bound on its length, even if that covering list contains repeats. -/
theorem size_le {D C : W} (uniq : D.Nodup) (sub : ∀ a ∈ D, a ∈ C) : D.length ≤ C.length := by
  induction D generalizing C with
  | nil => simp
  | cons a t ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp uniq
    have mem := sub a List.mem_cons_self
    have le := ih tail (C := C.erase a) (fun x hx =>
      (List.mem_erase_of_ne (a := x) (b := a) (fun e => fresh (e ▸ hx))).mpr (sub x (List.mem_cons_of_mem _ hx)))
    have len := List.length_erase_of_mem mem
    have pos : 0 < C.length := by cases C <;> simp_all
    simp only [List.length_cons]
    omega

/-- Any explicit list of rule variables covering the matched side must have
at least as many entries as there are distinct literal participants. -/
theorem instance_rank {r : Nat} (hr : 0 < r) {p q u v D C : W} {h : Sub}
    (ne : ∀ x, h x ≠ []) (cap : P455Quotient.Cap r (p ++ u.flatMap h ++ q))
    (compressed : P455SourceFamilies.Compressed r (p ++ u.flatMap h ++ q))
    (rule : TesterRule r u v) (uniq : D.Nodup) (cover : ∀ x ∈ u, x ∈ C)
    (changes : ∀ a ∈ D, ∃ b, proj a b (p ++ u.flatMap h ++ q) ≠
      proj a b (p ++ v.flatMap h ++ q)) : D.length ≤ C.length := by
  have sub (a) (ma : a ∈ D) : a ∈ C.map (fun x => (h x).headD 0) := by
    obtain ⟨b,diff⟩ := changes a ma
    obtain ⟨x,mx,e⟩ := changed_name hr ne cap compressed rule a b diff
    exact List.mem_map.mpr ⟨x,cover x mx,by simp [e]⟩
  simpa using size_le uniq sub

/-- The list of distinct variables of an oriented rule pair. -/
def names : W → W
  | [] => []
  | x :: w => if x ∈ w then names w else x :: names w

@[simp] theorem mem_names (a : Nat) (w : W) : a ∈ names w ↔ a ∈ w := by
  induction w with
  | nil => simp [names]
  | cons x w ih =>
    by_cases e : x ∈ w
    · simp only [names,if_pos e,ih,List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun eq => eq ▸ e) id⟩
    · simp [names,e,ih]

theorem names_distinct (w : W) : (names w).Nodup := by
  induction w with
  | nil => simp [names]
  | cons x w ih => by_cases e : x ∈ w <;> simp [names,e,ih]

def rank (u v : W) := (names (u ++ v)).length

theorem rank_swap (u v : W) : rank u v = rank v u := by
  apply Nat.le_antisymm
  · apply size_le (names_distinct _)
    simp [List.mem_append,Or.comm]
  · apply size_le (names_distinct _)
    simp [List.mem_append,Or.comm]

/-- This is the usual semigroup-word semantics in a monoid. The operation
alone occurs in rule terms. Empty contexts use the unit when evaluated. -/
structure Model (A : Type) where
  op : A → A → A
  unit : A
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  oneL : ∀ x, op unit x = x
  oneR : ∀ x, op x unit = x

namespace Model
variable {A : Type} (M : Model A)
def eval (f : Nat → A) : W → A
  | [] => M.unit
  | x :: xs => M.op (f x) (eval f xs)

def Valid (u v : W) := ∀ f, M.eval f u = M.eval f v

theorem eval_append (f : Nat → A) (u v : W) :
    M.eval f (u ++ v) = M.op (M.eval f u) (M.eval f v) := by
  induction u with
  | nil => simp [eval,M.oneL]
  | cons x t ih => simp [eval,ih,M.assoc]

theorem eval_instance (f : Nat → A) (h : Sub) (w : W) :
    M.eval f (w.flatMap h) = M.eval (fun x => M.eval f (h x)) w := by
  induction w with
  | nil => rfl
  | cons x t ih => simp [eval,eval_append,ih]

theorem step_sound {G : W → W → Prop} (valid : ∀ u v, G u v → M.Valid u v)
    {U V : W} (s : Step G U V) : M.Valid U V := by
  obtain ⟨u,v,p,q,h,orient,_,_,_,rfl,rfl⟩ := s
  intro f
  simp only [M.eval_append,M.eval_instance]
  rcases orient with g | g
  · rw [valid u v g]
  · rw [valid v u g]

theorem derives_sound {G : W → W → Prop} (valid : ∀ u v, G u v → M.Valid u v)
    {U V : W} (walk : Derives G U V) : M.Valid U V := by
  induction walk with
  | refl => intro _; rfl
  | snoc _ st ih => exact fun f => (ih f).trans (M.step_sound valid st f)
end Model

/-- Hypotheses on one actual pair of witness words; validity of the
distinguished identity and exhaustion of its semantic class are separate. -/
structure RankWitness {A : Type} (M : Model A) (r : Nat) (U V D : W) : Prop where
  nonempty : U ≠ [] ∧ V ≠ []
  different : U ≠ V
  identity : M.Valid U V
  two : ∀ w, M.Valid U w → w = U ∨ w = V
  cap : P455Quotient.Cap r U
  compressed : P455SourceFamilies.Compressed r U
  distinct : D.Nodup
  participants : ∀ a ∈ D, ∃ b, proj a b U ≠ proj a b V

/-- Every actual step which first leaves U has rule rank at least |D|. -/
theorem step_rank {A : Type} {M : Model A} {r : Nat} (hr : 0 < r)
    {U V D : W} (wit : RankWitness M r U V D)
    (testers : ∀ u v, M.Valid u v → TesterRule r u v)
    {G : W → W → Prop} (valid : ∀ u v, G u v → M.Valid u v) {T : W}
    (s : Step G U T) (diff : U ≠ T) :
    ∃ u v, G u v ∧ D.length ≤ rank u v := by
  have iden := M.step_sound valid s
  have direct := (wit.two T iden).resolve_left diff.symm
  subst T
  obtain ⟨u,v,p,q,h,oriented,_,_,ne,eq1,eq2⟩ := s
  have vr : M.Valid u v := oriented.elim (valid u v) (fun rev f => (valid v u rev f).symm)
  have cover (x) (m : x ∈ u) : x ∈ names (u ++ v) := by simp [m]
  have bound : D.length ≤ rank u v := by
    apply instance_rank hr ne (eq1 ▸ wit.cap) (eq1 ▸ wit.compressed) (testers _ _ vr)
      wit.distinct cover
    simpa only [← eq1, ← eq2] using wit.participants
  rcases oriented with forward | backward
  · exact ⟨u,v,forward,bound⟩
  · exact ⟨v,u,backward,rank_swap u v ▸ bound⟩

theorem derivation_rank {A : Type} {M : Model A} {r : Nat} (hr : 0 < r)
    {U V D : W} (wit : RankWitness M r U V D)
    (testers : ∀ u v, M.Valid u v → TesterRule r u v)
    {G : W → W → Prop} (valid : ∀ u v, G u v → M.Valid u v) (path : Derives G U V) :
    ∃ u v, G u v ∧ D.length ≤ rank u v :=
  step_rank hr wit testers valid (first_change wit.different
    (fun w walk => wit.two w (M.derives_sound valid walk)) path) wit.different

/-- The monoid M is fixed before the padding bound is chosen. No assumption
about the existence of an accepting computation or rectangle is encoded. -/
theorem no_finite_basis_of_witnesses {A : Type} (M : Model A) (r : Nat) (hr : 0 < r)
    (testers : ∀ u v, M.Valid u v → TesterRule r u v)
    (witnesses : ∀ k : Nat, ∃ U V D, RankWitness M r U V D ∧ k < D.length)
    (G : List (W × W)) (valid : ∀ u v, (u,v) ∈ G → M.Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ M.Valid U V ∧ ¬ Derives (fun u v => (u,v) ∈ G) U V := by
  let sizes := G.map (fun t => rank t.1 t.2)
  obtain ⟨U,V,D,w,large⟩ := witnesses sizes.sum
  refine ⟨U,V,w.nonempty.1,w.nonempty.2,w.identity,?_⟩
  intro derivation
  obtain ⟨u,v,mem,bound⟩ := derivation_rank hr w testers valid derivation
  have inSizes : rank u v ∈ sizes := List.mem_map.mpr ⟨(u,v),mem,rfl⟩
  have less (s : List Nat) (n) (m : n ∈ s) : n ≤ s.sum := by
    induction s with
    | nil => simp at m
    | cons z t ih =>
      simp only [List.sum_cons]
      rcases List.mem_cons.mp m with e | m
      · omega
      · have := ih m; omega
  have := less sizes (rank u v) inSizes
  omega

end P455FirstRewrite
