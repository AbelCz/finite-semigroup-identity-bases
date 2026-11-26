import Problem455FirstRewrite



namespace P455Schedule
abbrev Edges := Nat → Nat → Prop
abbrev Bits := Nat → Bool

inductive Path (R : Edges) : Nat → Nat → Prop
  | edge {x y} (e : R x y) : Path R x y
  | join {x y z} (l : Path R x y) (r : Path R y z) : Path R x z

def induced (C : List Nat) (E : Edges) : Edges := fun a b => a ∈ C ∧ b ∈ C ∧ E a b

def Acyclic (C : List Nat) (E : Edges) := ∀ a, ¬Path (induced C E) a a

def Good (C : List Nat) (E : Edges) (s : Bits) :=
  ∀ a b, E a b → (a ∈ C ∨ b ∈ C) → s a = true → s b = true

def Flip (C : List Nat) (E : Edges) (available : Nat → Prop) (s t : Bits) :=
  Good C E s ∧ Good C E t ∧ ∃ a ∈ C, available a ∧ s a ≠ t a ∧ ∀ b, b ≠ a → s b = t b

def Down (C : List Nat) (E : Edges) (available : Nat → Prop) (s t : Bits) :=
  Flip C E available s t ∧ ∀ a, t a = true → s a = true

def meet (A B : Bits) : Bits := fun a => A a && B a

private theorem minimal {R : Edges} (no : ∀ a, ¬ R a a)
    (tr : ∀ {a b c}, R a b → R b c → R a c) (xs : List Nat) (ne : xs ≠ []) :
    ∃ a ∈ xs, ∀ b ∈ xs, ¬ R b a := by
  induction xs with
  | nil => exact (ne rfl).elim
  | cons x xs ih =>
    by_cases emp : xs = []
    · subst xs
      refine ⟨x,List.mem_cons_self,?_⟩
      intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact no b
    obtain ⟨a,mem,first⟩ := ih emp
    by_cases e : R x a
    · refine ⟨x,List.mem_cons_self,?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with eq|hit
      · exact eq ▸ no x
      · exact fun k => first b hit (tr k e)
    · refine ⟨a,List.mem_cons_of_mem _ mem,?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with eq|hit
      · exact eq ▸ e
      · exact first b hit

private theorem switch {C E} (acy : Acyclic C E) (available : Nat → Prop) (s t : Bits)
    (sOK : Good C E s) (tOK : Good C E t) (todo : List Nat)
    (uniq : todo.Nodup)
    (all : ∀ a ∈ todo, a ∈ C ∧ available a ∧ s a = true ∧ t a = false)
    (cover : ∀ a, s a ≠ t a → a ∈ todo) :
    P455Quotient.Walk (Down C E available) s t := by
  classical
  by_cases empty : todo = []
  · have eq : s = t := by
      funext a; apply Classical.byContradiction; intro diff
      exact List.not_mem_nil (empty ▸ cover a diff)
    rw [eq]; exact .refl _
  obtain ⟨a,am,first⟩ :=
    minimal (R := Path (induced C E)) acy (fun m n => .join m n) todo empty
  obtain ⟨ac,ch,sa,ta⟩ := all a am
  let v : Bits := fun j => if j=a then false else s j
  have change : v a = false := by simp [v]
  have fixed (j) (h : j ≠ a) : v j = s j := by simp [v,h]
  have vOK : Good C E v := by
    intro i j edge touch on
    have si : s i = true := by
      by_cases eq : i = a
      · subst i; simp [change] at on
      · exact (fixed i eq).symm.trans on
    by_cases eq : j = a
    · subst j
      have off : t i = false := by
        cases e : t i with
        | false => rfl
        | true => have impossible := tOK i a edge (.inr ac) e; simp [ta] at impossible
      have active := cover i (by simp [si,off])
      exact False.elim (first i active (.edge ⟨(all i active).1,ac,edge⟩))
    · exact (fixed j eq).trans (sOK i j edge touch si)
  have single : Down C E available s v := by
    refine ⟨⟨sOK,vOK,a,ac,ch,by simp [sa,change],fun j ne => (fixed j ne).symm⟩,?_⟩
    intro j h
    by_cases eq : j=a
    · subst j; simp [change] at h
    · exact (fixed j eq).symm.trans h
  have next (j) (hj : j ∈ todo.erase a) :
      j ∈ C ∧ available j ∧ v j = true ∧ t j = false := by
    obtain ⟨ne,hit⟩ := uniq.mem_erase_iff.mp hj
    obtain ⟨h1,h2,h3,h4⟩ := all j hit
    exact ⟨h1,h2,(fixed j ne).trans h3,h4⟩
  have rem (j) (diff : v j ≠ t j) : j ∈ todo.erase a := by
    by_cases eq : j=a
    · subst j; exact False.elim (diff (change.trans ta.symm))
    · exact uniq.mem_erase_iff.mpr ⟨eq,cover j (fun h => diff ((fixed j eq).trans h))⟩
  have tail := switch acy available v t vOK tOK (todo.erase a) (uniq.erase a) next rem
  exact (P455Quotient.Walk.snoc (.refl _) single).trans tail
termination_by todo.length
decreasing_by
  have n := List.length_erase_of_mem am
  have pos : 0 < todo.length := List.length_pos_iff.mpr empty
  omega

private theorem down_to_meet {C E} (acy : Acyclic C E) (A B : Bits) (gA : Good C E A) (gB : Good C E B)
    (fixed : ∀ a, A a ≠ B a → a ∈ C) :
    P455Quotient.Walk (Down C E (fun a => A a=true ∧ B a=false)) A (meet A B) := by
  let todo := (P455FirstRewrite.names C).filter (fun a => A a && !B a)
  have inTodo (a) : a ∈ todo ↔ a ∈ C ∧ A a = true ∧ B a = false := by
    simp [todo,P455FirstRewrite.mem_names]
  have ok : Good C E (meet A B) := by
    intro i j edge hit h
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨gA i j edge hit a,gB i j edge hit b⟩
  apply switch acy _ _ _ gA ok todo ((P455FirstRewrite.names_distinct C).sublist List.filter_sublist)
  · intro a ha
    obtain ⟨hc,h1,h2⟩ := (inTodo a).mp ha
    exact ⟨hc,⟨h1,h2⟩,h1,by simp [meet,h2]⟩
  · intro a diff
    cases ha : A a <;> cases hb : B a <;> simp [meet,ha,hb] at diff
    exact (inTodo a).mpr ⟨fixed a (by simp [ha,hb]),ha,hb⟩

/-- Explicit two phases. Within each phase every changed vertex moves in a
    single direction. The starting-only and target-only vertex sets are disjoint. -/
theorem phases {C E} (acy : Acyclic C E) (A B : Bits) (gA : Good C E A) (gB : Good C E B)
    (fixed : ∀ a, A a ≠ B a → a ∈ C) :
    P455Quotient.Walk (Down C E (fun a => A a=true ∧ B a=false)) A (meet A B) ∧
    P455Quotient.Walk (Down C E (fun a => B a=true ∧ A a=false)) B (meet A B) := by
  have eq : meet B A = meet A B := by funext a; exact Bool.and_comm ..
  exact ⟨down_to_meet acy A B gA gB fixed,eq ▸ down_to_meet acy B A gB gA (fun a d => fixed a (Ne.symm d))⟩

def Toward (C : List Nat) (E : Edges) (goal : Bits) (s t : Bits) :=
  Flip C E (fun a => t a = goal a) s t

private theorem map_walk {R S : Bits → Bits → Prop} {a b : Bits}
    (path : P455Quotient.Walk R a b) (one : ∀ {u v}, R u v → S u v) : P455Quotient.Walk S a b := by
  induction path with
  | refl => exact .refl _
  | snoc _ m ih => exact .snoc ih (one m)

private theorem reverse_path {R : Bits → Bits → Prop} {a b : Bits}
    (h : P455Quotient.Walk (fun s t => R t s) a b) : P455Quotient.Walk R b a := by
  induction h with
  | refl => exact .refl _
  | snoc _ m ih => exact (P455Quotient.Walk.snoc (.refl _) m).trans ih

theorem schedule {C E} (acy : Acyclic C E) (A B : Bits) (gA : Good C E A) (gB : Good C E B)
    (fixed : ∀ a, A a ≠ B a → a ∈ C) :
    P455Quotient.Walk (Toward C E B) A B := by
  obtain ⟨lhs,rhs⟩ := phases acy A B gA gB fixed
  apply (map_walk lhs (S := Toward C E B) ?_).trans
  · exact reverse_path (map_walk rhs (S := fun s t => Toward C E B t s) (by
      intro s t st
      obtain ⟨⟨ok1,ok2,a,hc,ab,ne,unch⟩,down⟩ := st
      have ons : s a = true := by cases h : s a <;> cases k : t a <;> simp_all
      exact ⟨ok2,ok1,a,hc,ons.trans ab.1.symm,Ne.symm ne,fun j h => (unch j h).symm⟩))
  · intro s t st
    obtain ⟨⟨ok1,ok2,a,hc,ab,ne,unch⟩,down⟩ := st
    have off : t a = false := by cases h : s a <;> cases k : t a <;> simp_all
    exact ⟨ok1,ok2,a,hc,off.trans ab.2.symm,ne,unch⟩

/-- Realizing the safe Boolean singletons by bounded-rank word steps produces
    an ordinary multiplication-only equational deduction for the two words. -/
theorem derivation {C E} (acy : Acyclic C E) (A B : Bits) (gA : Good C E A) (gB : Good C E B)
    (fixed : ∀ a, A a ≠ B a → a ∈ C) (word : Bits → P455FirstRewrite.W)
    {M : P455FirstRewrite.Model α} (k : Nat)
    (one : ∀ s t, Toward C E B s t →
      P455FirstRewrite.Step (fun u v => M.Valid u v ∧ P455FirstRewrite.rank u v ≤ k) (word s) (word t)) :
    P455FirstRewrite.Derives (fun u v => M.Valid u v ∧ P455FirstRewrite.rank u v ≤ k) (word A) (word B) := by
  have lift {a b : Bits} (path : P455Quotient.Walk (Toward C E B) a b) :
      P455FirstRewrite.Derives (fun u v => M.Valid u v ∧ P455FirstRewrite.rank u v ≤ k)
        (word a) (word b) := by
    induction path with
    | refl => exact .refl _
    | snoc _ move ih => exact .snoc ih (one _ _ move)
  exact lift (schedule acy A B gA gB fixed)

end P455Schedule
