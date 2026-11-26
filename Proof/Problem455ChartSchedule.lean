import Problem455WordChart




namespace P455ChartSchedule
open P455Witness P455FirstRewrite P455GraphReduction P455GridAssembly P455GridRows
open P455SourceFamilies P455SlotSaturation P455Schedule P455Uncrossed P455CrossedSupport
open P455ReductionBoundary P455WordChart P455ActualGuards Problem455.Slots
abbrev W := List Nat

def switch (s : Bits) (i : Nat) : Bits := fun j => if j=i then !s j else s j
def Off (C : List Nat) (A s : Bits) := ∀ j, j ∉ C → s j=A j

structure Literal (r : Nat) (allow : Tag → Prop) (u v : W) (n : Node) where
  f : P455Closure.Frame Nat
  bit : Bool
  l : W
  k : W
  owner : f.p=[n.owner]
  mate : f.q=[n.mate]
  shape : f.Valid r allow noMark
  source : u=side f l k bit
  target : v=side f l k (!bit)

theorem Literal.step {r allow u v n} (g : Literal r allow u v n) (cp : P455Closure.Cap r u) :
    P455Closure.Move r allow noMark u v := ⟨g.f,g.bit,g.l,g.k,g.shape,g.source,g.target,cp⟩

theorem walk_cap {r allow u v} (h : P455WordChart.Walk r allow u v) (cap : P455Closure.Cap r u) :
    P455Closure.Cap r v := h.transport cap (fun mv _ => mv.cap_right)

private theorem walk_compressed {r allow u v} (h : P455WordChart.Walk r allow u v) (cmp : Compressed r u) :
    Compressed r v := h.transport cmp (fun mv old a b link => old a b ((Problem455BlockBridge.move_link mv a b).mpr link))

/-- Only assignments which agree with A on fixed records are represented.
    A one-bit change is a word equation describing factors and contexts,
    with no claim that the change is a valid identity in the monoid. -/
structure Geometry (r : Nat) (allow : Tag → Prop) (C : List Nat) (A : Bits)
    (word : Bits → W) (nodes : Nat → Node) : Prop where
  cover : ∀ n, Holds r allow noMark (word A) (typedNode n) → ∃ j, nodes j=n
  active : ∀ i ∈ C, Holds r allow noMark (word A) (typedNode (nodes i))
  value : ∀ s, Off C A s → Read s nodes r allow (word s)
  flip : ∀ s, Off C A s → ∀ i ∈ C,
    Nonempty (Literal r allow (word s) (word (switch s i)) (nodes i))

private theorem off_switch {A s C i} (off : Off C A s) (mem : i ∈ C) : Off C A (switch s i) := by
  intro j nj
  have ne : j≠i := fun e => nj (e ▸ mem)
  simpa [switch,ne] using off j nj

/-- Reach any prescribed bit assignment by literal unmarked moves. The
    cap is propagated through real moves and repeated indices in C are harmless. -/
theorem reach {r allow C A word nodes} (g : Geometry r allow C A word nodes) (B : Bits)
    (offB : Off C A B) (cp : P455Closure.Cap r (word A)) : P455WordChart.Walk r allow (word A) (word B) := by
  have fill (xs : List Nat) (sub : ∀ i∈xs, i∈C) : ∃ s, Off C A s ∧
      P455WordChart.Walk r allow (word A) (word s) ∧ ∀ i∈xs, s i=B i := by
    induction xs with
    | nil => exact ⟨A,fun _ _ => rfl,.refl _,by simp⟩
    | cons i xs ih =>
      obtain ⟨s,off,path,eq⟩ := ih (fun j mem => sub j (List.mem_cons_of_mem i mem))
      by_cases done : s i=B i
      · exact ⟨s,off,path,fun j mem => (List.mem_cons.mp mem).elim (fun ji => ji ▸ done) (eq j)⟩
      have ci := sub i List.mem_cons_self
      obtain ⟨f⟩ := g.flip s off i ci
      refine ⟨switch s i,off_switch off ci,.snoc path (f.step (walk_cap path cp)),?_⟩
      intro j mem
      by_cases ji : j=i
      · subst j; cases h : s i <;> cases z : B i <;> simp_all [switch]
      · simpa [switch,ji] using eq j ((List.mem_cons.mp mem).resolve_left ji)
  obtain ⟨s,off,path,hit⟩ := fill C (fun _ h => h)
  have eq : s=B := funext fun i => by
    by_cases hi : i∈C
    · exact hit i hi
    · exact (off i hi).trans (offB i hi).symm
  exact eq ▸ path

/-- No acyclicity, functionality, admissibility of a mixed bit word,
    edge inequalities or bounded deductions are input hypotheses. -/
theorem normalize_layout {r allow ts C A B word nodes} (law : Laws ts)
    (g : Geometry r allow C A word nodes) (offB : Off C A B)
    (different : ∀ i∈C, A i≠B i)
    (cap : P455Closure.Cap r (word A)) (cmp : Compressed r (word A))
    (valid : (P455FullSingleton.model r allow ts).Valid (word A) (word B)) :
    Derives (fun u v => (P455FullSingleton.model r allow ts).Valid u v ∧ rank u v ≤ P455MarkedRank.bound r)
      (word A) (word B) ∨ Nonempty (Rectangle allow ts) := by
  classical
  let E := WordEdge r allow noMark (word A) ts nodes
  have allA : Off C A A := fun _ _ => rfl
  have AB := reach g B offB cap
  have diff (i : Nat) (hi : i∈C) : Changed (word A) (word B) (nodes i) := by
    have typed := g.active i hi
    have left := g.value A allA i typed
    have right := g.value B offB i ((walk_query AB _).mp typed)
    intro eq
    have cross := left.symm.trans (eq.trans right)
    have distinct := different i hi
    cases x : A i <;> cases y : B i <;> simp_all [profile,pair,typed.1,Ne.symm typed.1]
  have funct (i : Nat) (mem : i∈C) : Functional r allow noMark (word A) ts (nodes i) :=
    P455PortUnique.functional cap (P455FullSingleton.guard_valid valid) (diff i mem)
      (.refl _) cmp _ (.inl ⟨rfl,rfl⟩) (g.active i mem)
  by_cases loop : ∃ a, Path (induced C E) a a
  · obtain ⟨a,p⟩ := loop
    exact .inr (rectangle_of_cycle law nodes C funct p)
  have goodA : Good C E A := good_of_identity nodes C cap valid (.refl _) (g.value _ allA) diff
  have goodB : Good C E B := good_of_identity nodes C (walk_cap AB cap) (fun f => (valid f).symm) AB
    (g.value _ offB) (fun i h eq => diff i h eq.symm)
  have fixed (a : Nat) (ne : A a≠B a) : a∈C := by
    apply Classical.byContradiction; intro out; exact ne (offB a out).symm
  have sched := schedule (C := C) (E := E) (fun a p => loop ⟨a,p⟩) A B goodA goodB fixed
  have steps (s : Bits) (path : P455Quotient.Walk (Toward C E B) A s) : Off C A s ∧
      Derives (fun u v => (P455FullSingleton.model r allow ts).Valid u v ∧ rank u v ≤ P455MarkedRank.bound r)
        (word A) (word s) := by
    induction path with
    | refl => exact ⟨allA,.refl _⟩
    | @snoc s t _ flip ih =>
      obtain ⟨gs,gt,i,mem,_,ne,others⟩ := flip
      have alt : t = switch s i := funext fun j => by
        by_cases ji : j=i
        · subst j; cases x : s i <;> cases y : t i <;> simp_all [switch]
        · simpa [switch,ji] using (others j ji).symm
      have ot : Off C A t := alt ▸ off_switch ih.1 mem
      have ps := reach g s ih.1 cap
      have pt := reach g t ot cap
      obtain ⟨f⟩ := g.flip s ih.1 i mem
      obtain ⟨f0⟩ := g.flip A allA i mem
      have tgt : word t=side f.f f.l f.k (!f.bit) := alt ▸ f.target
      have cs := walk_cap ps cap
      have ct := walk_cap pt cap
      have pair0 : P455Closure.Cap r (side f.f f.l f.k false) := by
        cases b : f.bit
        · simpa only [f.source,b] using cs
        · simpa only [tgt,b,Bool.not_true] using ct
      have noS := feasible nodes C s ps (g.value s ih.1) g.cover gs mem (g.active i mem)
      have noT := feasible nodes C t pt (g.value t ot) g.cover gt mem (g.active i mem)
      have localok (b : Bool) : ¬EdgeViolation r allow ts (side f.f f.l f.k b)
          (nodes i).owner (nodes i).mate := by
        rw [f.source] at noS; rw [tgt] at noT
        cases fb : f.bit <;> cases b <;> simp_all
      let layout : P455ReductionBoundary.Layout r allow ts (word A) (word B) (word s) (word t) :=
        ⟨(nodes i).owner,(nodes i).mate,f.f,f.l,f.k,f.bit,f.owner,f.mate,f.shape,pair0,
          ⟨f0.f,f0.bit,f0.l,f0.k,f0.owner,f0.mate,f0.shape,f0.source⟩,diff i mem,
          f.source ▸ ps,f.source ▸ walk_compressed ps cmp,localok,f.source,tgt⟩
      exact ⟨ot,.snoc ih.2 (layout.step cap valid)⟩
  exact .inl (steps B sched).2

end P455ChartSchedule
