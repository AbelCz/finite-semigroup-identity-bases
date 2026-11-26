import Problem455GraphReduction
import Problem455PortUnique




namespace P455WordChart
open P455Witness P455Paths P455GridRows P455GraphReduction P455GridAssembly
open P455SourceFamilies P455CrossedSupport P455ActualGuards P455SingletonEvaluation
open P455SlotSaturation P455Uncrossed P455PortReflection P455Schedule P455FirstRewrite Problem455.Slots
abbrev W := List Nat
abbrev Walk (r : Nat) (allow : Tag → Prop) := P455Quotient.Walk (P455Closure.Move r allow noMark)

private theorem free_if (p : Bool) (q : Query) (hq : markFree q=true) :
    markFree (flagQ p q)=true := by cases p <;> simp [flagQ,markFree,hq]

private theorem free_local (ts : Tiles) (e : EdgeCertificate) : markFree (localCert ts e)=true := by
  have hr (a b : Node) : markFree (rightward ts a b)=true := rfl
  have hd (a b : Node) : markFree (downward ts a b)=true := rfl
  simp only [localCert,allQ,markFree,free_if _ _ (hr ..),free_if _ _ (hd ..)]
  rw [free_if _ _ (show markFree (.both (downward ts e.right e.diagonal)
    (rightward ts e.down e.diagonal))=true from rfl)]
  rfl

private theorem free_successor (ts : Tiles) (e : EdgeCertificate) : markFree (chosenSuccessor ts e)=true := by
  dsimp only [chosenSuccessor]; split <;> rfl

theorem remark_arrow {r allow mark mark' w ts e} (a : Arrow r allow mark w ts e) :
    Arrow r allow mark' w ts e :=
  ⟨a.1,a.2.1,remark (free_local ..) a.2.2.1,remark (free_successor ..) a.2.2.2⟩

theorem walk_query {r allow u v} (p : Walk r allow u v) (q : Query) :
    Holds r allow noMark u q ↔ Holds r allow noMark v q := by
  induction p with
  | refl => rfl
  | snoc _ step ih => exact ih.trans (query_invariant step q)

theorem walk_arrow {r allow u v ts e} (p : Walk r allow u v) :
    Arrow r allow noMark u ts e ↔ Arrow r allow noMark v ts e := by
  simp only [Arrow,← walk_query p]

def Read (s : Bits) (nodes : Nat → Node) (r : Nat) (allow : Tag → Prop) (w : W) :=
  ∀ i, Holds r allow noMark w (typedNode (nodes i)) →
    select [(nodes i).owner,(nodes i).mate] w = profile (nodes i).owner (nodes i).mate (nodes i).tag (s i)

private theorem true_false_query {r allow ts u e} (edge : Arrow r allow noMark u ts e)
    (a : select [e.a.owner,e.a.mate] u = profile e.a.owner e.a.mate e.a.tag true)
    (b : select [e.b.owner,e.b.mate] u = profile e.b.owner e.b.mate e.b.tag false) :
    Holds r allow (fun _ _ => True) u (e.query ts) := by
  have h := remark_arrow (mark' := fun _ _ => True) edge
  exact ⟨⟨h.1.1,h.1.2.1,h.1.2.2.1,.inl trivial,a⟩,
    ⟨h.2.1.1,h.2.1.2.1,h.2.1.2.2.1,.inl trivial,b⟩,h.2.2.1,h.2.2.2,trivial⟩

def Changed (u v : W) (n : Node) := select [n.owner,n.mate] u ≠ select [n.owner,n.mate] v

/-- The endpoint inequalities follow by looking at the actual edge tester
    of a hypothetical descending edge. No opposite-word shape is needed. -/
theorem good_of_identity {r allow ts U V w A} (nodes : Nat → Node) (C : List Nat)
    (cap : P455Closure.Cap r U) (valid : (P455FullSingleton.model r allow ts).Valid U V)
    (graph : Walk r allow w U) (read : Read A nodes r allow U)
    (diff : ∀ i ∈ C, Changed U V (nodes i)) :
    Good C (WordEdge r allow noMark w ts nodes) A := by
  intro a b ed member on
  obtain ⟨e,ea,eb,aU⟩ := ed
  have atU := (walk_arrow graph).mp aU
  have left := read a (ea ▸ atU.1)
  have right := read b (eb ▸ atU.2.1)
  rw [← ea,on] at left
  rw [← eb] at right
  cases off : A b with
  | true => rfl
  | false =>
    rw [off] at right
    have mark := ((P455MarkedRank.valid_pair ..).mp ((P455MarkedRank.valid_pair ..).mp valid).2).1
    have edge := ((P455MarkedRank.valid_pair ..).mp mark).2
    have obs := P455EdgeProduct.endpoint_observed cap edge e (true_false_query atU left right)
    rcases member with mem|mem
    · exact False.elim (diff a mem (ea ▸ obs.1))
    · exact False.elim (diff b mem (eb ▸ obs.2))

private theorem bit_inj {a b : Nat} (ne : a≠b) (tag : Tag) {i j : Bool}
    (e : profile a b tag i = profile a b tag j) : i=j := by
  cases i <;> cases j <;> simp_all [profile,pair]

/-- Ordered roles are determined by a record on the unordered pair.
    Reversal would require both distinct letters to head the same projection. -/
theorem match_unique {r allow w} {n m : Node} (ok : Holds r allow noMark w (typedNode n))
    (other : Holds r allow noMark w (typedNode m)) (match' : Matches m n.owner n.mate) : m=n := by
  rcases match' with ⟨x,y⟩|⟨x,y⟩
  · exact P455PortUnique.node_unique m n x y other ok
  · obtain ⟨b,ob⟩ := ok.2.2.2
    obtain ⟨c,oc⟩ := other.2.2.2
    rw [x,y,select_pair_symm,ob] at oc
    have same := congrArg List.head? oc
    exact False.elim (ok.1 (by simpa [profile,profilePrefix] using same))

/-- Convert any failing incident marked edge into an actual descending
    graph edge. Coverage concerns typed records in the original word. -/
theorem feasible {r allow w ts v} (nodes : Nat → Node) (C : List Nat) (s : Bits)
    (p : Walk r allow w v) (read : Read s nodes r allow v)
    (cover : ∀ n, Holds r allow noMark w (typedNode n) → ∃ j, nodes j=n)
    (good : Good C (WordEdge r allow noMark w ts nodes) s)
    {i : Nat} (mem : i ∈ C) (typed : Holds r allow noMark w (typedNode (nodes i))) :
    ¬ EdgeViolation r allow ts v (nodes i).owner (nodes i).mate := by
  rintro ⟨e,side,mt,h⟩
  have typedA : Holds r allow noMark v (typedNode e.a) :=
    ⟨h.1.1,h.1.2.1,h.1.2.2.1,_,h.1.2.2.2.2⟩
  have typedB : Holds r allow noMark v (typedNode e.b) :=
    ⟨h.2.1.1,h.2.1.2.1,h.2.1.2.2.1,_,h.2.1.2.2.2.2⟩
  have arrV : Arrow r allow noMark v ts e :=
    ⟨typedA,typedB,remark (free_local ..) h.2.2.1,remark (free_successor ..) h.2.2.2.1⟩
  have arr := (walk_arrow p).mpr arrV
  have typedI := (walk_query p _).mp typed
  obtain ⟨a,b,ea,eb,incident⟩ : ∃ a b, nodes a=e.a ∧ nodes b=e.b ∧ (a∈C ∨ b∈C) := by
    cases side with
    | false =>
      obtain ⟨b,hb⟩ := cover _ arr.2.1
      exact ⟨i,b,(match_unique typedI typedA mt).symm,hb,.inl mem⟩
    | true =>
      obtain ⟨a,ha⟩ := cover _ arr.1
      exact ⟨a,i,ha,(match_unique typedI typedB mt).symm,.inr mem⟩
  have la := read a (ea ▸ typedA)
  have lb := read b (eb ▸ typedB)
  rw [ea] at la
  rw [eb] at lb
  have one := bit_inj typedA.1 _ (la.symm.trans h.1.2.2.2.2)
  have zero := bit_inj typedB.1 _ (lb.symm.trans h.2.1.2.2.2.2)
  have twice := good a b ⟨e,ea.symm,eb.symm,arr⟩ incident one
  simp [zero] at twice

end P455WordChart
