import Problem455GridAssembly
import Problem455ReductionBoundary




namespace P455GraphReduction
open P455GridAssembly P455GridRows P455Witness P455Schedule P455FirstRewrite

def WordEdge (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : List Nat)
    (ts : Tiles) (nodes : Nat → Node) : Edges :=
  fun a b => ∃ e : EdgeCertificate, e.a=nodes a ∧ e.b=nodes b ∧ Arrow r allow mark w ts e

private theorem path_list {R : Edges} {a b} (p : Path R a b) :
    ∃ (n : Nat) (v : Nat → Nat), 0<n ∧ v 0=a ∧ v n=b ∧ ∀ i, i<n → R (v i) (v (i+1)) := by
  induction p with
  | @edge a b ed =>
    exact ⟨1,fun i => if i=0 then a else b,by decide,by simp,by simp,by
      intro i lt
      have eq : i=0 := by omega
      simpa [eq] using ed⟩
  | @join a b c _ _ left right =>
    obtain ⟨n,v,np,v0,vn,vs⟩ := left
    obtain ⟨m,q,mp,q0,qm,qs⟩ := right
    let f (i : Nat) := if i<n then v i else q (i-n)
    have atN : f n=v n := by simp [f,q0,vn]
    refine ⟨n+m,f,by omega,by simp [f,np,v0],by simp [f,qm,show ¬n+m<n by omega,show n+m-n=m by omega],?_⟩
    intro i il
    by_cases lt : i<n
    · by_cases before : i+1<n
      · simpa [f,lt,before] using vs i lt
      · have eq : i+1=n := by omega
        have found := vs i lt
        rw [eq,← atN] at found
        simpa only [eq,show f i=v i by simp [f,lt]] using found
    · have step := qs (i-n) (by omega)
      have su : i+1-n=(i-n)+1 := by omega
      simpa [f,lt,show ¬i+1<n by omega,su] using step

/-- The no-rectangle hypothesis excludes actual graph cycles on any set C
    where ports at its indexed records are functional. The indexed records
    need not be distinct. The proof repeats a concrete nonempty finite path. -/
theorem rectangle_of_cycle {r allow mark w ts} (law : Laws ts)
    (nodes : Nat → Node) (C : List Nat)
    (funct : ∀ a ∈ C, Functional r allow mark w ts (nodes a))
    {a} (loop : Path (induced C (WordEdge r allow mark w ts nodes)) a a) :
    Nonempty (Rectangle allow ts) := by
  classical
  obtain ⟨n,v,positive,first,last,steps⟩ := path_list loop
  have chooseEdge (i : Nat) : ∃ e : EdgeCertificate, e.a=nodes (v (i%n)) ∧
      e.b=nodes (v ((i%n)+1)) ∧ Arrow r allow mark w ts e := (steps _ (Nat.mod_lt _ positive)).2.2
  let c (i : Nat) := Classical.choose (chooseEdge i)
  have spec (i : Nat) := Classical.choose_spec (chooseEdge i)
  apply rectangle_of_trace law c
  · intro i; exact (spec i).2.2
  · intro i
    change (Classical.choose (chooseEdge i)).b=(Classical.choose (chooseEdge (i+1))).a
    rw [(spec i).2.1,(spec (i+1)).1]
    have lt := Nat.mod_lt i positive
    rw [← Nat.mod_add_mod i n 1]
    by_cases small : i%n+1<n
    · rw [Nat.mod_eq_of_lt small]
    · have eq : i%n+1=n := by omega
      simp [eq,last,first]
  · intro i
    change Functional r allow mark w ts (Classical.choose (chooseEdge i)).a
    rw [(spec i).1]
    exact funct _ (steps _ (Nat.mod_lt _ positive)).1

/-- The geometric alternative no longer takes acyclicity as a premise.
    A specified family of legal local changes in an actual word graph
    either admits a bounded-rank deduction or supplies a legal rectangle. -/
theorem deduction_or_rectangle {r allow w ts} (law : Laws ts) (nodes : Nat → Node)
    (C : List Nat) (A B : Bits) (word : Bits → List Nat)
    (funct : ∀ a ∈ C, Functional r allow P455SlotSaturation.noMark w ts (nodes a))
    (start : Good C (WordEdge r allow P455SlotSaturation.noMark w ts nodes) A)
    (finish : Good C (WordEdge r allow P455SlotSaturation.noMark w ts nodes) B)
    (fixed : ∀ a, A a ≠ B a → a ∈ C) (cap : P455Closure.Cap r (word A))
    (valid : (P455FullSingleton.model r allow ts).Valid (word A) (word B))
    (localChange : ∀ s t, Toward C (WordEdge r allow P455SlotSaturation.noMark w ts nodes) B s t →
      Nonempty (P455ReductionBoundary.Layout r allow ts (word A) (word B) (word s) (word t))) :
    Derives (fun u v => (P455FullSingleton.model r allow ts).Valid u v ∧
        rank u v ≤ P455MarkedRank.bound r) (word A) (word B) ∨ Nonempty (Rectangle allow ts) := by
  classical
  by_cases existsLoop : ∃ a, Path (induced C (WordEdge r allow P455SlotSaturation.noMark w ts nodes)) a a
  · obtain ⟨a,loop⟩ := existsLoop
    exact .inr (rectangle_of_cycle law nodes C funct loop)
  · exact .inl (P455ReductionBoundary.scheduled_deduction
      (fun a p => existsLoop ⟨a,p⟩) A B start finish fixed word cap valid localChange)

end P455GraphReduction
