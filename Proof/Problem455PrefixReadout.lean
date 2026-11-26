import Problem455PrefixChunks



namespace P455ChartBuild
open P455Quotient P455Witness P455FirstRewrite P455Prefix P455WordChart
open P455SingletonEvaluation P455ChartSchedule P455Schedule P455SlotSaturation Problem455.Slots

def Touch (x y a b : Nat) := (x=a ∧ y=b) ∨ (y=a ∧ x=b)

theorem touch_symm {a b c d} (h : Touch a b c d) : Touch c d a b :=
  h.elim (fun p => .inl ⟨p.1.symm,p.2.symm⟩) (fun p => .inr ⟨p.2.symm,p.1.symm⟩)

theorem touch_trans {a b c d e f} (p : Touch a b c d) (q : Touch c d e f) : Touch a b e f := by
  rcases p with ⟨h,k⟩|⟨h,k⟩ <;> rcases q with ⟨l,m⟩|⟨l,m⟩ <;>
    simp_all [Touch]

private theorem quiet {a b x y : Nat} (no : ¬Touch x y a b) :
    select [a,b] [x,y] = select [a,b] [y,x] := by
  by_cases xa : x=a <;> by_cases xb : x=b <;> by_cases ya : y=a <;> by_cases yb : y=b <;>
    simp_all [Touch,select]

theorem read_projection (cs : List Chunk) (s t : Nat → Bool) (a b : Nat)
    (same : ∀ i x y, Chunk.turn i x y∈cs → Touch x.1 y.1 a b → s i=t i) :
    select [a,b] (labels s cs)=select [a,b] (labels t cs) := by
  induction cs with
  | nil => rfl
  | cons q cs ih =>
    have rest := ih (fun i x y m => same i x y (List.mem_cons_of_mem _ m))
    simp only [labels,render,List.flatMap_cons,List.map_append]
    change select [a,b] (((row s q).map Prod.fst) ++ labels s cs) =
      select [a,b] (((row t q).map Prod.fst) ++ labels t cs)
    rw [select_append,select_append,rest]
    apply congrArg (fun w : W => w ++ select [a,b] (labels t cs))
    cases q with
    | fixed => rfl
    | turn i x y =>
      by_cases h : Touch x.1 y.1 a b
      · simp only [row,same i x y List.mem_cons_self h]
      · cases g : s i <;> cases f : t i <;> simp only [row,g,f,Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil] <;>
          first | exact quiet h | exact (quiet h).symm

theorem match_roles {n m : Node} (p : Touch n.owner n.mate m.owner m.mate) : Matches n m.owner m.mate :=
  p.elim Or.inl (fun h => .inr ⟨h.2,h.1⟩)

theorem one_index {r allow u v a b i j x y f g}
    (p : PairInfo r allow u v i x y) (q : PairInfo r allow u v j f g)
    (px : Touch x.1 y.1 a b) (qy : Touch f.1 g.1 a b) : i=j := by
  have hm : Touch (nodes r u i).owner (nodes r u i).mate (nodes r u j).owner (nodes r u j).mate :=
    touch_trans (touch_symm p.roles) (touch_trans px (touch_trans (touch_symm qy) q.roles))
  have eq := P455WordChart.match_unique q.typedU p.typedU (match_roles hm)
  exact (index_node p.typedU).symm.trans ((congrArg (List.idxOf · (book r u)) eq).trans (index_node q.typedU))

noncomputable def initial (r : Nat) (u : W) : Bits := fun i => readBit u (nodes r u i)
def flags (A s : Bits) : Nat → Bool := fun i => s i != A i
noncomputable def chooseWord (r : Nat) (u : W) (cs : List Chunk) (s : Bits) := labels (flags (initial r u) s) cs

theorem initial_word {r u cs} (src : render Orig cs=events u) :
    chooseWord r u cs (initial r u)=u := by
  have base : flags (initial r u) (initial r u)=Orig := funext (fun _ => by simp [flags,Orig])
  rw [chooseWord,base,original_labels src]

def ending (A : Bits) (C : List Nat) : Bits := fun j => if j∈C then !A j else A j

theorem final_word {r u v cs} (dst : render Last cs=events v) :
    chooseWord r u cs (ending (initial r u) (active cs))=v := by
  have eq := renders_equal (t := Last) cs (s := flags (initial r u) (ending (initial r u) (active cs)))
    (fun i m => by cases h : initial r u i <;> simp [flags,ending,m,h,Last])
  exact (congrArg (List.map Prod.fst) eq).trans (final_labels dst)

private theorem transfer_typed {r allow n w t}
    (equal : select [n.owner,n.mate] w = select [n.owner,n.mate] t)
    (ok : Holds r allow noMark w (typedNode n)) : Holds r allow noMark t (typedNode n) := by
  obtain ⟨d,h⟩ := ok.2.2.2; exact ⟨ok.1,ok.2.1,ok.2.2.1,d,equal.symm.trans h⟩

private theorem choice_projection {r allow u v cs i x y} (info : AllInfo r allow u v cs)
    (src : render Orig cs=events u) (dst : render Last cs=events v)
    (use : Chunk.turn i x y∈cs) (a b : Nat) (touch : Touch x.1 y.1 a b) (s : Bits) :
    let w := chooseWord r u cs s
    if flags (initial r u) s i then select [a,b] w=select [a,b] v else select [a,b] w=select [a,b] u := by
  let f := flags (initial r u) s
  have fixed (j x' y') (m : Chunk.turn j x' y'∈cs) (h : Touch x'.1 y'.1 a b) : i=j :=
    one_index (info i x y use) (info j x' y' m) touch h
  cases bit : flags (initial r u) s i with
  | false =>
    simp only [Bool.false_eq_true,if_false]
    exact (read_projection cs f Orig a b (fun j _ _ m h => (fixed j _ _ m h) ▸ bit)).trans (congrArg _ (original_labels src))
  | true =>
    simp only [if_true]
    exact (read_projection cs f Last a b (fun j _ _ m h => (fixed j _ _ m h) ▸ bit)).trans (congrArg _ (final_labels dst))

theorem mixed_typed {r allow u v cs} (info : AllInfo r allow u v cs)
    (src : render Orig cs=events u) (dst : render Last cs=events v)
    (s : Bits) (i : Nat) (m : i∈active cs) :
    Holds r allow noMark (chooseWord r u cs s) (typedNode (nodes r u i)) := by
  obtain ⟨x,y,part⟩ := mem_active.mp m
  have h := info i x y part
  have p := choice_projection info src dst part _ _ h.roles s
  split at p
  · exact transfer_typed p.symm h.typedV
  · exact transfer_typed p.symm h.typedU

theorem mixed_read {r allow u v cs} (info : AllInfo r allow u v cs)
    (src : render Orig cs=events u) (dst : render Last cs=events v) (s : Bits)
    (off : Off (active cs) (initial r u) s) :
    Read s (nodes r u) r allow (chooseWord r u cs s) := by
  classical
  intro j typed
  let n := nodes r u j
  let w := chooseWord r u cs s
  change select [n.owner,n.mate] w = profile n.owner n.mate n.tag (s j)
  by_cases existsPart : ∃ i x y, Chunk.turn i x y∈cs ∧ Touch x.1 y.1 n.owner n.mate
  · obtain ⟨i,x,y,m,t⟩ := existsPart
    have h := info i x y m
    have matched : Matches (nodes r u i) n.owner n.mate := match_roles (touch_trans (touch_symm h.roles) t)
    have eq := choice_projection info src dst m n.owner n.mate t s
    have index {z : W} (source : Holds r allow noMark z (typedNode (nodes r u i)))
        (nOK : Holds r allow noMark z (typedNode n)) : i=j := by
      have identical := P455WordChart.match_unique nOK source matched
      exact (index_node source).symm.trans ((congrArg (List.idxOf · (book r u)) identical).trans (index_node typed))
    cases flag : flags (initial r u) s i with
    | false =>
      simp only [flag,Bool.false_eq_true,if_false] at eq
      have nOK := transfer_typed eq typed
      have ij := index h.typedU nOK
      subst i
      have bit : s j=initial r u j := by simpa [flags] using flag
      exact eq.trans (by rw [bit]; exact actual_read nOK)
    | true =>
      simp only [flag,if_true] at eq
      have nOK := transfer_typed eq typed
      have ij := index h.typedV nOK
      subst i
      have bit : s j= !initial r u j := by
        cases x : s j <;> cases y : initial r u j <;> simp_all [flags]
      have bitV : readBit v n=s j := h.bits.trans bit.symm
      exact eq.trans (by rw [← bitV]; exact actual_read nOK)
  · have no : j∉active cs := by
      intro jmem; obtain ⟨x,y,m⟩ := mem_active.mp jmem
      exact existsPart ⟨j,x,y,m,(info j x y m).roles⟩
    have eq : select [n.owner,n.mate] w=select [n.owner,n.mate] u := by
      exact (read_projection cs (flags (initial r u) s) Orig n.owner n.mate (fun i x y m t => (existsPart ⟨i,x,y,m,t⟩).elim)).trans (congrArg _ (original_labels src))
    have nOK := transfer_typed eq typed
    exact eq.trans (by rw [off j no]; exact actual_read nOK)

end P455ChartBuild
