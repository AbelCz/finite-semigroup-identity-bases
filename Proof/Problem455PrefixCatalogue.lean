import Problem455PrefixIsolation
import Problem455ChangedEvents
import Problem455ChartSchedule



namespace P455ChartBuild
open P455Quotient P455Witness P455FirstRewrite P455Prefix P455WordChart P455Uncrossed
open Problem455.Slots P455SlotSaturation
abbrev W := List Nat

def book (r : Nat) (u : W) : List Node :=
  u.flatMap (fun a => u.flatMap (fun b => (Problem455Finite.wordsUpTo [false,true] r).map (fun t => ⟨a,b,t⟩)))

theorem listed {r allow u n} (typed : Holds r allow noMark u (typedNode n)) : n∈book r u := by
  obtain ⟨_,len,_,bit,eq⟩ := typed
  have mem (c : Nat) (hc : c∈profile n.owner n.mate n.tag bit) : c∈u :=
    (List.mem_filter.mp (eq ▸ hc : c∈select [n.owner,n.mate] u)).1
  obtain ⟨a,b,t⟩ := n
  refine List.mem_flatMap.mpr ⟨a,mem _ (by simp [profile,profilePrefix]),List.mem_flatMap.mpr
    ⟨b,mem _ (by simp [profile,profilePrefix]),List.mem_map.mpr ⟨t,?_,rfl⟩⟩⟩
  apply Problem455Finite.covered
  · dsimp at len; omega
  · intro x _; cases x <;> simp

private theorem index_unique {α : Type} [DecidableEq α] (t : List α) {a b : α}
    (ma : a∈t) (mb : b∈t) (h : t.idxOf a=t.idxOf b) : a=b := by
  induction t with
  | nil => contradiction
  | cons c t ih =>
    by_cases ca : c=a <;> by_cases cb : c=b
    · exact ca.symm.trans cb
    · subst c; simp [List.idxOf_cons,cond_eq_if,beq_iff_eq,cb,Ne.symm cb] at h
    · subst c; simp [List.idxOf_cons,cond_eq_if,beq_iff_eq,ca,Ne.symm ca] at h
    · exact ih ((List.mem_cons.mp ma).resolve_left (Ne.symm ca))
        ((List.mem_cons.mp mb).resolve_left (Ne.symm cb))
        (by simpa [List.idxOf_cons,cond_eq_if,beq_iff_eq,ca,cb,Ne.symm] using h)

noncomputable def nodes (r : Nat) (u : W) (i : Nat) : Node := by
  classical
  exact if h : ∃ n ∈ book r u, (book r u).idxOf n=i then h.choose else ⟨0,0,[]⟩

theorem node_index {r u n} (m : n∈book r u) : nodes r u ((book r u).idxOf n) = n := by
  classical
  have h : ∃ y∈book r u, (book r u).idxOf y=(book r u).idxOf n := ⟨n,m,rfl⟩
  simp only [nodes,dif_pos h]
  exact index_unique _ h.choose_spec.1 m h.choose_spec.2

theorem index_node {r allow u v i} (ok : Holds r allow noMark v (typedNode (nodes r u i))) :
    (book r u).idxOf (nodes r u i)=i := by
  classical
  by_cases h : ∃ n∈book r u, (book r u).idxOf n=i
  · simpa only [nodes,dif_pos h] using h.choose_spec.2
  · have bad := ok.1
    simp [nodes,h] at bad

def readBit (w : W) (n : Node) : Bool :=
  decide (select [n.owner,n.mate] w=profile n.owner n.mate n.tag true)

theorem read_actual {w n bit} (ne : n.owner≠n.mate)
    (h : select [n.owner,n.mate] w = profile n.owner n.mate n.tag bit) : readBit w n=bit := by
  cases bit <;> simp_all [readBit,profile,pair]

theorem actual_read {r allow w n} (typed : Holds r allow noMark w (typedNode n)) :
    select [n.owner,n.mate] w = profile n.owner n.mate n.tag (readBit w n) := by
  obtain ⟨b,h⟩ := typed.2.2.2; rw [read_actual typed.1 h,h]

structure PairInfo (r : Nat) (allow : Tag → Prop) (u v : W) (i : Nat) (x y : Event) : Prop where
  roles : (x.1=(nodes r u i).owner ∧ y.1=(nodes r u i).mate) ∨
    (y.1=(nodes r u i).owner ∧ x.1=(nodes r u i).mate)
  typedU : Holds r allow noMark u (typedNode (nodes r u i))
  typedV : Holds r allow noMark v (typedNode (nodes r u i))
  bits : readBit v (nodes r u i) = !readBit u (nodes r u i)
  mutable : x.2=r-2 ∧ y.2=r-2

theorem label_pair {r allow ts u v} (cap : Cap r u) (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (x y : Event) (hx : P455ChangedEvents.Mates u v r x y) : ∃ i, PairInfo r allow u v i x y := by
  have ne : x.1≠y.1 := by
    rintro e
    apply hx.1
    have one (a : Nat) (w : W) : select [a,a] w = List.replicate (w.count a) a := by
      induction w with
      | nil => rfl
      | cons b t ih => by_cases f : b=a <;> simp_all [select,List.count_cons,List.replicate_succ,Ne.symm]
    rw [e,one,one,P455CellClassBinary.exact_counts cap valid]
  obtain ⟨a,b,tag,bit,ord,len,ok,ua,va⟩ := P455CellClassBinary.changed cap valid ne hx.1
  let n : Node := ⟨a,b,tag⟩
  have ab : a≠b := by rcases ord with ⟨p,q⟩|⟨p,q⟩ <;> rw [p,q] <;> first | exact ne | exact Ne.symm ne
  have pairs (w : W) : select [a,b] w = select [x.1,y.1] w := by
    rcases ord with ⟨p,q⟩|⟨p,q⟩ <;> rw [p,q]; exact select_swap _ _ _
  have U := (pairs u).trans ua
  have V := (pairs v).trans va
  have tU : Holds r allow noMark u (typedNode n) := ⟨ab,len,ok,bit,U⟩
  have tV : Holds r allow noMark v (typedNode n) := ⟨ab,len,ok,!bit,V⟩
  let i := (book r u).idxOf n
  have idx : nodes r u i = n := node_index (listed tU)
  refine ⟨i,?_⟩
  constructor
  · rw [idx]; exact ord.elim (fun h => .inl ⟨h.1.symm,h.2.symm⟩) (fun h => .inr ⟨h.1.symm,h.2.symm⟩)
  · rwa [idx]
  · rwa [idx]
  · rw [idx,read_actual (n:=n) ab U,read_actual (n:=n) ab V]
  · exact hx.2

end P455ChartBuild
