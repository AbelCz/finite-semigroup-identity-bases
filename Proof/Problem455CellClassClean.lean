import Problem455CellClassSnake





namespace P455CellClassClean
open P455RectangleRank P455CellClass P455CellClassFrames P455CellClassSnake
open P455Witness P455GridRows P455PortReflection P455SlotSaturation P455SingletonEvaluation
open P455CrossedSupport P455Paths P455TerminalTransfer P455ConstantLayout Problem455.Slots
abbrev W := List Nat

def SmallSlots (U : W) := ∀ o ∈ U, ∀ k, slotStart k → ∃ S : W,
  S.length ≤ 4 ∧ ∀ x, occupies U o k x → x ∈ S

def Ports (r : Nat) (allow : Tag → Prop) (ts : Tiles) (U : W) :=
  ∀ n : Node, Holds r allow noMark U (typedNode n) → Functional r allow noMark U ts n

theorem packed_counts {r allow t m z} (p : Phases r allow t m z)
    (names : ∀ x ∈ m++z,x<2*t) (bits : Nat → Bool) (a : Nat) (mem : a ∈ word t m z bits) :
    (word t m z bits).count a=r := by
  have small := word_names _ names _ mem
  obtain ⟨_,co,cm,_⟩ := flip_counts (cap_word p.capped bits)
    (closedAt p bits (show a/2<t by omega))
  have which : a=owner (a/2) ∨ a=mate (a/2) := by unfold owner mate; omega
  rcases which with eq|eq <;> first | exact eq ▸ co | exact eq ▸ cm




theorem record_roles {r allow mark t m z} (bits : Nat → Bool)
    (names : ∀ x ∈ m++z,x<2*t) (finalPair : ∀ i<t,select [owner i,mate i] z=[owner i,mate i])
    (n : Node) (obs : Holds r allow mark (word t m z bits) (typedNode n)) :
    ∃ i<t,n.owner=owner i ∧ n.mate=mate i := by
  let w := word t m z bits
  obtain ⟨ne,len,tag,bit,pr⟩ := obs
  have mem : n.owner ∈ select [n.owner,n.mate] w := by
    dsimp only [w]; rw [pr]; simp [profile,profilePrefix]
  have lt := word_names bits names n.owner (List.mem_filter.mp mem).1
  let i := n.owner/2
  have ix : i<t := by dsimp [i]; omega
  have own : n.owner=owner i ∨ n.owner=mate i := by unfold owner mate i; omega
  have mat : n.mate=owner i ∨ n.mate=mate i := by
    apply Classical.byContradiction; intro bad
    have forb := P455Structural.no_external_record (r:=r) (allow:=allow) (private_closed ix m z bits) own
      ⟨fun e => bad (Or.inl e),fun e => bad (Or.inr e)⟩
    exact forb (.inl ⟨n.tag,ne,len,tag,bit,pr⟩)
  rcases own with one|one <;> rcases mat with two|two
  · exact False.elim (ne (one.trans two.symm))
  · exact ⟨i,ix,one,two⟩
  · rw [one,two,select_pair_symm (owner i) (mate i)] at pr
    have last := congrArg List.getLast? pr
    simp [word,select_append,finalPair i ix,profile,List.getLast?_append] at last
    unfold owner mate at last; omega
  · exact False.elim (ne (one.trans two.symm))

theorem all_bits {r allow mark t m z} (c value : Bool)
    (names : ∀ x ∈ m++z,x<2*t) (finalPair : ∀ i<t,select [owner i,mate i] z=[owner i,mate i])
    (n : Node) (obs : Holds r allow mark (word t m z (constant c)) (markedNode n value)) : value=c := by
  obtain ⟨i,ix,o,a⟩ := record_roles (mark:=mark) (constant c) names finalPair n
    ⟨obs.1,obs.2.1,obs.2.2.1,value,obs.2.2.2.2⟩
  have pr := obs.2.2.2.2
  rw [o,a] at pr
  have known := read_bit ix m z (constant c) (finalPair i ix) n.tag ⟨value,pr⟩
  have eq := pr.symm.trans known
  have ne : owner i ≠ mate i := by simp [owner,mate]
  cases value <;> cases c <;> simp_all [constant,profile,pair]

private theorem slot_false {r allow mark t m z} (p : Phases r allow t m z)
    (names : ∀ x ∈ m++z,x<2*t) (size : SmallSlots (word t m z (constant false)))
    (s : SlotCertificate) (b : Bool)
    (obs : Holds r allow mark (word t m z (constant b)) (s.query r)) : False := by
  obtain ⟨_,_,term⟩ := slot_route s obs
  let w := word t m z (constant b)
  let zero := word t m z (constant false)
  let o := endpoint (if s.startAtMate then s.anchor.mate else s.anchor.owner) s.steps
  change Holds r allow mark w (terminalSlot r o s.terminalIndex s.defect) at term
  let q := terminalSlot r o s.terminalIndex s.defect
  have atW : Holds r allow noMark w q := remark (P455GuardProduct.free_term ..) term
  have walk := chain_walk p.capped (chain p (constant b))
  have back : P455Quotient.Walk (P455Closure.Move r allow noMark) w zero :=
    walk.symm (fun mv => mv.symm)
  have atZ := back.transport atW (fun mv h => (query_invariant mv _).mp h)
  change Holds r allow noMark zero (terminalSlot r o s.terminalIndex s.defect) at atZ
  cases d : s.defect with
  | deficient a =>
    rw [d] at atZ
    obtain ⟨⟨_,j,events⟩,under⟩ := atZ
    have mem := stamped_mem_label _ _ (a,j) (events.subset (by simp))
    have ct := packed_counts p names (constant false) a mem
    change zero.count a < r at under
    change zero.count a = r at ct
    omega
  | overflow xs =>
    rw [d] at atZ
    obtain ⟨count,sep,all,_⟩ := atZ
    change xs.length=5 at count
    have occupied (a : Nat) (h : a ∈ xs) :
        slotStart s.terminalIndex ∧ occupies zero o s.terminalIndex a := by
      have qh := (P455TerminalTransfer.holds_all _).mp all
        (.both (.count a r) (.slot o s.terminalIndex a)) (by simp [h])
      exact qh.2
    have someA : ∃ a, a ∈ xs := by cases xs with
                                    | nil => simp at count
                                    | cons a ys => exact ⟨a,List.mem_cons_self⟩
    obtain ⟨a,ha⟩ := someA
    obtain ⟨slot,j,ev⟩ := occupied a ha
    have ownMem := stamped_mem_label _ _ (o,s.terminalIndex) (ev.subset (by simp))
    obtain ⟨S,low,cover⟩ := size o ownMem s.terminalIndex slot
    have apart := (block_separation _).mp sep
    have nd : xs.Nodup := by
      apply (List.pairwise_cons.mp apart).2.imp_of_mem
      intro a b ha _ sep same
      subst b
      have req := (P455TerminalTransfer.holds_all _).mp all (.both (.count a r) (.slot o s.terminalIndex a))
        (List.mem_map.mpr ⟨a,ha,rfl⟩)
      have ca : Problem455Swap.occ a zero = r := (Problem455BlockBridge.occ_count ..).trans req.1
      exact sep ⟨ca,ca,.refl _⟩
    have le := P455FirstRewrite.size_le nd (fun x hx => cover _ (occupied _ hx).2)
    omega

theorem clean {r allow ts t m z} (p : Phases r allow t m z)
    (names : ∀ x ∈ m++z,x<2*t) (finalPair : ∀ i<t,select [owner i,mate i] z=[owner i,mate i])
    (small : SmallSlots (word t m z (constant false))) (ports : Ports r allow ts (word t m z (constant false)))
    (bit : Bool) (x y : Nat) : ¬ Violation r allow ts (word t m z (constant bit)) x y := by
  rintro ⟨c,_,_,read⟩
  cases c with
  | slot s => exact slot_false p names small s bit read
  | functionality f =>
    obtain ⟨marked,nb,nc,different,_⟩ := read
    have atB := neighbor_remark (dst := noMark) nb
    have atC := neighbor_remark (dst := noMark) nc
    have rec : Holds r allow noMark (word t m z (constant bit)) (typedNode f.anchor) :=
      ⟨marked.1,marked.2.1,marked.2.2.1,f.bit,marked.2.2.2.2⟩
    have walk := (chain_walk p.capped (chain p (constant bit))).symm (fun mv => mv.symm)
    have back (q : Query) (h : Holds r allow noMark (word t m z (constant bit)) q) :
        Holds r allow noMark (word t m z (constant false)) q :=
      walk.transport h (fun mv old => (query_invariant mv _).mp old)
    have eq := ports f.anchor (back _ rec) f.dir f.b f.c (back _ atB) (back _ atC)
    change ¬ Problem455Swap.SameBlock r _ _ _ at different
    rw [eq] at different
    obtain ⟨ca,cb⟩ := record_counts (cap_word p.capped (constant bit)) (neighbor_target_record atC)
    have occ : Problem455Swap.occ (if f.distinguishMate then f.c.mate else f.c.owner)
        (word t m z (constant bit)) = r := by
      rw [Problem455BlockBridge.occ_count]
      cases b : f.distinguishMate <;> simp only [b,Bool.false_eq_true,if_false,if_true] <;> assumption
    exact different ⟨occ,occ,.refl _⟩
  | edge e =>
    have yes := all_bits bit true names finalPair e.a read.1
    have no := all_bits bit false names finalPair e.b read.2.1
    cases bit <;> contradiction

/-- Remaining word data are only positive geometry and literal bounds
    on the zero word. No identity, negative tester assertion, mixed-word
    evidence, layout, or normal-form hypothesis is included. -/
structure Data (r : Nat) (allow : Tag → Prop) (ts : Tiles) (t : Nat) (m z : W) where
  phases : Phases r allow t m z
  names : ∀ x ∈ m++z,x<2*t
  finalPair : ∀ i<t,select [owner i,mate i] z=[owner i,mate i]
  small : SmallSlots (word t m z (constant false))
  ports : Ports r allow ts (word t m z (constant false))
  next : ∀ i, i+1<t → At r allow ts (word t m z (constant false)) i (i+1)
  wrap : 0<t → At r allow ts (word t m z (constant false)) (t-1) 0

def Data.geometry {r allow ts t m z} (d : Data r allow ts t m z) : Geometry r allow ts t m z :=
  ⟨d.phases,d.names,d.finalPair,fun bit i _ => clean d.phases d.names d.finalPair d.small d.ports bit
    (owner i) (mate i),d.next,d.wrap⟩

theorem no_basis {r allow ts} (hr : 0<r)
    (padding : ∀ k : Nat, ∃ (t : Nat) (m z : W), k<2*t ∧ Nonempty (Data r allow ts t m z))
    (basis : List (W × W)) (sound : ∀ u v, (u,v) ∈ basis → (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ U V, U ≠ [] ∧ V ≠ [] ∧ (P455FullSingleton.model r allow ts).Valid U V ∧
      ¬ P455FirstRewrite.Derives (fun u v => (u,v) ∈ basis) U V := by
  apply P455CellClassSnake.no_basis hr _ basis sound
  intro k; obtain ⟨t,m,z,g,⟨d⟩⟩ := padding k
  exact ⟨t,m,z,g,⟨d.geometry⟩⟩

end P455CellClassClean
