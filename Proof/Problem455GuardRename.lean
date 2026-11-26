import Problem455DefectRename
import Problem455OtherProjection
import Problem455GuardProduct




namespace P455GuardRename
open P455Witness P455Paths P455ContactLift P455SourceFamilies P455DefectRename
open P455ContactReflection P455PortReflection Problem455.Slots Problem455Swap

private theorem bigram_map (d : Nat → Nat) (inj : Injects d) (a b : Nat) (w : W) :
    bigram (d a) (d b) (w.map d) = bigram a b w := by
  induction w with
  | nil => rfl
  | cons c t ih =>
    cases t with
    | nil => simp [bigram,hit]
    | cons z t =>
      change hit _ _ (some (d c)) (some (d z)) + _ = hit _ _ (some c) (some z) + _
      have ca : d c = d a ↔ c = a := ⟨fun e => inj e,congrArg d⟩
      have zb : d z = d b ↔ z = b := ⟨fun e => inj e,congrArg d⟩
      simp only [hit,Option.some.injEq,ca,zb,← ih,List.map_cons]

private theorem link_names {r a b : Nat} {w : W} (hr : 0 < r) (edge : Link r w a b) :
    a ∈ w ∧ b ∈ w := by
  have l := out_bound a b (b+1) (by omega) w
  have r' := in_bound a (a+1) b (by omega) w
  have tail := tail_occ_le b w
  unfold Link at edge
  rw [Problem455BlockBridge.occ_count] at l tail
  rw [Problem455BlockBridge.occ_count] at r'
  rw [Problem455BlockBridge.occ_count] at tail
  exact ⟨List.count_pos_iff.mp (by omega), List.count_pos_iff.mp (by omega)⟩

/-- A renamed walk may be presented with arbitrary intermediate Nat labels.
Positivity forces each intermediate endpoint of each literal link to occur
in the mapped word, hence to have a preimage. -/
theorem sameBlock_reflect {r : Nat} (hr : 0 < r) (d : Nat → Nat) (inj : Injects d)
    (w : W) (a b : Nat) (same : SameBlock r (w.map d) (d a) (d b)) : SameBlock r w a b := by
  obtain ⟨ac,bc,path⟩ := same
  simp only [Problem455BlockBridge.occ_count,count_rename d inj] at ac bc
  refine ⟨Problem455BlockBridge.occ_count .. |>.trans ac,Problem455BlockBridge.occ_count .. |>.trans bc,?_⟩
  have lift (j) (p : Joined (Link r (w.map d)) (d a) j) :
      ∀ b', j = d b' → Joined (Link r w) a b' := by
    induction p with
    | refl => intro b' e; have ab := inj e; exact ab ▸ Joined.refl _
    | @extend y z prev last ih =>
      intro b' eq; subst z
      have mem : y ∈ w.map d := last.elim (fun xy => (link_names hr xy).1) (fun yx => (link_names hr yx).2)
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp mem
      apply Joined.extend (ih c rfl)
      simpa only [Link,bigram_map d inj] using last
  exact lift _ path b rfl

theorem rename_separate {r : Nat} (hr : 0 < r) (d : Nat → Nat) (inj : Injects d)
    (w : W) (a b : Nat) (sep : ¬ SameBlock r w a b) : ¬ SameBlock r (w.map d) (d a) (d b) :=
  fun same => sep (sameBlock_reflect hr d inj w a b same)

private theorem rename_slot_atom {r allow src dst w o i a} (d : Nat → Nat) (inj : Injects d)
    (h : Holds r allow src w (.slot o i a)) : Holds r allow dst (w.map d) (.slot (d o) i (d a)) := by
  obtain ⟨idx,j,seen⟩ := h
  exact ⟨idx,j,rename_sees d inj seen⟩

theorem rename_terminal {r allow src dst w o i} (hr : 0 < r) (d : Nat → Nat) (inj : Injects d)
    (kind : SlotDefect) (h : Holds r allow src w (terminalSlot r o i kind)) :
    Holds r allow dst (w.map d) (terminalSlot r (d o) i (sendDefect d kind)) := by
  cases kind with
  | deficient a =>
    exact ⟨rename_slot_atom d inj h.1,by simpa only [Holds,count_rename d inj] using h.2⟩
  | overflow xs =>
    have old := (P455TerminalTransfer.block_separation _).mp h.2.1
    have mapped : ((o :: xs).map d).Pairwise (fun a b => ¬ SameBlock r (w.map d) a b) :=
      old.map d (fun a b sep => rename_separate hr d inj w a b sep)
    refine ⟨by simpa using h.1,(P455TerminalTransfer.block_separation _).mpr mapped,?_,True.intro⟩
    apply (allQ_iff _).mpr
    intro q mem
    obtain ⟨b,inList,rfl⟩ := List.mem_map.mp mem
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp inList
    have orig : Holds r allow src w (.both (.count a r) (.slot o i a)) :=
      ((allQ_iff _).mp h.2.2.1) _ (List.mem_map_of_mem ha)
    exact ⟨(count_rename d inj w a).trans orig.1,rename_slot_atom d inj orig.2⟩

theorem rename_slot {r allow src w} (d : Nat → Nat) (inj : Injects d) (s : SlotCertificate)
    (h : Holds r allow src w (s.query r)) :
    Holds r allow (markNode (sendSlot d s).anchor) (w.map d) ((sendSlot d s).query r) := by
  have length : s.anchor.tag.length + 16 = r := h.1.2.1
  obtain ⟨len,walk,term⟩ := slot_route s h
  have start' : picked (sendSlot d s) = d (picked s) := by
    cases side : s.startAtMate <;> simp [sendSlot,picked,sendNode,side]
  refine ⟨rename_marked d inj s.anchor s.bit h.1,by simpa [sendSlot,relabel] using len,?_,True.intro⟩
  apply (route_iff ..).mpr
  change Walk _ _ _ _ (picked (sendSlot d s)) (relabel d s.steps) ∧ Holds _ _ _ _
    (terminalSlot r (endpoint (picked (sendSlot d s)) (relabel d s.steps)) s.terminalIndex (sendDefect d s.defect))
  rw [start',endpoint_relabel]
  exact ⟨rename_walk d inj _ _ walk, rename_terminal (by omega) d inj _ term⟩

private theorem rename_early {r allow src dst w} (d : Nat → Nat) (inj : Injects d) (xs ys : W)
    (h : Holds r allow src w (earlyBefore xs ys)) :
    Holds r allow dst (w.map d) (earlyBefore (xs.map d) (ys.map d)) := by
  apply (earlyBefore_iff _ _).mpr
  rintro x hx y hy
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  exact rename_order d inj [(a,2),(b,0)] ((earlyBefore_iff _ _).mp h a ha b hb)

theorem rename_port {r allow src dst w} (d : Nat → Nat) (inj : Injects d)
    (phase : Nat) (a b : Node) (port : Holds r allow src w (orientedPort phase a b)) :
    Holds r allow dst (w.map d) (orientedPort phase (sendNode d a) (sendNode d b)) := by
  refine ⟨rename_record d inj port.1,rename_record d inj port.2.1,?_,?_,True.intro⟩
  · rcases port.2.2.1 with f | rev
    · exact Or.inl (rename_early d inj (roles a) (roles b) f)
    · exact Or.inr (rename_early d inj (roles b) (roles a) rev)
  · let i := 3+2*phase
    exact rename_order d inj [(a.owner,i),(a.mate,i),(b.owner,i),(b.mate,i),
      (a.owner,i+1),(a.mate,i+1),(b.owner,i+1),(b.mate,i+1)] port.2.2.2.1

private theorem rename_rightward {r allow src dst w} (d : Nat → Nat) (inj : Injects d)
    (ts : Tiles) (a b : Node) (h : Holds r allow src w (rightward ts a b)) :
    Holds r allow dst (w.map d) (rightward ts (sendNode d a) (sendNode d b)) :=
  ⟨h.1,rename_port d inj _ a b h.2.1,rename_order d inj [(a.owner,13+a.tag.length),
    (b.owner,13+a.tag.length)] h.2.2.1,True.intro⟩

private theorem rename_downward {r allow src dst w} (d : Nat → Nat) (inj : Injects d)
    (ts : Tiles) (a b : Node) (h : Holds r allow src w (downward ts a b)) :
    Holds r allow dst (w.map d) (downward ts (sendNode d a) (sendNode d b)) :=
  ⟨h.1,rename_port d inj _ a b h.2⟩

theorem rename_neighbor {r allow src dst w} (d : Nat → Nat) (inj : Injects d)
    (ts : Tiles) (a b : Node) (dir : Dir) (h : Holds r allow src w (neighbor ts a b dir)) :
    Holds r allow dst (w.map d) (neighbor ts (sendNode d a) (sendNode d b) dir) := by
  cases dir <;> first | exact rename_rightward d inj _ _ _ h | exact rename_downward d inj _ _ _ h

theorem rename_func {r allow src w} (d : Nat → Nat) (inj : Injects d) (ts : Tiles)
    (f : FunctionalityCertificate) (h : Holds r allow src w (f.query ts)) :
    Holds r allow (markNode (sendFunc d f).anchor) (w.map d) ((sendFunc d f).query ts) := by
  have length : f.anchor.tag.length + 16 = r := h.1.2.1
  refine ⟨rename_marked d inj f.anchor f.bit h.1,rename_neighbor d inj ts f.anchor f.b f.dir h.2.1,
    rename_neighbor d inj ts f.anchor f.c f.dir h.2.2.1,?_,True.intro⟩
  cases e : f.distinguishMate <;> simpa [sendFunc,sendNode,e,Holds] using
    rename_separate (by omega) d inj w _ _ h.2.2.2.1

/-- Use keep.idxOf only on the projected literal alphabet. The total
injective extension may send unused names outside the bounded alphabet. -/
theorem canonical_slot {r allow src u} (keep : W) (s : SlotCertificate)
    (ho : s.anchor.owner ∈ keep) (hm : s.anchor.mate ∈ keep)
    (h : Holds r allow src (select keep u) (s.query r)) :
    ∃ s' : SlotCertificate, s'.anchor.owner = keep.idxOf s.anchor.owner ∧
      s'.anchor.mate = keep.idxOf s.anchor.mate ∧ s'.bit = s.bit ∧
      s'.defect = sendDefect (extend keep) s.defect ∧ Holds r allow (markNode s'.anchor)
      ((select keep u).map keep.idxOf) (s'.query r) := by
  let d := extend keep
  have eq := extend_map (keep := keep) (w := select keep u) (fun _ m => kept m)
  exact ⟨sendSlot d s,by simp [sendSlot,sendNode,d,extend,ho],by simp [sendSlot,sendNode,d,extend,hm],
    rfl,rfl, by simpa only [← eq,d] using rename_slot d (extend_inj keep) s h⟩

theorem canonical_func {r allow src u} (keep : W) (ts : Tiles) (f : FunctionalityCertificate)
    (ho : f.anchor.owner ∈ keep) (hm : f.anchor.mate ∈ keep)
    (h : Holds r allow src (select keep u) (f.query ts)) :
    ∃ f' : FunctionalityCertificate, f'.anchor.owner = keep.idxOf f.anchor.owner ∧
      f'.anchor.mate = keep.idxOf f.anchor.mate ∧ f'.bit = f.bit ∧ Holds r allow (markNode f'.anchor)
      ((select keep u).map keep.idxOf) (f'.query ts) := by
  let d := extend keep
  have eq := extend_map (keep := keep) (w := select keep u) (fun _ m => kept m)
  exact ⟨sendFunc d f,by simp [sendFunc,sendNode,d,extend,ho],by simp [sendFunc,sendNode,d,extend,hm],
    rfl, by simpa only [← eq,d] using rename_func d (extend_inj keep) ts f h⟩

private theorem cap_idx {r : Nat} {u keep : W} (h : P455Closure.Cap r (select keep u)) :
    P455Closure.Cap r ((select keep u).map keep.idxOf) := by
  rw [← extend_map (keep := keep) (w := select keep u) (fun _ m => kept m)]
  exact cap_rename _ (extend_inj keep) h

/-- The actual bounded one-mark guard sent to the finite product. The
projected word, marked roles and bound are recovered from the original
certificate for each of the deficient, overflow and duplicate-port cases. -/
theorem bounded_guard {r allow u} (cap : P455Closure.Cap r u) (ts : Tiles)
    (orig : P455GuardProduct.Guard)
    (ok : Holds r allow (markNode orig.anchor) u (orig.query r ts)) :
    ∃ (keep : W) (g : P455GuardProduct.Guard),
      keep.length ≤ P455GuardProduct.width orig.isFunc ∧ orig.anchor.owner ∈ keep ∧
      orig.anchor.mate ∈ keep ∧ g.isFunc = orig.isFunc ∧
      g.anchor.owner = keep.idxOf orig.anchor.owner ∧ g.anchor.mate = keep.idxOf orig.anchor.mate ∧
      P455Closure.Cap r ((select keep u).map keep.idxOf) ∧
      Holds r allow (markNode g.anchor) ((select keep u).map keep.idxOf) (g.query r ts) := by
  cases orig with
  | slot s =>
    change Holds r allow (markNode s.anchor) u (s.query r) at ok
    cases kind : s.defect with
    | deficient bad =>
      obtain ⟨len,walk,term⟩ := slot_route s ok
      rw [kind] at term
      obtain ⟨⟨index,inside⟩,defic⟩ := term
      let last := endpoint (picked s) s.steps
      have near : Near r allow (markNode s.anchor) u (picked s) last 6 := ⟨s.steps,walk,rfl,len⟩
      obtain ⟨keep,s',len',ho,hm,xa,yb,_,_,_,cp,test⟩ :=
        canonical_defect cap s.anchor s.bit s.startAtMate last s.terminalIndex bad ok.1 near index inside defic
      exact ⟨keep,.slot s',Nat.le_trans len' (by decide : 9 ≤ 43),ho,hm,rfl,xa,yb,cp,test⟩
    | overflow xs =>
      have length : s.anchor.tag.length + 16 = r := ok.1.2.1
      obtain ⟨keep,len,ho,hm,_,cp,projected⟩ :=
        P455OtherProjection.bounded_overflow (by omega) cap s xs kind ok
      obtain ⟨s',xa,yb,_,_,test⟩ := canonical_slot keep s ho hm projected
      exact ⟨keep,.slot s',len,ho,hm,rfl,xa,yb,cap_idx cp,test⟩
  | func f =>
    change Holds r allow (markNode f.anchor) u (f.query ts) at ok
    have length : f.anchor.tag.length + 16 = r := ok.1.2.1
    obtain ⟨keep,len,mem,cp,projected⟩ :=
      P455OtherProjection.bounded_functionality (by omega) cap ts f ok
    have ho := mem f.anchor.owner (by simp [roles])
    have hm := mem f.anchor.mate (by simp [roles])
    obtain ⟨f',xa,yb,_,test⟩ := canonical_func keep ts f ho hm projected
    exact ⟨keep,.func f',len,ho,hm,rfl,xa,yb,cap_idx cp,test⟩

end P455GuardRename
