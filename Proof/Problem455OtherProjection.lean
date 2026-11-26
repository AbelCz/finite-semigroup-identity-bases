import Problem455BlockSeparators




namespace P455OtherProjection
open P455Witness P455Paths P455SourceFamilies P455PortReflection P455DefectProjection Problem455.Slots
open Problem455Swap (SameBlock)

def Covers (keep xs : W) := ∀ a ∈ xs, a ∈ keep

private theorem fan {r w} (hr : 0 < r) (cp : P455Closure.Cap r w) (a : Nat) (xs : W)
    (ca : w.count a = r) (sat : ∀ b ∈ xs, w.count b = r)
    (diff : ∀ b ∈ xs, ¬ SameBlock r w a b) :
    ∃ aux : W, aux.length ≤ 2*xs.length ∧ ∀ keep : W, a ∈ keep → Covers keep xs → Covers keep aux →
      ∀ b ∈ xs, ¬ SameBlock r (select keep w) a b := by
  induction xs with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons x xs ih =>
    obtain ⟨c,d,wit⟩ := P455BlockSeparators.robust_separators hr cp ca (sat x (by simp)) (diff x (by simp))
    obtain ⟨more,len,win⟩ := ih (fun b h => sat b (by simp [h])) (fun b h => diff b (by simp [h]))
    refine ⟨c::d::more,by simp; omega,?_⟩
    intro keep ha members extra b hb
    rcases List.mem_cons.mp hb with rfl|hx
    · exact wit keep ha (members _ (by simp)) (extra _ (by simp)) (extra _ (by simp))
    · exact win keep ha (fun j hj => members j (by simp [hj])) (fun j hj => extra j (by simp [hj])) b hx

theorem simultaneous {r w} (hr : 0 < r) (cp : P455Closure.Cap r w) (xs : W)
    (sat : ∀ a ∈ xs, w.count a = r) (diff : xs.Pairwise (fun a b => ¬ SameBlock r w a b)) :
    ∃ aux : W, aux.length ≤ xs.length * (xs.length-1) ∧ ∀ keep : W, Covers keep xs → Covers keep aux →
      xs.Pairwise (fun a b => ¬ SameBlock r (select keep w) a b) := by
  induction xs with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons a xs ih =>
    obtain ⟨ds,pw⟩ := List.pairwise_cons.mp diff
    have st (b) (h : b ∈ xs) := sat b (by simp [h])
    obtain ⟨xs₁,n₁,k₁⟩ := fan hr cp a xs (sat a (by simp)) st ds
    obtain ⟨xs₂,n₂,k₂⟩ := ih st pw
    refine ⟨xs₁ ++ xs₂,?_,?_⟩
    · simp only [List.length_append,List.length_cons,Nat.add_sub_cancel]
      have le := Nat.add_le_add n₁ n₂
      cases n : xs.length with
      | zero => simpa only [n,Nat.mul_zero,Nat.zero_mul] using le
      | succ m =>
        simp [n,Nat.add_mul,Nat.mul_add,Nat.succ_mul,Nat.mul_succ] at *
        omega
    · intro keep mem more
      have keepX (b) (h : b ∈ xs) := mem b (by simp [h])
      exact List.pairwise_cons.mpr ⟨k₁ keep (mem a (by simp)) keepX (fun z h => more z (by simp [h])),
        k₂ keep keepX (fun z h => more z (by simp [h]))⟩

theorem walk_count {r allow mark w} (cap : P455Closure.Cap r w) (a : Nat) (p : List Step)
    (ct : w.count a = r) (walk : Walk r allow mark w a p) : w.count (endpoint a p) = r := by
  induction p generalizing a with
  | nil => exact ct
  | cons bc p ih =>
    obtain ⟨b,c⟩ := bc
    apply ih b _ walk.2
    cases c with
    | record tag rev =>
      cases rev with
      | false => exact (record_counts cap walk.1).2
      | true => exact (record_counts cap walk.1).1
    | port phase rev => exact walk.1.2.2.1

theorem bounded_overflow {r allow u} (hr : 0 < r) (cap : P455Closure.Cap r u) (s : SlotCertificate)
    (xs : W) (kind : s.defect = .overflow xs) (ok : Holds r allow (markNode s.anchor) u (s.query r)) :
    ∃ keep : W, keep.length ≤ 43 ∧ s.anchor.owner ∈ keep ∧ s.anchor.mate ∈ keep ∧
      Covers keep (s.steps.map Prod.fst ++ xs) ∧ P455Closure.Cap r (select keep u) ∧
      Holds r allow (markNode s.anchor) (select keep u) (s.query r) := by
  let a := picked s
  let t := endpoint a s.steps
  obtain ⟨bound,walk,term⟩ := slot_route s ok
  rw [kind] at term
  obtain ⟨len,diff,all,_⟩ := term
  have members (b : Nat) (h : b ∈ xs) :
      u.count b = r ∧ slotStart s.terminalIndex ∧ occupies u t s.terminalIndex b :=
    (allQ_iff _).mp all _ (List.mem_map_of_mem h)
  have ct := record_counts cap (marked_typed (a := s.anchor) (bit := s.bit) ok.1)
  have start : u.count a = r := by
    cases side : s.startAtMate <;> simp [a,picked,side,ct]
  have termCount := walk_count cap a s.steps start walk
  have st : ∀ b ∈ t::xs, u.count b = r := by
    intro b h; rcases List.mem_cons.mp h with rfl|h
    · exact termCount
    · exact (members b h).1
  obtain ⟨more,n,apart⟩ := simultaneous hr cap (t::xs) st ((P455TerminalTransfer.block_separation _).mp diff)
  let keep := s.anchor.owner :: s.anchor.mate :: (s.steps.map Prod.fst ++ xs ++ more)
  have owner : s.anchor.owner ∈ keep := by simp [keep]
  have mate : s.anchor.mate ∈ keep := by simp [keep]
  have used (z) (hz : z ∈ s.steps.map Prod.fst ++ xs) : z ∈ keep :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
  have keptOcc (b) (hb : b ∈ xs) := used b (List.mem_append_right _ hb)
  have path (m : Step) (hm : m ∈ s.steps) : m.1 ∈ keep :=
    used _ (List.mem_append_left _ (List.mem_map_of_mem hm))
  have pickedKept : a ∈ keep := by cases side : s.startAtMate <;> simp [a,picked,side,owner,mate]
  have last := endpoint_kept keep a s.steps pickedKept path
  have allSep := apart keep (by simpa [Covers] using And.intro last keptOcc)
    (fun z h => by simp [keep,h])
  refine ⟨keep,?_,owner,mate,used,select_cap keep cap,select_marked keep _ _ owner mate ok.1,bound,?_,True.intro⟩
  · change xs.length = 5 at len
    simp only [List.length_cons,len] at n
    simp [keep,len]
    omega
  · apply (route_iff ..).mpr
    refine ⟨select_walk keep a s.steps pickedKept path walk,?_⟩
    rw [kind]
    refine ⟨len,(P455TerminalTransfer.block_separation _).mpr allSep,?_,True.intro⟩
    apply (allQ_iff _).mpr
    intro q hq; obtain ⟨b,h,rfl⟩ := List.mem_map.mp hq
    have m := members b h
    exact ⟨(select_count keep u b (keptOcc b h)).trans m.1,m.2.1,select_slot keep t _ b last (keptOcc b h) m.2.2⟩

theorem select_early {r allow mark u} (keep xs ys : W) (hx : Covers keep xs) (hy : Covers keep ys)
    (obs : Holds r allow mark u (earlyBefore xs ys)) : Holds r allow mark (select keep u) (earlyBefore xs ys) := by
  apply (earlyBefore_iff _ _).mpr
  intro a ha b hb
  apply select_order keep _ _ ((earlyBefore_iff _ _).mp obs a ha b hb)
  simp [hx a ha,hy b hb]

theorem select_port {r allow mark u} (keep : W) (a b : Node) (i : Nat)
    (keepA : Covers keep (roles a)) (keepB : Covers keep (roles b))
    (obs : Holds r allow mark u (orientedPort i a b)) : Holds r allow mark (select keep u) (orientedPort i a b) := by
  have ao := keepA a.owner (by simp [roles]); have am := keepA a.mate (by simp [roles])
  have bo := keepB b.owner (by simp [roles]); have bm := keepB b.mate (by simp [roles])
  obtain ⟨ra,rb,early,order,_⟩ := obs
  refine ⟨select_record keep _ _ _ ao am ra,select_record keep _ _ _ bo bm rb,?_,?_,True.intro⟩
  · rcases early with e|e
    · exact .inl (select_early keep _ _ keepA keepB e)
    · exact .inr (select_early keep _ _ keepB keepA e)
  · apply select_order keep _ _ order; simp [ao,am,bo,bm]

theorem select_neighbor {r allow mark u} (keep : W) (ts : Tiles) (a b : Node) (dir : Dir)
    (keepA : Covers keep (roles a)) (keepB : Covers keep (roles b))
    (obs : Holds r allow mark u (neighbor ts a b dir)) :
    Holds r allow mark (select keep u) (neighbor ts a b dir) := by
  have ao := keepA a.owner (by simp [roles]); have bo := keepB b.owner (by simp [roles])
  cases dir with
  | down => exact ⟨obs.1,select_port keep _ _ _ keepA keepB obs.2⟩
  | up => exact ⟨obs.1,select_port keep _ _ _ keepB keepA obs.2⟩
  | right => exact ⟨obs.1,select_port keep _ _ _ keepA keepB obs.2.1,
      select_order keep _ (by simp [ao,bo]) obs.2.2.1,True.intro⟩
  | left => exact ⟨obs.1,select_port keep _ _ _ keepB keepA obs.2.1,
      select_order keep _ (by simp [ao,bo]) obs.2.2.1,True.intro⟩

theorem bounded_functionality {r allow u} (hr : 0 < r) (cap : P455Closure.Cap r u)
    (ts : Tiles) (f : FunctionalityCertificate)
    (ok : Holds r allow (markNode f.anchor) u (f.query ts)) :
    ∃ keep : W, keep.length ≤ 8 ∧ Covers keep (roles f.anchor ++ roles f.b ++ roles f.c) ∧
      P455Closure.Cap r (select keep u) ∧ Holds r allow (markNode f.anchor) (select keep u) (f.query ts) := by
  obtain ⟨anchor,nb,nc,apart,_⟩ := ok
  let role := roleOf f.distinguishMate
  have sat (n : Node) (obs : Holds r allow (markNode f.anchor) u (neighbor ts f.anchor n f.dir)) :
      u.count (role n) = r := by
    have ct := record_counts cap (neighbor_target_record obs)
    cases side : f.distinguishMate <;> simp [role,roleOf,side,ct]
  obtain ⟨x,y,diff⟩ := P455BlockSeparators.robust_separators hr cap (sat _ nb) (sat _ nc) apart
  let names := roles f.anchor ++ roles f.b ++ roles f.c
  let keep := x::y::names
  have k : Covers keep names := fun z hz => by simp [keep,hz]
  have ka : Covers keep (roles f.anchor) := fun z h => k z (by simp [names,h])
  have kb : Covers keep (roles f.b) := fun z h => k z (by simp [names,h])
  have kc : Covers keep (roles f.c) := fun z h => k z (by simp [names,h])
  have kr (n : Node) (h : Covers keep (roles n)) : role n ∈ keep := by
    apply h
    cases side : f.distinguishMate <;> simp [roles,role,roleOf,side]
  refine ⟨keep,by simp [keep,names,roles],k,select_cap keep cap,
    select_marked keep _ _ (ka _ (by simp [roles])) (ka _ (by simp [roles])) anchor,
    select_neighbor keep ts _ _ _ ka kb nb,select_neighbor keep ts _ _ _ ka kc nc,
    diff keep (kr _ kb) (kr _ kc) (by simp [keep]) (by simp [keep]),True.intro⟩

end P455OtherProjection
