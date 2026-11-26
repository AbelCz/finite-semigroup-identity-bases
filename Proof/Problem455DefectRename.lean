import Problem455DefectProjection



namespace P455DefectRename
open P455Witness P455Paths P455ContactLift P455SourceFamilies
open P455ContactReflection P455PortReflection P455DefectProjection Problem455.Slots

def decode (keep : W) (i : Nat) : Nat := (keep[i]?).getD 0

theorem decode_idx (keep : W) {a : Nat} (h : a ∈ keep) : decode keep (keep.idxOf a) = a := by
  induction keep with
  | nil => contradiction
  | cons b keep ih =>
    by_cases eq : b = a
    · subst b; simp [decode]
    · have ha : a ∈ keep := (List.mem_cons.mp h).resolve_left (Ne.symm eq)
      simpa [decode,List.idxOf_cons,cond_eq_if,beq_iff_eq,eq] using ih ha

theorem decode_map {keep w : W} (hs : ∀ a ∈ w, a ∈ keep) :
    (w.map keep.idxOf).map (decode keep) = w := by
  rw [List.map_map]
  calc
    _ = w.map id := List.map_congr_left (fun a ha => decode_idx keep (hs a ha))
    _ = w := List.map_id w

def extend (keep : W) (a : Nat) := if a ∈ keep then keep.idxOf a else keep.length + a

theorem extend_inj (keep : W) {a b : Nat} (h : extend keep a = extend keep b) : a = b := by
  by_cases ha : a ∈ keep <;> by_cases hb : b ∈ keep <;> simp only [extend,ha,hb,if_true,if_false] at h
  · simpa only [decode_idx keep ha, decode_idx keep hb] using congrArg (decode keep) h
  · have := List.idxOf_lt_length ha; omega
  · have := List.idxOf_lt_length hb; omega
  · omega

abbrev Injects (d : Nat → Nat) := ∀ {a b}, d a = d b → a = b

theorem select_map_inj (d : Nat → Nat) (inj : Injects d) (keep w : W) :
    select (keep.map d) (w.map d) = (select keep w).map d := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have iff : d a ∈ keep.map d ↔ a ∈ keep := by
      constructor
      · intro h; obtain ⟨b,hb,eq⟩ := List.mem_map.mp h; exact inj eq ▸ hb
      · exact List.mem_map_of_mem
    by_cases ha : a ∈ keep <;> simp_all [select]

theorem kept {keep w : W} {a : Nat} (h : a ∈ select keep w) : a ∈ keep := by
  simpa using (List.mem_filter.mp h).2

theorem extend_map {keep w : W} (hs : ∀ a ∈ w, a ∈ keep) :
    w.map (extend keep) = w.map keep.idxOf :=
  List.map_congr_left (fun a ha => by simp [extend, hs a ha])

theorem binary_select_map (keep w : W) {x y : Nat} (hx : x ∈ keep) (hy : y ∈ keep) :
    (select [x,y] w).map keep.idxOf =
    select [keep.idxOf x,keep.idxOf y] ((select keep w).map keep.idxOf) := by
  have h := select_map_inj (extend keep) (extend_inj keep) [x,y] (select keep w)
  rw [select_sub keep [x,y] w (by simpa using And.intro hx hy),
      extend_map (fun _ ha => kept ha),
      extend_map (keep := keep) (w := select [x,y] w) (by
        intro a ha; have hxy : a = x ∨ a = y := by simpa using kept ha
        rcases hxy with rfl|rfl <;> assumption)] at h
  simpa [extend,hx,hy] using h.symm

theorem count_rename (d : Nat → Nat) (inj : Injects d) (w : W) (a : Nat) :
    (w.map d).count (d a) = w.count a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases eq : b = a
    · subst b; simp [ih]
    · have ne : d b ≠ d a := fun e => eq (inj e)
      simp [eq,ne,ih, List.count_cons, beq_iff_eq]

theorem cap_rename {r w} (d : Nat → Nat) (inj : Injects d) (cp : P455Closure.Cap r w) :
    P455Closure.Cap r (w.map d) := by
  intro a
  by_cases mem : a ∈ w.map d
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp mem
    simpa only [count_rename d inj] using cp b
  · simp [List.count_eq_zero.mpr mem]

theorem rename_sees (d : Nat → Nat) (inj : Injects d) {w pat} (obs : sees w pat) :
    sees (w.map d) (pat.map (eventMap d)) := by
  unfold sees events at *
  rw [← stamp_map d w w (fun _ => 0) (fun _ => 0) (fun _ h => h) (fun _ _ _ _ h => inj h) (fun _ _ => rfl)]
  exact obs.map _

theorem rename_order {r allow src dst w} (d : Nat → Nat) (inj : Injects d) (pat : List Event)
    (h : Holds r allow src w (.order pat)) :
    Holds r allow dst (w.map d) (.order (pat.map (eventMap d))) := by
  refine ⟨?_,rename_sees d inj h.2⟩
  intro e he; obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he; exact h.1 f hf

theorem rename_pattern (d : Nat → Nat) (inj : Injects d) {w a b tag bit}
    (h : select [a,b] w = profile a b tag bit) :
    select [d a,d b] (w.map d) = profile (d a) (d b) tag bit := by
  rw [← map_profile d a b tag bit, ← h, ← select_map_inj d inj [a,b] w]
  rfl

theorem rename_marked {r allow src w} (d : Nat → Nat) (inj : Injects d) (n : Node) (bit : Bool)
    (h : Holds r allow src w (markedNode n bit)) :
    Holds r allow (markNode (sendNode d n)) (w.map d) (markedNode (sendNode d n) bit) :=
  ⟨fun e => h.1 (inj e),h.2.1,h.2.2.1,.inl ⟨rfl,rfl⟩,rename_pattern d inj h.2.2.2.2⟩

theorem rename_record {r allow src dst w a b tag} (d : Nat → Nat) (inj : Injects d)
    (h : Holds r allow src w (.record a b tag)) :
    Holds r allow dst (w.map d) (.record (d a) (d b) tag) := by
  obtain ⟨ne,len,ok,bit,pr⟩ := h
  exact ⟨fun e => ne (inj e),len,ok,bit,rename_pattern d inj pr⟩

theorem rename_contact {r allow src dst w} (d : Nat → Nat) (inj : Injects d) (a b : Nat) (c : ContactChoice)
    (h : Holds r allow src w (contact r a b c)) :
    Holds r allow dst (w.map d) (contact r (d a) (d b) c) := by
  cases c with
  | record tag rev => cases rev <;> exact rename_record d inj h
  | port phase rev =>
    obtain ⟨ab,ac,bc,early,obs,last⟩ := h
    refine ⟨fun e => ab (inj e),(count_rename d inj w a).trans ac,(count_rename d inj w b).trans bc,?_,?_,last⟩
    · rcases early with ⟨h,_⟩|⟨h,_⟩
      · exact .inl ⟨rename_order d inj [(a,2),(b,0)] h,True.intro⟩
      · exact .inr ⟨rename_order d inj [(b,2),(a,0)] h,True.intro⟩
    · cases rev <;> exact rename_order d inj _ obs

theorem rename_walk {r allow src dst w} (d : Nat → Nat) (inj : Injects d) (a : Nat) (p : List Step)
    (h : Walk r allow src w a p) :
    Walk r allow dst (w.map d) (d a) (relabel d p) := by
  induction p generalizing a with
  | nil => trivial
  | cons bc p ih => exact ⟨rename_contact d inj a bc.1 bc.2 h.1,ih _ h.2⟩

theorem rename_deficient {r allow w} (d : Nat → Nat) (inj : Injects d) (s : SlotCertificate)
    (b : Nat) (kind : s.defect = .deficient b) (h : Holds r allow (markNode s.anchor) w (s.query r)) :
    Holds r allow (markNode (sendSlot d s).anchor) (w.map d) ((sendSlot d s).query r) := by
  obtain ⟨len,walk,term⟩ := slot_route s h
  let start := picked s
  have start' : picked (sendSlot d s) = d start := by
    cases side : s.startAtMate <;> simp [sendSlot,picked,sendNode,start,side]
  rw [kind] at term
  obtain ⟨⟨slot,j,seen⟩,cnt⟩ := term
  refine ⟨rename_marked d inj s.anchor s.bit h.1,by simpa [sendSlot,relabel] using len,?_,True.intro⟩
  apply (route_iff ..).mpr
  change Walk _ _ _ _ (picked (sendSlot d s)) (relabel d s.steps) ∧ Holds _ _ _ _
    (terminalSlot r (endpoint (picked (sendSlot d s)) (relabel d s.steps)) s.terminalIndex (sendDefect d s.defect))
  rw [start',endpoint_relabel,kind]
  exact ⟨rename_walk d inj start s.steps walk,⟨slot,j,rename_sees d inj seen⟩,by simpa only [Holds,count_rename d inj] using cnt⟩

theorem canonical_defect {r allow mark u} (cap : P455Closure.Cap r u) (n : Node) (bit side : Bool)
    (t i bad : Nat) (anchor : Holds r allow (markNode n) u (markedNode n bit))
    (near : Near r allow mark u (if side then n.mate else n.owner) t 6)
    (slot : slotStart i) (occ : occupies u t i bad) (deficient : u.count bad < r) :
    ∃ (keep : W) (s : SlotCertificate), keep.length ≤ 9 ∧ n.owner ∈ keep ∧ n.mate ∈ keep ∧
      s.anchor.owner = keep.idxOf n.owner ∧ s.anchor.mate = keep.idxOf n.mate ∧ s.bit = bit ∧
      s.defect = .deficient (keep.idxOf bad) ∧ (∀ a ∈ (select keep u).map keep.idxOf, a < 9) ∧
      P455Closure.Cap r ((select keep u).map keep.idxOf) ∧
      Holds r allow (markNode s.anchor) ((select keep u).map keep.idxOf) (s.query r) := by
  obtain ⟨keep,s,len,ho,hm,hb,kind,anc,bs,cp,h⟩ :=
    bounded_defect_kind cap n bit side t i bad anchor near slot occ deficient
  let d := extend keep
  have mapEq := extend_map (keep := keep) (w := select keep u) (fun _ ha => kept ha)
  have valid := rename_deficient d (extend_inj keep) s bad kind (by simpa only [anc] using h)
  refine ⟨keep,sendSlot d s,len,ho,hm,by simp [sendSlot,sendNode,d,extend,anc,ho],
    by simp [sendSlot,sendNode,d,extend,anc,hm],bs,by simp [sendSlot,sendDefect,kind,d,extend,hb],?_,?_,?_⟩
  · intro a ha; obtain ⟨b,bm,rfl⟩ := List.mem_map.mp ha
    exact Nat.lt_of_lt_of_le (List.idxOf_lt_length (kept bm)) len
  · rw [← mapEq]; exact cap_rename d (extend_inj keep) cp
  · rw [← mapEq]; exact valid

end P455DefectRename
