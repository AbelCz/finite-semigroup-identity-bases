import Problem455SourceFamilies




namespace P455DefectProjection
open P455Witness P455Paths P455SourceFamilies Problem455.Slots

theorem select_sub (keep smaller u : W) (hs : ∀ a ∈ smaller, a ∈ keep) :
    select smaller (select keep u) = select smaller u := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    by_cases hx : x ∈ keep
    · by_cases hm : x ∈ smaller <;> simp_all [select]
    · have hm : x ∉ smaller := fun h => hx (hs _ h)
      simp_all [select]

theorem select_count (keep u : W) (a : Nat) (mem : a ∈ keep) :
    (select keep u).count a = u.count a :=
  List.count_filter (by simpa using mem)

theorem select_cap {r u} (keep : W) (cap : P455Closure.Cap r u) :
    P455Closure.Cap r (select keep u) := by
  intro a
  by_cases mem : a ∈ keep
  · simpa only [select_count keep u _ mem] using cap a
  · have missing : a ∉ select keep u := by simp [select,mem]
    simp [List.count_eq_zero.mpr missing]

theorem select_order {r allow mark u} (keep : W) (pat : List Event)
    (hs : ∀ e ∈ pat, e.1 ∈ keep) (obs : Holds r allow mark u (.order pat)) :
    Holds r allow mark (select keep u) (.order pat) :=
  ⟨obs.1, P455ContactReflection.sees_select keep u pat hs obs.2⟩

theorem select_marked {r allow mark u} (keep : W) (n : Node) (b : Bool)
    (ho : n.owner ∈ keep) (hm : n.mate ∈ keep) (obs : Holds r allow mark u (markedNode n b)) :
    Holds r allow mark (select keep u) (markedNode n b) := by
  obtain ⟨ne,len,tag,mk,eq⟩ := obs
  refine ⟨ne,len,tag,mk,(select_sub keep [n.owner,n.mate] u ?_).trans eq⟩
  simpa using And.intro ho hm

theorem select_record {r allow mark u} (keep : W) (a b : Nat) (tag : Tag) (ha : a ∈ keep)
    (hb : b ∈ keep) (obs : Holds r allow mark u (.record a b tag)) :
    Holds r allow mark (select keep u) (.record a b tag) := by
  obtain ⟨ne,len,ok,bit,eq⟩ := obs
  exact ⟨ne,len,ok,bit,(select_sub keep [a,b] u (by simpa using And.intro ha hb)).trans eq⟩

theorem select_contact {r allow mark u} (keep : W) (a b : Nat) (c : ContactChoice)
    (ha : a ∈ keep) (hb : b ∈ keep) (obs : Holds r allow mark u (contact r a b c)) :
    Holds r allow mark (select keep u) (contact r a b c) := by
  cases c with
  | record tag rev =>
    cases rev with
    | false => exact select_record keep a b tag ha hb obs
    | true => exact select_record keep b a tag hb ha obs
  | port phase rev =>
    obtain ⟨ab,ac,bc,early,order,endQ⟩ := obs
    refine ⟨ab,(select_count keep u a ha).trans ac,(select_count keep u b hb).trans bc,?_,?_,endQ⟩
    · rcases early with ⟨f,_⟩|⟨f,_⟩
      · exact .inl ⟨select_order keep _ (by simpa using And.intro ha hb) f,True.intro⟩
      · exact .inr ⟨select_order keep _ (by simpa using And.intro hb ha) f,True.intro⟩
    · cases rev <;> apply select_order keep _ _ order <;> simp [ha,hb]

theorem select_walk {r allow mark u} (keep : W) (a : Nat) (p : List Step)
    (ha : a ∈ keep) (hs : ∀ m ∈ p, m.1 ∈ keep) (w : Walk r allow mark u a p) :
    Walk r allow mark (select keep u) a p := by
  induction p generalizing a with
  | nil => trivial
  | cons bc rest ih =>
    obtain ⟨b,c⟩ := bc
    have hb := hs (b,c) (by simp)
    exact ⟨select_contact keep a b c ha hb w.1,ih b hb (fun s h => hs s (by simp [h])) w.2⟩

theorem endpoint_kept (keep : W) (a : Nat) (p : List Step) (ha : a ∈ keep)
    (hs : ∀ m ∈ p, m.1 ∈ keep) : endpoint a p ∈ keep := by
  induction p generalizing a with
  | nil => exact ha
  | cons bc p ih => exact ih bc.1 (hs bc (by simp)) (fun s h => hs s (by simp [h]))

theorem select_slot {u : W} (keep : W) (t i b : Nat)
    (ht : t ∈ keep) (hb : b ∈ keep) (obs : occupies u t i b) :
    occupies (select keep u) t i b := by
  obtain ⟨j,h⟩ := obs
  exact ⟨j,P455ContactReflection.sees_select keep u _ (by simp [hb,ht]) h⟩

/-- A genuine slot component of alphabet size at most nine suffices for a
    deficient occupant. The cap and all unchanged occurrence indices are
    derived in the projection. Both orientations and length-zero routes
    are allowed; the keep list can repeat names. -/
theorem bounded_defect_kind {r allow mark u} (cap : P455Closure.Cap r u) (n : Node) (bit side : Bool)
    (t i bad : Nat) (anchor : Holds r allow (markNode n) u (markedNode n bit))
    (near : Near r allow mark u (if side then n.mate else n.owner) t 6)
    (slot : slotStart i) (occ : occupies u t i bad) (deficient : u.count bad < r) :
    ∃ (keep : W) (s : SlotCertificate), keep.length ≤ 9 ∧ n.owner ∈ keep ∧ n.mate ∈ keep ∧
      bad ∈ keep ∧ s.defect = .deficient bad ∧ s.anchor = n ∧ s.bit = bit ∧ P455Closure.Cap r (select keep u) ∧
      Holds r allow (markNode n) (select keep u) (s.query r) := by
  let a := if side then n.mate else n.owner
  obtain ⟨p,w,ep,len⟩ := near
  let keep := n.owner :: n.mate :: bad :: p.map Prod.fst
  have h1 : n.owner ∈ keep := by simp [keep]
  have h2 : n.mate ∈ keep := by simp [keep]
  have h3 : bad ∈ keep := by simp [keep]
  have start : a ∈ keep := by cases side <;> simp [a,h1,h2]
  have ins : ∀ m ∈ p, m.1 ∈ keep := fun m hm => by simp [keep,List.mem_map_of_mem hm]
  have last : t ∈ keep := ep ▸ endpoint_kept keep a p start ins
  let s : SlotCertificate := ⟨n,bit,side,p,i,.deficient bad⟩
  refine ⟨keep,s,by simpa [keep] using (show p.length + 3 ≤ 9 by omega),h1,h2,h3,rfl,rfl,rfl,
    select_cap keep cap,select_marked keep n bit h1 h2 anchor,len,?_,True.intro⟩
  apply (route_iff ..).mpr
  refine ⟨remark_walk _ _ (select_walk keep a p start ins w),?_⟩
  change (slotStart i ∧ occupies (select keep u) (endpoint a p) i bad) ∧ (select keep u).count bad < r
  rw [show endpoint a p = t from ep, select_count keep u bad h3]
  exact ⟨⟨slot,select_slot keep t i bad last h3 occ⟩,deficient⟩

theorem bounded_defect {r allow mark u} (cap : P455Closure.Cap r u) (n : Node) (bit side : Bool)
    (t i bad : Nat) (anchor : Holds r allow (markNode n) u (markedNode n bit))
    (near : Near r allow mark u (if side then n.mate else n.owner) t 6)
    (slot : slotStart i) (occ : occupies u t i bad) (deficient : u.count bad < r) :
    ∃ (keep : W) (s : SlotCertificate), keep.length ≤ 9 ∧ n.owner ∈ keep ∧ n.mate ∈ keep ∧
      s.anchor = n ∧ s.bit = bit ∧ P455Closure.Cap r (select keep u) ∧
      Holds r allow (markNode n) (select keep u) (s.query r) := by
  obtain ⟨keep,s,len,ho,hm,_,_,anc,bs,cp,h⟩ :=
    bounded_defect_kind cap n bit side t i bad anchor near slot occ deficient
  exact ⟨keep,s,len,ho,hm,anc,bs,cp,h⟩

end P455DefectProjection
