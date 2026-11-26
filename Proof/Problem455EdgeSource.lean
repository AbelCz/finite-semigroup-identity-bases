import Problem455CertificateReach
import Problem455PortReflection
import Problem455ContactLift



namespace P455EdgeSource
open P455Witness P455Paths P455CertificateReach P455PortReflection P455ContactReflection
open P455ContactLift

def sendEdge (d : Nat → Nat) (e : EdgeCertificate) : EdgeCertificate :=
  ⟨sendNode d e.a, sendNode d e.b, sendNode d e.right, sendNode d e.left,
    sendNode d e.down, sendNode d e.up, sendNode d e.diagonal⟩

def endpointMarks (d : Nat → Nat) (e : EdgeCertificate) (s t : Nat) : Prop :=
  (s = d e.a.owner ∧ t = d e.a.mate) ∨ (s = d e.b.owner ∧ t = d e.b.mate)

private theorem when_true {r allow mark w b q} (f : b = true → Holds r allow mark w q) :
    Holds r allow mark w (flagQ b q) := by
  cases b
  · exact True.intro
  · exact f rfl

private theorem read_guard {r allow mark w b q} (hb : b = true)
    (f : Holds r allow mark w (flagQ b q)) : Holds r allow mark w q := by simpa [flagQ,hb] using f

/-- Retain one real four-role port between the endpoints. This also supplies
    the injectivity needed for the final first-owner comparison. -/
theorem endpoint_port {r allow mark w} (ts : Tiles) (e : EdgeCertificate)
    (ok : Holds r allow mark w (e.query ts)) :
    ∃ p, Holds r allow mark w (orientedPort p e.a e.b) ∨
         Holds r allow mark w (orientedPort p e.b e.a) := by
  have lc := ok.2.2.1
  have succ := ok.2.2.2.1
  unfold chosenSuccessor at succ
  dsimp only at succ
  split at succ
  next ret => exact ⟨4,succ.2.1⟩
  next noReturn =>
    have eq := succ.1
    cases row : endOfRow ts e.a with
    | true =>
      have down : ts.bottom e.a.tag = false := by simpa [row] using noReturn
      have target : e.down = e.b := by simpa [row] using eq
      have ok := read_guard (by simp [down]) lc.2.2.1
      exact ⟨_,.inl (target ▸ ok.2)⟩
    | false =>
      cases odd : ts.oddRow e.a.tag with
      | true =>
        have left : ts.left e.a.tag = false := by simpa [endOfRow,odd] using row
        have target : e.left = e.b := by simpa [row,odd] using eq
        have ok := read_guard (by simp [left]) lc.2.1
        exact ⟨_,.inr (target ▸ ok.2.1)⟩
      | false =>
        have right : ts.right e.a.tag = false := by simpa [endOfRow,odd] using row
        have target : e.right = e.b := by simpa [row,odd] using eq
        have ok := read_guard (by simp [right]) lc.1
        exact ⟨_,.inl (target ▸ ok.2.1)⟩

theorem edge_source {r allow mark v h l k d} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (ts : Tiles) (e : EdgeCertificate)
    (supply : ∀ n, Active ts e n → UniformOn r v h d (roles n))
    (ok : Holds r allow mark (l ++ v.flatMap h ++ k) (e.query ts)) :
    Holds r allow (endpointMarks d e) v ((sendEdge d e).query ts) := by
  have both {n m} (an : Active ts e n) (am : Active ts e m) :
      UniformOn r v h d (roles n ++ roles m) := by
    intro y hy
    rcases List.mem_append.mp hy with h|h
    · exact supply n an y h
    · exact supply m am y h
  have localRight (rr : ts.right e.a.tag = false) :=
    read_guard (by simp [rr]) ok.2.2.1.1
  have localLeft (ll : ts.left e.a.tag = false) :=
    read_guard (by simp [ll]) ok.2.2.1.2.1
  have localDown (dd : ts.bottom e.a.tag = false) :=
    read_guard (by simp [dd]) ok.2.2.1.2.2.1
  have localUp (uu : ts.top e.a.tag = false) :=
    read_guard (by simp [uu]) ok.2.2.1.2.2.2.1
  have localSq (rr : ts.right e.a.tag = false) (dd : ts.bottom e.a.tag = false) :=
    read_guard (by simp [rr,dd]) ok.2.2.1.2.2.2.2.1
  have hs : Holds r allow (endpointMarks d e) v (localCert ts (sendEdge d e)) := by
    refine ⟨when_true (fun b => ?_),when_true (fun b => ?_),when_true (fun b => ?_),
            when_true (fun b => ?_),when_true (fun b => ?_),True.intro⟩
    · have rr : ts.right e.a.tag = false := by simpa [sendEdge,sendNode] using b
      exact reflect_rightward hr cap ts _ _ (both .anchor (.right rr)) (localRight rr)
    · have ll : ts.left e.a.tag = false := by simpa [sendEdge,sendNode] using b
      exact reflect_rightward hr cap ts _ _ (both (.left ll) .anchor) (localLeft ll)
    · have dd : ts.bottom e.a.tag = false := by simpa [sendEdge,sendNode] using b
      exact reflect_downward hr cap ts _ _ (both .anchor (.down dd)) (localDown dd)
    · have uu : ts.top e.a.tag = false := by simpa [sendEdge,sendNode] using b
      exact reflect_downward hr cap ts _ _ (both (.up uu) .anchor) (localUp uu)
    · obtain ⟨rr,dd⟩ : ts.right e.a.tag = false ∧ ts.bottom e.a.tag = false := by
        simpa [sendEdge,sendNode] using b
      exact ⟨reflect_downward hr cap ts _ _ (both (.right rr) (.diagonal rr dd)) (localSq rr dd).1,
             reflect_rightward hr cap ts _ _ (both (.down dd) (.diagonal rr dd)) (localSq rr dd).2⟩
  have aBit := reflect_markedNode hr cap e.a true (supply _ .anchor) (endpointMarks d e)
    (Or.inl (Or.inl ⟨rfl,rfl⟩)) ok.1
  have bBit := reflect_markedNode hr cap e.b false (supply _ .successor) (endpointMarks d e)
    (Or.inl (Or.inr ⟨rfl,rfl⟩)) ok.2.1
  refine ⟨aBit,bBit,hs,?_,True.intro⟩
  have rel (pat) (mem : ∀ u ∈ pat, u.1 ∈ roles e.a ++ roles e.b) (ord :
      Holds r allow mark (l ++ v.flatMap h ++ k) (.order pat)) :
      Holds r allow mark v (.order (pat.map (eventMap d))) := by
    obtain ⟨p,forward|back⟩ := endpoint_port ts e ok
    · exact port_owner_order hr cap _ _ p (both .anchor .successor) forward pat mem ord
    · exact port_owner_order hr cap _ _ p (both .successor .anchor) back pat
        (fun u hu => by have := mem u hu; simpa [or_comm] using this) ord
  have suc := ok.2.2.2.1
  unfold chosenSuccessor at suc ⊢
  dsimp only [sendEdge,sendNode] at suc ⊢
  change Holds r allow _ v (if endOfRow ts e.a && ts.bottom e.a.tag then _ else _) 
  split at suc
  next ret =>
    rw [if_pos ret]
    have ord := rel [(e.b.owner,0),(e.a.owner,0)] (by simp [roles]) suc.2.2.1
    refine ⟨suc.1,?_,ord,True.intro⟩
    rcases suc.2.1 with f|b
    · exact .inl (reflect_port hr cap _ _ _ (both .anchor .successor) f)
    · exact .inr (reflect_port hr cap _ _ _ (both .successor .anchor) b)
  next noReturn =>
    rw [if_neg noReturn]
    have ord := rel [(e.a.owner,0),(e.b.owner,0)] (by simp [roles]) suc.2
    refine ⟨?_,ord⟩
    change (if endOfRow ts e.a then sendNode d e.down else
      if ts.oddRow e.a.tag then sendNode d e.left else sendNode d e.right) = sendNode d e.b
    have eq := suc.1
    cases row : endOfRow ts e.a <;> cases parity : ts.oddRow e.a.tag <;>
      simp only [row,parity,Bool.false_eq_true,if_false,if_true] at eq ⊢ <;>
      exact congrArg (sendNode d) eq

/-- A guarded source seed on the owner of either marked endpoint supplies
    every active record used above. No map of the tester alphabet is assumed. -/
theorem edge_source_of_seed {r allow mark v h l k seed J} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (ts : Tiles) (e : EdgeCertificate)
    (ok : Holds r allow mark (l ++ v.flatMap h ++ k) (e.query ts))
    (startAtSecond : Bool)
    (start : Supplies v h r seed (if startAtSecond then e.b.owner else e.a.owner))
    (guard : Guard r allow mark v seed J) (budget : 4 ≤ J) :
    Holds r allow (endpointMarks (donor v h r) e) v ((sendEdge (donor v h r) e).query ts) := by
  apply edge_source hr cap ts e _ ok
  intro n active y hy
  have role : y = n.owner ∨ y = n.mate := by simpa [roles] using hy
  obtain ⟨a,b⟩ := edge_reach cap ts e ok active role
  have near : Near r allow mark (l ++ v.flatMap h ++ k)
      (if startAtSecond then e.b.owner else e.a.owner) y 4 := by cases startAtSecond <;> assumption
  exact (lift_near hr cap start guard budget near).1

/-- Starting at a mate rather than an owner costs one record contact.
    Only a donor for this one chosen occurrence label is needed. -/
theorem edge_source_from_role {r allow mark v h l k seed J} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (ts : Tiles) (e : EdgeCertificate)
    (ok : Holds r allow mark (l ++ v.flatMap h ++ k) (e.query ts))
    (atSecond atMate : Bool)
    (start : let a := if atSecond then e.b else e.a
             Supplies v h r seed (if atMate then a.mate else a.owner))
    (guard : Guard r allow mark v seed J) (budget : (if atMate then 5 else 4) ≤ J) :
    Holds r allow (endpointMarks (donor v h r) e) v ((sendEdge (donor v h r) e).query ts) := by
  cases atMate with
  | false =>
    cases atSecond
    · exact edge_source_of_seed hr cap ts e ok false start guard budget
    · exact edge_source_of_seed hr cap ts e ok true start guard budget
  | true =>
    apply edge_source hr cap ts e _ ok
    intro n active y hy
    have role : y = n.owner ∨ y = n.mate := by simpa [roles] using hy
    obtain ⟨a,b⟩ := edge_reach cap ts e ok active role
    cases atSecond
    · have step := (record_pair (marked_typed ok.1)).2
      exact (lift_near hr cap start guard budget (near_trans step a)).1
    · have step := (record_pair (marked_typed ok.2.1)).2
      exact (lift_near hr cap start guard budget (near_trans step b)).1

end P455EdgeSource
