import Problem455EdgeSource
import Problem455SourceFamilies
import Problem455OriginalWalk
import Problem455OriginalTerminal
import Problem455OriginalEdges




namespace P455SourceTheorem
open P455Witness P455Paths P455ContactLift P455SourceFamilies P455PortReflection
open P455EdgeSource P455Retained P455OriginalWalk Problem455.Slots

def startLabel (c : Certificate) (second mate : Bool) : Nat :=
  match c with
  | .slot s => picked s
  | .functionality f => f.anchor.owner
  | .edge e =>
    let n := if second then e.b else e.a
    if mate then n.mate else n.owner

def transferred (d : Nat → Nat) : Certificate → Certificate
  | .slot s => .slot (sendSlot d s)
  | .functionality f => .functionality (sendFunc d f)
  | .edge e => .edge (sendEdge d e)

def sourceMarks (d : Nat → Nat) : Certificate → Marking
  | .slot s => markNode (sendNode d s.anchor)
  | .functionality f => markNode (sendNode d f.anchor)
  | .edge e => endpointMarks d e

def SourceEvidence (r : Nat) (allow : Tag → Prop) (ts : Tiles) (v : W) (h : Nat → W)
    (seed : Nat) : Certificate → Prop
  | .slot s => SlotResult r allow v h seed s
  | .functionality f => FuncResult r allow ts v h f
  | .edge e => Holds r allow (endpointMarks (donor v h r) e) v ((sendEdge (donor v h r) e).query ts)

theorem in_source {r allow mark v h l k seed} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (ts : Tiles) (c : Certificate)
    (second mate : Bool) (ok : Holds r allow mark (l ++ v.flatMap h ++ k) (c.query r ts))
    (start : Supplies v h r seed (startLabel c second mate)) (guard : Guard r allow mark v seed 6) :
    SourceEvidence r allow ts v h seed c := by
  cases c with
  | slot s => exact slot_source hr cap s ok start guard
  | functionality f => exact functionality_source hr cap ts f ok start guard
  | edge e => exact edge_source_from_role hr cap ts e ok second mate start guard (by split <;> decide)

theorem compressed_query {r allow ts v h seed c} (ev : SourceEvidence r allow ts v h seed c)
    (cmp : Compressed r v) :
    Holds r allow (sourceMarks (donor v h r) c) v ((transferred (donor v h r) c).query r ts) := by
  cases c with
  | slot s => exact ev.2.2.2 cmp
  | functionality f => exact ev.2.2.2.2 cmp
  | edge e => exact ev

/-- Form in the evaluated rule word. Each bounded literal contact walk is
    transported with the identical sequence of choices. -/
theorem arbitrary_reps_source_gadget {r allow mark T} (capT : P455Quotient.Cap r T)
    (val : Nat → P455Quotient.Q (rules r allow mark) T) (v : W) (h : Nat → W)
    (reps : ∀ x ∈ v, P455Quotient.ofWord (rules r allow mark) T (h x) = val x)
    (live : P455Quotient.eval (rules r allow mark) capT val v ≠ P455Quotient.zero (rules r allow mark) T)
    (ts : Tiles) (c : Certificate) (initial : Holds r allow mark T (c.query r ts))
    (second mate : Bool) (seed : Nat) (hr : 0 < r)
    (start : Supplies v h r seed (startLabel c second mate)) (guard : Guard r allow mark v seed 6) :
    ∃ z l k, P455Quotient.Variant (rules r allow mark) T z ∧ z = l ++ v.flatMap h ++ k ∧
      Holds r allow mark z (c.query r ts) ∧ SourceEvidence r allow ts v h seed c ∧
      ∀ p : List Step, p.length ≤ 6 → Walk r allow mark z (startLabel c second mate) p →
        Walk r allow mark v seed (relabel (donor v h r) p) ∧
        Supplies v h r (donor v h r (endpoint (startLabel c second mate) p))
                        (endpoint (startLabel c second mate) p) := by
  obtain ⟨z,l,k,path,eq,ok⟩ := arbitrary_reps_designated capT val v h reps live c ts initial
  subst z
  have cap : P455Closure.Cap r (l ++ v.flatMap h ++ k) :=
    fun s => (P455Quotient.count_walk _ path s) ▸ capT s
  exact ⟨_,l,k,path,rfl,ok,in_source hr cap ts c second mate ok start guard,
    fun p bp wp => P455ContactLift.lift_walk hr cap start guard p bp wp⟩

theorem expanded_query {r allow mark ts v h e kept seed c second mate T}
    (exp : Expansion v e kept) (hr : 1 < r) (capU : P455Closure.Cap r (v.flatMap e))
    (capF : P455Closure.Cap r (v.flatMap h))
    (original : OriginalGuard r allow mark (v.flatMap e) kept seed 6)
    (start : Supplies v h r seed (startLabel c second mate))
    (ev : SourceEvidence r allow ts v h seed c)
    (initial : Holds r allow mark T (c.query r ts)) (cmp : Compressed r (v.flatMap e)) :
    let d := donor v h r
    Holds r allow (sourceMarks d c) (v.flatMap e) ((transferred d c).query r ts) := by
  let d := donor v h r
  have pos : 0 < r := by omega
  cases c with
  | edge ed =>
    exact P455OriginalEdges.expand_edge exp hr capU ev
  | functionality f =>
    obtain ⟨bit,b,c,dist,_⟩ := ev
    exact ⟨P455OriginalEdges.expand_markedNode exp hr capU bit,
      P455OriginalEdges.expand_neighbor exp hr capU f.dir b,
      P455OriginalEdges.expand_neighbor exp hr capU f.dir c,compressed_separates cmp dist,True.intro⟩
  | slot s =>
    obtain ⟨bit,walk,terminal,_⟩ := ev
    have eq : d (picked s) = seed := donor_eq pos capF start
    have big := exp.walk hr capU _ _ walk
    let m := markNode (sendNode d s.anchor)
    let finalLabel := endpoint (picked s) s.steps
    have ep : endpoint seed (relabel d s.steps) = d finalLabel := by rw [← eq,endpoint_relabel]
    have pickEq : picked (sendSlot d s) = d (picked s) := by
      cases z : s.startAtMate <;> simp [picked,sendSlot,sendNode,z]
    obtain ⟨len,_,termT⟩ := slot_route s initial
    have valid := valid_slot s.defect termT
    have bigWalk : Walk r allow mark (v.flatMap e) seed (relabel d s.steps) :=
      remark_walk _ _ big
    have reach : Near r allow mark (v.flatMap e) seed (d finalLabel) 6 :=
      ⟨relabel d s.steps,bigWalk,ep,by simpa [relabel] using len⟩
    have ownerKept := (original _ reach).1
    have transfer (y : Nat) (inside : occupies v (d finalLabel) s.terminalIndex y) (cnt : v.count y = r) :
        occupies (v.flatMap e) (d finalLabel) s.terminalIndex y ∧ (v.flatMap e).count y = r := by
      have present : y ∈ v := List.count_pos_iff.mp (by omega)
      have ky : kept y := by
        apply Classical.byContradiction
        intro absent
        have := (exp.gaps y present absent).1
        omega
      have mem : y ∈ e y := by rw [exp.literal y present ky]; simp
      exact ⟨exp.in_original_slot _ _ _ ownerKept inside y mem,(exp.count_eq _ (fun _ h => h) y ky).trans cnt⟩
    have term : Holds r allow m (v.flatMap e)
        (terminalSlot r (d finalLabel) s.terminalIndex (sendDefect d s.defect)) :=
      rebuild_terminal_in d s.defect valid cmp (fun hh => donor_eq pos capF hh) transfer terminal
    refine ⟨P455OriginalEdges.expand_markedNode exp hr capU bit,by simpa [sendSlot,relabel] using len,?_,True.intro⟩
    apply (route_iff ..).mpr
    change Walk r allow m (v.flatMap e) (picked (sendSlot d s)) (relabel d s.steps) ∧
      Holds r allow m (v.flatMap e) (terminalSlot r (endpoint (picked (sendSlot d s)) (relabel d s.steps))
          s.terminalIndex (sendDefect d s.defect))
    rw [pickEq,endpoint_relabel]
    exact ⟨eq.symm ▸ big,term⟩

/-- The complete quotient-to-original-word result. The evaluation substitutes h
    in the smaller word v. Independently e expands the fresh gaps of v to the
    original source word U. No equality between these two substitutions is used. -/
theorem arbitrary_reps_original_gadget {r allow mark T} (capT : P455Quotient.Cap r T)
    (val : Nat → P455Quotient.Q (rules r allow mark) T) (v : W) (h : Nat → W)
    (reps : ∀ x ∈ v, P455Quotient.ofWord (rules r allow mark) T (h x) = val x)
    (live : P455Quotient.eval (rules r allow mark) capT val v ≠ P455Quotient.zero (rules r allow mark) T)
    (ts : Tiles) (c : Certificate) (initial : Holds r allow mark T (c.query r ts))
    (second mate : Bool) (seed : Nat) (hr : 1 < r)
    (start : Supplies v h r seed (startLabel c second mate))
    {e kept} (exp : Expansion v e kept) (capU : P455Closure.Cap r (v.flatMap e))
    (original : OriginalGuard r allow mark (v.flatMap e) kept seed 6) :
    let d := donor v h r
    let u := v.flatMap e
    let a := startLabel c second mate
    ∃ z l k, P455Quotient.Variant (rules r allow mark) T z ∧ z = l ++ v.flatMap h ++ k ∧
      Holds r allow mark z (c.query r ts) ∧ SourceEvidence r allow ts v h seed c ∧
      (Compressed r u → Holds r allow (sourceMarks d c) u ((transferred d c).query r ts)) ∧
      ∀ p : List Step, p.length ≤ 6 → Walk r allow mark z a p →
        Walk r allow mark u seed (relabel d p) ∧ endpoint seed (relabel d p) = d (endpoint a p) ∧
        (relabel d p).length = p.length ∧ kept (d (endpoint a p)) ∧
        Supplies v h r (d (endpoint a p)) (endpoint a p) ∧ Supplies u h r (d (endpoint a p)) (endpoint a p) := by
  obtain ⟨z,l,k,path,eq,ok,source,_⟩ := arbitrary_reps_source_gadget capT val v h reps live ts c initial
    second mate seed (by omega) start (exp.guard hr capU original)
  subst z
  have cap : P455Closure.Cap r (l ++ v.flatMap h ++ k) :=
    fun s => (P455Quotient.count_walk _ path s) ▸ capT s
  exact ⟨_,l,k,path,rfl,ok,source,expanded_query exp hr capU (factor_cap cap) original start source initial,
    fun p len walk => P455OriginalWalk.lift_walk exp hr capU original cap start p len walk⟩

end P455SourceTheorem
