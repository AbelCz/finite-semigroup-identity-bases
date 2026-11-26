import Problem455ContactLift
import Problem455CertificateReach
import Problem455PortReflection
import Problem455TerminalTransfer

/- Source interpretations of the designated slot and duplicate-neighbor
   certificates. Block distinctions require no repeated links to be read
   literally back in the source. The weaker name/count conclusions do not. -/
namespace P455SourceFamilies
open P455Witness P455Paths P455ContactLift P455PortReflection Problem455.Slots

def markNode (a : Node) : Marking := fun x y => x = a.owner ∧ y = a.mate
def picked (s : SlotCertificate) := if s.startAtMate then s.anchor.mate else s.anchor.owner
def sendDefect (d : Nat → Nat) : SlotDefect → SlotDefect
  | .deficient a => .deficient (d a)
  | .overflow xs => .overflow (xs.map d)
def sendSlot (d : Nat → Nat) (s : SlotCertificate) : SlotCertificate :=
  { s with anchor := sendNode d s.anchor, steps := relabel d s.steps, defect := sendDefect d s.defect }
def sendFunc (d : Nat → Nat) (f : FunctionalityCertificate) : FunctionalityCertificate :=
  { f with anchor := sendNode d f.anchor, b := sendNode d f.b, c := sendNode d f.c }

def Compressed (r : Nat) (v : W) := ∀ a b, ¬ Problem455Swap.Link r v a b

theorem compressed_separates {r v} (cmp : Compressed r v) {a b : Nat} (ne : a ≠ b) :
    ¬ Problem455Swap.SameBlock r v a b := by
  intro same
  have joined := same.2.2
  cases joined with
  | refl => exact ne rfl
  | extend _ adj => rcases adj with f|b <;> exact cmp _ _ (by assumption)

private theorem remark_contact {r allow mark src w a b} (c : ContactChoice)
    (obs : V r allow mark w (contact r a b c)) : V r allow src w (contact r a b c) := by
  apply remark _ obs
  cases c with
  | record tag rev => cases rev <;> rfl
  | port phase rev => rfl

theorem remark_walk {r allow mark src w} (a : Nat) (p : List Step)
    (h : Walk r allow mark w a p) : Walk r allow src w a p := by
  induction p generalizing a with
  | nil => exact True.intro
  | cons pair p ih => exact ⟨remark_contact pair.2 h.1,ih pair.1 h.2⟩

theorem valid_slot {r allow mark w o i} (d : SlotDefect)
    (q : V r allow mark w (terminalSlot r o i d)) : slotStart i := by
  cases d with
  | deficient a => exact q.1.1
  | overflow xs =>
    cases xs with
    | nil => have h : ([] : List Nat).length = 5 := q.1; contradiction
    | cons a _ => exact q.2.2.1.1.2.1

theorem rebuild_terminal_in {r v u h x i} (d : Nat → Nat) (a : SlotDefect)
    (slot : slotStart i) (cmp : Compressed r u)
    (unique : ∀ {a y}, Supplies v h r y a → d a = y)
    (inside : ∀ y, occupies v x i y → v.count y = r → occupies u x i y ∧ u.count y = r)
    {allow mark} (lifted : P455TerminalTransfer.Lift v h x i r a) :
    Holds r allow mark u (terminalSlot r x i (sendDefect d a)) := by
  cases a with
  | deficient s => exact lifted.elim
  | overflow xs =>
    obtain ⟨f,len,nd,spec⟩ := lifted
    have eq (a : Nat) (inxs : a∈xs) : d a = f a :=
      unique ⟨(spec a inxs).2.2,(spec a inxs).2.1⟩
    have maps : xs.map d = xs.map f := List.map_congr_left eq
    have bs : (x :: xs.map d).Pairwise (fun a b => ¬ Problem455Swap.SameBlock r u a b) := by
      rw [maps]; exact nd.imp (fun ne => compressed_separates cmp ne)
    refine ⟨by simpa using len,(P455TerminalTransfer.block_separation _).mpr bs,?_,True.intro⟩
    apply (allQ_iff _).mpr
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have sp := spec a ha
    have out := inside (f a) sp.1 sp.2.2
    exact eq a ha ▸ And.intro out.2 (And.intro slot out.1)

theorem rebuild_terminal {r v h x i} (d : Nat → Nat) (a : SlotDefect)
    (slot : slotStart i) (cmp : Compressed r v)
    (unique : ∀ {a y}, Supplies v h r y a → d a = y)
    {allow mark} (lifted : P455TerminalTransfer.Lift v h x i r a) :
    Holds r allow mark v (terminalSlot r x i (sendDefect d a)) :=
  rebuild_terminal_in d a slot cmp unique (fun _ o cnt => ⟨o,cnt⟩) lifted

def SlotResult (r : Nat) (allow : Tag → Prop) (v : W) (h : Nat → W) (seed : Nat)
    (s : SlotCertificate) : Prop :=
  let d := donor v h r
  let s' := sendSlot d s
  let m := markNode s'.anchor
  Holds r allow m v (markedNode s'.anchor s.bit) ∧
  Walk r allow m v seed s'.steps ∧
  P455TerminalTransfer.Lift v h (d (endpoint (picked s) s.steps)) s.terminalIndex r s.defect ∧
  (Compressed r v → Holds r allow m v (s'.query r))

theorem slot_source {r allow mark v h l k seed} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (s : SlotCertificate)
    (ok : V r allow mark (l ++ v.flatMap h ++ k) (s.query r))
    (start : Supplies v h r seed (picked s)) (guard : Guard r allow mark v seed 6) :
    SlotResult r allow v h seed s := by
  let d := donor v h r
  let m := markNode (sendNode d s.anchor)
  have seedEq : d (picked s) = seed := donor_eq hr (factor_cap cap) start
  have anch : V r allow mark (l ++ v.flatMap h ++ k) (markedNode s.anchor s.bit) := ok.1
  have ports := record_pair (marked_typed anch)
  have rolesU : UniformOn r v h d (roles s.anchor) := by
    intro u mem
    have links : Near r allow mark (l ++ v.flatMap h ++ k) (picked s) u 1 := by
      rcases (show u=s.anchor.owner ∨ u=s.anchor.mate by simpa [roles] using mem) with rfl|rfl
      · cases z : s.startAtMate <;> simp only [picked,z,Bool.false_eq_true,if_false,if_true]
        · exact near_self _ _
        · exact ports.2
      · cases z : s.startAtMate <;> simp only [picked,z,Bool.false_eq_true,if_false,if_true]
        · exact ports.1
        · exact near_self _ _
    exact (lift_near hr cap start guard (by decide : 1 ≤ 6) links).1
  have bit := reflect_markedNode hr cap s.anchor s.bit rolesU m (.inl ⟨rfl,rfl⟩) anch
  obtain ⟨len,outputWalk,terminal⟩ := slot_route s ok
  have walks := lift_walk hr cap start guard s.steps len outputWalk
  let endLabel := endpoint (picked s) s.steps
  have ext : Near r allow mark (l ++ v.flatMap h ++ k) (picked s) endLabel 6 :=
    ⟨s.steps,outputWalk,rfl,len⟩
  obtain ⟨en,towards⟩ := lift_near hr cap start guard (Nat.le_refl _) ext
  have slot := valid_slot s.defect terminal
  have g := guard (d endLabel) towards s.terminalIndex slot
  have lf := P455TerminalTransfer.terminal v h l k (d endLabel) endLabel s.terminalIndex r
    hr cap en.1 en.2 g s.defect terminal
  have sw : Walk r allow m v seed (relabel d s.steps) := remark_walk _ _ walks.1
  refine ⟨bit,sw,lf,?_⟩
  intro cmp
  have term : V r allow m v (terminalSlot r (d endLabel) s.terminalIndex (sendDefect d s.defect)) :=
    rebuild_terminal d s.defect slot cmp (fun hh => donor_eq hr (factor_cap cap) hh) lf
  have pickEq : picked (sendSlot d s) = d (picked s) := by
    cases z : s.startAtMate <;> simp [picked,sendSlot,sendNode,z]
  refine ⟨bit,by simpa [sendSlot,relabel] using len,?_,True.intro⟩
  apply (route_iff ..).mpr
  change Walk r allow m v (picked (sendSlot d s)) (relabel d s.steps) ∧
    V r allow m v (terminalSlot r (endpoint (picked (sendSlot d s)) (relabel d s.steps))
        s.terminalIndex (sendDefect d s.defect))
  rw [pickEq,endpoint_relabel]
  exact ⟨seedEq.symm ▸ sw,term⟩

def roleOf (b : Bool) (n : Node) := if b then n.mate else n.owner

def FuncResult (r : Nat) (allow : Tag → Prop) (ts : Tiles) (v : W) (h : Nat → W)
    (f : FunctionalityCertificate) : Prop :=
  let f' := sendFunc (donor v h r) f
  let m := markNode f'.anchor
  Holds r allow m v (markedNode f'.anchor f'.bit) ∧
  Holds r allow m v (neighbor ts f'.anchor f'.b f'.dir) ∧
  Holds r allow m v (neighbor ts f'.anchor f'.c f'.dir) ∧
  roleOf f'.distinguishMate f'.b ≠ roleOf f'.distinguishMate f'.c ∧
  (Compressed r v → Holds r allow m v (f'.query ts))

theorem functionality_source {r allow mark v h l k seed} (hr : 0 < r)
    (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k)) (ts : Tiles) (f : FunctionalityCertificate)
    (ok : V r allow mark (l ++ v.flatMap h ++ k) (f.query ts))
    (start : Supplies v h r seed f.anchor.owner) (guard : Guard r allow mark v seed 6) :
    FuncResult r allow ts v h f := by
  let d := donor v h r
  let m := markNode (sendNode d f.anchor)
  have supplies (n : Node) (use : n=f.anchor ∨ n=f.b ∨ n=f.c) : UniformOn r v h d (roles n) := by
    intro a ha
    have reach := P455CertificateReach.functionality_reach cap ts f ok use
      (show a=n.owner ∨ a=n.mate by simpa [roles] using ha)
    exact (lift_near hr cap start guard (by decide : 2 ≤ 6) reach).1
  have union (n : Node) (use : n=f.anchor ∨ n=f.b ∨ n=f.c) :
      UniformOn r v h d (roles f.anchor ++ roles n) := by
    intro a ha
    rcases List.mem_append.mp ha with h1|h2
    · exact supplies _ (.inl rfl) _ h1
    · exact supplies n use _ h2
  have bit := reflect_markedNode hr cap f.anchor f.bit (supplies _ (.inl rfl)) m (.inl ⟨rfl,rfl⟩) ok.1
  have b := neighbor_remark (dst := m) (reflect_neighbor hr cap ts f.anchor f.b f.dir (union _ (.inr (.inl rfl))) ok.2.1)
  have c := neighbor_remark (dst := m) (reflect_neighbor hr cap ts f.anchor f.c f.dir (union _ (.inr (.inr rfl))) ok.2.2.1)
  have rb (n : Node) : roleOf f.distinguishMate n ∈ roles n := by
    cases e : f.distinguishMate <;> simp [roleOf,roles,e]
  have sb := supplies f.b (.inr (.inl rfl)) _ (rb f.b)
  have sc := supplies f.c (.inr (.inr rfl)) _ (rb f.c)
  have neat : d (roleOf f.distinguishMate f.b) ≠ d (roleOf f.distinguishMate f.c) := by
    intro eq
    have same := Problem455SameDonor.sameDonor v h _ sb.1 (factor_cap cap) _ _ sb.2 (eq.symm ▸ sc.2)
    apply ok.2.2.2.1
    exact Problem455Swap.sameBlock_factor ⟨l,k,rfl⟩
      (fun a => by rw [Problem455BlockBridge.occ_count]; exact cap a) same
  have mapped (n : Node) : roleOf f.distinguishMate (sendNode d n) = d (roleOf f.distinguishMate n) := by
    cases f.distinguishMate <;> rfl
  have neq : roleOf f.distinguishMate (sendNode d f.b) ≠ roleOf f.distinguishMate (sendNode d f.c) := by
    simpa only [mapped] using neat
  exact ⟨bit,b,c,neq,fun cmp => ⟨bit,b,c,compressed_separates cmp neq,True.intro⟩⟩

end P455SourceFamilies
