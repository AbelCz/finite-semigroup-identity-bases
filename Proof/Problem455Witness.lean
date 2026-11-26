import Problem455ObservationBridge
import Problem455BlockBridge
import Problem455Quotient
import Problem455Finite





namespace P455Witness
open Problem455.Slots
abbrev W := List Nat
abbrev Tag := List Bool
abbrev Marking := Nat → Nat → Prop

/- A finite conjunction/disjunction of observations on a single word.
   A static test depends only on the chosen certificate and tile alphabet. -/
inductive Query where
  | fixed (p : Prop)
  | count (a n : Nat)
  | deficient (a : Nat)
  | record (a b : Nat) (tag : Tag)
  | markedBit (a b : Nat) (tag : Tag) (bit : Bool)
  | order (pattern : List Event)
  | slot (owner i a : Nat)
  | separate (a b : Nat)
  | both (x y : Query)
  | either (x y : Query)

def Holds (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) : Query → Prop
  | .fixed p => p
  | .count a n => w.count a = n
  | .deficient a => w.count a < r
  | .record a b tag => a ≠ b ∧ tag.length + 16 = r ∧ allow tag ∧ typed w a b tag
  | .markedBit a b tag bit => a ≠ b ∧ tag.length + 16 = r ∧ allow tag ∧ (mark a b ∨ mark b a) ∧
        select [a,b] w = profile a b tag bit
  | .order pat => (∀ e ∈ pat, e.2 ≠ r - 2) ∧ sees w pat
  | .slot o i a => slotStart i ∧ occupies w o i a
  | .separate a b => ¬ Problem455Swap.SameBlock r w a b
  | .both x y => Holds r allow mark w x ∧ Holds r allow mark w y
  | .either x y => Holds r allow mark w x ∨ Holds r allow mark w y

theorem unordered_projection {r allow mark u v} (h : P455Closure.Move r allow mark u v)
    (a b : Nat) (hm : mark a b ∨ mark b a) : select [a,b] u = select [a,b] v := by
  rcases hm with forward | reverse
  · exact h.marked_proj a b forward
  · simpa only [select_pair_symm b a] using h.marked_proj b a reverse

theorem query_invariant {r allow mark u v} (h : P455Closure.Move r allow mark u v) (q : Query) :
    Holds r allow mark u q ↔ Holds r allow mark v q := by
  induction q with
  | fixed => rfl
  | count a n => simp only [Holds, h.count_eq a]
  | deficient a => simp only [Holds, h.count_eq a]
  | record a b tag =>
    simp only [Holds]
    constructor <;> rintro ⟨ne,len,ok,t⟩
    · exact ⟨ne,len,ok,(h.typed_iff a b tag ne len).mp t⟩
    · exact ⟨ne,len,ok,(h.typed_iff a b tag ne len).mpr t⟩
  | markedBit a b tag bit =>
    simp only [Holds]
    constructor <;> rintro ⟨ne,len,ok,mk,t⟩
    · exact ⟨ne,len,ok,mk,(unordered_projection h a b mk) ▸ t⟩
    · exact ⟨ne,len,ok,mk,(unordered_projection h a b mk).symm ▸ t⟩
  | order pat =>
    constructor <;> rintro ⟨imm,t⟩
    · exact ⟨imm,(h.order_iff pat imm).mp t⟩
    · exact ⟨imm,(h.order_iff pat imm).mpr t⟩
  | slot o i a =>
    constructor <;> rintro ⟨hi,t⟩
    · exact ⟨hi,(h.slot_iff o i a hi).mp t⟩
    · exact ⟨hi,(h.slot_iff o i a hi).mpr t⟩
  | separate a b => exact not_congr (Problem455BlockBridge.move_sameBlock h a b)
  | both _ _ ih jh => exact and_congr ih jh
  | either _ _ ih jh => exact or_congr ih jh

def allQ : List Query → Query
  | [] => .fixed True
  | q :: qs => .both q (allQ qs)
def flagQ (b : Bool) (q : Query) : Query := if b then q else .fixed True
structure Node where
  owner : Nat
  mate : Nat
  tag : Tag
  deriving DecidableEq

def typedNode (n : Node) := Query.record n.owner n.mate n.tag
def markedNode (n : Node) (b : Bool) := Query.markedBit n.owner n.mate n.tag b
def earlier (a i b j : Nat) := Query.order [(a,i),(b,j)]

/-- Last early copy of every role on the left precedes the first of every role
    on the right. Indices throughout are zero-based. -/
def earlyBefore (xs ys : W) := allQ (xs.flatMap fun x => ys.map fun y => earlier x 2 y 0)
def earlyDisjoint (xs ys : W) := Query.either (earlyBefore xs ys) (earlyBefore ys xs)

inductive ContactChoice where
  | record (tag : Tag) (reverseRoles : Bool)
  | port (phase : Fin 5) (reverseOrder : Bool)

def contact (r a b : Nat) : ContactChoice → Query
  | .record tag rev => if rev then .record b a tag else .record a b tag
  | .port port rev =>
    let i := 3 + 2 * port.val
    let x := if rev then b else a
    let y := if rev then a else b
    allQ [.fixed (a ≠ b), .count a r, .count b r, earlyDisjoint [a] [b],
          .order [(x,i),(y,i),(x,i+1),(y,i+1)]]

def route (r start : Nat) (steps : List (Nat × ContactChoice)) (terminal : Nat → Query) : Query :=
  match steps with
  | [] => terminal start
  | (b,c) :: rest => .both (contact r start b c) (route r b rest terminal)

inductive SlotDefect where
  | deficient (a : Nat)
  | overflow (occupants : List Nat)

def differentBlocks : W → Query
  | [] => .fixed True
  | a :: xs => .both (allQ (xs.map (Query.separate a))) (differentBlocks xs)

def terminalSlot (r owner i : Nat) : SlotDefect → Query
  | .deficient a => .both (.slot owner i a) (.deficient a)
  | .overflow xs =>
    allQ [.fixed (xs.length = 5), differentBlocks (owner :: xs),
          allQ (xs.map fun a => .both (.count a r) (.slot owner i a))]

structure SlotCertificate where
  anchor : Node
  bit : Bool
  startAtMate : Bool
  steps : List (Nat × ContactChoice)
  terminalIndex : Nat
  defect : SlotDefect

def SlotCertificate.query (s : SlotCertificate) (r : Nat) : Query :=
  let start := if s.startAtMate then s.anchor.mate else s.anchor.owner
  allQ [markedNode s.anchor s.bit, .fixed (s.steps.length ≤ 6),
        route r start s.steps (fun o => terminalSlot r o s.terminalIndex s.defect)]

/-- All data from machine tiles are fixed independently of the word. -/
structure Tiles where
  horizontal : Tag → Tag → Prop
  vertical : Tag → Tag → Prop
  left : Tag → Bool
  right : Tag → Bool
  top : Tag → Bool
  bottom : Tag → Bool
  oddColumn : Tag → Bool
  oddRow : Tag → Bool

def orientedPort (phase : Nat) (a b : Node) : Query :=
  let i := 3 + 2 * phase
  let x := a.owner; let y := a.mate; let z := b.owner; let t := b.mate
  allQ [typedNode a, typedNode b, earlyDisjoint [x,y] [z,t],
        .order [(x,i),(y,i),(z,i),(t,i),(x,i+1),(y,i+1),(z,i+1),(t,i+1)]]

inductive Dir | right | left | down | up

def rightward (ts : Tiles) (a b : Node) :=
  allQ [.fixed (ts.horizontal a.tag b.tag), orientedPort (if ts.oddColumn a.tag then 1 else 0) a b,
        earlier a.owner (13+a.tag.length) b.owner (13+a.tag.length)]

def downward (ts : Tiles) (a b : Node) : Query :=
  .both (.fixed (ts.vertical a.tag b.tag))
    (orientedPort (if ts.oddRow a.tag then 3 else 2) a b)

def neighbor (ts : Tiles) (a b : Node) : Dir → Query
  | .right => rightward ts a b
  | .left => rightward ts b a
  | .down => downward ts a b
  | .up => downward ts b a

structure FunctionalityCertificate where
  anchor : Node
  bit : Bool
  b : Node
  c : Node
  dir : Dir
  distinguishMate : Bool

def FunctionalityCertificate.query (f : FunctionalityCertificate) (ts : Tiles) :=
  let role := fun n : Node => if f.distinguishMate then n.mate else n.owner
  allQ [markedNode f.anchor f.bit, neighbor ts f.anchor f.b f.dir,
        neighbor ts f.anchor f.c f.dir, .separate (role f.b) (role f.c)]

structure EdgeCertificate where
  a : Node
  b : Node
  right : Node
  left : Node
  down : Node
  up : Node
  diagonal : Node

def endOfRow (ts : Tiles) (a : Node) :=
  if ts.oddRow a.tag then ts.left a.tag else ts.right a.tag

def localCert (ts : Tiles) (e : EdgeCertificate) :=
  let a := e.a
  allQ [flagQ (!ts.right a.tag) (rightward ts a e.right),
        flagQ (!ts.left a.tag) (rightward ts e.left a),
        flagQ (!ts.bottom a.tag) (downward ts a e.down),
        flagQ (!ts.top a.tag) (downward ts e.up a),
        flagQ (!ts.right a.tag && !ts.bottom a.tag)
          (.both (downward ts e.right e.diagonal) (rightward ts e.down e.diagonal))]

def chosenSuccessor (ts : Tiles) (e : EdgeCertificate) : Query :=
  let a := e.a; let b := e.b
  if endOfRow ts a && ts.bottom a.tag then
    allQ [.fixed ((ts.top b.tag && ts.left b.tag && !ts.oddRow b.tag && !ts.oddColumn b.tag) = true),
          .either (orientedPort 4 a b) (orientedPort 4 b a), earlier b.owner 0 a.owner 0]
  else
    let next := if endOfRow ts a then e.down else if ts.oddRow a.tag then e.left else e.right
    .both (.fixed (next = b)) (earlier a.owner 0 b.owner 0)

def EdgeCertificate.query (e : EdgeCertificate) (ts : Tiles) :=
  allQ [markedNode e.a true, markedNode e.b false, localCert ts e, chosenSuccessor ts e]

inductive Certificate where
  | slot (s : SlotCertificate)
  | functionality (f : FunctionalityCertificate)
  | edge (e : EdgeCertificate)

def Certificate.query (c : Certificate) (r : Nat) (ts : Tiles) :=
  match c with
  | .slot s => s.query r
  | .functionality f => f.query ts
  | .edge e => e.query ts

abbrev rules := Problem455Finite.rules

/-- Every enclosing variant keeps the same designated certificate, even when
    a chosen literal representative (or the whole product) is a proper factor. -/
theorem every_variant {r allow mark T w} (path : P455Quotient.Variant (rules r allow mark) T w)
    (c : Certificate) (ts : Tiles) :
    Holds r allow mark T (c.query r ts) → Holds r allow mark w (c.query r ts) := by
  intro h
  exact path.transport h (fun mv old => (query_invariant mv _).mp old)

theorem arbitrary_reps_designated {r allow mark T} (cap : P455Quotient.Cap r T)
    {β : Type} (val : β → P455Quotient.Q (rules r allow mark) T) (v : List β)
    (h : β → W) (reps : ∀ x ∈ v, P455Quotient.ofWord (rules r allow mark) T (h x) = val x)
    (live : P455Quotient.eval (rules r allow mark) cap val v ≠ P455Quotient.zero (rules r allow mark) T)
    (c : Certificate) (ts : Tiles) (initial : Holds r allow mark T (c.query r ts)) :
    ∃ w l t, P455Quotient.Variant (rules r allow mark) T w ∧
      w = l ++ v.flatMap h ++ t ∧ Holds r allow mark w (c.query r ts) := by
  apply P455Quotient.designated (rules r allow mark) cap val v h reps live _ initial
  exact fun mv old => (query_invariant mv _).mp old

end P455Witness
