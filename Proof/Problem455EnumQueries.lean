import Problem455EnumBasic
namespace P455Enum
open P455Witness Problem455.Slots Problem455Swap
theorem linkNames {r a b} {w : List Nat} (hr : 0<r) (edge : Link r w a b) : a∈w ∧ b∈w := by
  have l := out_bound a b (b+1) (by omega) w
  have u := in_bound a (a+1) b (by omega) w
  have t := tail_occ_le b w
  unfold Link at edge
  simp only [Problem455BlockBridge.occ_count] at l u t
  exact ⟨List.count_pos_iff.mp (by omega),List.count_pos_iff.mp (by omega)⟩

instance linkD (r) (w : List Nat) (a b) : Decidable (Link r w a b) := by unfold Link; infer_instance

def stable (r) (w s : List Nat) := ∀ a∈s, ∀ b∈w, (Link r w a b ∨ Link r w b a) → b∈s
instance stableD (r w s) : Decidable (stable r w s) := by unfold stable; infer_instance

def joinedD {r} (hr : 0<r) (w : List Nat) (x y : Nat) : Decidable (Joined (Link r w) x y) :=
  let vertices := x::w
  let subsets := Problem455Finite.wordsUpTo vertices vertices.length
  decidable_of_iff (∀ s∈subsets, x∈s → stable r w s → y∈s) (by
    constructor
    · intro closed
      classical
      let s := vertices.filter (fun a => decide (Joined (Link r w) x a))
      have mem {a} : a∈s ↔ a∈vertices ∧ Joined (Link r w) x a := by simp [s]
      have ins : s∈subsets := Problem455Finite.covered _ _ _ (List.length_filter_le ..) (fun a m => (mem.mp m).1)
      have st : stable r w s := fun a ma b mb ed =>
        mem.mpr ⟨List.mem_cons_of_mem _ mb,.extend (mem.mp ma).2 ed⟩
      exact (mem.mp (closed s ins (mem.mpr ⟨List.mem_cons_self,.refl _⟩) st)).2
    · intro path s _ start st
      induction path with
      | refl => exact start
      | extend p ed ih =>
        exact st _ ih _ (ed.elim (fun h => (linkNames hr h).2) (fun h => (linkNames hr h).1)) ed)

def blockD {r} (hr : 0<r) (w : List Nat) (a b) : Decidable (SameBlock r w a b) := by
  letI := joinedD hr w a b
  unfold SameBlock
  infer_instance

instance seesD (w pat) : Decidable (sees w pat) := by unfold sees; infer_instance
instance slotStartD (i) : Decidable (slotStart i) := by unfold slotStart; infer_instance
instance occupiesD (w o i a) : Decidable (occupies w o i a) :=
  @search _ ((events w).map Prod.snd) _ (fun _ => seesD ..) (fun j h =>
     List.mem_map.mpr ⟨(a,j),h.subset (by simp),rfl⟩)
instance typedD (w a b tag) : Decidable (typed w a b tag) := by unfold typed; infer_instance

/-- Only static propositions require a certificate-specific decision procedure. -/
def Stat : Query → Type
  | .fixed p => Decidable p
  | .both a b | .either a b => Stat a × Stat b
  | _ => Unit
def holdsD {r} (hr : 0<r) (allow : Tag → Prop) [DecidablePred allow]
    (mark : Marking) [DecidableRel mark] (w : List Nat) : (q : Query) → Stat q → Decidable (Holds r allow mark w q)
  | .fixed _, s => s
  | .count ..,_ | .deficient ..,_ | .record ..,_ | .markedBit ..,_ | .order ..,_ | .slot ..,_ => by unfold Holds; infer_instance
  | .separate a b,_ => by letI := blockD hr w a b; unfold Holds; infer_instance
  | .both a b,s | .either a b,s => by
    letI := holdsD hr allow mark w a s.1
    letI := holdsD hr allow mark w b s.2
    unfold Holds
    infer_instance

def statAll {qs : List Query} (f : ∀ q∈qs, Stat q) : Stat (allQ qs) :=
  match qs with
  | [] => isTrue trivial
  | q::_ => (f q List.mem_cons_self,statAll (fun a m => f a (List.mem_cons_of_mem _ m)))
def statMap {α} {xs : List α} (f : α→Query) (g : ∀ x, Stat (f x)) : Stat (allQ (xs.map f)) :=
  match xs with
  | [] => isTrue trivial
  | x::xs => (g x,@statMap _ xs f g)
def statAppend (xs ys : List Query) (h : Stat (allQ xs)) (k : Stat (allQ ys)) :
    Stat (allQ (xs++ys)) := match xs with
  | [] => k
  | _::xs => (h.1,statAppend xs ys h.2 k)
def statEarly (xs ys : List Nat) : Stat (earlyBefore xs ys) :=
  match xs with
  | [] => isTrue trivial
  | x::xs => statAppend _ _ (statMap (fun y=>earlier x 2 y 0) (xs:=ys) (fun _=>())) (statEarly xs ys)
def statContact (r a b) (c : ContactChoice) : Stat (contact r a b c) := by
  cases c with
  | record t rev => cases rev <;> exact ()
  | port p rev => exact (inferInstanceAs (Decidable _),(),(),(statEarly _ _,statEarly _ _),(),isTrue trivial)
def statDiff (xs : List Nat) : Stat (differentBlocks xs) :=
  match xs with
  | [] => isTrue trivial
  | _::xs => (statMap _ (fun _=>()),statDiff xs)
def statTerminal (r o i) (d : SlotDefect) : Stat (terminalSlot r o i d) := by
  cases d with
  | deficient a => exact ((),())
  | overflow xs => exact (inferInstanceAs (Decidable _),statDiff _,statMap _ (fun _=>((),())),isTrue trivial)
def statRoute (r o : Nat) (xs : List (Nat × ContactChoice)) (f : Nat→Query)
    (sf : ∀ i, Stat (f i)) : Stat (route r o xs f) :=
  match xs with
  | [] => sf o
  | (b,c)::xs => (statContact r o b c,statRoute r b xs f sf)
def statSlot (r) (s : SlotCertificate) : Stat (s.query r) :=
  ((),inferInstanceAs (Decidable _),statRoute _ _ _ _ (fun _ => statTerminal ..),isTrue trivial)
def statPort (p) (a b : Node) : Stat (orientedPort p a b) :=
  ((),(),(statEarly ..,statEarly ..),(),isTrue trivial)
def statRight (n) (a b : Node) : Stat (rightward (P455PaddedTiles.system n) a b) :=
  (horizontalD ..,statPort ..,(),isTrue trivial)
def statDown (n) (a b : Node) : Stat (downward (P455PaddedTiles.system n) a b) :=
  (verticalD ..,statPort ..)
def statNeighbor (n) (a b : Node) : (d : Dir) → Stat (neighbor (P455PaddedTiles.system n) a b d)
  | .right | .left => statRight ..
  | .down | .up => statDown ..
def statFunc (n) (f : FunctionalityCertificate) : Stat (f.query (P455PaddedTiles.system n)) :=
  ((),statNeighbor ..,statNeighbor ..,(),isTrue trivial)
def statFlag (b : Bool) {q : Query} (s : Stat q) : Stat (flagQ b q) := by cases b <;> first | exact s | exact isTrue trivial
def statEdge (n) (e : EdgeCertificate) : Stat (e.query (P455PaddedTiles.system n)) := by
  refine ((),(),?_,?_,isTrue trivial)
  · exact (statFlag _ (statRight ..),statFlag _ (statRight ..),statFlag _ (statDown ..),
      statFlag _ (statDown ..),statFlag _ (statDown ..,statRight ..),isTrue trivial)
  · unfold chosenSuccessor
    dsimp only
    split
    · exact (inferInstanceAs (Decidable _),(statPort ..,statPort ..),(),isTrue trivial)
    · exact (inferInstanceAs (Decidable _),())
end P455Enum
