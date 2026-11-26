import Problem455SingletonEvaluation
import Problem455FirstTesters




namespace P455GuardProduct
open P455Witness P455SlotProduct P455SourceFamilies P455CrossedSupport
open P455PortReflection P455SlotSaturation P455DefectRename P455FirstRewrite
open Problem455.Slots
abbrev W := List Nat

inductive Guard where
  | slot (s : SlotCertificate)
  | func (f : FunctionalityCertificate)

def Guard.anchor : Guard → Node | .slot s => s.anchor | .func f => f.anchor
def Guard.bit : Guard → Bool | .slot s => s.bit | .func f => f.bit
def Guard.isFunc : Guard → Bool | .slot _ => false | .func _ => true
def Guard.query (g : Guard) (r : Nat) (ts : Tiles) : Query := match g with
  | .slot s => s.query r | .func f => f.query ts
def Guard.withBit (g : Guard) (b : Bool) : Guard := match g with
  | .slot s => .slot {s with bit := b} | .func f => .func {f with bit := b}
def width (isFunc : Bool) : Nat := if isFunc then 8 else 43
def words (r : Nat) (kind : Bool) := Problem455Finite.wordsUpTo (List.range (width kind)) (width kind*r)
structure Index (r : Nat) (allow : Tag → Prop) (ts : Tiles) where
  kind : Bool
  pos : Fin (words r kind).length
  a : Fin (width kind)
  b : Fin (width kind)
  cap : P455Closure.Cap r ((words r kind).get pos)
  accepted : ∃ g : Guard, g.isFunc = kind ∧ g.anchor.owner = a.val ∧ g.anchor.mate = b.val ∧
    Holds r allow (pairMark a b) ((words r kind).get pos) (g.query r ts)

def Index.T (i : Index r allow ts) := (words r i.kind).get i.pos
def Index.R (i : Index r allow ts) := rules r allow (pairMark i.a i.b)
abbrev Carrier (r : Nat) (allow : Tag → Prop) (ts : Tiles) :=
  (i : Index r allow ts) → P455Quotient.Q i.R i.T

def product (r : Nat) (allow : Tag → Prop) (ts : Tiles) : Model (Carrier r allow ts) where
  op := fun u v i => P455Quotient.mul i.R i.cap (u i) (v i)
  unit := fun i => P455Quotient.ofWord i.R i.T []
  assoc := fun u v w => funext (fun i => P455Quotient.mul_assoc i.R i.cap (u i) (v i) (w i))
  oneL := fun u => funext (fun i => (P455Quotient.unit_laws i.R i.cap (u i)).1)
  oneR := fun u => funext (fun i => (P455Quotient.unit_laws i.R i.cap (u i)).2)

theorem observed {r allow ts u w} (valid : (product r allow ts).Valid u w)
    (i : Index r allow ts) (h : Nat → W) :
    P455Quotient.ofWord i.R i.T (u.flatMap h) = P455Quotient.ofWord i.R i.T (w.flatMap h) := by
  let val : Nat → Carrier r allow ts := fun x j => P455Quotient.ofWord j.R j.T (h x)
  have comp (z : W) : (product r allow ts).eval val z i = P455Quotient.ofWord i.R i.T (z.flatMap h) := by
    induction z with
    | nil => rfl
    | cons a z ih =>
      change P455Quotient.mul i.R i.cap (val a i) _ = _
      rw [ih]; rfl
  exact (comp u).symm.trans ((congrFun (valid val) i).trans (comp w))

theorem test_projects {r allow ts u w} (valid : (product r allow ts).Valid u w)
    (keep : W) {x y : Nat} (ho : x ∈ keep) (hm : y ∈ keep)
    (g : Guard) (n : Bool) (kind : g.isFunc = n) (len : keep.length ≤ width n)
    (xa : g.anchor.owner = keep.idxOf x) (yb : g.anchor.mate = keep.idxOf y)
    (capT : P455Closure.Cap r ((select keep u).map keep.idxOf))
    (test : Holds r allow (markNode g.anchor) ((select keep u).map keep.idxOf) (g.query r ts)) :
    select [x,y] u = select [x,y] w := by
  let T := (select keep u).map keep.idxOf
  have labels : ∀ a ∈ T, a < width n := by
    intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact Nat.lt_of_lt_of_le (List.idxOf_lt_length (kept hb)) len
  obtain ⟨j,eq⟩ := List.get_of_mem (Problem455Finite.covered (List.range (width n)) _ T
    (capped_length _ T capT labels) (fun a ha => List.mem_range.mpr (labels a ha)))
  let a : Fin (width n) := ⟨keep.idxOf x, Nat.lt_of_lt_of_le (List.idxOf_lt_length ho) len⟩
  let b : Fin (width n) := ⟨keep.idxOf y, Nat.lt_of_lt_of_le (List.idxOf_lt_length hm) len⟩
  have fm : markNode g.anchor = pairMark a b := by unfold markNode pairMark; rw [xa,yb]
  let i : Index r allow ts := ⟨n,j,a,b,eq.symm ▸ capT,g,kind,xa,yb,eq.symm ▸ (fm ▸ test)⟩
  have coord := observed valid i (image keep)
  rw [image_word,image_word] at coord
  have eqT : T = i.T := eq.symm
  change P455Quotient.ofWord i.R i.T T = _ at coord
  rw [eqT] at coord
  have good : P455Quotient.Good i.R i.T i.T := ⟨_,.refl _,[],[],by simp⟩
  have path := ((P455Quotient.same_nonzero_class i.R good).mp coord).2
  have pr : select [a.val,b.val] i.T = select [a.val,b.val] ((select keep w).map keep.idxOf) :=
    path.transport (P := fun z => select [a.val,b.val] i.T = select [a.val,b.val] z) rfl
      (fun mv old => old.trans (mv.marked_proj _ _ ⟨rfl,rfl⟩))
  rw [← eqT] at pr
  change select [keep.idxOf x,keep.idxOf y] ((select keep u).map keep.idxOf) = _ at pr
  rw [← binary_select_map keep u ho hm, ← binary_select_map keep w ho hm] at pr
  have k (z : W) (c : Nat) (hc : c ∈ select [x,y] z) : c ∈ keep := by
    rcases (by simpa using kept hc : c=x ∨ c=y) with e|e
    · exact e ▸ ho
    · exact e ▸ hm
  have decoded := congrArg (List.map (decode keep)) pr
  simpa only [decode_map (k u),decode_map (k w)] using decoded

private theorem free_all (qs : List Query) (all : ∀ q ∈ qs, markFree q = true) : markFree (allQ qs) = true := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [allQ,markFree,all q (by simp),ih (fun t ht => all t (by simp [ht]))]

private theorem free_sep (xs : W) : markFree (differentBlocks xs) = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have every : markFree (allQ (xs.map (Query.separate a))) = true := by
      apply free_all; intro q h; obtain ⟨_,_,rfl⟩ := List.mem_map.mp h; rfl
    simp [differentBlocks,markFree,ih,every]

theorem free_term (r o i : Nat) (d : SlotDefect) : markFree (terminalSlot r o i d) = true := by
  cases d with
  | deficient => rfl
  | overflow xs =>
    have terms : markFree (allQ (xs.map fun a => Query.both (.count a r) (.slot o i a))) = true := by
      apply free_all; intro q h; obtain ⟨_,_,rfl⟩ := List.mem_map.mp h; rfl
    simp [terminalSlot,allQ,markFree,terms,free_sep]

private theorem free_route (s : SlotCertificate) (r a : Nat) (p : List P455Paths.Step) :
    markFree (route r a p (fun o => terminalSlot r o s.terminalIndex s.defect)) = true := by
  induction p generalizing a with
  | nil => exact free_term .. 
  | cons bc p ih =>
    have ct : markFree (contact r a bc.1 bc.2) = true := by
      cases c : bc.2 with
      | record tag rev => cases rev <;> rfl
      | port phase rev => rfl
    simp [route,markFree,ct,ih]

def Guard.tail (g : Guard) (r : Nat) (ts : Tiles) : Query := match g with
  | .slot s => allQ [.fixed (s.steps.length ≤ 6),route r (picked s) s.steps (fun o => terminalSlot r o s.terminalIndex s.defect)]
  | .func f => allQ [neighbor ts f.anchor f.b f.dir,neighbor ts f.anchor f.c f.dir,
      .separate (if f.distinguishMate then f.b.mate else f.b.owner) (if f.distinguishMate then f.c.mate else f.c.owner)]

theorem tail_free (g : Guard) (r : Nat) (ts : Tiles) : markFree (g.tail r ts) = true := by
  cases g with
  | slot s => simp [Guard.tail,allQ,markFree,free_route]
  | func f => simp [Guard.tail,allQ,markFree,free_neighbor]

theorem split_query (g : Guard) (r : Nat) (ts : Tiles) (b : Bool) :
    (g.withBit b).query r ts = .both (markedNode g.anchor b) (g.tail r ts) := by cases g <;> rfl

theorem replay {r allow ts u v} (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u v)
    (g : Guard) (ok : Holds r allow (markNode g.anchor) u (g.query r ts)) :
    ∃ b, Holds r allow (markNode g.anchor) v ((g.withBit b).query r ts) := by
  have same : g.withBit g.bit = g := by cases g <;> rfl
  have parts := ok
  rw [← same,split_query] at parts
  obtain ⟨ne,length,tag,_,eq⟩ := parts.1
  have rec : Holds r allow noMark u (typedNode g.anchor) := ⟨ne,length,tag,g.bit,eq⟩
  have obs := path.transport rec (fun mv old => (query_invariant mv _).mp old)
  obtain ⟨ne',length',tag',b,eq'⟩ := obs
  have tail : Holds r allow noMark u (g.tail r ts) := remark (tail_free ..) parts.2
  have last := path.transport tail (fun mv old => (query_invariant mv _).mp old)
  refine ⟨b,?_⟩
  rw [split_query]
  exact ⟨⟨ne',length',tag',.inl ⟨rfl,rfl⟩,eq'⟩,remark (tail_free ..) last⟩

end P455GuardProduct
