import Problem455EdgeProjection
import Problem455FirstTesters
import Problem455SlotProduct




namespace P455EdgeProduct
open P455Witness P455Paths P455EdgeSource P455EdgeProjection P455PortReflection P455CertificateReach
open P455DefectRename P455SlotProduct Problem455.Slots
open P455FirstRewrite (Model)
abbrev W := List Nat

def words (r : Nat) := Problem455Finite.wordsUpTo (List.range 14) (14*r)

def marks (a b c d : Nat) (x y : Nat) := (x = a ∧ y = b) ∨ (x = c ∧ y = d)

structure Index (r : Nat) (allow : Tag → Prop) (ts : Tiles) where
  num : Fin (words r).length
  a : Fin 14
  b : Fin 14
  c : Fin 14
  d : Fin 14
  cap : P455Closure.Cap r ((words r).get num)
  test : ∃ e : EdgeCertificate, e.a.owner = a.val ∧ e.a.mate = b.val ∧
    e.b.owner = c.val ∧ e.b.mate = d.val ∧
    (∀ x : Nat, x ∈ (words r).get num ↔ x ∈ names ts e) ∧
    Holds r allow (marks a b c d) ((words r).get num) (e.query ts)

def Index.T (i : Index r allow ts) := (words r).get i.num
def Index.R (i : Index r allow ts) := rules r allow (marks i.a i.b i.c i.d)
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

theorem names_send (f : Nat → Nat) (ts : Tiles) (e : EdgeCertificate) :
    names ts (sendEdge f e) = (names ts e).map f := by
  cases rr : ts.right e.a.tag <;> cases dd : ts.bottom e.a.tag <;>
    cases ll : ts.left e.a.tag <;> cases uu : ts.top e.a.tag <;>
    simp [names,nodes,candidates,sendEdge,sendNode,roles,rr,dd,ll,uu,List.filter_cons]

/-- At either endpoint of a true identity the complete 1,0 edge test
    forces both marked binary projections to agree with the opposite
    word. The opposite word is arbitrary. -/
theorem endpoint_observed {r allow mark ts u w} (cap : P455Closure.Cap r u)
    (valid : (product r allow ts).Valid u w) (e : EdgeCertificate)
    (ok : Holds r allow mark u (e.query ts)) :
    select [e.a.owner,e.a.mate] u = select [e.a.owner,e.a.mate] w ∧
    select [e.b.owner,e.b.mate] u = select [e.b.owner,e.b.mate] w := by
  let keep := names ts e
  let T := template ts e u
  let f := keep.idxOf
  obtain ⟨ct,namesT,cert⟩ := canonical_edge cap ts e ok
  have hr : 0 < r := by have h : e.a.tag.length + 16 = r := ok.1.2.1; omega
  have exactT (x : Nat) : x ∈ T ↔ x ∈ names ts (sendEdge f e) := by
    rw [names_send]
    constructor
    · intro h; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
      exact List.mem_map_of_mem (kept hz)
    · intro h; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
      apply List.mem_map_of_mem
      apply List.count_pos_iff.mp
      change 0 < (select keep u).count z
      rw [P455DefectProjection.select_count keep u z hz,saturated cap ts e ok hz]
      exact hr
  have low (a : Nat) (h : a ∈ keep) : f a < 14 :=
    Nat.lt_of_lt_of_le (List.idxOf_lt_length h) (names_bound ts e)
  have ao := covered (ts := ts) (e := e) .anchor e.a.owner (by simp [roles])
  have am := covered (ts := ts) (e := e) .anchor e.a.mate (by simp [roles])
  have bo := covered (ts := ts) (e := e) .successor e.b.owner (by simp [roles])
  have bm := covered (ts := ts) (e := e) .successor e.b.mate (by simp [roles])
  let a : Fin 14 := ⟨_,low _ ao⟩
  let b : Fin 14 := ⟨_,low _ am⟩
  let c : Fin 14 := ⟨_,low _ bo⟩
  let d : Fin 14 := ⟨_,low _ bm⟩
  have lowT (x : Nat) (h : x ∈ T) := (namesT x h).1
  obtain ⟨j,eq⟩ := List.get_of_mem (Problem455Finite.covered (List.range 14) _ T
    (capped_length _ T ct lowT) (fun x h => List.mem_range.mpr (lowT x h)))
  let i : Index r allow ts := ⟨j,a,b,c,d,eq.symm ▸ ct,sendEdge f e,rfl,rfl,rfl,rfl,
    eq.symm ▸ exactT,eq.symm ▸ cert⟩
  have comp := observed valid i (image keep)
  rw [image_word,image_word] at comp
  have sameT : T = i.T := eq.symm
  change P455Quotient.ofWord i.R i.T T = _ at comp
  rw [sameT] at comp
  have good : P455Quotient.Good i.R i.T i.T := ⟨_,.refl _,[],[],by simp⟩
  have path := ((P455Quotient.same_nonzero_class i.R good).mp comp).2
  have recover (x y : Nat) (hx : x ∈ keep) (hy : y ∈ keep) (markPair : marks a b c d (f x) (f y)) :
      select [x,y] u = select [x,y] w := by
    have pr := path.transport (P := fun z => select [f x,f y] i.T = select [f x,f y] z) rfl
      (fun mv old => old.trans (mv.marked_proj _ _ markPair))
    rw [← sameT] at pr
    change select [keep.idxOf x,keep.idxOf y] ((select keep u).map keep.idxOf) = _ at pr
    rw [← binary_select_map keep u hx hy,← binary_select_map keep w hx hy] at pr
    have k (z : W) (j : Nat) (mem : j ∈ select [x,y] z) : j ∈ keep := by
      rcases (by simpa using kept mem : j=x ∨ j=y) with rfl|rfl <;> assumption
    simpa only [decode_map (k u),decode_map (k w)] using congrArg (List.map (decode keep)) pr
  exact ⟨recover _ _ ao am (.inl ⟨rfl,rfl⟩),recover _ _ bo bm (.inr ⟨rfl,rfl⟩)⟩

end P455EdgeProduct
