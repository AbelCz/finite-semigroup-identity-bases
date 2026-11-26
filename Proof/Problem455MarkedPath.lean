import Problem455CrossedSupport
import Problem455Compression




namespace P455MarkedPath
open P455Witness P455Paths P455ContactLift P455SourceFamilies P455SourceTheorem
open P455CrossedSupport P455OriginalWalk P455Compression

noncomputable def ruleWord (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y : Nat) :=
  small u (retained r allow mark u x y)

/-- A source statement independent of any arbitrary donor map or proposed
    walk in the source. All ordered comparisons and all witness labels in its
    query are the result of the three concrete tester proofs. -/
theorem crossed_gadget {r allow mark T} (capT : P455Quotient.Cap r T)
    (u : W) (capU : P455Closure.Cap r u) (x y : Nat) (flip : ClosedFlip r allow u x y)
    (uniform : UniformSlots r allow mark u x y)
    (h : Nat → W) (val : Nat → P455Quotient.Q (rules r allow mark) T)
    (reps : ∀ a ∈ ruleWord r allow mark u x y, P455Quotient.ofWord (rules r allow mark) T (h a) = val a)
    (live : P455Quotient.eval (rules r allow mark) capT val (ruleWord r allow mark u x y) ≠
            P455Quotient.zero (rules r allow mark) T)
    (ts : Tiles) (c : Certificate) (valid : Holds r allow mark T (c.query r ts))
    (second mate : Bool) (cross : Crosses (markedRecord c second) h x y) :
    let names := retained r allow mark u x y
    let v := ruleWord r allow mark u x y
    let d := donor v h r
    let a := startLabel c second mate
    ∃ seed z l k, (seed = x ∨ seed = y) ∧ Supplies v h r seed a ∧
      P455Quotient.Variant (rules r allow mark) T z ∧ z = l ++ v.flatMap h ++ k ∧
      Holds r allow mark z (c.query r ts) ∧ SourceEvidence r allow ts v h seed c ∧
      (Compressed r u → Holds r allow (sourceMarks d c) u ((transferred d c).query r ts)) ∧
      ∀ p : List Step, p.length ≤ 6 → Walk r allow mark z a p →
        Walk r allow mark u seed (relabel d p) ∧ endpoint seed (relabel d p) = d (endpoint a p) ∧
        (relabel d p).length = p.length ∧ d (endpoint a p) ∈ names ∧
        Supplies v h r (d (endpoint a p)) (endpoint a p) ∧ Supplies u h r (d (endpoint a p)) (endpoint a p) := by
  let names := retained r allow mark u x y
  let v := ruleWord r allow mark u x y
  let e := expand u names
  have exp : P455Retained.Expansion v e (fun a => a ∈ names) := canonical u names
  have orig : v.flatMap e = u := recover u names
  obtain ⟨hr,cx,cy,_⟩ := flip_counts capU flip
  have pos : 0 < r := by omega
  have hx : x ∈ u := List.count_pos_iff.mp (cx.symm ▸ pos)
  have hy : y ∈ u := List.count_pos_iff.mp (cy.symm ▸ pos)
  obtain ⟨seed,side,img⟩ := choose_seed c second mate cross
  have guard := actual_guard pos capU hx hy side uniform
  have ks := (guard seed (near_self _ _)).1
  have count : u.count seed = r := side.elim (fun eq => eq.symm ▸ cx) (fun eq => eq.symm ▸ cy)
  have start : Supplies v h r seed (startLabel c second mate) := ⟨(counts_retained u names seed ks).trans count,img⟩
  have cap : P455Closure.Cap r (v.flatMap e) := orig.symm ▸ capU
  have guard' : OriginalGuard r allow mark (v.flatMap e) (fun a => a ∈ names) seed 6 := orig.symm ▸ guard
  obtain ⟨z,l,k,path,eq,vw,ev,cmp,walks⟩ :=
    arbitrary_reps_original_gadget capT val v h reps live ts c valid second mate seed hr start exp cap guard'
  rw [orig] at cmp walks
  exact ⟨seed,z,l,k,side,start,path,eq,vw,ev,cmp,walks⟩

end P455MarkedPath
