import Problem455SlotProduct
import Problem455DefectRename




namespace P455SlotSaturation
open P455Witness P455Paths P455ContactLift P455OriginalWalk P455CrossedSupport
open P455SlotProduct P455SourceFamilies P455SourceTheorem P455MarkedPath
open P455DefectRename Problem455.Slots

theorem uniform_of_identity {r allow mark u w x y} (cap : P455Closure.Cap r u)
    (valid : Identity r allow u w) (flip : ClosedFlip r allow u x y)
    (changed : select [x,y] u ≠ select [x,y] w) : UniformSlots r allow mark u x y := by
  obtain ⟨tag,bit,marked⟩ := flip_anchor cap flip
  let n : Node := ⟨x,y,tag⟩
  intro t near i slot bad occ
  apply Classical.byContradiction
  intro ne
  have defic : u.count bad < r := by have := cap bad; omega
  have route : ∃ side : Bool, Near r allow mark u (if side then n.mate else n.owner) t 6 := by
    rcases near with hx | hy
    · exact ⟨false,hx⟩
    · exact ⟨true,hy⟩
  obtain ⟨side,rt⟩ := route
  obtain ⟨keep,s,len,ho,hm,sx,sy,_,kind,labels,capT,test⟩ :=
    canonical_defect cap n bit side t i bad marked rt slot occ defic
  let T := (select keep u).map keep.idxOf
  have mem : T ∈ templates r := Problem455Finite.covered _ _ _
    (capped_length 9 T capT labels) (fun a ha => List.mem_range.mpr (labels a ha))
  obtain ⟨j,eq⟩ := List.get_of_mem mem
  let a : Fin 9 := ⟨keep.idxOf x, Nat.lt_of_lt_of_le (List.idxOf_lt_length ho) len⟩
  let b : Fin 9 := ⟨keep.idxOf y, Nat.lt_of_lt_of_le (List.idxOf_lt_length hm) len⟩
  have xa : s.anchor.owner = a.val := sx
  have yb : s.anchor.mate = b.val := sy
  have fm : markNode s.anchor = pairMark a b := by
    unfold markNode pairMark
    rw [xa,yb]
  have tc : Holds r allow (pairMark a b) T (s.query r) := fm ▸ test
  let idx : Index r allow := ⟨j,a,b,eq.symm ▸ capT,
    s, keep.idxOf bad,kind,xa,yb,eq.symm ▸ tc⟩
  have proj := marked_test valid keep idx eq.symm
  change select [keep.idxOf x, keep.idxOf y] _ = select [keep.idxOf x, keep.idxOf y] _ at proj
  rw [← binary_select_map keep u ho hm, ← binary_select_map keep w ho hm] at proj
  have kept' (word : W) (c : Nat) (hc : c ∈ select [x,y] word) : c ∈ keep := by
    rcases (by simpa using kept hc : c = x ∨ c = y) with h|h
    · exact h ▸ ho
    · exact h ▸ hm
  have decoded := congrArg (List.map (decode keep)) proj
  dsimp only [n] at decoded
  exact changed (by simpa only [decode_map (kept' u),decode_map (kept' w)] using decoded)

abbrev noMark : Marking := fun _ _ => False

theorem pull_walk {r allow mark u v} (mv : P455Closure.Move r allow noMark u v)
    (t : Nat) (p : List Step) (w : Walk r allow mark v t p) : Walk r allow mark u t p := by
  have w0 : Walk r allow noMark v t p := remark_walk t p w
  apply remark_walk (mark := noMark) t p
  clear w
  induction p generalizing t with
  | nil => trivial
  | cons bc tail ih => exact ⟨(query_invariant mv _).mpr w0.1, ih _ w0.2⟩

theorem uniform_variant {r allow mark u v x y}
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u v)
    (uf : UniformSlots r allow mark u x y) : UniformSlots r allow mark v x y := by
  apply path.transport uf
  intro w z mv old t near i slot b occ
  have pull {s} (h : Near r allow mark z s t 6) : Near r allow mark w s t 6 := by
    obtain ⟨p,wa,ep,len⟩ := h
    exact ⟨p,pull_walk mv s p wa,ep,len⟩
  exact (mv.count_eq b).symm.trans (old t (near.imp pull pull) i slot b ((mv.slot_iff t i b slot).mpr occ))

theorem crossed_at_variant {r allow mark T} (capT : P455Quotient.Cap r T)
    (u : W) (capU : P455Closure.Cap r u) (x y : Nat) (flip : ClosedFlip r allow u x y)
    (u₀ w : W) (cap₀ : P455Closure.Cap r u₀) (identity : Identity r allow u₀ w)
    (flip₀ : ClosedFlip r allow u₀ x y) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ u)
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
        Supplies v h r (d (endpoint a p)) (endpoint a p) ∧ Supplies u h r (d (endpoint a p)) (endpoint a p) :=
  crossed_gadget capT u capU x y flip
    (uniform_variant path (uniform_of_identity cap₀ identity flip₀ changed))
    h val reps live ts c valid second mate cross

end P455SlotSaturation
