import Problem455GuardRename
import Problem455GuardSubproduct
import Problem455SupportBound



namespace P455ActualGuards
open P455Witness P455SourceFamilies P455GuardProduct P455SingletonEvaluation
open P455SlotSaturation P455CrossedSupport Problem455.Slots P455Paths P455SupportBound
abbrev W := List Nat

theorem matched_change {x y u w} (n : Node) (m : Matches n x y)
    (diff : select [x,y] u ≠ select [x,y] w) : select [n.owner,n.mate] u ≠ select [n.owner,n.mate] w := by
  rcases m with ⟨a,b⟩|⟨a,b⟩
  · simpa only [a,b] using diff
  · simpa only [a,b,select_pair_symm y x] using diff

theorem no_guard {r allow ts u₀ w v x y} (cap₀ : P455Closure.Cap r u₀)
    (identity : (product r allow ts).Valid u₀ w)
    (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ v)
    (g : Guard) (anchor : Matches g.anchor x y) :
    ¬ Holds r allow (markNode g.anchor) v (g.query r ts) := by
  intro bad
  obtain ⟨b,back⟩ := replay (path.symm P455Closure.Move.symm) g bad
  let c := g.withBit b
  have same : c.anchor = g.anchor := by cases g <;> rfl
  have q : Holds r allow (markNode c.anchor) u₀ (c.query r ts) := same.symm ▸ back
  obtain ⟨keep,f,len,ho,hm,kind,ax,ay,capT,read⟩ := P455GuardRename.bounded_guard cap₀ ts c q
  exact (matched_change c.anchor (same ▸ anchor) changed)
    (test_projects identity keep ho hm f c.isFunc kind len ax ay capT read)

theorem capacity {r allow mark ts u₀ w v x y} (cap₀ : P455Closure.Cap r u₀)
    (identity : (product r allow ts).Valid u₀ w)
    (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ v)
    (flip₀ : ClosedFlip r allow u₀ x y) (capV : P455Closure.Cap r v) (flipV : ClosedFlip r allow v x y)
    (cmp : Compressed r v) : Capacity r allow mark v x y 4 := by
  have unif : UniformSlots r allow mark v x y :=
    uniform_variant path (P455GuardSubproduct.uniform cap₀ identity flip₀ changed)
  apply capacity_of_no_overflow unif cmp
  intro t ball i sl xs read
  obtain ⟨tag,bit,marked⟩ := P455SlotProduct.flip_anchor capV flipV
  let n : Node := ⟨x,y,tag⟩
  have hit : ∃ side : Bool, Near r allow mark v (if side then n.mate else n.owner) t 6 :=
    ball.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  obtain ⟨side,p,walk,ep,len⟩ := hit
  let s : SlotCertificate := ⟨n,bit,side,p,i,.overflow xs⟩
  apply no_guard cap₀ identity changed path (.slot s) (.inl ⟨rfl,rfl⟩)
  refine ⟨marked,len,?_,True.intro⟩
  apply (route_iff ..).mpr
  exact ⟨remark_walk _ _ walk,ep.symm ▸ P455PortReflection.remark (P455GuardProduct.free_term r t i (.overflow xs)) read⟩

def EdgeViolation (r : Nat) (allow : Tag → Prop) (ts : Tiles) (v : W) (x y : Nat) :=
  ∃ (e : EdgeCertificate) (s : Bool), Matches (markedRecord (.edge e) s) x y ∧
    Holds r allow (P455SourceTheorem.sourceMarks id (.edge e)) v (e.query ts)

theorem only_edge {r allow ts u₀ w v x y} (cap₀ : P455Closure.Cap r u₀)
    (identity : (product r allow ts).Valid u₀ w)
    (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ v)
    (bad : Violation r allow ts v x y) : EdgeViolation r allow ts v x y := by
  obtain ⟨c,s,anchor,read⟩ := bad
  cases c with
  | slot p => exact False.elim (no_guard cap₀ identity changed path (.slot p) anchor read)
  | functionality f => exact False.elim (no_guard cap₀ identity changed path (.func f) anchor read)
  | edge e => exact ⟨e,s,anchor,read⟩

end P455ActualGuards
