import Problem455GuardProduct




namespace P455GuardSubproduct
open P455Witness P455SlotProduct P455GuardProduct P455DefectProjection
open P455FirstRewrite
abbrev W := List Nat

theorem letters {A : W} {w : W} {k : Nat} (mem : w ∈ Problem455Finite.wordsUpTo A k) :
    ∀ a ∈ w, a ∈ A := by
  induction k generalizing w with
  | zero => simp [Problem455Finite.wordsUpTo] at mem; simp [mem]
  | succ k ih =>
    rcases List.mem_cons.mp mem with e|rest
    · simp [e]
    · obtain ⟨x,hx,m⟩ := List.mem_flatMap.mp rest
      obtain ⟨v,vm,rfl⟩ := List.mem_map.mp m
      exact fun a ha => (List.mem_cons.mp ha).elim (fun e => e ▸ hx) (ih vm a)

theorem represented {r allow ts} (i : P455SlotProduct.Index r allow) :
    ∃ j : P455GuardProduct.Index r allow ts, j.T = i.T ∧ j.a.val = i.a.val ∧ j.b.val = i.b.val := by
  obtain ⟨s,d,_,ax,ay,obs⟩ := i.test
  have pos : i.T ∈ templates r := List.get_mem ..
  have ns (a : Nat) (h : a ∈ i.T) : a < 9 := List.mem_range.mp (letters pos a h)
  have sub (a : Nat) (h : a ∈ i.T) : a < width false := by have := ns a h; change a < 43; omega
  obtain ⟨n,eq⟩ := List.get_of_mem (Problem455Finite.covered (List.range (width false)) _ i.T
    (capped_length _ _ i.cap sub) (fun a ha => List.mem_range.mpr (sub a ha)))
  let a : Fin (width false) := ⟨i.a.val,by have := i.a.isLt; change _ < 43; omega⟩
  let b : Fin (width false) := ⟨i.b.val,by have := i.b.isLt; change _ < 43; omega⟩
  let g : Guard := .slot s
  let j : P455GuardProduct.Index r allow ts := ⟨false,n,a,b,eq.symm ▸ i.cap,
    g,rfl,ax,ay,eq.symm ▸ obs⟩
  exact ⟨j,eq,rfl,rfl⟩

/-- The designated projection valuation is sufficient to force saturation.
    This version only requests validity in the full guard product and uses
    the actual bounded tester produced for the bad slot. -/
theorem uniform {r allow mark ts u w x y} (hr : P455Closure.Cap r u)
    (ident : (product r allow ts).Valid u w) (flip : P455CrossedSupport.ClosedFlip r allow u x y)
    (changed : Problem455.Slots.select [x,y] u ≠ Problem455.Slots.select [x,y] w) :
    P455CrossedSupport.UniformSlots r allow mark u x y := by
  obtain ⟨tag,bit,marked⟩ := flip_anchor hr flip
  let n : Node := ⟨x,y,tag⟩
  intro t near i slot bad occ
  apply Classical.byContradiction
  intro ne
  have lt : u.count bad < r := by have := hr bad; omega
  have route : ∃ s : Bool, P455Paths.Near r allow mark u (if s then n.mate else n.owner) t 6 :=
    near.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  obtain ⟨s,h⟩ := route
  obtain ⟨keep,c,len,ho,hm,ax,ay,_,_,_,capT,q⟩ :=
    P455DefectRename.canonical_defect hr n bit s t i bad marked h slot occ lt
  apply changed
  exact test_projects ident keep ho hm (.slot c) false rfl
    (by change keep.length ≤ 43; omega) ax ay capT q

end P455GuardSubproduct
