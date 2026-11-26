import Problem455CellClass

/- Fixed phase tokens may occur amid unrestricted fillers. This reconstructs
   literal singleton frames and simultaneous paths to arbitrary bit assignments. -/
namespace P455CellClassFrames
open P455FirstRewrite P455RectangleRank P455Closure P455ConstantLayout P455CrossedSupport
open P455Witness P455Uncrossed P455SlotSaturation Problem455.Slots
abbrev W := List Nat

def token (x y : Nat) (b : Bool) := if b then y else x
def phase (x y : Nat) (tag : Tag) := (fixedPhases tag).map (token x y)

private theorem extract_head {x : Nat} {xs w : W} (trace : (x::xs).Sublist w) :
    ∃ L K : W, w = L ++ x::K ∧ xs.Sublist K := by
  obtain ⟨a,b,rfl,inA,sub⟩ := List.cons_sublist_iff.mp trace
  obtain ⟨p,q,rfl⟩ := List.append_of_mem inA
  exact ⟨p,q++b,by simp [List.append_assoc],sub.trans (List.sublist_append_right q b)⟩

private theorem flat_eq {α β : Type} {xs : List α} {f g : α → List β}
    (eq : ∀ a ∈ xs, f a = g a) : xs.flatMap f = xs.flatMap g :=
  congrArg List.flatten (List.map_congr_left eq)

private def spelling (x y : Nat) (es : List (W × Bool)) : W := es.flatMap (fun e => e.1 ++ [token x y e.2])

private theorem interstices (x y : Nat) (bits : List Bool) (w : W)
    (trace : (bits.map (token x y)).Sublist w) :
    ∃ es K, es.map Prod.snd = bits ∧ w = spelling x y es ++ K := by
  induction bits generalizing w with
  | nil => exact ⟨[],w,rfl,rfl⟩
  | cons b bs ih =>
    obtain ⟨l,d,rfl,sub⟩ := extract_head trace
    obtain ⟨es,k,order,rfl⟩ := ih d sub
    exact ⟨(l,b)::es,k,by simp [order],by simp [spelling,List.flatMap_cons,List.append_assoc]⟩

def displayed (l : W) (x y : Nat) (m z : W) (c : Bool) :=
  l ++ P455Structural.early x y ++ m ++ Problem455.Slots.pair x y c ++ z




theorem typed_from_phases {r allow} {x y : Nat} (ne : x ≠ y) (tag : Tag) (tl : tag.length+16=r)
    (allowed : allow tag) (l m z : W) (middle : (phase x y tag).Sublist m)
    (finalPair : [x,y].Sublist z) (cap : Cap r (displayed l x y m z false)) :
    ∃ (f : Frame Nat) (k : W), f.tag=tag ∧ f.p=[x] ∧ f.q=[y] ∧ f.Valid r allow noMark ∧
      ∀ c, displayed l x y m z c = side f l k c := by
  obtain ⟨es,rest,order,midEq⟩ := interstices x y (fixedPhases tag) m middle
  obtain ⟨p,s,hz,sub⟩ := extract_head finalPair
  obtain ⟨q,k,last,_⟩ := extract_head sub
  let f : Frame Nat := ⟨x,[],[],y,tag,es,rest,p,q⟩
  have md : f.mid = spelling x y es := by
    unfold Frame.mid spelling
    apply flat_eq
    intro e _
    cases b : e.2 <;> simp [f,Frame.p,Frame.q,token,b]
  have each (c : Bool) : displayed l x y m z c = side f l k c := by
    cases c <;> simp [displayed,side,Frame.core,md,midEq,hz,last,f,Frame.early,Frame.p,Frame.q,
      Frame.pair,P455Structural.early,Problem455.Slots.pair,List.append_assoc]
  refine ⟨f,k,rfl,rfl,rfl,?_,each⟩
  apply f.valid_of_capped_shape (by change r=16+tag.length; omega) allowed order
      (by simp [f,Frame.p]) (by simp [f,Frame.q])
      (by simp [f,Frame.p,Frame.q,ne]) (by simp [noMark]) false l k
  change Cap r (side f l k false)
  rw [← each]; exact cap

theorem from_phases {r allow} {x y : Nat} (ne : x ≠ y) (tag : Tag) (tl : tag.length+16=r)
    (allowed : allow tag) (l m z : W) (middle : (phase x y tag).Sublist m)
    (finalPair : [x,y].Sublist z) (cap : Cap r (displayed l x y m z false)) :
    ∃ (f : Frame Nat) (k : W), f.p=[x] ∧ f.q=[y] ∧ f.Valid r allow noMark ∧
      ∀ c, displayed l x y m z c = side f l k c := by
  obtain ⟨f,k,_,rest⟩ := typed_from_phases ne tag tl allowed l m z middle finalPair cap
  exact ⟨f,k,rest⟩

def revise (bits : Nat → Bool) (i : Nat) (c : Bool) (j : Nat) := if j=i then c else bits j

theorem count_word (t : Nat) (middle tail : W) (bits : Nat → Bool) (x : Nat) :
    (word t middle tail bits).count x = (word t middle tail (constant false)).count x := by
  have one (i : Nat) : (mutableCell bits i).count x = (mutableCell (constant false) i).count x := by
    cases b : bits i <;> simp [mutableCell,constant,b,List.count_cons,Nat.add_comm]
  have ls (a : List Nat) : (a.flatMap (mutableCell bits)).count x =
      (a.flatMap (mutableCell (constant false))).count x := by
    induction a with
    | nil => rfl
    | cons z zs ih => simp only [List.flatMap_cons,List.count_append,ih,one]
  simp only [word,List.count_append,ls]

theorem cap_word {r t : Nat} {middle tail : W}
    (zeroCap : Cap r (word t middle tail (constant false))) (bits : Nat → Bool) :
    Cap r (word t middle tail bits) := fun x => count_word t middle tail bits x ▸ zeroCap x

theorem same_word {t : Nat} (m z : W) {s b : Nat → Bool} (agree : ∀ i<t,s i=b i) :
    word t m z s = word t m z b := by
  have eq : (List.range t).flatMap (mutableCell s) = (List.range t).flatMap (mutableCell b) := by
    apply flat_eq; intro i hi; simp [mutableCell,agree i (List.mem_range.mp hi)]
  simp only [word,eq]

def Used (t : Nat) (x y : Nat) := ∃ i<t, x=owner i ∧ y=mate i

/-- Raw rectangle data used here: each cell's prescribed fixed-phase
    tokens occur in the middle, and its two final symbols occur in order
    in the tail. No hypothesis on a mixed-word identity or rewrite. -/
structure Phases (r : Nat) (allow : Tag → Prop) (t : Nat) (m z : W) where
  tag : Nat → Tag
  length : ∀ i<t, (tag i).length+16=r
  allowed : ∀ i<t, allow (tag i)
  tokens : ∀ i<t, (phase (owner i) (mate i) (tag i)).Sublist m
  finalPair : ∀ i<t, [owner i,mate i].Sublist z
  capped : Cap r (word t m z (constant false))

theorem typed_frame {r allow t m z} (p : Phases r allow t m z) (bits : Nat → Bool) {i} (ix : i<t) :
    ∃ (f : Frame Nat) (l k : W), f.tag=p.tag i ∧ f.p=[owner i] ∧ f.q=[mate i] ∧ f.Valid r allow noMark ∧
      ∀ c, word t m z (revise bits i c) = side f l k c := by
  let lo := List.range i
  let hi := (List.range (t-(i+1))).map (fun v => i+1+v)
  have rr : List.range t = (lo ++ [i]) ++ hi := by
    conv => lhs; arg 1; rw [show t=(i+1)+(t-(i+1)) by omega]
    rw [List.range_add,List.range_succ]
  have lower : i ∉ lo := by simp [lo]
  have higher : i ∉ hi := by
    intro h; obtain ⟨v,_,eq⟩ := List.mem_map.mp h; omega
  let L := lo.flatMap privateCell
  let M := hi.flatMap privateCell ++ m ++ lo.flatMap (mutableCell bits)
  let Z := hi.flatMap (mutableCell bits) ++ z
  have fix (s : List Nat) (away : i ∉ s) (c : Bool) :
      s.flatMap (mutableCell (revise bits i c)) = s.flatMap (mutableCell bits) := by
    apply flat_eq; intro j hj
    have d : j ≠ i := fun e => away (e ▸ hj)
    simp [mutableCell,revise,d]
  have e (c : Bool) : word t m z (revise bits i c) = displayed L (owner i) (mate i) M Z c := by
    simp only [word,rr,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      fix lo lower,fix hi higher]
    cases c <;> simp [displayed,privateCell,P455Structural.early,L,M,Z,mutableCell,revise,pair,List.append_assoc]
  have mid := (p.tokens i ix).trans ((List.sublist_append_right (hi.flatMap privateCell) m).trans
    (List.sublist_append_left _ (lo.flatMap (mutableCell bits))))
  have fin : [owner i,mate i].Sublist Z := (p.finalPair i ix).trans (List.sublist_append_right _ z)
  have cp := cap_word p.capped (revise bits i false)
  obtain ⟨f,k,tag,hp,hq,valid,both⟩ := typed_from_phases (by simp [owner,mate]) (p.tag i) (p.length i ix)
    (p.allowed i ix) L M Z mid fin (e false ▸ cp)
  exact ⟨f,L,k,tag,hp,hq,valid,fun c => (e c).trans (both c)⟩

theorem frameAt {r allow t m z} (p : Phases r allow t m z) (bits : Nat → Bool) {i} (ix : i<t) :
    ∃ (f : Frame Nat) (l k : W), f.p=[owner i] ∧ f.q=[mate i] ∧ f.Valid r allow noMark ∧
      ∀ c, word t m z (revise bits i c) = side f l k c := by
  obtain ⟨f,l,k,_,rest⟩ := typed_frame p bits ix
  exact ⟨f,l,k,rest⟩

theorem typed_cell {r allow t m z} (p : Phases r allow t m z) (bits : Nat → Bool) {i} (ix : i<t)
    (mark : Marking) : Holds r allow mark (word t m z bits) (typedNode ⟨owner i,mate i,p.tag i⟩) := by
  obtain ⟨f,l,k,tag,hp,hq,valid,both⟩ := typed_frame p bits ix
  have eq : word t m z bits = side f l k (bits i) := (same_word m z
    (fun j _ => show bits j = revise bits i (bits i) j by by_cases e : j=i <;> simp [revise,e])).trans (both _)
  have cp := cap_word p.capped bits
  rw [eq] at cp ⊢
  refine ⟨by simp [owner,mate],p.length i ix,p.allowed i ix,bits i,?_⟩
  have c := f.cross_projection valid (bits i) l k cp (owner i) (mate i) (hp ▸ List.mem_cons_self) (hq ▸ List.mem_cons_self)
  rw [P455SlotProduct.profile_eq,tag] at c
  simpa [select,side] using c

theorem chain {r allow t m z} (p : Phases r allow t m z) (bits : Nat → Bool) :
    Chain r allow (Used t) (word t m z (constant false)) (word t m z bits) := by
  let active (n j : Nat) := if j<n then bits j else false
  have step (i : Nat) (ix : i<t) : Chain r allow (Used t) (word t m z (active i))
      (word t m z (active (i+1))) := by
    obtain ⟨f,l,k,hp,hq,valid,both⟩ := frameAt p (active i) ix
    have low : word t m z (active i) = side f l k false := by
      rw [← both]; apply same_word; intro j _; by_cases same : j=i <;> simp [revise,active,same]
    have high : word t m z (active (i+1)) = side f l k (bits i) := by
      rw [← both]; apply same_word; intro j _
      by_cases same : j=i
      · simp [revise,active,same]
      · have iff : j<i+1 ↔ j<i := by omega
        simp [revise,active,same,iff]
    cases b : bits i
    · rw [b] at high; rw [low,high]; exact .refl _
    · rw [b] at high
      exact .snoc (.refl _) ⟨owner i,mate i,f,false,l,k,⟨i,ix,rfl,rfl⟩,hp,hq,valid,low,high⟩
  have upto (n : Nat) (hn : n≤t) : Chain r allow (Used t) (word t m z (constant false)) (word t m z (active n)) := by
    induction n with
    | zero =>
      have idw : word t m z (constant false) = word t m z (active 0) := same_word m z (by simp [active,constant])
      rw [idw]; exact .refl _
    | succ n ih => exact (ih (by omega)).trans (step n (by omega))
  have finish : word t m z (active t) = word t m z bits := same_word m z (fun i hi => by simp [active,hi])
  exact finish ▸ upto t (Nat.le_refl t)

end P455CellClassFrames
