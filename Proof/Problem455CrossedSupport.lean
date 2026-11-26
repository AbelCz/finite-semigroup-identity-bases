import Problem455SourceTheorem

/- The guard used for a crossed flip is constructed from the two actual
   source names. The remaining geometric premise concerns only the counts
   of literal original-slot occupants in the indicated radius. -/
namespace P455CrossedSupport
open P455Witness P455Paths P455ContactLift P455SourceFamilies
open P455OriginalWalk P455SourceTheorem Problem455.Slots

def ClosedFlip (r : Nat) (allow : Tag → Prop) (u : W) (x y : Nat) : Prop :=
  ∃ (f : P455Closure.Frame Nat) (b : Bool) (l k : W),
    f.p = [x] ∧ f.q = [y] ∧ f.Valid r allow (fun _ _ => False) ∧ u = l ++ f.core b ++ k

theorem flip_counts {r allow u x y} (cap : P455Closure.Cap r u) (flip : ClosedFlip r allow u x y) :
    1 < r ∧ u.count x = r ∧ u.count y = r ∧ x ≠ y := by
  obtain ⟨f,b,l,k,hp,hq,v,rfl⟩ := flip
  have one (a : Nat) (mem : a ∈ f.p ∨ a ∈ f.q) : (l ++ f.core b ++ k).count a = r := by
    have sat := v.2.2.2.2.2.2.2 a mem
    have bit : (f.core b).count a = r := by cases b <;> first | exact sat | exact (f.count_core a true).trans sat
    have bound := cap a; simp only [List.count_append,bit] at bound ⊢; omega
  have xp : x ∈ f.p := by simp [hp]
  have yq : y ∈ f.q := by simp [hq]
  exact ⟨by have := v.1; omega,one _ (.inl xp),one _ (.inr yq),
    fun e => v.2.2.2.2.2.1 _ xp (e ▸ yq)⟩

def markedRecord (c : Certificate) (second : Bool) : Node :=
  match c with
  | .slot s => s.anchor
  | .functionality f => f.anchor
  | .edge e => if second then e.b else e.a

/-- Either orientation of the chosen unordered pair across the two images. -/
def Crosses (n : Node) (h : Nat → W) (x y : Nat) : Prop :=
  (n.owner ∈ h x ∧ n.mate ∈ h y) ∨ (n.owner ∈ h y ∧ n.mate ∈ h x)

theorem start_role (c : Certificate) (second mate : Bool) :
    startLabel c second mate = (markedRecord c second).owner ∨
    startLabel c second mate = (markedRecord c second).mate := by
  cases c with
  | slot s => cases e : s.startAtMate <;> simp [picked,startLabel,markedRecord,e]
  | functionality f => exact .inl rfl
  | edge e => cases mate <;> simp [startLabel,markedRecord]

theorem choose_seed {h x y} (c : Certificate) (second mate : Bool)
    (cross : Crosses (markedRecord c second) h x y) :
    ∃ seed, (seed = x ∨ seed = y) ∧ startLabel c second mate ∈ h seed := by
  rcases start_role c second mate with owner|other
  · rcases cross with c1|c2
    · exact ⟨x,.inl rfl,owner.symm ▸ c1.1⟩
    · exact ⟨y,.inr rfl,owner.symm ▸ c2.1⟩
  · rcases cross with c1|c2
    · exact ⟨y,.inr rfl,other.symm ▸ c1.2⟩
    · exact ⟨x,.inl rfl,other.symm ▸ c2.2⟩

def InBall (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y t : Nat) :=
  Near r allow mark u x t 6 ∨ Near r allow mark u y t 6

def UniformSlots (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y : Nat) :=
  ∀ t, InBall r allow mark u x y t → ∀ i, slotStart i → ∀ b, occupies u t i b → u.count b = r

def Needed (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y b : Nat) : Prop :=
  InBall r allow mark u x y b ∨ ∃ t i, InBall r allow mark u x y t ∧ slotStart i ∧ occupies u t i b

/-- Finite retained support. Repetitions in the carrier list u do not affect
    membership. Tile compatibility and allowed tags can be arbitrary predicates. -/
noncomputable def retained (r : Nat) (allow : Tag → Prop) (mark : Marking) (u : W) (x y : Nat) : W := by
  classical
  exact u.filter (fun b => decide (Needed r allow mark u x y b))

theorem mem_retained {r allow mark u x y b} :
    b ∈ retained r allow mark u x y ↔ b ∈ u ∧ Needed r allow mark u x y b := by
  classical
  simp [retained]

theorem walked_name {r allow mark u} (hr : 0 < r) (cap : P455Closure.Cap r u) (a : Nat)
    (p : List Step) (ha : a ∈ u) (w : Walk r allow mark u a p) : endpoint a p ∈ u := by
  induction p generalizing a with
  | nil => exact ha
  | cons step ps ih =>
    obtain ⟨b,c⟩ := step
    have count := (P455Retained.contact_counts cap w.1).2
    exact ih b (List.count_pos_iff.mp (count.symm ▸ hr)) w.2

theorem actual_guard {r allow mark u x y seed} (hr : 0 < r) (cap : P455Closure.Cap r u)
    (hx : x ∈ u) (hy : y ∈ u) (side : seed = x ∨ seed = y) (unif : UniformSlots r allow mark u x y) :
    OriginalGuard r allow mark u (fun a => a ∈ retained r allow mark u x y) seed 6 := by
  intro t near
  have ball : InBall r allow mark u x y t := side.elim (fun a => .inl (a ▸ near)) (fun a => .inr (a ▸ near))
  have hs : seed ∈ u := side.elim (fun a => a.symm ▸ hx) (fun a => a.symm ▸ hy)
  obtain ⟨p,w,eq,_⟩ := near
  have ht := eq ▸ walked_name hr cap seed p hs w
  refine ⟨mem_retained.mpr ⟨ht,.inl ball⟩,?_⟩
  intro i hi b between
  have inside : b ∈ u := by
    obtain ⟨j,events⟩ := between
    exact stamped_mem_label _ _ (b,j) (events.subset (by simp))
  exact ⟨mem_retained.mpr ⟨inside,.inr ⟨t,i,ball,hi,between⟩⟩,unif t ball i hi b between⟩

end P455CrossedSupport
