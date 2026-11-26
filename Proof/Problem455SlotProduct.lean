import Problem455DefectProjection
import Problem455MarkedPath




namespace P455SlotProduct
open P455Witness P455Paths P455SourceFamilies P455CrossedSupport Problem455.Slots

def alphabet := List.range 9
def templates (r : Nat) := Problem455Finite.wordsUpTo alphabet (9*r)
def pairMark (a b : Nat) : Marking := fun x y => x = a ∧ y = b

structure Index (r : Nat) (allow : Tag → Prop) where
  num : Fin (templates r).length
  a : Fin 9
  b : Fin 9
  cap : P455Closure.Cap r ((templates r).get num)
  test : ∃ (s : SlotCertificate) (d : Nat), s.defect = .deficient d ∧
    s.anchor.owner = a.val ∧ s.anchor.mate = b.val ∧
    Holds r allow (pairMark a.val b.val) ((templates r).get num) (s.query r)

def Index.T (i : Index r allow) := (templates r).get i.num
def Index.R (i : Index r allow) := rules r allow (pairMark i.a i.b)
abbrev Carrier (r : Nat) (allow : Tag → Prop) := (i : Index r allow) → P455Quotient.Q i.R i.T

def evalP (v : Nat → Carrier r allow) (w : W) : Carrier r allow :=
  fun i => P455Quotient.eval i.R i.cap (fun x => v x i) w

def Identity (r : Nat) (allow : Tag → Prop) (u w : W) :=
  ∀ v : Nat → Carrier r allow, evalP v u = evalP v w

theorem index_injective {i j : Index r allow} (n : i.num = j.num) (a : i.a = j.a)
    (b : i.b = j.b) : i = j := by cases i; cases j; cases n; cases a; cases b; rfl

theorem coordinate_finite (i : Index r allow) (q : P455Quotient.Q i.R i.T) :
    q ∈ Problem455Finite.carrier i.R i.T := Problem455Finite.carrier_complete .. 

private theorem remove_count (w : W) (a : Nat) :
    (w.filter (· != a)).length + w.count a = w.length := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    by_cases eq : a = b
    · subst b; simp [List.count_cons] at ih ⊢; omega
    · simp [List.count_cons,eq,Ne.symm eq,beq_iff_eq] at ih ⊢; omega

theorem capped_length {r : Nat} (k : Nat) (w : W) (cap : P455Closure.Cap r w)
    (names : ∀ x ∈ w, x < k) : w.length ≤ k*r := by
  induction k generalizing w with
  | zero => cases w with
            | nil => simp
            | cons x xs => exact False.elim (Nat.not_lt_zero _ (names x (by simp)))
  | succ k ih =>
    have cp : P455Closure.Cap r (w.filter (· != k)) :=
      fun x => Nat.le_trans (List.Sublist.count_le x List.filter_sublist) (cap x)
    have low := ih _ cp (fun x hx => by
      obtain ⟨mem,p⟩ := List.mem_filter.mp hx
      have h := names x mem
      have e : x ≠ k := by simpa [bne_iff_ne] using p
      omega)
    have ct := cap k
    have tot := remove_count w k
    rw [Nat.succ_mul]; omega

def image (keep : W) (a : Nat) : W := if a ∈ keep then [keep.idxOf a] else []
theorem image_word (keep w : W) :
    w.flatMap (image keep) = (select keep w).map keep.idxOf := by
  induction w with
  | nil => rfl
  | cons a t ih => by_cases h : a ∈ keep <;> simp [image,select,h,ih, List.flatMap_cons] at *

/-- A true identity at the finite product specializes simultaneously at
    the coordinatewise erasing-and-renaming valuation, even if other
    coordinates send some of its one-letter words to zero. -/
theorem marked_test {r allow u w} (valid : Identity r allow u w) (keep : W)
    (i : Index r allow) (eq : (select keep u).map keep.idxOf = i.T) :
    select [i.a.val,i.b.val] ((select keep u).map keep.idxOf) =
    select [i.a.val,i.b.val] ((select keep w).map keep.idxOf) := by
  let v : Nat → Carrier r allow := fun x j => P455Quotient.ofWord j.R j.T (image keep x)
  have comp := congrFun (valid v) i
  change P455Quotient.eval i.R i.cap _ u = P455Quotient.eval i.R i.cap _ w at comp
  rw [P455Quotient.eval_rep i.R i.cap (fun x => v x i) u (image keep) (fun _ _ => rfl),
      P455Quotient.eval_rep i.R i.cap (fun x => v x i) w (image keep) (fun _ _ => rfl),image_word,image_word,eq] at comp
  have good : P455Quotient.Good i.R i.T i.T := ⟨i.T,.refl _,[],[],by simp⟩
  have path := ((P455Quotient.same_nonzero_class i.R good).mp comp).2
  rw [eq]
  apply P455Quotient.Walk.transport (P := fun z => select [i.a.val,i.b.val] i.T = select [i.a.val,i.b.val] z) path rfl
  intro z z' mv old
  exact old.trans (mv.marked_proj _ _ ⟨rfl,rfl⟩)

private theorem tag_map (x y : Nat) (t : Tag) :
    (t.flatMap P455Closure.phasePair).map (fun b => if b then y else x) = t.flatMap (pair x y) := by
  induction t with
  | nil => rfl
  | cons b t ih => cases b <;> simp [List.flatMap_cons,P455Closure.phasePair,pair,ih]

theorem profile_eq (x y : Nat) (t : Tag) (b : Bool) :
    P455Closure.Frame.profileWord x y t b = profile x y t b := by
  cases b <;> simp [P455Closure.Frame.profileWord,P455Closure.Frame.profileBits,
    P455Closure.fixedPhases,P455Closure.phasePair,profile,profilePrefix,pair,
    List.replicate_succ,tag_map,List.append_assoc]

theorem flip_anchor {r allow u x y} (cap : P455Closure.Cap r u)
    (flip : ClosedFlip r allow u x y) : ∃ tag bit,
    Holds r allow (markNode ⟨x,y,tag⟩) u (markedNode ⟨x,y,tag⟩ bit) := by
  obtain ⟨_,_,_,ne⟩ := flip_counts cap flip
  obtain ⟨f,b,l,k,hp,hq,ok,rfl⟩ := flip
  refine ⟨f.tag,b,ne,by change f.tag.length + 16 = r; have h := ok.1; omega,ok.2.1,.inl ⟨rfl,rfl⟩,?_⟩
  have h := f.cross_projection ok b l k cap x y (by simp [hp]) (by simp [hq])
  simpa [select,profile_eq] using h

end P455SlotProduct
