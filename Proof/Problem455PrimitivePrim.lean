import Problem455EnumEdges
import Problem455RealizerPrim
import Problem455Table
import Mathlib.Computability.Primrec

/- The primitive tester coordinates, in the enumeration order of the actual
   product. The computations below are certified in mathlib's Primrec. -/
namespace P455CataloguePrim
variable {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
theorem filter' {f : A → List B} {p : A → B → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun x => (f x).filter (p x)) := P455GraphPrim.filter hf hp

theorem count' [DecidableEq B] : Primrec₂ (fun (xs : List B) (a : B) => xs.count a) := by
  have f : Primrec (fun p : List B × B => (p.1.filter (fun a => a == p.2)).length) :=
    Primrec.list_length.comp (filter' Primrec.fst ((Primrec.beq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂))
  exact f.of_eq (fun _ => by simp [List.count,List.countP_eq_length_filter])
theorem all' {f : A→List B} {p : A→B→Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have h : Primrec (fun a => (f a).foldr (fun b t => p a b && t) true) :=
    Primrec.list_foldr hf (Primrec.const true) ((Primrec.and.comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂)
  apply h.of_eq
  intro x
  generalize f x = l
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem mem' [DecidableEq B] : PrimrecRel (fun (a : B) (xs : List B) => a∈xs) := by
  have h := Primrec.nat_lt.comp (Primrec.const 0) (count'.comp (Primrec.snd (α:=B) (β:=List B)) Primrec.fst)
  exact h.of_eq (fun _ => by simp [List.count_pos_iff])
theorem distinct' [DecidableEq B] : Primrec (@P455Table.distinct B _) := by
  have h : Primrec (fun xs : List B => List.recOn (motive := fun _ => List B) xs ([] : List B) (fun a tail result =>
      if a∈tail then result else a::result)) :=
    Primrec.list_rec Primrec.id (Primrec.const [])
      ((Primrec.ite (mem'.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂)
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a l ih => exact congrArg (fun acc => if a∈l then acc else a::acc) ih

theorem words' : Primrec₂ (@Problem455Finite.wordsUpTo B) := P455GraphPrim.wordsUpTo

abbrev W := List Nat
abbrev Spec := W × Option (List (Nat×Nat))
def accept (r : Nat) (w : W) : Bool :=
  decide (w=List.replicate r 0) ||
    ((w.all (fun a => decide (a=0 ∨ a=1))) &&
     (w.all (fun a => decide (w.count a≤r))) && decide (0<w.count 0) &&
     decide (0<w.count 1) && decide (w.count 0 < r ∨ w.count 1 < r))

theorem accepted (r : Nat) (w : W) : accept r w=true ↔ w=P455FirstTesters.power r ∨ P455FirstTesters.Binary r w := by
  have cap : (∀ a∈w,w.count a≤r) ↔ P455Quotient.Cap r w := by
    constructor
    · intro h a
      by_cases m : a∈w
      · exact h a m
      · simp [List.count_eq_zero.mpr m]
    · exact fun h a _ => h a
  simp [accept,P455FirstTesters.power,P455FirstTesters.Binary,List.all_eq_true,cap,and_assoc]

theorem accept' : Primrec₂ accept := by
  let F := Nat×W
  have p0 : Primrec (fun z : F => List.replicate z.1 0) :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec₂.const (0:Nat))).of_eq (fun z=>by simp [List.map_const'])
  have names : Primrec (fun z : F => z.2.all (fun a => decide (a=0 ∨ a=1))) :=
    all' Primrec.snd ((PrimrecPred.or (Primrec.eq.comp (Primrec.snd (α:=F) (β:=Nat)) (Primrec.const 0))
      (Primrec.eq.comp Primrec.snd (Primrec.const 1))).to₂)
  have cap : Primrec (fun z : F => z.2.all (fun a => decide (z.2.count a ≤ z.1))) :=
    all' Primrec.snd ((Primrec.nat_le.comp (count'.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).to₂)
  have c0 : Primrec (fun z : F => z.2.count 0) := count'.comp Primrec.snd (Primrec.const 0)
  have c1 : Primrec (fun z : F => z.2.count 1) := count'.comp Primrec.snd (Primrec.const 1)
  have lo := Primrec.or.comp (Primrec.nat_lt.comp c0 Primrec.fst) (Primrec.nat_lt.comp c1 Primrec.fst)
  exact Primrec.or.comp (Primrec.eq.comp Primrec.snd p0) (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp names cap) (Primrec.nat_lt.comp (Primrec.const 0) c0))
      (Primrec.nat_lt.comp (Primrec.const 0) c1)) (lo.of_eq (fun _=>by simp)))

def plain (r : Nat) := (Problem455Finite.wordsUpTo [0,1] (2*r)).filter (accept r)
theorem plain' : Primrec plain :=
  filter' (words'.comp (Primrec.const [0,1]) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)) accept'

theorem actual (r : Nat) : (P455Enum.primitive r).list.map Subtype.val = plain r := by
  unfold P455Enum.primitive P455Enum.selectSub plain
  simp only [List.map_map,Function.comp_def,List.attach_map_val,List.attach_map_subtype_val]
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simp [accepted]

theorem map_distinct {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : X → Y) (inj : Function.Injective f)
    (s : List X) : (P455Table.distinct s).map f = P455Table.distinct (s.map f) := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have mem : f x∈xs.map f ↔ x∈xs := by simp [inj.eq_iff]
    by_cases m : x∈xs <;> simp [P455Table.distinct,m,mem,ih]

def primitive (r : Nat) : List Spec :=
  (P455Table.distinct (P455Enum.primitive r).list).map (fun i => (i.val,none))
theorem primitive' : Primrec primitive := by
  have hs : Primrec (fun r => (P455Table.distinct (plain r)).map (fun w => (w,(none : Option (List (Nat×Nat)))))) :=
    Primrec.list_map (distinct'.comp plain') ((Primrec.snd.pair (Primrec.const none)).to₂)
  apply hs.of_eq
  intro r
  rw [←actual,←map_distinct Subtype.val Subtype.val_injective,List.map_map]
  rfl
end P455CataloguePrim
