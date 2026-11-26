import Problem455Encoded
import Problem455IndexedProduct
import Problem455EffectiveQRaw



namespace P455Packed
open P455Table P455TableProduct P455TableFactors P455NumericProduct P455IndexedProduct
open P455PaddedTiles P455FirstRewrite P455Quotient

abbrev Spec := List Nat × Option (List (Nat × Nat))

structure Payload where
  r : Nat
  tags : List (List Bool)
  primitive : List Spec
  guard : List Spec
  edge : List Spec
  binary : List Spec
  structural : List Spec

def moves (r : Nat) (tags : List (List Bool)) (marks : Option (List (Nat×Nat))) :
    List Nat → List Nat → Bool := match marks with
  | none => fun _ _ => false
  | some pairs => P455EffectiveQMove.moveB r tags (fun a b => decide ((a,b)∈pairs))

def factorRows (r : Nat) (tags : List (List Bool)) (s : Spec) :=
  P455EffectiveQRaw.rows (moves r tags s.2) s.1

def serialize (p : Payload) : Matrix :=
  let group := fun (xs : List Spec) => assemble (xs.map (factorRows p.r p.tags))
  tensor (group p.primitive)
    (tensor (tensor (group p.guard) (group p.edge)) (tensor (group p.binary) (group p.structural)))

def names {I : Type} (c : Listing I) (record : I → Spec) :=
  letI := c.eq
  (distinct c.items).map record

def primSpec (i : P455FirstTesters.Index r) : Spec := (i.val,none)
def structSpec (i : P455StructuralProduct.Index r allow) : Spec := (i.T,none)
def binSpec (i : P455BinaryProduct.Index r allow) : Spec := (i.T,if i.prof then some [] else none)
def oneSpec (i : P455GuardProduct.Index r allow ts) : Spec := (i.T,some [(i.a.val,i.b.val)])
def twoSpec (i : P455EdgeProduct.Index r allow ts) : Spec :=
  (i.T,some [(i.a.val,i.b.val),(i.c.val,i.d.val)])

def prepared {n} (M : MachineTable n) : Payload :=
  let C := P455Encoded.indices M
  ⟨widthCode n+16,P455Enum.tags M,names C.primitive primSpec,names C.guard oneSpec,
    names C.edge twoSpec,names C.binary binSpec,names C.structural structSpec⟩

private theorem raw_correct (R : Rules Nat) (e : List Nat → List Nat → Bool)
    (correct : ∀ a b, e a b=true ↔ R.step a b) (T : List Nat) (cap : Cap R.r T) :
    Represents (P455EffectiveQRaw.rows e T) (quotientModel R T cap) :=
  ⟨P455EffectiveQRaw.ops R e correct T,(P455EffectiveQRaw.matrix_eq R e correct T).symm,
    ⟨P455EffectiveQRaw.presentation R e correct T cap⟩⟩

private theorem plain (r tags) (T : List Nat) (cap : Cap r T) :
    Represents (factorRows r tags (T,none)) (quotientModel (P455FirstTesters.plain r) T cap) :=
  raw_correct _ _ (fun _ _ => by simp [P455FirstTesters.plain,moves]) T cap

private theorem marked {n} (M : MachineTable n) (r : Nat) (T : List Nat) (pairs : List (Nat×Nat))
    (mark : Nat→Nat→Prop) (same : ∀ x y, (x,y)∈pairs ↔ mark x y) (cap : Cap r T) :
    Represents (factorRows r (P455Enum.tags M) (T,some pairs))
      (quotientModel (Problem455Finite.rules r (allowed M) mark) T cap) := by
  apply raw_correct
  exact P455EffectiveQMove.move_iff (fun _ => P455Enum.mem_tags (M:=M))
    (fun x y => (Iff.of_eq (decide_eq_true_eq)).trans (same x y)) r

private theorem group {I : Type} {F : I → Type} (M : (i : I) → Model (F i))
    (C : Listing I) (record : I → Spec) (r tags)
    (yes : ∀ i, Represents (factorRows r tags (record i)) (M i)) :
    Represents (assemble ((names C record).map (factorRows r tags))) (full M) := by
  letI := C.eq
  simpa only [names,List.map_map,Function.comp_def] using
    complete_product M (fun i => factorRows r tags (record i)) yes (distinct C.items)
      (nodup_distinct _) (fun i => (mem_distinct ..).mpr (C.all i))

private theorem binary_factor {n} (M : MachineTable n) (r : Nat)
    (i : P455BinaryProduct.Index r (allowed M)) :
    Represents (factorRows r (P455Enum.tags M) (binSpec i)) (quotientModel i.R i.T i.bound) := by
  rcases i with ⟨num,prof,cap,accepted⟩
  cases prof with
  | false => exact plain r (P455Enum.tags M) _ cap
  | true => exact marked M r _ [] P455SlotSaturation.noMark (by simp [P455SlotSaturation.noMark]) cap

set_option maxHeartbeats 1200000 in
theorem serialize_represents {n} (M : MachineTable n) :
    Represents (serialize (prepared M)) (P455Global.monoid M) := by
  let r := widthCode n+16
  let L := P455Enum.tags M
  let C := P455Encoded.indices M
  have prim : Represents (assemble ((names C.primitive primSpec).map (factorRows r L)))
      (P455FirstTesters.product r) :=
    group (fun i : P455FirstTesters.Index r => quotientModel _ _ i.cap) C.primitive primSpec _ _
      (fun i => plain r L i.val i.cap)
  have structural : Represents (assemble ((names C.structural structSpec).map (factorRows r L)))
      (P455StructuralProduct.product r (allowed M)) :=
    group (fun i : P455StructuralProduct.Index r (allowed M) => quotientModel (P455FirstTesters.plain r) i.T i.cap)
      C.structural structSpec _ _ (fun i => plain r L i.T i.cap)
  have guards : Represents (assemble ((names C.guard oneSpec).map (factorRows r L)))
      (P455GuardProduct.product r (allowed M) (system n)) :=
    group (fun i : P455GuardProduct.Index r (allowed M) (system n) => quotientModel i.R i.T i.cap)
      C.guard oneSpec _ _ (fun i => marked M r i.T _ _ (by intros; simp [P455SlotProduct.pairMark]) i.cap)
  have edges : Represents (assemble ((names C.edge twoSpec).map (factorRows r L)))
      (P455EdgeProduct.product r (allowed M) (system n)) :=
    group (fun i : P455EdgeProduct.Index r (allowed M) (system n) => quotientModel i.R i.T i.cap)
      C.edge twoSpec _ _ (fun i => marked M r i.T _ _ (by intros; simp [P455EdgeProduct.marks]) i.cap)
  have binary : Represents (assemble ((names C.binary binSpec).map (factorRows r L)))
      (P455BinaryProduct.model r (allowed M)) :=
    group (fun i : P455BinaryProduct.Index r (allowed M) => quotientModel i.R i.T i.bound)
      C.binary binSpec r L (binary_factor M r)
  have combined := represents_tensor prim (represents_tensor (represents_tensor guards edges)
    (represents_tensor binary structural))
  dsimp only [serialize,prepared,P455Global.monoid,P455FullSingleton.model,P455MarkedRank.model]
  exact combined

end P455Packed
