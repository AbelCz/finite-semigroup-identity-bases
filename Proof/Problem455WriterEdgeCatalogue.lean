import Problem455WriterBinary
import Problem455WriterEdgeTypes

namespace P455WriterEdge
open P455Witness P455PaddedTiles P455WriterTiles

abbrev Quad := Nat × Nat × Nat × Nat
abbrev Key := Nat × Quad
abbrev Predicate := List Nat → Quad → Bool

def quads := choices (List.range 14) (choices (List.range 14) (choices (List.range 14) (List.range 14)))
def atKey (r i : Nat) := (P455EdgeProduct.words r)[i]?.getD []
def key (i : P455EdgeProduct.Index r allow ts) : Key := (i.num.val,i.a.val,i.b.val,i.c.val,i.d.val)

theorem key_inj : Function.Injective (@key r allow ts) := by
  rintro ⟨j,a,b,c,d,_,_⟩ ⟨k,p,q,s,t,_,_⟩ he
  change (j.val,a.val,b.val,c.val,d.val)=(k.val,p.val,q.val,s.val,t.val) at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨jEq,aEq,bEq,cEq,dEq⟩:=he
  cases Fin.ext jEq; cases Fin.ext aEq; cases Fin.ext bEq; cases Fin.ext cEq; cases Fin.ext dEq; rfl

def filtered (r : Nat) (ok : Predicate) :=
  (choices (List.range (P455EdgeProduct.words r).length) quads).filter fun k => ok (atKey r k.1) k.2

def asSpec (r : Nat) (k : Key) : P455Packed.Spec :=
  (atKey r k.1,some [(k.2.1,k.2.2.1),(k.2.2.2.1,k.2.2.2.2)])

def family (r : Nat) (ok : Predicate) := (P455Table.distinct (filtered r ok)).map (asSpec r)

def ValidKey (M : MachineTable n) (r : Nat) (w : List Nat) (k : Quad) : Prop :=
  P455Closure.Cap r w ∧ ∃ e : EdgeCertificate, e.a.owner=k.1 ∧ e.a.mate=k.2.1 ∧ e.b.owner=k.2.2.1 ∧ e.b.mate=k.2.2.2 ∧
    (∀ x, x∈w ↔ x∈P455EdgeProjection.names (system n) e) ∧
    Holds r (allowed M) (P455EdgeProduct.marks k.1 k.2.1 k.2.2.1 k.2.2.2) w (e.query (system n))

theorem getAt (r : Nat) (i : Fin (P455EdgeProduct.words r).length) : atKey r i.val=(P455EdgeProduct.words r).get i := by
  simp [atKey,i.isLt]

def vals (x : P455Enum.EdgeKey r) : Key := (x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.1.val,x.2.2.2.2.val)
private theorem attachKeys (xs : List (P455Enum.EdgeKey r)) :
    xs.attach.map (fun x => vals x.val) = xs.map vals := List.attach_map_val ..

theorem filtered_correct (M : MachineTable n) (hr : 0<r) (ok : Predicate)
    (correct : ∀ w k, ok w k=true ↔ ValidKey M r w k) :
    (P455Enum.edge hr M).list.map key=filtered r ok := by
  let nums := (P455Enum.fins 14).list
  let xs := choices (P455Enum.fins (P455EdgeProduct.words r).length).list (choices nums (choices nums (choices nums nums)))
  have ord : xs.map vals=choices (List.range (P455EdgeProduct.words r).length) quads := by
    unfold xs nums quads vals
    rw [←List.map_coe_finRange,←List.map_coe_finRange (n:=14)]
    simp only [choices,P455Enum.fins,List.map_flatMap,List.map_map,List.flatMap_map,Function.comp_def]
  unfold filtered
  rw [←ord,List.filter_map]
  unfold P455Enum.edge
  simp only [P455Enum.Cover.map,P455Enum.coverSub,P455Enum.selectSub,List.map_map,Function.comp_def,key]
  change (List.map (fun x => @vals r x.val) (List.attach (_ : List (P455Enum.EdgeKey r))))=_
  rw [@attachKeys r]
  apply congrArg (List.map vals); apply List.filter_congr
  intro x _; apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,correct,vals,getAt,ValidKey]

theorem family_correct (M : MachineTable n) (hr : 0<r) (ok : Predicate)
    (correct : ∀ w k, ok w k=true ↔ ValidKey M r w k) :
    family r ok=P455Packed.names (P455Encoded.useCover (P455Enum.edge hr M)) P455Packed.twoSpec := by
  unfold family; rw [←filtered_correct M hr ok correct,←P455CataloguePrim.map_distinct key key_inj,List.map_map]
  unfold P455Packed.names P455Encoded.useCover
  apply List.map_congr_left; intro i _
  change (atKey r i.num.val,_) = _
  rw [getAt]; rfl

variable {A : Type} [Primcodable A]
theorem wordsRec : Primrec P455EdgeProduct.words :=
  P455GraphPrim.wordsUpTo.comp (.const (List.range 14)) (Primrec.nat_mul.comp (.const 14) Primrec.id)
theorem atKeyRec : Primrec₂ atKey :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (wordsRec.comp Primrec.fst) Primrec.snd) (.const [])

theorem familyRec {r : A→Nat} {ok : A→Predicate} (hr : Primrec r)
    (h : Primrec (fun p : (A × List Nat) × Quad => ok p.1.1 p.1.2 p.2)) :
    Primrec fun x => family (r x) (ok x) := by
  have ks := choicesRec (Primrec.list_range.comp (Primrec.list_length.comp (wordsRec.comp hr))) (.const quads)
  have src := Primrec.fst (α:=A) (β:=Key)
  have k := Primrec.snd (α:=A) (β:=Key)
  have w := atKeyRec.comp (hr.comp src) (Primrec.fst.comp k)
  have z := Primrec.snd.comp k
  have f : Primrec (fun x => filtered (r x) (ok x)) := P455GraphPrim.filter ks (h.comp ((src.pair w).pair z)).to₂
  have t := Primrec.snd.comp z
  have u := Primrec.snd.comp t
  have ab := (Primrec.fst.comp z).pair (Primrec.fst.comp t)
  exact Primrec.list_map (P455CataloguePrim.distinct'.comp f) (w.pair (Primrec.option_some.comp
    (Primrec.list_cons.comp ab (Primrec.list_cons.comp u (.const []))))).to₂

end P455WriterEdge
