import Problem455WriterSlots
import Problem455WriterEdgePorts
namespace P455WriterGuard
open P455WriterTiles (choices choicesRec)
open P455WriterQueryLeaves (Env ModelsEnv)
open P455PaddedTiles P455GuardProduct
open P455Witness (Tag Holds)
abbrev Key := Bool × Nat × Nat × Nat

def environment (r : Nat) (ts : List Tag) (w : List Nat) (a b : Nat) : Env := (r,ts,[(a,b)],w)
def checker (r n : Nat) (ts : List Tag) (w : List Nat) (k : Bool) (a b : Nat) :=
  let e := environment r ts w a b
  P455EffectiveQMove.capB r w && (if k then P455WriterEdge.funcAccept e n a b else P455WriterSlots.slotAccept e a b)

def ValidKey (r : Nat) (M : MachineTable n) (w : List Nat) (k : Bool) (a b : Nat) :=
  P455Closure.Cap r w ∧ ∃ g : Guard, g.isFunc=k ∧ g.anchor.owner=a ∧ g.anchor.mate=b ∧
    Holds r (allowed M) (P455SlotProduct.pairMark a b) w (g.query r (system n))

theorem checker_ok {r : Nat} (hr : 0<r) (M : MachineTable n) (w k a b) :
    checker r n (P455Enum.tags M) w k a b=true ↔ ValidKey r M w k a b := by
  let e := environment r (P455Enum.tags M) w a b
  have h : ModelsEnv e r (allowed M) (P455SlotProduct.pairMark a b) w :=
    ⟨rfl,fun _ => P455Enum.mem_tags,fun _ _ => by simp [e,environment,P455SlotProduct.pairMark],rfl,hr⟩
  unfold checker ValidKey
  simp only [Bool.and_eq_true,P455EffectiveQMove.cap_iff]
  apply and_congr_right
  intro _
  cases k with
  | false =>
    change P455WriterSlots.slotAccept e a b=true ↔ _
    rw [P455WriterSlots.slotAccept_ok M h rfl]
    constructor
    · rintro ⟨s,ha,hb,ok⟩; exact ⟨.slot s,rfl,ha,hb,ok⟩
    · rintro ⟨s|f,k,ha,hb,ok⟩; exact ⟨s,ha,hb,ok⟩; cases k
  | true =>
    change P455WriterEdge.funcAccept e n a b=true ↔ _
    rw [P455WriterEdge.funcAccept_ok M h rfl]
    constructor
    · rintro ⟨f,ha,hb,ok⟩; exact ⟨.func f,rfl,ha,hb,ok⟩
    · rintro ⟨s|f,k,ha,hb,ok⟩; cases k; exact ⟨f,ha,hb,ok⟩

def wordAt (r : Nat) (kind : Bool) (i : Nat) := (words r kind)[i]?.getD []
def base (r : Nat) (k : Bool) := choices (List.range (words r k).length)
  (choices (List.range (width k)) (List.range (width k)))
def keys (r : Nat) : List Key := [false,true].flatMap fun k => (base r k).map (Prod.mk k)
def filtered (r n : Nat) (ts : List Tag) :=
  (keys r).filter fun k => checker r n ts (wordAt r k.1 k.2.1) k.1 k.2.2.1 k.2.2.2
def spec (r : Nat) (k : Key) : P455Packed.Spec := (wordAt r k.1 k.2.1,some [(k.2.2.1,k.2.2.2)])
def family (r n : Nat) (ts : List Tag) := (P455Table.distinct (filtered r n ts)).map (spec r)

def key (i : Index r allow ts) : Key := (i.kind,i.pos.val,i.a.val,i.b.val)

theorem key_inj : Function.Injective (@key r allow ts) := by
  rintro ⟨k,i,a,b,_,_⟩ ⟨k',i',a',b',_,_⟩ h
  change (k,i.val,a.val,b.val)=(k',i'.val,a'.val,b'.val) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl,hi,ha,hb⟩ := h
  cases Fin.ext hi; cases Fin.ext ha; cases Fin.ext hb; rfl

def vals (x : P455Enum.GuardKey r) : Key := (x.1,x.2.1.val,x.2.2.1.val,x.2.2.2.val)
private theorem attachKeys (xs : List (P455Enum.GuardKey r)) :
    xs.attach.map (fun x => vals x.val) = xs.map vals := List.attach_map_val ..

theorem wordAt_get (r : Nat) (k : Bool) (i : Fin (words r k).length) :
    wordAt r k i.val=(words r k).get i := by simp [wordAt,i.isLt]

def coreKeys (r : Nat) : List (P455Enum.GuardKey r) :=
  (P455Enum.sigmaCover P455Enum.bools _ (fun k =>
    P455Enum.pairCover (P455Enum.fins (words r k).length) (P455Enum.pairCover (P455Enum.fins (width k)) (P455Enum.fins (width k))))).list

theorem key_order (r : Nat) : (coreKeys r).map vals = keys r := by
  have one (k : Bool) : ((P455Enum.pairCover (P455Enum.fins (words r k).length)
      (P455Enum.pairCover (P455Enum.fins (width k)) (P455Enum.fins (width k)))).list.map
        (fun p => @vals r ⟨k,p⟩)) = (base r k).map (Prod.mk k) := by
    unfold base vals
    rw [←List.map_coe_finRange,←List.map_coe_finRange (n:=width k)]
    simp only [P455Enum.pairCover,P455Enum.Cover.bind,P455Enum.fins,choices,List.map_flatMap,List.map_map,List.flatMap_map,Function.comp_def]
  unfold coreKeys keys
  simp only [P455Enum.sigmaCover,List.map_flatMap,List.map_map,Function.comp_def]
  exact congrArg (List.flatMap · [false,true]) (funext one)

theorem filtered_ok (M : MachineTable n) (hr : 0<r) :
    (P455Enum.guard hr M).list.map key = filtered r n (P455Enum.tags M) := by
  unfold filtered
  rw [←key_order,List.filter_map]
  unfold P455Enum.guard
  simp only [P455Enum.Cover.map,P455Enum.coverSub,P455Enum.selectSub,List.map_map,Function.comp_def,key]
  change (List.map (fun x => @vals r x.val) (List.attach (_ : List (P455Enum.GuardKey r)))) = _
  rw [@attachKeys r]
  apply congrArg (List.map vals); apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,vals,wordAt_get,checker_ok hr,ValidKey]

theorem family_ok (M : MachineTable n) (hr : 0<r) :
    family r n (P455Enum.tags M)=P455Packed.names (P455Encoded.useCover (P455Enum.guard hr M)) P455Packed.oneSpec := by
  unfold family
  rw [←filtered_ok M hr,←P455CataloguePrim.map_distinct key key_inj,List.map_map]
  unfold P455Packed.names P455Encoded.useCover
  apply List.map_congr_left
  intro i _
  change (wordAt r i.kind i.pos.val,_) = _
  rw [wordAt_get]
  rfl

end P455WriterGuard
