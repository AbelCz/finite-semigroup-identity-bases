import Problem455EnumStructural
namespace P455Enum
open P455Witness P455Paths P455PaddedTiles P455CatalogueBounds P455GuardProduct Problem455.Slots
def choices (ts : List Tag) : List ContactChoice :=
  ts.flatMap (fun t => bools.list.map (.record t)) ++ (fins 5).list.flatMap (fun p=>bools.list.map (.port p))
def steps (w : List Nat) (ts : List Tag) : List Step :=
  w.flatMap fun b => (choices ts).map (Prod.mk b)
theorem occMem {w o i a} (h : occupies w o i a) : a∈w := by
  obtain ⟨j,pat⟩ := h
  exact Problem455.Slots.stamped_mem_label _ _ (a,j) (pat.subset (by simp))
theorem step_mem {r w mark a b c} (M : MachineTable n) (h : Holds r (allowed M) mark w (contact r a b c)) :
    (b,c)∈steps w (tags M) := by
  have cell := P455ContactGeometry.contact_slot h
  obtain ⟨_,_,occ⟩ := cell
  apply List.mem_flatMap.mpr
  refine ⟨b,occMem occ,List.mem_map.mpr ⟨c,?_,rfl⟩⟩
  unfold choices
  cases c with
  | port p v => exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,(fins 5).mem _,List.mem_map_of_mem (bools.mem v)⟩)
  | record t v =>
    have allow : allowed M t := by cases v <;> exact h.2.2.1
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨t,mem_tags.mpr allow,List.mem_map_of_mem (bools.mem v)⟩)
theorem walk_steps {r w mark start} (M : MachineTable n) (p : List Step)
    (walk : Walk r (allowed M) mark w start p) : ∀ e∈p,e∈steps w (tags M) := by
  induction p generalizing start with
  | nil => simp
  | cons e es ih =>
    rcases e with ⟨b,c⟩
    intro z mz
    exact (List.mem_cons.mp mz).elim (fun eq=>eq ▸ step_mem M walk.1) (ih walk.2 z)
def defects (w : List Nat) :=
  w.map SlotDefect.deficient ++ (Problem455Finite.wordsUpTo w 5).map SlotDefect.overflow
theorem defect_mem {r allow mark w o i} (d : SlotDefect) (valid : Holds r allow mark w (terminalSlot r o i d)) :
    d∈defects w := by
  cases d with
  | deficient a => exact List.mem_append_left _ (List.mem_map_of_mem (occMem valid.1.2))
  | overflow xs =>
    have pos (a) (m : a∈xs) : w.count a=r ∧ slotStart i ∧ occupies w o i a :=
      (allQ_iff _).mp valid.2.2.1 _ (List.mem_map_of_mem m)
    exact List.mem_append_right _ (List.mem_map_of_mem (Problem455Finite.covered _ _ xs
      (Nat.le_of_eq valid.1) (fun a m => occMem (pos a m).2.2)))
def slots (w : List Nat) (ts : List Tag) : List SlotCertificate :=
  (pool w ts).flatMap fun a=>bools.list.flatMap fun b=>bools.list.flatMap fun role=>
    (Problem455Finite.wordsUpTo (steps w ts) 6).flatMap fun p=>(List.range 12).flatMap fun i=>
      (defects w).map fun d=>⟨a,b,role,p,i,d⟩
theorem slot_mem {r mark w} (M : MachineTable n) (s : SlotCertificate) (h : Holds r (allowed M) mark w (s.query r)) :
    s∈slots w (tags M) := by
  obtain ⟨len,walk,term⟩ := slot_route s h
  have a := record_in_pool (tags M) (fun _ h=>mem_tags.mpr h) _ (marked_typed h.1)
  have i := P455SourceFamilies.valid_slot _ term
  have ilt : s.terminalIndex <12 := by unfold slotStart at i; omega
  have pp := Problem455Finite.covered _ _ _ len (walk_steps M _ walk)
  simp only [slots,List.mem_flatMap,List.mem_map]
  exact ⟨_,a,_,bools.mem _,_,bools.mem _,_,pp,_,List.mem_range.mpr ilt,_,defect_mem _ term,rfl⟩
def directions : Cover Dir := ⟨[.right,.left,.down,.up],fun d=>by cases d <;> simp⟩
def functionalities (w : List Nat) (ts : List Tag) : List FunctionalityCertificate :=
  let nodes:=pool w ts
  nodes.flatMap fun a=>bools.list.flatMap fun bit=>nodes.flatMap fun b=>nodes.flatMap fun c=>
    directions.list.flatMap fun d=>bools.list.map fun role=>⟨a,bit,b,c,d,role⟩
theorem func_mem {r mark w} (M : MachineTable n) (f : FunctionalityCertificate)
    (ok : Holds r (allowed M) mark w (f.query (system n))) : f∈functionalities w (tags M) := by
  obtain ⟨a,b,c⟩ := bounded_functionality (tags M) (fun _ h=>mem_tags.mpr h) _ ok
  simp only [functionalities,List.mem_flatMap,List.mem_map]
  exact ⟨_,a,_,bools.mem _,_,b,_,c,_,directions.mem _,_,bools.mem _,rfl⟩
def guards (w : List Nat) (ts : List Tag) : List Guard :=
  (slots w ts).map .slot ++ (functionalities w ts).map .func
instance pairD (a b : Nat) : DecidableRel (P455SlotProduct.pairMark a b) := by
  intro x y; unfold P455SlotProduct.pairMark; infer_instance
def guardOK {r} (hr : 0<r) (M : MachineTable n) (w : List Nat) (kind : Bool) (a b : Nat) :
    Decidable (∃ g : Guard, g.isFunc=kind ∧ g.anchor.owner=a ∧ g.anchor.mate=b ∧
      Holds r (allowed M) (P455SlotProduct.pairMark a b) w (g.query r (system n))) := by
  refine @search _ (guards w (tags M)) _ ?_ ?_
  · intro g
    letI := holdsD hr (allowed M) (P455SlotProduct.pairMark a b) w (g.query r (system n))
      (by cases g with | slot s => exact statSlot r s | func f => exact statFunc n f)
    infer_instance
  · intro g h
    cases g with
    | slot s => exact List.mem_append_left _ (List.mem_map_of_mem (slot_mem M s h.2.2.2))
    | func f => exact List.mem_append_right _ (List.mem_map_of_mem (func_mem M f h.2.2.2))

def sigmaCover (s : Cover α) (b : α→Type) (t : (i : α)→Cover (b i)) : Cover (Sigma b) :=
  ⟨s.list.flatMap (fun i => (t i).list.map (Sigma.mk i)),fun ⟨i,v⟩ =>
    List.mem_flatMap.mpr ⟨i,s.mem _,List.mem_map_of_mem ((t i).mem v)⟩⟩
abbrev GuardKey (r : Nat) := (k : Bool) × (Fin (words r k).length × Fin (width k) × Fin (width k))
def guard {r} (hr : 0<r) (M : MachineTable n) : Cover (Index r (allowed M) (system n)) :=
  let p (key : GuardKey r) := let w:=(words r key.1).get key.2.1
    P455Closure.Cap r w ∧ ∃g : Guard, g.isFunc=key.1 ∧ g.anchor.owner=key.2.2.1.val ∧ g.anchor.mate=key.2.2.2.val ∧
      Holds r (allowed M) (P455SlotProduct.pairMark key.2.2.1 key.2.2.2) w (g.query r (system n))
  letI : DecidablePred p := fun key => by
    let w:=(words r key.1).get key.2.1
    letI := capD r w; letI := guardOK hr M w key.1 key.2.2.1 key.2.2.2
    unfold p; dsimp only; infer_instance
  let keys : Cover (GuardKey r) := sigmaCover bools _ (fun k => pairCover (fins _) (pairCover (fins _) (fins (width k))))
  (coverSub keys p).map (fun c=>⟨c.val.1,c.val.2.1,c.val.2.2.1,c.val.2.2.2,c.property.1,c.property.2⟩)
    (fun ⟨k,i,a,b,cp,ok⟩=>⟨⟨⟨k,i,a,b⟩,cp,ok⟩,rfl⟩)
end P455Enum
