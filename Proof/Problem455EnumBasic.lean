import Problem455CatalogueBounds
import Problem455PaddedTiles
import Problem455FullSingleton
 
namespace P455Enum
open P455PaddedTiles P455Witness Problem455.Slots
structure Cover (α : Type) where
  list : List α
  mem : ∀ x, x ∈ list

def Cover.map (s : Cover α) (f : α → β) (sur : ∀ y, ∃ x, f x=y) : Cover β :=
  ⟨s.list.map f,fun y => let ⟨x,e⟩ := sur y; List.mem_map.mpr ⟨x,s.mem x,e⟩⟩

def Cover.bind (s : Cover α) (f : α → Cover β) (g : α → β → γ)
    (sur : ∀ y, ∃ a b, g a b=y) : Cover γ :=
  ⟨s.list.flatMap fun a => (f a).list.map (g a),fun y => by
    obtain ⟨a,b,e⟩ := sur y
    exact List.mem_flatMap.mpr ⟨a,s.mem a,List.mem_map.mpr ⟨b,(f a).mem b,e⟩⟩⟩

def selectSub (xs : List α) (p : α → Prop) [DecidablePred p] := (xs.filter p).attach.map
  (fun t => (⟨t.val,by simpa using (List.mem_filter.mp t.property).2⟩ : Subtype p))

theorem selectSub_full {xs : List α} {p : α → Prop} [DecidablePred p] (x : Subtype p)
    (m : x.val ∈ xs) : x ∈ selectSub xs p := by
  have yes : x.val ∈ xs.filter p := List.mem_filter.mpr ⟨m,decide_eq_true x.property⟩
  unfold selectSub
  apply List.mem_map.mpr
  exact ⟨⟨x.val,yes⟩,List.mem_attach ..,Subtype.ext rfl⟩

def bools : Cover Bool := ⟨[false,true],fun b=>by cases b <;> simp⟩
def fins (n : Nat) : Cover (Fin n) :=
  ⟨List.finRange n,fun a => by
    have h : a.val < (List.finRange n).length := by simp
    simpa using List.getElem_mem (l := List.finRange n) h⟩
def options (s : Cover α) : Cover (Option α) :=
  ⟨none::s.list.map some,fun x=>by cases x with
    | none => simp
    | some a => exact List.mem_cons_of_mem _ (List.mem_map_of_mem (s.mem a))⟩
def tiles (n : Nat) : Cover (Tile n) :=
  let bs := bools.list
  let plain := (fins n).list
  let opt := (options (fins n)).list
  ⟨(bs.flatMap fun a => (bs.flatMap fun b => (bs.flatMap fun c => (bs.flatMap fun d => (bs.flatMap fun e => (bs.flatMap fun f => (opt.flatMap fun l => (plain.flatMap fun v => (opt.flatMap fun r => (plain.map fun z => ⟨a,b,c,d,e,f,l,v,r,z⟩)))))))))), by
     intro p
     cases p with
     | mk a b c d e f l v r z =>
       simp only [List.mem_flatMap,List.mem_map]
       exact ⟨a,bools.mem _,b,bools.mem _,c,bools.mem _,d,bools.mem _,e,bools.mem _,f,bools.mem _,
          l,(options (fins n)).mem _,v,(fins n).mem _,r,(options (fins n)).mem _,z,(fins n).mem _,rfl⟩⟩

def search (s : List α) (p : α → Prop) [DecidablePred p]
    (bound : ∀ x, p x → x∈s) : Decidable (∃ x,p x) :=
  decidable_of_iff (∃ x∈s,p x) ⟨fun ⟨x,_,h⟩ => ⟨x,h⟩,fun ⟨x,h⟩ => ⟨x,bound x h,h⟩⟩
def Cover.existsD (s : Cover α) (p : α → Prop) [DecidablePred p] : Decidable (∃ x,p x) :=
  search s.list p (fun x _ => s.mem x)
instance admittedD (M : MachineTable n) (p : Tile n) : Decidable (Admitted M p) := by
  unfold Admitted; infer_instance
def tags (M : MachineTable n) := ((tiles n).list.filter (Admitted M)).map code
theorem mem_tags {M : MachineTable n} {tag} : tag∈tags M ↔ allowed M tag := by
  simp only [tags,List.mem_map,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun ⟨p,⟨_,h⟩,e⟩=>⟨p,e,h⟩,fun ⟨p,e,h⟩=>⟨p,⟨(tiles n).mem p,h⟩,e⟩⟩
instance allowedD (M : MachineTable n) (t) : Decidable (allowed M t) :=
  decidable_of_iff _ mem_tags
instance horizontalD (n : Nat) (s t) : Decidable ((system n).horizontal s t) := by
  unfold system Horizontal
  exact @Cover.existsD _ (tiles n) _ (fun p => @Cover.existsD _ (tiles n) _ (fun q => inferInstance))
instance verticalD (n : Nat) (s t) : Decidable ((system n).vertical s t) := by
  unfold system Vertical
  exact @Cover.existsD _ (tiles n) _ (fun p => @Cover.existsD _ (tiles n) _ (fun q => inferInstance))

def capD (r : Nat) (w : List Nat) : Decidable (P455Closure.Cap r w) :=
  decidable_of_iff (∀ x∈w,w.count x≤r) ⟨fun h x => by
    by_cases m : x∈w
    · exact h x m
    · simp [List.count_eq_zero.mpr m],fun h x _ => h x⟩
def primitive (r : Nat) : Cover (P455FirstTesters.Index r) :=
  let xs := Problem455Finite.wordsUpTo [0,1] (2*r)
  letI : DecidablePred (fun w : List Nat => w=P455FirstTesters.power r ∨ P455FirstTesters.Binary r w) := fun w => by
    letI : Decidable (P455Quotient.Cap r w) := capD r w
    unfold P455FirstTesters.Binary
    infer_instance
  ⟨selectSub xs _,fun i => selectSub_full i (P455FirstTesters.index_covered i)⟩
end P455Enum
