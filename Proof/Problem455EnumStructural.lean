import Problem455EnumQueries
namespace P455Enum
open P455Witness P455Structural P455PaddedTiles P455BinaryEquality Problem455.Slots
theorem profile_names {a b tag bit} : a∈profile a b tag bit ∧ b∈profile a b tag bit := by
  simp [profile,profilePrefix]
def profileD (r) (M : MachineTable n) (w : List Nat) : Decidable (IsProfile r (allowed M) w) :=
  decidable_of_iff (∃ a∈w, ∃ b∈w, ∃ t∈tags M, ∃ bit : Bool,
    a≠b ∧ t.length+16=r ∧ w=profile a b t bit) (by
      constructor
      · rintro ⟨a,_,b,_,t,mt,v,ne,len,eq⟩; exact ⟨a,b,t,v,ne,len,mem_tags.mp mt,eq⟩
      · rintro ⟨a,b,t,v,ne,len,mt,rfl⟩
        exact ⟨a,profile_names.1,b,profile_names.2,t,mem_tags.mpr mt,v,ne,len,rfl⟩)
def pairCover (a : Cover α) (b : Cover β) : Cover (α×β) :=
  a.bind (fun _=>b) Prod.mk (fun ⟨x,y⟩=>⟨x,y,rfl⟩)
def coverSub (s : Cover α) (p : α→Prop) [DecidablePred p] : Cover (Subtype p) :=
  ⟨selectSub s.list p,fun i=>selectSub_full i (s.mem _)⟩

def binary (r) (M : MachineTable n) : Cover (P455BinaryProduct.Index r (allowed M)) :=
  let xs := Problem455Finite.wordsUpTo [0,1] (2*r)
  let p (c : Fin xs.length × Bool) := let T:=xs.get c.1; P455Closure.Cap r T ∧
    (T=P455FirstTesters.power r ∨ 0<T.count 0 ∧ 0<T.count 1) ∧ (c.2=true ↔ IsProfile r (allowed M) T)
  letI : DecidablePred p := fun c => by
    letI := capD r (xs.get c.1)
    letI := profileD r M (xs.get c.1)
    unfold p; dsimp only; infer_instance
  (coverSub (pairCover (fins _) bools) p).map
    (fun c=>⟨c.val.1,c.val.2,c.property.1,c.property.2⟩)
    (fun ⟨i,b,cp,ok⟩=>⟨⟨(i,b),cp,ok⟩,rfl⟩)

theorem rec_names {r allow w a b} (h : Rec w r allow a b) : a∈w ∧ b∈w := by
  obtain ⟨t,_,_,_,bit,eq⟩ := h
  have m := @profile_names a b t bit
  rw [←eq] at m
  exact ⟨(List.mem_filter.mp m.1).1,(List.mem_filter.mp m.2).1⟩
theorem edge_names {r allow w a b} (h : Edge w r allow a b) : a∈w ∧ b∈w :=
  h.elim rec_names (fun z => ⟨(rec_names z).2,(rec_names z).1⟩)
instance recD (r) (M : MachineTable n) (w a b) : Decidable (Rec w r (allowed M) a b) := by
  unfold Rec
  exact @search _ (tags M) _ (fun t => by unfold Holds; infer_instance)
    (fun t z => mem_tags.mpr z.2.2.1)
instance edgeD (r) (M : MachineTable n) (w a b) : Decidable (Edge w r (allowed M) a b) := by
  unfold Edge; infer_instance
theorem words_bound {α : Type} (alphabet : List α) (k) {w : List α}
    (mem : w∈Problem455Finite.wordsUpTo alphabet k) : w.length≤k := by
  induction k generalizing w with
  | zero => simpa [Problem455Finite.wordsUpTo] using mem
  | succ k ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · simp
    obtain ⟨a,_,hit⟩ := List.mem_flatMap.mp tail
    obtain ⟨q,m,rfl⟩ := List.mem_map.mp hit
    exact Nat.succ_le_succ (ih m)
def widthD (k : Nat) (w : List Nat) : Decidable (Width k w) :=
  decidable_of_iff (∃ C∈Problem455Finite.wordsUpTo w k,∀ x∈w,x∈C) (by
    constructor
    · rintro ⟨C,h,c⟩
      exact ⟨C,words_bound _ _ h,c⟩
    · rintro ⟨C,len,c⟩
      let V := C.filter (fun x=>x∈w)
      have toV (x) (m : x∈w) : x∈V := by simp [V,c _ m,m]
      exact ⟨V,Problem455Finite.covered _ _ _ (Nat.le_trans (List.length_filter_le ..) len)
        (fun _ m => of_decide_eq_true (List.mem_filter.mp m).2),toV⟩)
def overlapD (r) (M : MachineTable n) (w) : Decidable (Overlap w r (allowed M)) :=
  decidable_of_iff (∃ o∈w, ∃ p∈w, ∃ q∈w, o≠p ∧ o≠q ∧ p≠q ∧ Edge w r (allowed M) o p ∧ Edge w r (allowed M) o q)
    ⟨fun ⟨o,_,p,_,q,_,h⟩=>⟨o,p,q,h⟩,fun ⟨o,p,q,h⟩ =>
      ⟨o,(edge_names h.2.2.2.1).1,p,(edge_names h.2.2.2.1).2,q,(edge_names h.2.2.2.2).2,h⟩⟩
def intrusionD (r) (M : MachineTable n) (w) : Decidable (Intrusion w r (allowed M)) :=
  decidable_of_iff (∃ o∈w, ∃ p∈w, ∃ e∈events w, o≠p ∧ e.1≠o ∧ e.1≠p ∧ Rec w r (allowed M) o p ∧
    sees w [(o,0),e,(p,2)]) ⟨fun ⟨o,_,p,_,e,_,h⟩=>⟨o,p,e.1,e.2,h⟩,fun ⟨o,p,z,j,h⟩=>
      ⟨o,(rec_names h.2.2.2.1).1,p,(rec_names h.2.2.2.1).2,(z,j),h.2.2.2.2.subset (by simp),h⟩⟩
def compressedD {r} (hr : 0<r) (w) : Decidable (P455SourceFamilies.Compressed r w) :=
  decidable_of_iff (∀ a∈w,∀ b∈w,¬Problem455Swap.Link r w a b)
    ⟨fun f _ _ lk=>f _ (linkNames hr lk).1 _ (linkNames hr lk).2 lk,fun f a _ b _=>f a b⟩
def structural {r} (hr : 0<r) (M : MachineTable n) : Cover (P455StructuralProduct.Index r (allowed M)) :=
  let xs := P455StructuralProduct.templates r
  let p (i : Fin xs.length) := let w:=xs.get i; P455Closure.Cap r w ∧ P455SourceFamilies.Compressed r w ∧ Structural w r (allowed M)
  letI : DecidablePred p := fun i => by
    let w:=xs.get i
    letI := capD r w; letI := compressedD hr w
    letI := widthD 4 w; letI := widthD 3 w; letI := overlapD r M w; letI := intrusionD r M w
    unfold p Structural; dsimp only; infer_instance
  (coverSub (fins _) p).map (fun c=>⟨c.val,c.property.1,c.property.2.1,c.property.2.2⟩)
    (fun ⟨i,cp,cmp,st⟩=>⟨⟨i,cp,cmp,st⟩,rfl⟩)
end P455Enum
