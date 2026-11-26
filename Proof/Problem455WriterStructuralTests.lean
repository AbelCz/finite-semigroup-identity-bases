import Problem455WriterObservations
namespace P455WriterStructural
open P455WriterTiles P455WriterProfiles P455WriterObservations P455PaddedTiles
open P455Structural (Rec Edge Intrusion Width Overlap)
open Problem455.Slots
local instance (w : W) (p : List Event) : Decidable (sees w p) := P455Enum.seesD w p

def recordB (r : Nat) (ts : Tags) (w : W) (a b : Nat) :=
  decide (a≠b) && (choices ts [false,true]).any (fun tb =>
    decide (tb.1.length+16=r ∧ select [a,b] w=profile a b tb.1 tb.2))

def edgeB (r : Nat) (ts : Tags) (w : W) (a b : Nat) :=
  recordB r ts w a b || recordB r ts w b a

theorem record_correct (M : MachineTable n) (r w a b) :
    recordB r (P455Enum.tags M) w a b=true ↔ Rec w r (allowed M) a b := by
  simp only [recordB,choices,List.any_eq_true,List.mem_flatMap,List.mem_map,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hne,_,⟨t,mt,bit,_,rfl⟩,le,eq⟩
    exact ⟨t,hne,le,P455Enum.mem_tags.mp mt,bit,eq⟩
  · rintro ⟨t,hne,le,mt,bit,eq⟩
    refine ⟨hne,(t,bit),⟨t,P455Enum.mem_tags.mpr mt,bit,?_,rfl⟩,le,eq⟩
    cases bit <;> simp

theorem edge_correct (M : MachineTable n) (r w a b) :
    edgeB r (P455Enum.tags M) w a b=true ↔ Edge w r (allowed M) a b := by
  simp only [edgeB,Bool.or_eq_true,record_correct,Edge]

def widthB (k : Nat) (w : W) := (Problem455Finite.wordsUpTo w k).any fun c => w.all fun x => decide (x∈c)

theorem width_correct (k : Nat) (w : W) : widthB k w=true ↔ Width k w := by
  simp only [widthB,List.any_eq_true,List.all_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨c,m,h⟩
    exact ⟨c,P455Enum.words_bound _ _ m,h⟩
  · rintro ⟨c,lim,h⟩
    let t := c.filter fun x => x∈w
    have cover (x) (m : x∈w) : x∈t := by simp [t,h x m,m]
    exact ⟨t,Problem455Finite.covered _ _ t ((List.length_filter_le ..).trans lim)
      (fun _ m => of_decide_eq_true (List.mem_filter.mp m).2),cover⟩

def overlapB (r : Nat) (ts : Tags) (w : W) :=
  (choices w (choices w w)).any fun k =>
    decide (k.1≠k.2.1 ∧ k.1≠k.2.2 ∧ k.2.1≠k.2.2) &&
    edgeB r ts w k.1 k.2.1 && edgeB r ts w k.1 k.2.2

theorem overlap_correct (M : MachineTable n) (r w) :
    overlapB r (P455Enum.tags M) w=true ↔ Overlap w r (allowed M) := by
  simp only [overlapB,choices,List.any_eq_true,List.mem_flatMap,List.mem_map,Bool.and_eq_true,
    decide_eq_true_eq,edge_correct]
  constructor
  · rintro ⟨_,⟨o,_,_,⟨p,_,q,_,rfl⟩,rfl⟩,⟨⟨op,oq,pq⟩,ep⟩,eq⟩
    exact ⟨o,p,q,op,oq,pq,ep,eq⟩
  · rintro ⟨o,p,q,op,oq,pq,ep,eq⟩
    exact ⟨_,⟨o,(P455Enum.edge_names ep).1,_,⟨p,(P455Enum.edge_names ep).2,q,(P455Enum.edge_names eq).2,rfl⟩,rfl⟩,
      ⟨⟨op,oq,pq⟩,ep⟩,eq⟩

def intrusionB (r : Nat) (ts : Tags) (w : W) :=
  (choices w (choices w (events w))).any fun k =>
    decide (k.1≠k.2.1 ∧ k.2.2.1≠k.1 ∧ k.2.2.1≠k.2.1) &&
    recordB r ts w k.1 k.2.1 && decide (sees w [(k.1,0),k.2.2,(k.2.1,2)])

theorem intrusion_correct (M : MachineTable n) (r w) :
    intrusionB r (P455Enum.tags M) w=true ↔ Intrusion w r (allowed M) := by
  simp only [intrusionB,choices,List.any_eq_true,List.mem_flatMap,List.mem_map,Bool.and_eq_true,
    decide_eq_true_eq,record_correct]
  constructor
  · rintro ⟨_,⟨o,_,_,⟨p,_,e,_,rfl⟩,rfl⟩,⟨⟨op,zo,zp⟩,rec⟩,s⟩
    exact ⟨o,p,e.1,e.2,op,zo,zp,rec,s⟩
  · rintro ⟨o,p,z,j,op,zo,zp,rec,s⟩
    exact ⟨_,⟨o,(P455Enum.rec_names rec).1,_,⟨p,(P455Enum.rec_names rec).2,(z,j),s.subset (by simp),rfl⟩,rfl⟩,
      ⟨⟨op,zo,zp⟩,rec⟩,s⟩

def compressedB (r : Nat) (w : W) :=
  (choices w w).all fun p => decide (Problem455Swap.bigram p.1 p.2 w ≠ r)

theorem compressed_correct {r : Nat} (pos : 0<r) (w : W) :
    compressedB r w=true ↔ P455SourceFamilies.Compressed r w := by
  simp only [compressedB,choices,List.all_eq_true,List.mem_flatMap,List.mem_map,decide_eq_true_eq]
  constructor
  · intro h a b link
    exact h (a,b) ⟨a,(P455Enum.linkNames pos link).1,b,(P455Enum.linkNames pos link).2,rfl⟩ link
  · rintro h _ ⟨a,_,b,_,rfl⟩
    exact h a b

end P455WriterStructural
