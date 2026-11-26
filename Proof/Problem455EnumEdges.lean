import Problem455EnumGuards
namespace P455Enum
open P455Witness P455Paths P455PaddedTiles P455CatalogueBounds P455EdgeProduct P455EdgeProjection
def certificates (w : List Nat) (ts : List Tag) : List EdgeCertificate :=
  let nodes := pool w ts
  nodes.flatMap fun a => nodes.flatMap fun b => nodes.flatMap fun right => nodes.flatMap fun left =>
    nodes.flatMap fun down => nodes.flatMap fun up => nodes.map fun diag => ⟨a,b,right,left,down,up,diag⟩
theorem bounded_mem {w ts} (e : EdgeCertificate) (all : ∀ v∈fields e,v∈pool w ts) : e∈certificates w ts := by
  simp only [certificates,List.mem_flatMap,List.mem_map]
  exact ⟨_,all e.a (by simp [fields]),_,all e.b (by simp [fields]),_,all e.right (by simp [fields]),
    _,all e.left (by simp [fields]),_,all e.down (by simp [fields]),_,all e.up (by simp [fields]),
    _,all e.diagonal (by simp [fields]),rfl⟩
instance markD (a b c d : Nat) : DecidableRel (marks a b c d) := by
  intro x y; unfold marks; infer_instance
def sameNamesD (w v : List Nat) : Decidable (∀ x : Nat,x∈w ↔ x∈v) :=
  decidable_of_iff ((∀ x∈w,x∈v) ∧ ∀ x∈v,x∈w)
    ⟨fun ⟨f,g⟩ x=>⟨f x,g x⟩,fun h=>⟨fun x=>(h x).1,fun x=>(h x).2⟩⟩
def edgeAccept {r} (hr : 0<r) (M : MachineTable n) (w : List Nat) (cp : P455Closure.Cap r w)
    (a b c d : Nat) : Decidable (∃ e : EdgeCertificate, e.a.owner=a ∧ e.a.mate=b ∧ e.b.owner=c ∧ e.b.mate=d ∧
      (∀ x : Nat, x∈w ↔ x∈names (system n) e) ∧ Holds r (allowed M) (marks a b c d) w (e.query (system n))) :=
  let p (e : EdgeCertificate) := e.a.owner=a ∧ e.a.mate=b ∧ e.b.owner=c ∧ e.b.mate=d ∧
      (∀ x : Nat, x∈w ↔ x∈names (system n) e) ∧ Holds r (allowed M) (marks a b c d) w (e.query (system n))
  letI : DecidablePred p := fun e=>by
    letI := sameNamesD w (names (system n) e)
    letI := holdsD hr (allowed M) (marks a b c d) w _ (statEdge n e)
    unfold p; infer_instance
  decidable_of_iff (∃ e∈certificates w (tags M),p e) ⟨fun ⟨e,_,h⟩=>⟨e,h⟩,by
    rintro ⟨e,h1,h2,h3,h4,ns,h⟩
    obtain ⟨k,ka,kb,eq,read,bounds⟩ := bounded_edge cp (tags M) (fun _ h=>mem_tags.mpr h) e h
    exact ⟨k,bounded_mem k bounds,by rw [ka,h1],by rw [ka,h2],by rw [kb,h3],by rw [kb,h4],
      by simpa only [eq] using ns,read⟩⟩
abbrev EdgeKey (r : Nat) := Fin (words r).length × Fin 14 × Fin 14 × Fin 14 × Fin 14
def edge {r} (hr : 0<r) (M : MachineTable n) : Cover (Index r (allowed M) (system n)) :=
  let p (key : EdgeKey r) := let w := (words r).get key.1
    let (a,b,c,d) := key.2
    P455Closure.Cap r w ∧ ∃ e : EdgeCertificate, e.a.owner=a.val ∧ e.a.mate=b.val ∧ e.b.owner=c.val ∧ e.b.mate=d.val ∧
      (∀ x : Nat, x∈w ↔ x∈names (system n) e) ∧ Holds r (allowed M) (marks a b c d) w (e.query (system n))
  letI : DecidablePred p := fun ⟨i,a,b,c,d⟩=>by
    let w:=(words r).get i
    letI := capD r w
    by_cases cp : P455Closure.Cap r w
    · letI := edgeAccept hr M w cp a b c d
      unfold p; dsimp only; infer_instance
    · exact .isFalse (fun h=>cp h.1)
  let keys : Cover (EdgeKey r) := pairCover (fins _) (pairCover (fins _) (pairCover (fins _) (pairCover (fins _) (fins _))))
  (coverSub keys p).map (fun z=>⟨z.val.1,z.val.2.1,z.val.2.2.1,z.val.2.2.2.1,z.val.2.2.2.2,z.property.1,z.property.2⟩)
    (fun ⟨i,a,b,c,d,cp,ok⟩=>⟨⟨(i,a,b,c,d),cp,ok⟩,rfl⟩)

deriving instance DecidableEq for P455GuardProduct.Index
deriving instance DecidableEq for P455EdgeProduct.Index
deriving instance DecidableEq for P455StructuralProduct.Index
deriving instance DecidableEq for P455BinaryProduct.Index

end P455Enum
