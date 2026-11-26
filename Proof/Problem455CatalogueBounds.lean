import Problem455EdgeProduct

/- Exact finite witness search for the two-mark catalogue. Syntactically
   unused fields are unbounded in the Lean index. Every successful
   witness has a representative using only occurring names and admitted
   tags, even when nodes and labels alias. -/
namespace P455CatalogueBounds
open P455Witness P455Paths P455CertificateReach P455EdgeProjection Problem455.Slots
abbrev W := List Nat

def canonical (ts : Tiles) (e : EdgeCertificate) : EdgeCertificate :=
  ⟨e.a,e.b,if ts.right e.a.tag then e.a else e.right,
    if ts.left e.a.tag then e.a else e.left,if ts.bottom e.a.tag then e.a else e.down,
    if ts.top e.a.tag then e.a else e.up,
    if ts.right e.a.tag || ts.bottom e.a.tag then e.a else e.diagonal⟩

theorem query_canonical (ts : Tiles) (e : EdgeCertificate) :
    (canonical ts e).query ts = e.query ts := by
  cases rr : ts.right e.a.tag <;> cases ll : ts.left e.a.tag <;>
    cases dd : ts.bottom e.a.tag <;> cases uu : ts.top e.a.tag <;> cases oo : ts.oddRow e.a.tag <;>
      simp [canonical,EdgeCertificate.query,localCert,chosenSuccessor,endOfRow,flagQ,rr,ll,dd,uu,oo]

theorem names_canonical (ts : Tiles) (e : EdgeCertificate) : names ts (canonical ts e)=names ts e := by
  cases rr : ts.right e.a.tag <;> cases ll : ts.left e.a.tag <;>
    cases dd : ts.bottom e.a.tag <;> cases uu : ts.top e.a.tag <;>
      simp [canonical,names,nodes,candidates,rr,ll,dd,uu,List.filter_cons]

def fields (e : EdgeCertificate) := [e.a,e.b,e.right,e.left,e.down,e.up,e.diagonal]

theorem original_active (ts : Tiles) (e : EdgeCertificate) {a : Node}
    (h : a∈fields (canonical ts e)) : Active ts e a := by
  simp only [fields,canonical,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with eq|eq|eq|eq|eq|eq|eq <;> rw [eq]
  · exact .anchor
  · exact .successor
  · cases f : ts.right e.a.tag <;> simp only [f,Bool.false_eq_true,if_false,if_true]
    · exact .right f
    · exact .anchor
  · cases f : ts.left e.a.tag <;> simp only [f,Bool.false_eq_true,if_false,if_true]
    · exact .left f
    · exact .anchor
  · cases f : ts.bottom e.a.tag <;> simp only [f,Bool.false_eq_true,if_false,if_true]
    · exact .down f
    · exact .anchor
  · cases f : ts.top e.a.tag <;> simp only [f,Bool.false_eq_true,if_false,if_true]
    · exact .up f
    · exact .anchor
  · cases rr : ts.right e.a.tag <;> cases dd : ts.bottom e.a.tag <;>
      simp only [rr,dd,Bool.or_false,Bool.or_true,Bool.false_eq_true,if_false,if_true]
    · exact .diagonal rr dd
    all_goals exact .anchor

def pool (w : W) (tags : List Tag) := w.flatMap (fun x => w.flatMap (fun y => tags.map (Node.mk x y)))

theorem record_in_pool {r allow mark w} (tags : List Tag) (finiteTags : ∀ t,allow t → t ∈ tags)
    (node : Node) (valid : Holds r allow mark w (typedNode node)) : node ∈ pool w tags := by
  obtain ⟨_,_,yes,bit,pr⟩ := valid
  have mem (z : Nat) (side : z=node.owner ∨ z=node.mate) : z∈w := by
    have m : z ∈ select [node.owner,node.mate] w := by
      rw [pr]; rcases side with rfl|rfl <;> simp [profile,profilePrefix]
    exact (List.mem_filter.mp m).1
  exact List.mem_flatMap.mpr ⟨node.owner,mem _ (.inl rfl),List.mem_flatMap.mpr
    ⟨node.mate,mem _ (.inr rfl),List.mem_map.mpr ⟨node.tag,finiteTags _ yes,rfl⟩⟩⟩

/-- The exact name-set side condition and both marked name-pairs are
    kept. Arbitrary unused original nodes need not be encoded or bounded. -/
theorem bounded_edge {r allow mark ts w} (cap : P455Closure.Cap r w)
    (tags : List Tag) (finiteTags : ∀ t,allow t → t∈tags) (e : EdgeCertificate)
    (read : Holds r allow mark w (e.query ts)) :
    ∃ c : EdgeCertificate, c.a=e.a ∧ c.b=e.b ∧ names ts c=names ts e ∧
      Holds r allow mark w (c.query ts) ∧ ∀ n ∈ fields c, n ∈ pool w tags := by
  exact ⟨canonical ts e,rfl,rfl,names_canonical ..,(query_canonical ts e) ▸ read,
    fun n mem => record_in_pool tags finiteTags n (active_owner cap ts e read (original_active ts e mem)).2⟩

/-- A catalogue position and its literal template are interchangeable for
    duplicate-free finite alphabets, including all five alphabets used by
    the concrete model. Distinct isomorphic templates remain separate. -/
theorem words_nodup {α : Type} (alphabet : List α) (nd : alphabet.Nodup) (bound : Nat) :
    (Problem455Finite.wordsUpTo alphabet bound).Nodup := by
  induction bound with
  | zero => simp [Problem455Finite.wordsUpTo]
  | succ n ih =>
    apply List.nodup_cons.mpr
    constructor
    · simp [List.mem_flatMap]
    · apply List.pairwise_flatMap.mpr
      constructor
      · intro a _
        exact ih.map (List.cons a) (fun x y ne eq => ne (List.cons.inj eq).2)
      · apply nd.imp
        intro a b ab x hx y hy same
        obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
        exact ab (List.cons.inj same).1

theorem bounded_functionality {r allow ts mark w} (tags : List Tag)
    (finiteTags : ∀ t,allow t → t∈tags) (f : FunctionalityCertificate)
    (ok : Holds r allow mark w (f.query ts)) :
    f.anchor ∈ pool w tags ∧ f.b ∈ pool w tags ∧ f.c ∈ pool w tags := by
  exact ⟨record_in_pool tags finiteTags _ (marked_typed ok.1),
    record_in_pool tags finiteTags _ (neighbor_target_record ok.2.1),
    record_in_pool tags finiteTags _ (neighbor_target_record ok.2.2.1)⟩

end P455CatalogueBounds
