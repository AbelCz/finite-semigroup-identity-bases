import Problem455Retained
import Problem455PortReflection




namespace P455OriginalEdges
open Problem455.Slots P455Witness P455Paths P455Retained P455PortReflection

section
variable {r : Nat} {v : W} {e : Nat → W} {kept : Nat → Prop}
    {allow : Tag → Prop} {mark : Marking}

theorem kept_roles (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {a : Node} (rec : Holds r allow mark v (typedNode a)) : ∀ x ∈ roles a, kept x := by
  obtain ⟨cnt,cn'⟩ := record_counts (exp.small_cap hr cap) rec
  intro x hx
  have ct : v.count x = r := by
    rcases (show x = a.owner ∨ x = a.mate by simpa [roles] using hx) with eq|eq
    · exact eq ▸ cnt
    · exact eq ▸ cn'
  apply Classical.byContradiction
  intro gap
  have := (exp.gaps x (List.count_pos_iff.mp (by omega)) gap).1
  omega

theorem expand_markedNode (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {a : Node} {bit : Bool} (rec : Holds r allow mark v (markedNode a bit)) :
    Holds r allow mark (v.flatMap e) (markedNode a bit) := by
  have eq := exp.select_eq v (roles a) (fun _ h => h) (kept_roles exp hr cap (marked_typed rec))
  exact ⟨rec.1,rec.2.1,rec.2.2.1,rec.2.2.2.1,eq.trans rec.2.2.2.2⟩

theorem expand_typedNode (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {a : Node} (rec : Holds r allow mark v (typedNode a)) : Holds r allow mark (v.flatMap e) (typedNode a) :=
  exp.contact hr cap (.record a.tag false) rec

theorem expand_order (exp : Expansion v e kept) {p : List Event}
    (labels : ∀ ev ∈ p, kept ev.1) (ord : Holds r allow mark v (.order p)) :
    Holds r allow mark (v.flatMap e) (.order p) := by
  let ks := p.map Prod.fst
  have all : ∀ a ∈ ks, kept a := by
    intro a h
    obtain ⟨ev,he,rfl⟩ := List.mem_map.mp h
    exact labels ev he
  refine ⟨ord.1,P455ContactReflection.select_sees ks _ p ?_⟩
  rw [exp.select_eq v ks (fun _ h => h) all]
  exact P455ContactReflection.sees_select ks _ p (fun ev he => List.mem_map_of_mem he) ord.2

theorem expand_earlier (exp : Expansion v e kept) {a i b j}
    (ha : kept a) (hb : kept b) (ord : Holds r allow mark v (earlier a i b j)) :
    Holds r allow mark (v.flatMap e) (earlier a i b j) :=
  expand_order exp (by simp [ha,hb]) ord

theorem expand_port (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {p : Nat} {a b : Node} (port : Holds r allow mark v (orientedPort p a b)) :
    Holds r allow mark (v.flatMap e) (orientedPort p a b) := by
  obtain ⟨ra,rb,early,order,_⟩ := port
  have ka := kept_roles exp hr cap ra
  have kb := kept_roles exp hr cap rb
  have earl {xs ys : W} (kx : ∀ a ∈ xs, kept a) (ky : ∀ a ∈ ys, kept a)
      (obs : Holds r allow mark v (earlyBefore xs ys)) :
      Holds r allow mark (v.flatMap e) (earlyBefore xs ys) := by
    apply (earlyBefore_iff _ _).mpr
    exact fun a ha b hb => expand_earlier exp (kx a ha) (ky b hb) ((earlyBefore_iff _ _).mp obs a ha b hb)
  refine ⟨expand_typedNode exp hr cap ra,expand_typedNode exp hr cap rb,?_,?_,True.intro⟩
  · exact early.elim (fun h => Or.inl (earl ka kb h)) (fun h => Or.inr (earl kb ka h))
  · have ka' : kept a.owner ∧ kept a.mate := by simpa [roles] using ka
    have kb' : kept b.owner ∧ kept b.mate := by simpa [roles] using kb
    exact expand_order exp (by simp [ka'.1,ka'.2,kb'.1,kb'.2]) order

theorem expand_right (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {ts : Tiles} {a b : Node} (q : Holds r allow mark v (rightward ts a b)) :
    Holds r allow mark (v.flatMap e) (rightward ts a b) := by
  have p := q.2.1
  exact ⟨q.1,expand_port exp hr cap p,expand_earlier exp (kept_roles exp hr cap p.1 _ (by simp [roles]))
    (kept_roles exp hr cap p.2.1 _ (by simp [roles])) q.2.2.1,True.intro⟩

theorem expand_down (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {ts : Tiles} {a b : Node} (q : Holds r allow mark v (downward ts a b)) :
    Holds r allow mark (v.flatMap e) (downward ts a b) := ⟨q.1,expand_port exp hr cap q.2⟩

theorem expand_neighbor (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {ts : Tiles} {a b : Node} (d : Dir) (q : Holds r allow mark v (neighbor ts a b d)) :
    Holds r allow mark (v.flatMap e) (neighbor ts a b d) := by
  cases d with
  | right => exact expand_right exp hr cap q
  | left => exact expand_right exp hr cap q
  | down => exact expand_down exp hr cap q
  | up => exact expand_down exp hr cap q

private theorem flag {b : Bool} {q : Query}
    (f : Holds r allow mark v q → Holds r allow mark (v.flatMap e) q)
    (h : Holds r allow mark v (flagQ b q)) : Holds r allow mark (v.flatMap e) (flagQ b q) := by
  cases b
  · exact True.intro
  · exact f h

theorem expand_edge (exp : Expansion v e kept) (hr : 1 < r) (cap : P455Closure.Cap r (v.flatMap e))
    {ts : Tiles} {edge : EdgeCertificate} (query : Holds r allow mark v (edge.query ts)) :
    Holds r allow mark (v.flatMap e) (edge.query ts) := by
  obtain ⟨a,b,localQ,succ,_⟩ := query
  refine ⟨expand_markedNode exp hr cap a,expand_markedNode exp hr cap b,?_,?_,True.intro⟩
  · exact ⟨flag (expand_right exp hr cap) localQ.1,flag (expand_right exp hr cap) localQ.2.1,
      flag (expand_down exp hr cap) localQ.2.2.1,flag (expand_down exp hr cap) localQ.2.2.2.1,
      flag (fun ⟨d,r⟩ => ⟨expand_down exp hr cap d,expand_right exp hr cap r⟩) localQ.2.2.2.2.1,
      True.intro⟩
  · have ka : kept edge.a.owner := kept_roles exp hr cap (marked_typed a) _ (by simp [roles])
    have kb : kept edge.b.owner := kept_roles exp hr cap (marked_typed b) _ (by simp [roles])
    unfold chosenSuccessor at succ ⊢
    dsimp only at succ ⊢
    split at succ
    next ret =>
      rw [if_pos ret]
      exact ⟨succ.1,succ.2.1.elim (fun f => Or.inl (expand_port exp hr cap f))
        (fun b => Or.inr (expand_port exp hr cap b)),expand_earlier exp kb ka succ.2.2.1,True.intro⟩
    next notRet =>
      rw [if_neg notRet]
      exact ⟨succ.1,expand_earlier exp ka kb succ.2⟩

end
end P455OriginalEdges
