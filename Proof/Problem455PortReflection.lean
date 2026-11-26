import Problem455ContactGeometry
import Problem455ContactReflection




namespace P455PortReflection
open Problem455.Slots P455Witness P455ContactReflection P455ContactGeometry

def roles (a : Node) : W := [a.owner,a.mate]
def sendNode (d : Nat → Nat) (a : Node) : Node := ⟨d a.owner,d a.mate,a.tag⟩
def UniformOn (r : Nat) (v : W) (h : Nat → W) (d : Nat → Nat) (xs : W) :=
  ∀ a ∈ xs, v.count (d a) = r ∧ a ∈ h (d a)

theorem holds_all {r allow mark w} (xs : List Query) :
    Holds r allow mark w (allQ xs) ↔ ∀ q ∈ xs, Holds r allow mark w q := by
  induction xs with
  | nil => simp [allQ,Holds]
  | cons q qs ih => simp only [allQ,Holds,ih,List.forall_mem_cons]

theorem earlyBefore_iff {r allow mark w} (xs ys : W) :
    Holds r allow mark w (earlyBefore xs ys) ↔
    ∀ a ∈ xs, ∀ b ∈ ys, Holds r allow mark w (earlier a 2 b 0) := by
  simp only [earlyBefore,holds_all,List.mem_flatMap,List.mem_map]
  constructor
  · intro h a ha b hb
    exact h _ ⟨a,ha,b,hb,rfl⟩
  · rintro h _ ⟨a,ha,b,hb,rfl⟩
    exact h a ha b hb

section Uniform
variable {r : Nat} {v l k : W} {h : Nat → W} {d : Nat → Nat}
    {allow : Tag → Prop} {mark : Marking}

theorem record_roles_distinct (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (a : Node) (uniform : UniformOn r v h d (roles a))
    (rec : Holds r allow mark (l ++ v.flatMap h ++ k) (typedNode a)) :
    d a.owner ≠ d a.mate := by
  intro eq
  obtain ⟨hx,hs⟩ := uniform a.owner (by simp [roles])
  obtain ⟨_,ht⟩ := uniform a.mate (by simp [roles])
  have nc := contact_excludes_image hr cap hx hs
    (c := .record a.tag false) (b := a.mate) rec
  exact nc (eq ▸ ht)

theorem reflect_typedNode (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (a : Node) (uniform : UniformOn r v h d (roles a))
    (rec : Holds r allow mark (l ++ v.flatMap h ++ k) (typedNode a)) :
    Holds r allow mark v (typedNode (sendNode d a)) := by
  obtain ⟨hx,hs⟩ := uniform a.owner (by simp [roles])
  obtain ⟨hy,ht⟩ := uniform a.mate (by simp [roles])
  exact reflect_contact hr cap hx hy (record_roles_distinct hr cap a uniform rec)
    hs ht (.record a.tag false) rec

theorem reflect_markedNode (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (a : Node) (bit : Bool) (uniform : UniformOn r v h d (roles a)) (sourceMark : Marking)
    (marked : sourceMark (d a.owner) (d a.mate) ∨ sourceMark (d a.mate) (d a.owner))
    (rec : Holds r allow mark (l ++ v.flatMap h ++ k) (markedNode a bit)) :
    Holds r allow sourceMark v (markedNode (sendNode d a) bit) := by
  obtain ⟨ne,len,code,_,eq⟩ := rec
  have rec' : Holds r allow mark (l ++ v.flatMap h ++ k) (typedNode a) :=
    ⟨ne,len,code,bit,eq⟩
  obtain ⟨hx,hs⟩ := uniform a.owner (by simp [roles])
  obtain ⟨hy,ht⟩ := uniform a.mate (by simp [roles])
  have diff := record_roles_distinct hr cap a uniform rec'
  exact ⟨diff,len,code,marked,reflect_profile hr cap hx hy diff hs ht a.tag bit eq⟩

theorem port_injective (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (a b : Node) (phase : Nat) (uniform : UniformOn r v h d (roles a ++ roles b))
    (port : Holds r allow mark (l ++ v.flatMap h ++ k) (orientedPort phase a b)) :
    ∀ s ∈ roles a ++ roles b, ∀ t ∈ roles a ++ roles b, d s = d t → s = t := by
  have each (n : Node) (uni : UniformOn r v h d (roles n))
      (rec : Holds r allow mark (l ++ v.flatMap h ++ k) (typedNode n)) :
      ∀ z ∈ roles n, ∀ t ∈ roles n, d z = d t → z = t := by
    have distinct := record_roles_distinct hr cap n uni rec
    intro z hz t ht eq
    simp [roles] at hz ht
    rcases hz with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all
  have ua : UniformOn r v h d (roles a) := fun x hx => uniform x (by simp [hx])
  have ub : UniformOn r v h d (roles b) := fun x hx => uniform x (by simp [hx])
  have cross (s) (hs : s ∈ roles a) (t) (ht : t ∈ roles b) : d s ≠ d t := by
    intro eq
    obtain ⟨hx,sa⟩ := ua s hs
    obtain ⟨_,tb⟩ := ub t ht
    rw [← eq] at tb
    have early : Holds r allow mark (l ++ v.flatMap h ++ k) (earlyDisjoint (roles a) (roles b)) :=
      port.2.2.1
    rcases early with e | e
    · exact same_image_no_early hr cap hx sa tb (by decide : 0 < 2)
        (((earlyBefore_iff _ _).mp e s hs t ht).2)
    · exact same_image_no_early hr cap hx tb sa (by decide : 0 < 2)
        (((earlyBefore_iff _ _).mp e t ht s hs).2)
  intro s hs t ht eq
  rcases List.mem_append.mp hs with hs | hs <;> rcases List.mem_append.mp ht with ht | ht
  · exact each a ua port.1 s hs t ht eq
  · exact (cross s hs t ht eq).elim
  · exact (cross t ht s hs eq.symm).elim
  · exact each b ub port.2.1 s hs t ht eq

theorem port_owner_order (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (a b : Node) (phase : Nat) (uniform : UniformOn r v h d (roles a ++ roles b))
    (port : Holds r allow mark (l ++ v.flatMap h ++ k) (orientedPort phase a b))
    (pat : List Event) (inside : ∀ e ∈ pat, e.1 ∈ roles a ++ roles b)
    (order : Holds r allow mark (l ++ v.flatMap h ++ k) (.order pat)) :
    Holds r allow mark v (.order (pat.map (eventMap d))) :=
  reflect_order_query hr cap _ d uniform (port_injective hr cap a b phase uniform port)
    pat inside order

theorem reflect_port (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (a b : Node) (phase : Nat) (uniform : UniformOn r v h d (roles a ++ roles b))
    (port : Holds r allow mark (l ++ v.flatMap h ++ k) (orientedPort phase a b)) :
    Holds r allow mark v (orientedPort phase (sendNode d a) (sendNode d b)) := by
  have ua : UniformOn r v h d (roles a) := fun x hx => uniform x (by simp [hx])
  have ub : UniformOn r v h d (roles b) := fun x hx => uniform x (by simp [hx])
  have transfer := port_owner_order hr cap a b phase uniform port
  have early (xs ys : W) (within : ∀ z ∈ xs ++ ys, z ∈ roles a ++ roles b)
      (order : Holds r allow mark (l ++ v.flatMap h ++ k) (earlyBefore xs ys)) :
      Holds r allow mark v (earlyBefore (xs.map d) (ys.map d)) := by
    apply (earlyBefore_iff _ _).mpr
    intro u hu v' hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    have pat := transfer [(i,2),(j,0)] (by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl
      · exact within i (by simp [hi])
      · exact within j (by simp [hj]))
      ((earlyBefore_iff _ _).mp order i hi j hj)
    simpa [eventMap,earlier] using pat
  refine ⟨reflect_typedNode hr cap a ua port.1,reflect_typedNode hr cap b ub port.2.1,?_,?_,True.intro⟩
  · rcases port.2.2.1 with e | e
    · exact Or.inl (early (roles a) (roles b) (fun _ hz => hz) e)
    · exact Or.inr (early (roles b) (roles a) (fun z hz => by simpa [or_comm] using hz) e)
  · let i := 3+2*phase
    have pat := transfer [(a.owner,i),(a.mate,i),(b.owner,i),(b.mate,i),
      (a.owner,i+1),(a.mate,i+1),(b.owner,i+1),(b.mate,i+1)] (by simp [roles]) port.2.2.2.1
    simpa [eventMap, sendNode, i] using pat

theorem reflect_rightward (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (ts : Tiles) (a b : Node) (uniform : UniformOn r v h d (roles a ++ roles b))
    (dir : Holds r allow mark (l ++ v.flatMap h ++ k) (rightward ts a b)) :
    Holds r allow mark v (rightward ts (sendNode d a) (sendNode d b)) := by
  have order := port_owner_order hr cap a b _ uniform dir.2.1
    [(a.owner,13+a.tag.length),(b.owner,13+a.tag.length)] (by simp [roles]) dir.2.2.1
  exact ⟨dir.1,reflect_port hr cap a b _ uniform dir.2.1,
    by simpa [sendNode,eventMap,earlier] using order,True.intro⟩

theorem reflect_downward (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (ts : Tiles) (a b : Node) (uniform : UniformOn r v h d (roles a ++ roles b))
    (dir : Holds r allow mark (l ++ v.flatMap h ++ k) (downward ts a b)) :
    Holds r allow mark v (downward ts (sendNode d a) (sendNode d b)) :=
  ⟨dir.1,reflect_port hr cap a b _ uniform dir.2⟩

theorem reflect_neighbor (hr : 0 < r) (cap : P455Closure.Cap r (l ++ v.flatMap h ++ k))
    (ts : Tiles) (a b : Node) (dir : Dir) (uniform : UniformOn r v h d (roles a ++ roles b))
    (port : Holds r allow mark (l ++ v.flatMap h ++ k) (neighbor ts a b dir)) :
    Holds r allow mark v (neighbor ts (sendNode d a) (sendNode d b) dir) := by
  have rev : UniformOn r v h d (roles b ++ roles a) := fun x hx =>
    uniform x (by simpa [or_comm] using hx)
  cases dir
  · exact reflect_rightward hr cap ts a b uniform port
  · exact reflect_rightward hr cap ts b a rev port
  · exact reflect_downward hr cap ts a b uniform port
  · exact reflect_downward hr cap ts b a rev port

end Uniform

/-- Structural independence of the ambient marking. Only a designated
    marked-bit query reads it. The record and ordering parts of a port
    can therefore be used with any source marking. -/
def markFree : Query → Bool
  | .markedBit .. => false
  | .both x y | .either x y => markFree x && markFree y
  | _ => true

theorem remark {r w allow} {src dst : Marking} {q : Query} (free : markFree q = true)
    (holds : Holds r allow src w q) : Holds r allow dst w q := by
  induction q with
  | fixed | count | deficient | record | order | slot | separate => exact holds
  | markedBit => cases free
  | both x y hx hy =>
    have both := Bool.and_eq_true_iff.mp free
    exact ⟨hx both.1 holds.1, hy both.2 holds.2⟩
  | either x y hx hy =>
    have both := Bool.and_eq_true_iff.mp free
    exact holds.elim (fun a => Or.inl (hx both.1 a)) (fun b => Or.inr (hy both.2 b))

theorem free_port (i : Nat) (a b : Node) : markFree (orientedPort i a b) = true := rfl
theorem free_neighbor (ts : Tiles) (a b : Node) (dir : Dir) :
    markFree (neighbor ts a b dir) = true := by cases dir <;> rfl

theorem port_remark {r w allow} {src dst : Marking} {i a b}
    (holds : Holds r allow src w (orientedPort i a b)) : Holds r allow dst w (orientedPort i a b) :=
  remark (free_port i a b) holds

theorem neighbor_remark {r w allow} {src dst : Marking} {ts a b dir}
    (holds : Holds r allow src w (neighbor ts a b dir)) : Holds r allow dst w (neighbor ts a b dir) :=
  remark (free_neighbor ts a b dir) holds

end P455PortReflection
