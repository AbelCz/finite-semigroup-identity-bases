import Problem455Witness

/- Routes are expressed in the same concrete contact predicates as the
   certificate. Each step records its record or port orientation. -/
namespace P455Paths
open P455Witness Problem455.Slots

abbrev Step := Nat × ContactChoice
def Walk (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) (s : Nat) :
    List Step → Prop
  | [] => True
  | (b,c) :: rest => Holds r allow mark w (contact r s b c) ∧ Walk r allow mark w b rest

def endpoint (s : Nat) : List Step → Nat
  | [] => s
  | (b,_) :: rest => endpoint b rest

theorem route_iff {r allow mark w} (s : Nat) (p : List Step) (f : Nat → Query) :
    Holds r allow mark w (route r s p f) ↔
      Walk r allow mark w s p ∧ Holds r allow mark w (f (endpoint s p)) := by
  induction p generalizing s with
  | nil => simp [route, Walk, endpoint]
  | cons p ps ih => rcases p with ⟨b,c⟩; simp only [route,Holds,Walk,endpoint,ih,and_assoc]

def Near (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) (s b J : Nat) : Prop :=
  ∃ p, Walk r allow mark w s p ∧ endpoint s p = b ∧ p.length ≤ J

theorem near_self {r allow mark w} (s J : Nat) : Near r allow mark w s s J :=
  ⟨[],True.intro,rfl,Nat.zero_le _⟩

theorem near_one {r allow mark w s t} (c : ContactChoice)
    (hc : Holds r allow mark w (contact r s t c)) : Near r allow mark w s t 1 :=
  ⟨[(t,c)],⟨hc,True.intro⟩,rfl,Nat.le_refl _⟩

theorem near_mono {r allow mark w s b n m} (h : Near r allow mark w s b n) (le : n ≤ m) :
    Near r allow mark w s b m := by
  obtain ⟨p,v,e,len⟩ := h; exact ⟨p,v,e,Nat.le_trans len le⟩

theorem walk_append {r allow mark w} (a : Nat) (p q : List Step) :
    Walk r allow mark w a (p++q) ↔ Walk r allow mark w a p ∧ Walk r allow mark w (endpoint a p) q := by
  induction p generalizing a with
  | nil => simp [Walk,endpoint]
  | cons ab p ih => obtain ⟨b,c⟩ := ab; simp [Walk,endpoint,ih,and_assoc]

theorem endpoint_append (a : Nat) (p q : List Step) :
    endpoint a (p++q) = endpoint (endpoint a p) q := by
  induction p generalizing a with
  | nil => rfl
  | cons ab p ih => exact ih ab.1

theorem near_trans {r allow mark w a b c i j} (h : Near r allow mark w a b i)
    (g : Near r allow mark w b c j) : Near r allow mark w a c (i+j) := by
  obtain ⟨p,hp,ep,lp⟩ := h
  obtain ⟨q,hq,eq,lq⟩ := g
  exact ⟨p++q,(walk_append ..).mpr ⟨hp,ep.symm ▸ hq⟩,
         by rw [endpoint_append,ep,eq], by simp; omega⟩

abbrev V (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) := Holds r allow mark w

theorem allQ_iff {r allow mark w} (qs : List Query) :
    V r allow mark w (allQ qs) ↔ ∀ q ∈ qs, V r allow mark w q := by
  induction qs with
  | nil => simp [allQ,V,Holds]
  | cons x xs ih => change (_ ∧ V r allow mark w (allQ xs)) ↔ _; simp [ih]

theorem slot_route {r allow mark w} (s : SlotCertificate)
    (ok : V r allow mark w (s.query r)) :
    let a := if s.startAtMate then s.anchor.mate else s.anchor.owner
    s.steps.length ≤ 6 ∧ Walk r allow mark w a s.steps ∧
    V r allow mark w (terminalSlot r (endpoint a s.steps) s.terminalIndex s.defect) := by
  simp only [SlotCertificate.query,allQ,Holds,V] at ok
  exact ⟨ok.2.1,(route_iff ..).mp ok.2.2.1⟩

theorem record_counts {r allow mark w a b tag}
    (bound : P455Closure.Cap r w) (rec : V r allow mark w (.record a b tag)) :
    w.count a = r ∧ w.count b = r := by
  obtain ⟨ne,hl,_,bit,eq⟩ := rec
  have n := congrArg List.length eq
  simp only [length_select_pair a b ne,profile,List.length_append,profile_prefix_length] at n
  have ca := bound a; have cb := bound b
  cases bit <;> simp [pair] at n <;> omega

theorem record_pair {r allow mark w} {n : Node} (rec : V r allow mark w (typedNode n)) :
    Near r allow mark w n.owner n.mate 1 ∧ Near r allow mark w n.mate n.owner 1 :=
  ⟨near_one (.record n.tag false) rec, near_one (.record n.tag true) rec⟩

private theorem stamp_lower (n : Nat → Nat) (w : W) (a i : Nat)
    (h : (a,i) ∈ stamp n w) : n a ≤ i := by
  induction w generalizing n with
  | nil => simp [stamp] at h
  | cons b w ih =>
    rcases List.mem_cons.mp h with he|hh
    · cases he; exact Nat.le_refl _
    · have z := ih (advance n [b]) hh; simp only [advance] at z; omega

theorem stamp_unique (n : Nat → Nat) (w : W) : (stamp n w).Nodup := by
  induction w generalizing n with
  | nil => simp [stamp]
  | cons a w ih =>
    apply List.nodup_cons.mpr
    refine ⟨fun bad => ?_, ih _⟩
    have low := stamp_lower (advance n [a]) w a (n a) bad
    simp [advance] at low
    omega

theorem owner_early {r allow mark w} (a b : Node)
    (early : V r allow mark w (earlyDisjoint [a.owner,a.mate] [b.owner,b.mate])) :
    V r allow mark w (earlyDisjoint [a.owner] [b.owner]) := by
  rcases early with h|h
  · left; exact ⟨h.1,True.intro⟩
  · right; exact ⟨h.1,True.intro⟩

theorem owner_port {r allow mark w} (cap : P455Closure.Cap r w) (p : Fin 5) (a b : Node)
    (ok : V r allow mark w (orientedPort p a b)) :
    V r allow mark w (contact r a.owner b.owner (.port p false)) ∧
    V r allow mark w (contact r b.owner a.owner (.port p true)) := by
  obtain ⟨na,nb,early,order,_⟩ := ok
  let i := 3 + 2*p.val
  let pat := [(a.owner,i),(b.owner,i),(a.owner,i+1),(b.owner,i+1)]
  have sub : pat.Sublist [(a.owner,i),(a.mate,i),(b.owner,i),(b.mate,i),
            (a.owner,i+1),(a.mate,i+1),(b.owner,i+1),(b.mate,i+1)] := by
    exact .cons₂ _ (.cons _ (.cons₂ _ (.cons _ (.cons₂ _ (.cons _ (.cons₂ _ (List.nil_sublist _)))))))
  have obs : V r allow mark w (.order pat) :=
    ⟨fun e he => order.1 e (sub.subset he),sub.trans order.2⟩
  have nd := (stamp_unique (fun _ => 0) w).sublist obs.2
  have ne : a.owner ≠ b.owner := by
    intro eq
    have := (List.nodup_cons.mp nd).1
    exact this (by simp [eq])
  have xa := (record_counts cap na).1
  have xb := (record_counts cap nb).1
  have ed := owner_early a b early
  exact ⟨⟨ne,xa,xb,ed,obs,True.intro⟩,⟨Ne.symm ne,xb,xa,ed.symm,obs,True.intro⟩⟩

/-- One actual port yields an owner contact in both directions. -/
def Joined (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) (a b : Node) :=
  Near r allow mark w a.owner b.owner 1 ∧ Near r allow mark w b.owner a.owner 1

theorem port_joined {r allow mark w} (cap : P455Closure.Cap r w) (n : Nat) (hn : n < 5)
    {a b : Node} (ok : V r allow mark w (orientedPort n a b)) : Joined r allow mark w a b := by
  obtain ⟨f,g⟩ := owner_port cap ⟨n,hn⟩ a b ok
  exact ⟨near_one _ f,near_one _ g⟩

theorem right_paths {r allow mark w ts a b} (cap : P455Closure.Cap r w)
    (ok : V r allow mark w (rightward ts a b)) : Joined r allow mark w a b :=
  port_joined cap _ (by split <;> decide) ok.2.1
theorem down_paths {r allow mark w ts a b} (cap : P455Closure.Cap r w)
    (ok : V r allow mark w (downward ts a b)) : Joined r allow mark w a b :=
  port_joined cap _ (by split <;> decide) ok.2

theorem neighbor_paths {r allow mark w ts a b} (cap : P455Closure.Cap r w) (d : Dir)
    (ok : V r allow mark w (neighbor ts a b d)) : Joined r allow mark w a b := by
  cases d with
  | right => exact right_paths cap ok
  | left => exact (right_paths cap ok).symm
  | down => exact down_paths cap ok
  | up => exact (down_paths cap ok).symm

theorem neighbor_target_record {r allow mark w ts a b d}
    (ok : V r allow mark w (neighbor ts a b d)) : V r allow mark w (typedNode b) := by
  cases d with
  | right => exact ok.2.1.2.1
  | left => exact ok.2.1.1
  | down => exact ok.2.2.1
  | up => exact ok.2.1

theorem marked_typed {r allow mark w a bit} (m : V r allow mark w (markedNode a bit)) :
    V r allow mark w (typedNode a) := ⟨m.1,m.2.1,m.2.2.1,bit,m.2.2.2.2⟩

end P455Paths
