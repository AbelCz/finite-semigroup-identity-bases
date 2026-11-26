import Problem455PaddedPorts
import Problem455ContactGeometry



namespace P455PaddedPorts
open P455RectangleRank Problem455.Slots

theorem count_one {ks : W} (nd : ks.Nodup) {a : Nat} (m : a∈ks) : ks.count a=1 := by
  induction ks with
  | nil => simp at m
  | cons x ks ih =>
    obtain ⟨out,tail⟩ := List.nodup_cons.mp nd
    by_cases e : a=x
    · subst x; simp [List.count_cons,List.count_eq_zero.mpr out]
    · have z : a∈ks := by simpa [e] using m
      simp [List.count_cons,e,Ne.symm e,ih tail z]

theorem count_phase (bs : List Block) (c : Nat) :
    (phase bs).count c = 2*(bs.flatMap cells).count c := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change ((cells b ++ cells b) ++ phase bs).count c=2*((cells b) ++ bs.flatMap cells).count c
    simp only [List.count_append,ih]; omega

theorem count_role (s : W) (c a : Nat) (target : a=owner c ∨ a=mate c) :
    (s.flatMap roles).count a=s.count c := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    simp only [List.flatMap_cons,List.count_append,ih]
    by_cases eq : k=c
    · subst k
      rcases target with rfl|rfl <;> simp [roles,List.count_cons,owner,mate] <;> omega
    · have non : a∉roles k := by
        unfold roles
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        unfold owner mate at target ⊢; omega
      simp [List.count_eq_zero.mpr non,List.count_cons,eq,Ne.symm eq]

/-- Context can contribute arbitrarily many other events, including earlier
or later copies of the four observed roles. Only the counts at the actual
phase boundary are relevant. -/
theorem indexed_window {ks pre mid post : W} {k : Nat} (nd : ks.Nodup)
    (before : ∀ a∈ks, pre.count a=k) (inside : ∀ a∈ks, mid.count a=2) :
    sees (pre++mid++post) (stamp (fun _=>k) (ks++ks)) ↔ select ks mid=ks++ks := by
  let active (e : Event) := decide (e.1∈ks ∧ k≤e.2 ∧ e.2<k+2)
  let zero : Nat → Nat := fun _=>0
  let p : Nat → Nat := fun a=>pre.count a
  let q : Nat → Nat := fun a=>pre.count a+mid.count a
  have whole : events (pre++mid++post)=stamp zero pre ++ (stamp p mid ++ stamp q post) := by
    simp only [List.append_assoc,events,stamp_append]
    have e : advance (fun _=>0) pre=p := by funext a; simp [advance,p]
    have f : advance p mid=q := by rfl
    rw [e,f]
  have none₁ : (stamp zero pre).filter active=[] := by
    apply List.filter_eq_nil_iff.mpr
    rintro ⟨a,i⟩ mem yes
    obtain ⟨m,lo,_⟩ := of_decide_eq_true yes
    have lim := (P455ContactGeometry.stamp_range zero pre mem).2
    change i<0+pre.count a at lim
    have := before a m; omega
  have none₂ : (stamp q post).filter active=[] := by
    apply List.filter_eq_nil_iff.mpr
    rintro ⟨a,i⟩ mem yes
    obtain ⟨m,_,hi⟩ := of_decide_eq_true yes
    have lim := (P455ContactGeometry.stamp_range q post mem).1
    change pre.count a+mid.count a≤i at lim
    have := before a m; have := inside a m; omega
  have middle : (stamp p mid).filter active=stamp (fun _=>k) (select ks mid) := by
    rw [P455ContactGeometry.project_stamp ks mid (fun _=>k) p (fun a m => (before a m).symm)]
    apply List.filter_congr
    rintro ⟨a,i⟩ mem
    by_cases m : a∈ks
    · have lim := P455ContactGeometry.stamp_range p mid mem
      change pre.count a≤i ∧ i<pre.count a+mid.count a at lim
      have := before a m; have := inside a m
      simp [active,m,show k≤i by omega,show i<k+2 by omega]
    · simp [active,m]
  have observed : (events (pre++mid++post)).filter active=stamp (fun _=>k) (select ks mid) := by
    simp only [whole,List.filter_append,none₁,none₂,middle,List.append_nil,List.nil_append]
  have full : (stamp (fun _=>k) (ks++ks)).filter active = stamp (fun _=>k) (ks++ks) := by
    apply List.filter_eq_self.mpr
    rintro ⟨x,i⟩ m
    have mem := stamped_mem_label (fun _=>k) (ks++ks) _ m
    have mx : x∈ks := by simpa using mem
    have lim := P455ContactGeometry.stamp_range (fun _=>k) (ks++ks) m
    simp only [List.count_append,count_one nd mx] at lim
    exact decide_eq_true ⟨mx,lim.1,by omega⟩
  constructor
  · intro seq
    have sub := seq.filter active
    change ((stamp (fun _=>k) (ks++ks)).filter active).Sublist ((events (pre++mid++post)).filter active) at sub
    rw [full,observed] at sub
    have words := sub.map Prod.fst
    simp only [labels_of_stamp] at words
    have perm : (select ks mid).Perm (ks++ks) := by
      apply List.perm_iff_count.mpr
      intro a
      by_cases m : a∈ks
      · unfold select
        rw [List.count_filter (p:=fun e => decide (e ∈ ks)) (decide_eq_true m),List.count_append,inside a m,count_one nd m]
      · have no : a∉select ks mid := by simp [select,m]
        simp [List.count_eq_zero.mpr no,List.count_eq_zero.mpr m]
    exact (words.eq_of_length perm.length_eq.symm).symm
  · intro eq
    rw [←eq,←observed]
    exact List.filter_sublist ..

def portPattern (i j k : Nat) : List Event :=
  [(owner i,k),(mate i,k),(owner j,k),(mate j,k),
   (owner i,k+1),(mate i,k+1),(owner j,k+1),(mate j,k+1)]

theorem indexed_port_exact {bs : List Block} {pre post : W} {i j k : Nat} (ne : i≠j)
    (nd : (bs.flatMap cells).Nodup) (mi : i∈bs.flatMap cells) (mj : j∈bs.flatMap cells)
    (prefixCount : ∀ a∈roles i ++ roles j, pre.count a=k) :
    sees (pre++letters bs++post) (portPattern i j k) ↔ Block.pair i j∈bs := by
  let ks := roles i ++ roles j
  have dis : owner i≠mate i ∧ owner j≠mate j ∧ owner i≠owner j ∧ owner i≠mate j ∧
      mate i≠owner j ∧ mate i≠mate j := by unfold owner mate; omega
  have nod : ks.Nodup := by simp [ks,roles,dis.1,dis.2.1,dis.2.2.1,dis.2.2.2.1,dis.2.2.2.2.1,dis.2.2.2.2.2]
  have window (a) (used : a∈ks) : (letters bs).count a=2 := by
    have ea : (a=owner i ∨ a=mate i) ∨ (a=owner j ∨ a=mate j) := by
      simpa only [ks,roles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using used
    rcases ea with ai|aj
    · rw [letters,count_role _ i a ai,count_phase,count_one nd mi]
    · rw [letters,count_role _ j a aj,count_phase,count_one nd mj]
  have ev : stamp (fun _=>k) (ks++ks)=portPattern i j k := by
    rw [stamp_append,stamp_at (fun _=>k) k ks nod (fun _ _ => rfl),
      stamp_at (advance (fun _=>k) ks) (k+1) ks nod (fun a m=>by simp [advance,count_one nod m])]
    rfl
  rw [← ev,indexed_window nod prefixCount window]
  exact literal_phase_exact nd i j ne

/-- The original tester query, without any hypothesis that it holds. The
static typed-record and early-disjoint requirements are displayed separately
from the geometric matching criterion. -/
theorem oriented_port_iff {r : Nat} (hr : 16≤r) (allow : P455Witness.Tag → Prop)
    (mark : P455Witness.Marking) (port : Fin 5) (tagI tagJ : P455Witness.Tag)
    {bs : List Block} {pre post : W} {i j : Nat} (ne : i≠j)
    (nd : (bs.flatMap cells).Nodup) (mi : i∈bs.flatMap cells) (mj : j∈bs.flatMap cells)
    (prefixCount : ∀ a∈roles i ++ roles j, pre.count a=3+2*port.val) :
    let a : P455Witness.Node := ⟨owner i,mate i,tagI⟩
    let b : P455Witness.Node := ⟨owner j,mate j,tagJ⟩
    let H := P455Witness.Holds r allow mark (pre++letters bs++post)
    H (P455Witness.orientedPort port.val a b) ↔ H (P455Witness.typedNode a) ∧
      H (P455Witness.typedNode b) ∧ H (P455Witness.earlyDisjoint (roles i) (roles j)) ∧
      Block.pair i j∈bs := by
  dsimp only
  have obs := indexed_port_exact (post:=post) ne nd mi mj prefixCount
  constructor
  · rintro ⟨ta,tb,ear,ord,_⟩
    exact ⟨ta,tb,ear,obs.mp ord.2⟩
  · rintro ⟨ta,tb,ear,matchEdge⟩
    refine ⟨ta,tb,ear,⟨?_,obs.mpr matchEdge⟩,True.intro⟩
    intro e m
    have lt := port.isLt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h|h|h|h|h|h|h|h <;> rw [h] <;> dsimp <;> omega

end P455PaddedPorts
