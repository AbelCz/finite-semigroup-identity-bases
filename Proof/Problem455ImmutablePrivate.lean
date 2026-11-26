import Problem455FlipFromWord

/- Protected literal factors pass to a mixed evaluation of the indexed
   adjacent-swap layout. The target is an arbitrary actual word. -/
namespace P455ImmutablePrivate
open P455Structural Problem455.Slots
abbrev W := List Nat
private def initial (a b : Nat) : List Event := [(a,0),(a,1),(b,0),(a,2),(b,1),(b,2)]

theorem stamp_length (n : Nat → Nat) (w : W) : (stamp n w).length=w.length := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih => simp [stamp,ih]

theorem read_names (n : Nat → Nat) (w : W) : (stamp n w).map Prod.fst=w := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih => simp [stamp,ih]

private theorem stamp_low {n : Nat → Nat} {w : W} {a i : Nat} (m : (a,i)∈stamp n w) : n a≤i := by
  induction w generalizing n with
  | nil => contradiction
  | cons b w ih =>
    rcases List.mem_cons.mp m with h|h
    · cases h; exact Nat.le_refl _
    · have lower := ih h
      simp only [advance] at lower; omega

private theorem whole_core {a b : Nat} (ne : a≠b) (l : W) (ax : a∉l) (bx : b∉l) (q : W) :
    events (l++early a b++q) = events l ++ (initial a b ++ stamp (advance (fun _ => 0) (l++early a b)) q) := by
  have la := List.count_eq_zero.mpr ax
  have lb := List.count_eq_zero.mpr bx
  simp [events,stamp_append,initial,early,stamp,advance,List.count_cons,ne,Ne.symm ne,la,lb]
  simp only [advance_append,List.append_assoc,List.singleton_append,List.nil_append]
  rfl

private theorem prefix_of_reads {α : Type} (xs ys : List α)
    (same : ∀ (i : Nat) (e : α), xs[i]?=some e → ys[i]?=some e) : xs <+: ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have first := same 0 a rfl
    cases ys with
    | nil => contradiction
    | cons b ys =>
      have ab : b=a := Option.some.inj first
      subst b
      obtain ⟨q,eq⟩ := ih ys (fun i e h => same (i+1) e h)
      exact ⟨q,congrArg (List.cons a) eq⟩

/-- Agreement only at the original *immutable* events suffices. This
    covers partially flipped layouts and avoids assuming the target
    remains closed or even capped. -/
theorem closed_transport {r : Nat} {u v : W} {a b : Nat} (hr : 5≤r)
    (closed : Closed u a b)
    (agree : ∀ (i : Nat) (e : Event), (events u)[i]?=some e → e.2≠r-2 → (events v)[i]?=some e) :
    Closed v a b := by
  obtain ⟨ne,l,q,eu,ax,bx⟩ := closed
  let old := initial a b
  have core := whole_core ne l ax bx q
  have atNew (j : Nat) (e : Event) (someE : old[j]?=some e) :
      (events v)[l.length+j]?=some e := by
    obtain ⟨bound,fnd⟩ := List.getElem?_eq_some_iff.mp someE
    have mem : e ∈ old := fnd ▸ List.getElem_mem bound
    have small : e.2≤2 := by
      simp only [old,initial,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with h|h|h|h|h|h <;> rw [h] <;> simp
    apply agree _ _ _ (by omega)
    rw [eu,core,List.getElem?_append_right (by
      change (stamp (fun _ => 0) l).length ≤ l.length+j
      rw [stamp_length]; omega)]
    simp only [events,stamp_length,Nat.add_sub_cancel_left]
    exact (List.getElem?_append_left bound).trans someE
  have vlen : l.length<v.length := by
    have m := atNew 0 (a,0) rfl
    obtain ⟨lt,_⟩ := List.getElem?_eq_some_iff.mp m
    simpa [events,stamp_length] using lt
  let low := v.take l.length
  let hi := v.drop l.length
  have split : low++hi=v := List.take_append_drop .. 
  have ll : (stamp (fun _ => 0) low).length=l.length := by
    simp [stamp_length,low,Nat.min_eq_left (Nat.le_of_lt vlen)]
  have tail : old <+: stamp (advance (fun _ => 0) low) hi := by
    apply prefix_of_reads
    intro i e got
    have m := atNew i e got
    change (stamp (fun _ => 0) v)[l.length+i]?=some e at m
    rw [←split,stamp_append,List.getElem?_append_right (by omega),ll] at m
    simpa only [show l.length+i-l.length=i by omega] using m
  obtain ⟨z,ez⟩ := tail
  have lowFirst (c : Nat) (h : (c,0) ∈ old) : c∉low := by
    have m : (c,0)∈stamp (advance (fun _ => 0) low) hi := ez ▸ List.mem_append_left z h
    have le := stamp_low m
    change 0+low.count c≤0 at le
    exact List.count_eq_zero.mp (by omega)
  have fst := congrArg (List.map Prod.fst) ez
  simp only [List.map_append,read_names] at fst
  change early a b ++ List.map Prod.fst z = hi at fst
  exact ⟨ne,low,z.map Prod.fst,by rw [←split,←fst]; simp [List.append_assoc],
    lowFirst a (by simp [old,initial]),lowFirst b (by simp [old,initial])⟩

end P455ImmutablePrivate
