import Problem455PrefixCatalogue




namespace P455ChartBuild
open P455Quotient P455Witness P455FirstRewrite P455Prefix P455WordChart P455Uncrossed P455SlotSaturation
open P455Alignment P455ChangedEvents Problem455.Slots

inductive Chunk where
  | fixed (x : Event)
  | turn (i : Nat) (x y : Event)
  deriving DecidableEq

def row (rev : Nat → Bool) : Chunk → List Event
  | .fixed x => [x]
  | .turn i x y => if rev i then [y,x] else [x,y]

def render (rev : Nat → Bool) (cs : List Chunk) := cs.flatMap (row rev)
def labels (rev : Nat → Bool) (cs : List Chunk) := (render rev cs).map Prod.fst
def active (cs : List Chunk) : List Nat := cs.flatMap (fun | .turn i _ _ => [i] | .fixed _ => [])

abbrev Orig : Nat → Bool := fun _ => false
abbrev Last : Nat → Bool := fun _ => true

def AllInfo (r : Nat) (allow : Tag → Prop) (u v : W) (cs : List Chunk) :=
  ∀ i x y, Chunk.turn i x y ∈ cs → PairInfo r allow u v i x y

theorem indexed_chunks {r allow ts u v} (hr : 0<r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (cmp : P455SourceFamilies.Compressed r u) :
    ∃ cs, AllInfo r allow u v cs ∧ render Orig cs=events u ∧ render Last cs=events v := by
  have non {a b} (d : ChangedPair u v a b) : a≠b := by
    rintro rfl; apply d
    have refl (z : Nat) (w : W) : select [z,z] w=List.replicate (w.count z) z := by
      induction w with
      | nil => rfl
      | cons a w ih => by_cases e : a=z <;> simp_all [select,List.count_cons,List.replicate_succ,Ne.symm]
    rw [refl,refl,P455CellClassBinary.exact_counts cap valid]
  have bs := blocks_of_matching cap valid (fun _ _ _ e f => disjoint_changes hr cap valid cmp (non e) (non f) e f)
  suffices lemma : ∀ {p q}, Blocks (Mates u v r) p q →
      ∃ cs, AllInfo r allow u v cs ∧ render Orig cs=p ∧ render Last cs=q from lemma bs
  intro p q h
  induction h with
  | nil => exact ⟨[],fun _ _ _ h => False.elim (List.not_mem_nil h),rfl,rfl⟩
  | fixed a _ ih =>
    obtain ⟨cs,info,l,k⟩ := ih
    refine ⟨.fixed a::cs,?_,?_,?_⟩
    · intro i x y m; exact info _ _ _ (by simpa using m)
    · simp [render,row,← l]
    · simp [render,row,← k]
  | pair x y mate _ ih =>
    obtain ⟨cs,info,l,k⟩ := ih
    obtain ⟨i,rec⟩ := label_pair cap valid x y mate
    refine ⟨.turn i x y::cs,?_,?_,?_⟩
    · intro j a b m
      rcases List.mem_cons.mp m with eql|tail
      · cases eql; exact rec
      · exact info _ _ _ tail
    · simp [render,row,Orig,← l]
    · simp [render,row,Last,← k]

theorem mem_active {cs : List Chunk} {i : Nat} : i ∈ active cs ↔ ∃ x y, Chunk.turn i x y∈cs := by
  constructor
  · intro m
    obtain ⟨q,mem,h⟩ := List.mem_flatMap.mp m
    cases q with
    | fixed x => exact False.elim (List.not_mem_nil h)
    | turn j a b => obtain rfl : i=j := List.mem_singleton.mp h; exact ⟨a,b,mem⟩
  · rintro ⟨x,y,h⟩; exact List.mem_flatMap.mpr ⟨.turn i x y,h,List.mem_cons_self⟩

theorem renders_equal {s t : Nat → Bool} (cs : List Chunk)
    (eq : ∀ i∈active cs, s i=t i) : render s cs=render t cs := by
  unfold render List.flatMap
  apply congrArg List.flatten
  apply List.map_congr_left
  intro q mem; cases q with
  | fixed => rfl
  | turn i x y => simp only [row,eq i (mem_active.mpr ⟨x,y,mem⟩)]

theorem pos_perm (s t : Nat → Bool) (cs : List Chunk) : (render s cs).Perm (render t cs) := by
  induction cs with
  | nil => exact .refl _
  | cons q cs ih =>
    apply List.Perm.append _ ih
    cases q with
    | fixed => exact .refl _
    | turn i x y =>
      cases e : s i <;> cases f : t i <;> simp only [row,e,f,Bool.false_eq_true,if_false,if_true] <;>
        first | exact .refl _ | exact .swap _ _ _

theorem original_labels {cs u} (orig : render Orig cs=events u) : labels Orig cs=u := by
  rw [labels,orig,events,labels_of_stamp]
theorem final_labels {cs v} (last : render Last cs=events v) : labels Last cs=v := by
  rw [labels,last,events,labels_of_stamp]

private theorem stamp_swap (n : Nat → Nat) (x y : Nat) (ne : x≠y) (t : W) :
    stamp n (y::x::t) = (y,n y)::(x,n x)::stamp (advance (advance n [x]) [y]) t := by
  have oa : advance n [y] x = n x := by simp [advance,ne,Ne.symm ne]
  have tail : advance (advance n [y]) [x]=advance (advance n [x]) [y] := by funext z; simp [advance]; omega
  simp only [stamp,oa,tail]

/-- Choosing arbitrary orientations preserves the occurrence numbers in every
    rendered event; the result really is the stamp of its underlying word. -/
theorem stamp_render {r allow u v} (cs : List Chunk) (info : AllInfo r allow u v cs)
    (n : Nat → Nat) (base : stamp n (labels Orig cs)=render Orig cs) (s : Nat → Bool) :
    stamp n (labels s cs) = render s cs := by
  induction cs generalizing n with
  | nil => rfl
  | cons q cs ih =>
    have tail : AllInfo r allow u v cs := fun i x y m => info _ _ _ (List.mem_cons_of_mem _ m)
    cases q with
    | fixed x =>
      change (x.1,n x.1)::stamp (advance n [x.1]) (labels Orig cs)=x::render Orig cs at base
      exact List.cons.injEq _ _ _ _ |>.mpr ⟨(List.cons.inj base).1,ih tail _ (List.cons.inj base).2⟩
    | turn i x y =>
      have rec := info i x y List.mem_cons_self
      have ne : x.1≠y.1 := by
        rcases rec.roles with ⟨a,b⟩|⟨a,b⟩
        · rw [a,b]; exact rec.typedU.1
        · rw [b,a]; exact Ne.symm rec.typedU.1
      have h := base
      change stamp n (x.1::y.1::labels Orig cs)=x::y::render Orig cs at h
      have diff : advance n [x.1] y.1=n y.1 := by simp [advance,ne,Ne.symm ne]
      simp only [stamp,diff,List.cons.injEq] at h
      have rest := ih tail _ h.2.2
      cases f : s i with
      | false =>
        simpa only [labels,render,List.flatMap_cons,row,f,Bool.false_eq_true,if_false,
          List.cons_append,List.nil_append,List.map_cons,stamp,diff,h.1,h.2.1,List.cons.injEq,true_and] using rest
      | true =>
        simp only [labels,render,List.flatMap_cons,row,f,if_true,List.cons_append,List.nil_append,List.map_cons]
        rw [stamp_swap n _ _ ne]
        exact List.cons.injEq _ _ _ _ |>.mpr ⟨h.2.1,List.cons.injEq _ _ _ _ |>.mpr ⟨h.1,rest⟩⟩

theorem immutable {r allow u v} (cs : List Chunk) (info : AllInfo r allow u v cs) (s : Nat→Bool) :
    ∀ (k : Nat) (e : Event), (render Orig cs)[k]? = some e → e.2 ≠ r-2 → (render s cs)[k]? = some e := by
  induction cs with
  | nil => simp [render]
  | cons q cs ih =>
    have tail : AllInfo r allow u v cs := fun i x y m => info _ _ _ (List.mem_cons_of_mem _ m)
    cases q with
    | fixed x =>
      intro k e atK low; cases k with
      | zero => exact atK
      | succ k => exact ih tail _ _ atK low
    | turn i x y =>
      intro k e atK low
      have ranks := (info i x y List.mem_cons_self).mutable
      cases k with
      | zero => exact False.elim (low ((Option.some.inj atK) ▸ ranks.1))
      | succ k => cases k with
        | zero => exact False.elim (low ((Option.some.inj atK) ▸ ranks.2))
        | succ k =>
          cases f : s i <;> simpa only [render,List.flatMap_cons,row,f,Bool.false_eq_true,if_false,if_true,
            List.cons_append,List.nil_append,List.getElem?_cons_succ] using ih tail _ _ atK low

end P455ChartBuild
