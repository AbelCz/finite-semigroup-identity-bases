import Problem455SlotSaturation




namespace P455ProfileComponent
open P455Witness P455Closure P455SlotProduct P455SlotSaturation Problem455.Slots
abbrev W := List Nat

theorem profile_support (a b : Nat) (tag : Tag) (bit : Bool) {z : Nat}
    (m : z ∈ profile a b tag bit) : z = a ∨ z = b := by
  rw [← profile_eq] at m
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp m
  cases c <;> simp

theorem profile_length (a b : Nat) (tag : Tag) (bit : Bool) :
    (profile a b tag bit).length = 2 * (tag.length + 16) := by
  cases bit <;> simp [profile,pair,profile_prefix_length] <;> omega

theorem profile_cap {a b : Nat} (ne : a ≠ b) (tag : Tag) (bit : Bool) :
    Cap (tag.length + 16) (profile a b tag bit) := by
  intro x
  have tagct (x : Nat) : (tag.flatMap (pair a b)).count x ≤ tag.length := by
    induction tag with
    | nil => simp
    | cons f tag ih =>
      cases f <;> by_cases xa : a=x <;> by_cases xb : b=x <;>
        simp [List.flatMap_cons,pair,List.count_cons,beq_iff_eq,xa,xb,ne,Ne.symm ne] at * <;> omega
  have cp := tagct x
  cases bit <;> by_cases xa : a=x <;> by_cases xb : b=x <;>
    simp [profile,profilePrefix,pair,List.replicate_succ,List.count_cons,beq_iff_eq,xa,xb,ne,Ne.symm ne] at * <;> omega

def frame (a b : Nat) (tag : Tag) : Frame Nat :=
  ⟨a,[],[],b,tag,(fixedPhases tag).map (fun token => ([],token)),[],[],[]⟩

theorem frame_core (a b : Nat) (tag : Tag) (bit : Bool) :
    (frame a b tag).core bit = profile a b tag bit := by
  have md (ls : List Bool) : (ls.map (fun token => (([] : W),token))).flatMap
      (fun e => e.1 ++ (if e.2 then [b] else [a])) = ls.map (fun k => if k then b else a) := by
    induction ls with
    | nil => rfl
    | cons c ls ih => cases c <;> simp [List.flatMap_cons, ih] at *
  rw [← profile_eq]
  cases bit <;> simp [Frame.core,Frame.early,Frame.mid,Frame.pair,Frame.p,Frame.q,frame,
    Frame.profileWord,Frame.profileBits,md,phasePair,List.append_assoc]

theorem forward {r allow a b tag} (ne : a ≠ b) (length : tag.length+16 = r)
    (allowed : allow tag) (bit : Bool) :
    Move r allow noMark (profile a b tag bit) (profile a b tag (!bit)) := by
  let f := frame a b tag
  have cp : Cap r (profile a b tag bit) := length ▸ profile_cap ne tag bit
  have cf : Cap r ([] ++ f.core bit ++ []) := by simpa [f,frame_core] using cp
  refine ⟨f,bit,[],[],f.valid_of_capped_shape (by change r = 16+tag.length; omega) allowed
     (by simp [f,frame,List.map_map,Function.comp_def]) (by simp [f,frame,Frame.p])
     (by simp [f,frame,Frame.q]) (by simpa [f,frame,Frame.p,Frame.q] using ne)
     (by simp [noMark]) bit [] [] cf,by simp [f,frame_core],by simp [f,frame_core],cp⟩

theorem variants {r allow a b tag} (ne : a ≠ b) (length : tag.length+16 = r)
    (allowed : allow tag) (bit : Bool) (u : W) :
    P455Quotient.Variant (rules r allow noMark) (profile a b tag bit) u ↔
      ∃ v : Bool, u = profile a b tag v := by
  constructor
  · intro path
    have supp (x : Nat) (inU : x ∈ u) : x=a ∨ x=b := by
      have ct := P455Quotient.count_walk (rules r allow noMark) path x
      exact profile_support a b tag bit (List.count_pos_iff.mp (ct ▸ List.count_pos_iff.mpr inU))
    have selfU : select [a,b] u = u := by apply List.filter_eq_self.mpr; simpa using supp
    have selfT : select [a,b] (profile a b tag bit) = profile a b tag bit := by
      apply List.filter_eq_self.mpr
      intro x h; simpa using profile_support a b tag bit h
    have typed' := path.transport (P := fun z => typed z a b tag) ⟨bit,selfT⟩
      (fun mv yes => (mv.typed_iff a b tag ne length).mp yes)
    simpa [typed,selfU] using typed'
  · rintro ⟨v,rfl⟩
    cases bit <;> cases v
    · exact .refl _
    · exact .snoc (.refl _) (forward ne length allowed false)
    · exact .snoc (.refl _) (forward ne length allowed true)
    · exact .refl _

theorem factors {r allow a b tag} (ne : a ≠ b) (length : tag.length+16 = r)
    (allowed : allow tag) (bit : Bool) (u : W) :
    P455Quotient.Good (rules r allow noMark) (profile a b tag bit) u ↔
      ∃ v : Bool, P455Quotient.Factor u (profile a b tag v) := by
  constructor
  · rintro ⟨w,p,f⟩; obtain ⟨v,rfl⟩ := (variants ne length allowed bit w).mp p; exact ⟨v,f⟩
  · rintro ⟨v,f⟩; exact ⟨_,(variants ne length allowed bit _).mpr ⟨v,rfl⟩,f⟩

theorem move_size {r allow mark} {u v : W} (h : Move r allow mark u v) : 2*r ≤ u.length := by
  obtain ⟨f,t,l,k,ok,rfl,_,cp⟩ := h
  have pr := f.cross_projection ok t l k cp f.pHead f.qLast (by simp [Frame.p]) (by simp [Frame.q])
  have small := List.length_filter_le (fun a => decide (a=f.pHead ∨ a=f.qLast)) (l ++ f.core t ++ k)
  rw [pr,profile_eq,profile_length] at small
  have eq := ok.1
  omega

theorem proper_singleton {r allow a b tag bit u v} (live : P455Quotient.Good (rules r allow noMark)
    (profile a b tag bit) u) (short : u.length < 2*r) :
    P455Quotient.ofWord (rules r allow noMark) (profile a b tag bit) u =
      P455Quotient.ofWord (rules r allow noMark) (profile a b tag bit) v ↔ u=v := by
  constructor
  · intro eq
    have path := ((P455Quotient.same_nonzero_class _ live).mp eq).2
    exact path.transport (P := fun z => u=z) rfl (fun mv e => by
      subst_vars; have := move_size mv; omega)
  · rintro rfl; rfl

theorem classes {r allow a b tag} (ne : a ≠ b) (length : tag.length+16 = r)
    (allowed : allow tag) (bit : Bool) (u v : W) :
    let R := rules r allow noMark
    let T := profile a b tag bit
    P455Quotient.ofWord R T u = P455Quotient.ofWord R T v ↔ u=v ∨
      ((∃ i : Bool, u = profile a b tag i) ∧ (∃ j : Bool, v = profile a b tag j)) ∨
      (¬ (∃ i : Bool, P455Quotient.Factor u (profile a b tag i)) ∧
       ¬ (∃ j : Bool, P455Quotient.Factor v (profile a b tag j))) := by
  let R := rules r allow noMark
  let T := profile a b tag bit
  change P455Quotient.ofWord R T u = P455Quotient.ofWord R T v ↔ _
  constructor
  · intro eq
    by_cases valid : P455Quotient.Good R T u
    · by_cases short : u.length < 2*r
      · exact .inl ((proper_singleton valid short).mp eq)
      · obtain ⟨i,L,K,e⟩ := (factors ne length allowed bit u).mp valid
        have lens := congrArg List.length e
        simp only [profile_length,length,List.length_append] at lens
        have lk : L=[] ∧ K=[] := ⟨List.length_eq_zero_iff.mp (by omega),List.length_eq_zero_iff.mp (by omega)⟩
        have full : u = profile a b tag i := by simpa [lk.1,lk.2] using e.symm
        have path := ((P455Quotient.same_nonzero_class _ valid).mp eq).2
        rw [full] at path
        exact .inr (.inl ⟨⟨i,full⟩,(variants ne length allowed i v).mp path⟩)
    · have dead : ¬ P455Quotient.Good R T v := by
        intro g; exact valid (((P455Quotient.same_nonzero_class _ g).mp eq.symm).1)
      exact .inr (.inr ⟨fun h => valid ((factors ne length allowed bit u).mpr h),
        fun h => dead ((factors ne length allowed bit v).mpr h)⟩)
  · rintro (rfl|⟨⟨i,rfl⟩,⟨j,rfl⟩⟩|⟨du,dv⟩)
    · rfl
    · have live (b' : Bool) : P455Quotient.Good R T (profile a b tag b') :=
        (factors ne length allowed bit _).mpr ⟨b',[],[],by simp⟩
      exact (P455Quotient.same_nonzero_class _ (live i)).mpr
        ⟨live j,(variants ne length allowed i _).mpr ⟨j,rfl⟩⟩
    · apply Quotient.sound; exact .inl ⟨fun gu => du ((factors ne length allowed bit u).mp gu),
        fun gv => dv ((factors ne length allowed bit v).mp gv)⟩

end P455ProfileComponent
