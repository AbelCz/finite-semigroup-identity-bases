import Problem455PrefixReadout
import Problem455ImmutablePrivate



namespace P455ChartBuild
open P455Quotient P455Witness P455FirstRewrite P455Prefix P455WordChart P455Uncrossed
open P455ChartSchedule P455Schedule P455SlotSaturation Problem455.Slots

private theorem marker {r allow u v cs i} (info : AllInfo r allow u v cs) (activeI : i∈active cs) :
    ((nodes r u i).owner,r-2) ∈ render Orig cs := by
  obtain ⟨x,y,m⟩ := mem_active.mp activeI
  have p := info _ _ _ m
  apply List.mem_flatMap.mpr
  refine ⟨.turn i x y,m,?_⟩
  rcases p.roles with ⟨h,_⟩|⟨h,_⟩
  · exact List.mem_cons.mpr (.inl (Prod.ext h p.mutable.1).symm)
  · exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr (Prod.ext h p.mutable.2).symm))

theorem active_distinct {r allow u v} (cs : List Chunk) (info : AllInfo r allow u v cs)
    (nd : (render Orig cs).Nodup) : (active cs).Nodup := by
  induction cs with
  | nil => simp [active]
  | cons q cs ih =>
    have tail : AllInfo r allow u v cs := fun i x y m => info _ _ _ (List.mem_cons_of_mem _ m)
    cases q with
    | fixed => exact ih tail (List.nodup_cons.mp nd).2
    | turn i x y =>
      change (x::y::render Orig cs).Nodup at nd
      have mx := (List.nodup_cons.mp nd).1
      obtain ⟨my,nt⟩ := List.nodup_cons.mp (List.nodup_cons.mp nd).2
      change (i::active cs).Nodup
      refine List.nodup_cons.mpr ⟨?_,ih tail nt⟩
      intro mem
      have m := marker tail mem
      have p := info i x y List.mem_cons_self
      rcases p.roles with ⟨h,_⟩|⟨h,_⟩
      · exact mx (List.mem_cons_of_mem _ ((show x=((nodes r u i).owner,r-2) from Prod.ext h p.mutable.1).symm ▸ m))
      · exact my ((show y=((nodes r u i).owner,r-2) from Prod.ext h p.mutable.2).symm ▸ m)

private theorem count_before (n : Nat → Nat) (l t : List Event) (x y : Event) (ne : x.1≠y.1)
    (h : stamp n ((l++x::y::t).map Prod.fst)=l++x::y::t) :
    n x.1 + (l.map Prod.fst).count x.1 = x.2 ∧ n y.1 + (l.map Prod.fst).count y.1=y.2 := by
  simp only [List.map_append,List.map_cons,stamp_append] at h
  have e := List.append_inj_right h (by rw [P455ImmutablePrivate.stamp_length,List.length_map])
  obtain ⟨hx,sub⟩ := List.cons.inj e
  obtain ⟨hy,_⟩ := List.cons.inj sub
  exact ⟨congrArg Prod.snd hx,by simpa [advance,ne,Ne.symm ne] using congrArg Prod.snd hy⟩

private theorem flags_switch (A s : Bits) (i : Nat) :
    flags A (switch s i) i = !flags A s i ∧ ∀ j, j≠i → flags A (switch s i) j=flags A s j := by
  constructor
  · cases e : s i <;> cases f : A i <;> simp [flags,switch,e,f]
  · intro j ne; simp [flags,switch,ne]

theorem mixed_stamp {r allow u v cs} (info : AllInfo r allow u v cs) (src : render Orig cs=events u)
    (s : Bits) : events (chooseWord r u cs s) = render (flags (initial r u) s) cs := by
  exact stamp_render cs info _ (by rw [original_labels src,src]; rfl) _

/-- Actual factorization with identical surrounding words before and after
    a bit switch, at precisely the r-2 numbered copies of its two names. -/
theorem switched_place {r allow u v cs} (info : AllInfo r allow u v cs)
    (src : render Orig cs=events u) (s : Bits) (i : Nat) (use : i∈active cs) :
    let n := nodes r u i
    ∃ pre post : W, ∃ d : Bool,
      chooseWord r u cs s = pre ++ pair n.owner n.mate d ++ post ∧
      chooseWord r u cs (switch s i) = pre ++ pair n.owner n.mate (!d) ++ post ∧
      pre.count n.owner = r-2 ∧ pre.count n.mate = r-2 := by
  obtain ⟨x,y,m⟩ := mem_active.mp use
  obtain ⟨p,q,e⟩ := List.append_of_mem m
  subst cs
  let f := flags (initial r u) s
  let g := flags (initial r u) (switch s i)
  have turn := info i x y m
  have nd := active_distinct _ info (src ▸ P455Paths.stamp_unique _ _)
  change (active (p++Chunk.turn i x y::q)).Nodup at nd
  have ins : active (p++Chunk.turn i x y::q)=active p ++ i::active q := by
    simp [active,List.flatMap_append]
  rw [ins] at nd
  obtain ⟨_,nq,dis⟩ := List.pairwise_append.mp nd
  have ip : i ∉ active p := fun m => dis i m i List.mem_cons_self rfl
  have iq := (List.nodup_cons.mp nq).1
  have relation := flags_switch (initial r u) s i
  have eq (cs : List Chunk) (absent : i∉active cs) : render g cs=render f cs :=
    renders_equal cs (fun j m => relation.2 j (fun e => absent (e ▸ m)))
  have first := eq p ip; have last := eq q iq
  let pre := labels f p
  let post := labels f q
  have orig : stamp (fun _ => 0) ((render Orig p++x::y::render Orig q).map Prod.fst) =
      render Orig p++x::y::render Orig q := by
    have stamp0 : stamp (fun _ => 0) (labels Orig (p++Chunk.turn i x y::q))=render Orig (p++Chunk.turn i x y::q) := by
      rw [original_labels src,src]; rfl
    simpa [labels,render,List.flatMap_append,Orig,row] using stamp0
  have ne : x.1≠y.1 := by rcases turn.roles with ⟨a,b⟩|⟨a,b⟩ <;> rw [a,b] <;>
                             first | exact turn.typedU.1 | exact Ne.symm turn.typedU.1
  have cnt := count_before _ _ _ x y ne orig
  have perm : pre.Perm ((render Orig p).map Prod.fst) := (pos_perm f Orig p).map _
  have cx : pre.count x.1 = r-2 := (perm.count_eq x.1).trans ((by simpa using cnt.1 : ((render Orig p).map Prod.fst).count x.1 = x.2).trans turn.mutable.1)
  have cy : pre.count y.1 = r-2 := (perm.count_eq y.1).trans ((by simpa using cnt.2 : ((render Orig p).map Prod.fst).count y.1 = y.2).trans turn.mutable.2)
  have view (h : Nat → Bool) : labels h (p++Chunk.turn i x y::q)=
      labels h p ++ (row h (.turn i x y)).map Prod.fst ++ labels h q := by
    simp [labels,render,List.flatMap_append,List.append_assoc]
  have L : chooseWord r u (p++Chunk.turn i x y::q) s =
      pre ++ (row f (.turn i x y)).map Prod.fst ++ post := view f
  have R : chooseWord r u (p++Chunk.turn i x y::q) (switch s i)=
      pre ++ (row g (.turn i x y)).map Prod.fst ++ post := by
    simpa only [chooseWord,labels,first,last] using view g
  have flip : g i = !f i := relation.1
  dsimp only
  rcases turn.roles with ⟨xo,ym⟩|⟨yo,xm⟩
  · refine ⟨pre,post,f i,?_,?_,xo ▸ cx,ym ▸ cy⟩
    · cases d : f i <;> simpa only [row,d,pair,Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil,xo,ym] using L
    · cases d : f i <;> simpa only [row,flip,d,pair,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil,xo,ym] using R
  · refine ⟨pre,post,!f i,?_,?_,yo ▸ cy,xm ▸ cx⟩
    · cases d : f i <;> simpa only [row,d,pair,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil,yo,xm] using L
    · cases d : f i <;> simpa only [row,flip,d,pair,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil,yo,xm] using R

end P455ChartBuild
