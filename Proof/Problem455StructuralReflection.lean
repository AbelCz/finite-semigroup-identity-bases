import Problem455FullSingleton



namespace P455StructuralReflection
open P455Structural P455Witness P455SourceFamilies P455DefectRename P455SlotProduct
open P455FirstTesters P455FirstRewrite P455Quotient Problem455.Slots Problem455Swap

private theorem map_edge {r allow w a b} (f : Nat → Nat) (inj : Injects f)
    (edge : Edge w r allow a b) : Edge (w.map f) r allow (f a) (f b) := by
  rcases edge with ⟨tag,rec⟩|⟨tag,rec⟩
  · exact .inl ⟨tag,rename_record f inj rec⟩
  · exact .inr ⟨tag,rename_record f inj rec⟩

theorem rename_test {r allow w} (f : Nat → Nat) (inj : Injects f)
    (test : Structural w r allow) : Structural (w.map f) r allow := by
  have width {k} (ww : Width k w) : Width k (w.map f) := by
    obtain ⟨c,len,covers⟩ := ww
    refine ⟨c.map f,by simpa using len,?_⟩
    intro a m
    obtain ⟨b,mb,rfl⟩ := List.mem_map.mp m
    exact List.mem_map_of_mem (covers b mb)
  rcases test with ⟨ww,o,p,q,op,oq,pq,ep,eq⟩|⟨ww,o,p,z,j,op,zo,zp,⟨tag,rec⟩,see⟩
  · exact .inl ⟨width ww,f o,f p,f q,fun h => op (inj h),fun h => oq (inj h),
      fun h => pq (inj h),map_edge f inj ep,map_edge f inj eq⟩
  · exact .inr ⟨width ww,f o,f p,f z,j,fun h => op (inj h),fun h => zo (inj h),
      fun h => zp (inj h),⟨tag,rename_record f inj rec⟩,rename_sees f inj see⟩

private theorem bigram_map (f : Nat → Nat) (inj : Injects f) (x y : Nat) (w : List Nat) :
    bigram (f x) (f y) (w.map f)=bigram x y w := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [bigram,hit]
    | cons b t =>
      change hit _ _ (some (f a)) (some (f b)) + _ = hit _ _ (some a) (some b) + _
      have left : f a=f x ↔ a=x := ⟨fun e => inj e,congrArg f⟩
      have right : f b=f y ↔ b=y := ⟨fun e => inj e,congrArg f⟩
      simp only [hit,Option.some.injEq,left,right,← ih,List.map_cons]

theorem rename_compressed {r w} (hr : 0<r) (f : Nat → Nat) (inj : Injects f)
    (cmp : Compressed r w) : Compressed r (w.map f) := by
  intro a b h
  have le := out_bound a b (b+1) (by omega) (w.map f)
  have ri := in_bound a (a+1) b (by omega) (w.map f)
  have up := tail_occ_le b (w.map f)
  simp only [Problem455BlockBridge.occ_count] at le ri up
  change bigram a b (w.map f)=r at h
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp (show 0<(w.map f).count a by omega))
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp (show 0<(w.map f).count b by omega))
  exact cmp x y ((bigram_map f inj x y w).symm.trans h)

theorem literal_projection {r allow ts u v} (hr : 0 < r) (cap : P455Closure.Cap r u)
    (ident : (P455FullSingleton.model r allow ts).Valid u v) (keep : List Nat) (width : keep.length ≤ 4)
    (test : Structural (select keep u) r allow) (cmp : Compressed r (select keep u)) :
    select keep u = select keep v := by
  let T := (select keep u).map keep.idxOf
  have eq : (select keep u).map (extend keep)=T := extend_map (fun _ mem => kept mem)
  have cp : P455Closure.Cap r T := eq ▸ cap_rename _ (extend_inj keep) (P455DefectProjection.select_cap keep cap)
  have st : Structural T r allow := eq ▸ rename_test _ (extend_inj keep) test
  have nc : Compressed r T := eq ▸ rename_compressed hr _ (extend_inj keep) cmp
  have low (x) (mem : x∈T) : x<4 := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    exact Nat.lt_of_lt_of_le (List.idxOf_lt_length (kept ha)) width
  have found := Problem455Finite.covered (List.range 4) (4*r) T (capped_length 4 T cp low)
    (fun x mem => List.mem_range.mpr (low x mem))
  obtain ⟨idx,pos⟩ := List.get_of_mem found
  let i : P455StructuralProduct.Index r allow := ⟨idx,pos.symm ▸ cp,pos.symm ▸ nc,pos.symm ▸ st⟩
  have iden := ((P455MarkedRank.valid_pair ..).mp
    (((P455MarkedRank.valid_pair ..).mp ((P455MarkedRank.valid_pair ..).mp ident).2).2)).2
  let vname (a : Nat) (j : P455StructuralProduct.Index r allow) := ofWord (plain r) j.T (image keep a)
  have observed := congrFun (iden vname) i
  rw [P455StructuralProduct.coordinate,P455StructuralProduct.coordinate] at observed
  have product (w : List Nat) : eval (plain r) i.cap (fun a => vname a i) w =
      ofWord (plain r) i.T ((select keep w).map keep.idxOf) :=
    (eval_rep _ _ _ _ (image keep) (fun _ _ => rfl)).trans (congrArg _ (image_word keep w))
  rw [product,product] at observed
  have sameT : i.T=T := pos
  rw [sameT] at observed
  have live : Good (plain r) T T := ⟨T,.refl _,[],[],by simp⟩
  have walk := ((same_nonzero_class _ live).mp observed).2
  have identical := walk.transport (P := fun w => T=w) rfl (fun bad _ => False.elim bad)
  exact (decode_map (fun _ mem => kept mem)).symm.trans
    ((congrArg (List.map (decode keep)) identical).trans (decode_map (fun _ mem => kept mem)))

end P455StructuralReflection
