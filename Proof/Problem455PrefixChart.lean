import Problem455PrefixPlaces
import Problem455PrefixGlobal
import Problem455FlipFromWord



namespace P455ChartBuild
open P455Quotient P455Witness P455FirstRewrite P455Prefix P455WordChart P455Uncrossed
open P455ChartSchedule P455Schedule P455SlotSaturation P455Structural Problem455.Slots

theorem geometry_from_chunks {r allow ts u v cs} (hr : 0<r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (cmp : P455SourceFamilies.Compressed r u)
    (info : AllInfo r allow u v cs) (src : render Orig cs=events u) (dst : render Last cs=events v) :
    Geometry r allow (active cs) (initial r u) (chooseWord r u cs) (nodes r u) := by
  constructor
  · rw [initial_word src]
    intro n ok; exact ⟨(book r u).idxOf n,node_index (listed ok)⟩
  · rw [initial_word src]
    intro i m; obtain ⟨x,y,p⟩ := mem_active.mp m; exact (info i x y p).typedU
  · exact mixed_read info src dst
  · intro s _ i m
    obtain ⟨x,y,p⟩ := mem_active.mp m
    have data := info i x y p
    let n := nodes r u i
    let w := chooseWord r u cs s
    have typed := data.typedU
    have edit : Changed u v n.owner n.mate := by
      intro eq
      have bits : readBit u n=readBit v n := by simp only [readBit,eq]
      have unequal (b : Bool) : b≠ !b := by cases b <;> decide
      exact unequal (readBit u n) (bits.trans data.bits)
    have both := isolated_pair hr cap valid cmp typed.1 edit
    have only (z : Nat) (za : z≠n.owner) (zb : z≠n.mate) :
        ¬ Edge u r allow n.owner z ∧ ¬ Edge u r allow n.mate z :=
      ⟨fun e => zb (both.1 z e).symm,fun e => za (both.2 z e).symm⟩
    have closed := P455PrivatePhase.closed_changed cap valid (show Rec u r allow n.owner n.mate from
      ⟨n.tag,typed⟩) edit only
    have large : 5≤r := by have := typed.2.1; omega
    have stamped := mixed_stamp info src s
    have clean : Closed w n.owner n.mate := P455ImmutablePrivate.closed_transport large closed (by
      intro k e base immutableI
      rw [show events w=render (flags (initial r u) s) cs from stamped]
      exact immutable cs info _ k e (src.symm ▸ base) immutableI)
    have live := mixed_typed info src dst s i m
    have perm : w.Perm u := (show w.Perm (labels Orig cs) from (pos_perm _ Orig cs).map _).trans
      ((original_labels src) ▸ List.Perm.refl _)
    have cp : Cap r w := fun a => Nat.le_trans (Nat.le_of_eq (perm.count_eq a)) (cap a)
    obtain ⟨pre,post,bit,start,endWord,ca,cb⟩ := switched_place info src s i m
    rw [start,endWord]
    apply P455FlipFromWord.literal n pre post bit
    · simpa only [w,start] using cp
    · simpa only [start] using live
    · simpa only [w,start] using clean
    · exact ca
    · exact cb

theorem capped_schedule_or_rectangle {r allow ts u v} (hr : 0<r) (law : P455GridRows.Laws ts)
    (cap : Cap r u) (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (cmp : P455SourceFamilies.Compressed r u) :
    Derives (fun a b => (P455FullSingleton.model r allow ts).Valid a b ∧ rank a b≤P455MarkedRank.bound r) u v ∨
      Nonempty (P455GridAssembly.Rectangle allow ts) := by
  obtain ⟨cs,info,src,dst⟩ := indexed_chunks hr cap valid cmp
  have g := geometry_from_chunks hr cap valid cmp info src dst
  let A := initial r u
  let C := active cs
  have off : Off C A (ending A C) := by intro i out; simp [ending,out]
  have diff (i : Nat) (m : i∈C) : A i≠ending A C i := by cases h : A i <;> simp [ending,m,h]
  have left := initial_word (r:=r) src
  have right := final_word (r:=r) dst (u:=u)
  simpa only [A,C,left,right] using normalize_layout law g off diff (left.symm ▸ cap)
    (left.symm ▸ cmp) (show (P455FullSingleton.model r allow ts).Valid
      (chooseWord r u cs A) (chooseWord r u cs (ending A C)) by simpa only [A,C,left,right] using valid)

/-- Entire arbitrary-word implication. No chart, changed-pair matching,
    normalization, graph acyclicity or accepting rectangle is supplied. -/
theorem arbitrary_schedule_or_rectangle {r allow ts u v} (hr : 0<r) (law : P455GridRows.Laws ts)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) :
    Derives (fun a b => (P455FullSingleton.model r allow ts).Valid a b ∧
      rank a b ≤ max (P455MarkedRank.bound r) (2*(r+2)+1)) u v ∨
      Nonempty (P455GridAssembly.Rectangle allow ts) := by
  obtain ⟨A,B,h,_,ca,_,cmp,_,ok,_,_,_,_,lift⟩ := normalized_compressed hr valid
  exact (capped_schedule_or_rectangle hr law ca ok cmp).imp_left (lift _)

end P455ChartBuild
