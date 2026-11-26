import Problem455PrefixMatching



namespace P455Prefix
open P455Quotient P455FirstRewrite P455Witness P455Structural Problem455.Slots
open Problem455Swap (Link)
open P455DefectProjection (select_cap)

private theorem linked_changes {r b c a} {u v : Word} (cu : Cap r u) (cv : Cap r v)
    (ul : Link r u b c) (vl : Link r v b c) (bc : b≠c) (ba : b≠a) (ca : c≠a) :
    Changed u v b a ↔ Changed u v c a := by
  have hu := linked_shadow cu ul bc ba ca
  have hv := linked_shadow cv vl bc ba ca
  let d := exchange b c
  have dd : d ∘ d = id := by
    funext y; by_cases x : y=b <;> by_cases z : y=c <;> simp_all [d,exchange,Function.comp_def,Ne.symm]
  have inj (t s : Word) (h : t.map d = s.map d) : t=s := by
    have both := congrArg (List.map d) h
    simpa only [List.map_map,dd,List.map_id_fun] using both
  constructor
  · intro changed equal
    exact changed (hu.symm.trans ((congrArg (List.map d) equal).trans hv))
  · intro changed equal
    apply changed; apply inj; rw [show (select [c,a] u).map d=select [b,a] u from hu,
      show (select [c,a] v).map d=select [b,a] v from hv,equal]

private theorem edge_ne {r allow u a c} (e : Edge u r allow a c) : a≠c := by
  rcases e with ⟨_,h,_,_,_⟩|⟨_,h,_,_,_⟩
  · exact h
  · exact Ne.symm h

theorem incident_record {r allow ts u v a b c} (hr : 0 < r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (cmp : P455SourceFamilies.Compressed r u)
    (ab : a≠b) (eb : Changed u v a b) (ec : Edge u r allow a c) : b=c := by
  by_cases bc : b=c
  · exact bc
  have ac := edge_ne ec
  let k := [a,b,c]
  have ma : a∈k := by simp [k]
  have mb : b∈k := by simp [k]
  have mc : c∈k := by simp [k]
  have id3 := select_valid _ k valid
  have cu := select_cap k cap
  have cv : Cap r (select k v) := fun t => P455CellClassBinary.exact_counts cu id3 t ▸ cu t
  have left := changed_symm.mp ((selected_change k ma mb).mpr eb)
  have right : Changed (select k u) (select k v) c a := by
    rcases neighbors_link hr cap valid ab ac bc eb ec with l|l
    · exact (linked_changes cu cv l ((identity_link hr cu id3 b c).mp l) bc ab.symm ac.symm).mp left
    · exact (linked_changes cu cv l ((identity_link hr cu id3 c b).mp l) (Ne.symm bc) ac.symm ab.symm).mpr left
  exact disjoint_changes hr cap valid cmp ab ac eb ((selected_change k ma mc).mp (changed_symm.mpr right))

theorem isolated_pair {r allow ts u v a b} (hr : 0 < r) (cap : Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v) (cmp : P455SourceFamilies.Compressed r u)
    (ab : a≠b) (edit : Changed u v a b) :
    (∀ c, Edge u r allow a c → b=c) ∧ (∀ c, Edge u r allow b c → a=c) :=
  ⟨fun _ rec => incident_record hr cap valid cmp ab edit rec,
   fun _ rec => incident_record hr cap valid cmp ab.symm (changed_symm.mp edit) rec⟩

end P455Prefix
