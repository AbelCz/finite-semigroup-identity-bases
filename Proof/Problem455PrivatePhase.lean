import Problem455PrefixLinkInvariance
import Problem455ChangedEvents




namespace P455PrivatePhase
open P455Witness P455Structural P455ChangedEvents P455Prefix P455DefectProjection
open P455ContactReflection Problem455.Slots
open Problem455Swap (Link)
abbrev W := List Nat

theorem edge_project {r allow u a b} (k : W) (ka : a∈k) (kb : b∈k) :
    Edge (select k u) r allow a b ↔ Edge u r allow a b := by
  have x := select_sub k [a,b] u (by simpa using And.intro ka kb)
  have y := select_sub k [b,a] u (by simpa using And.intro kb ka)
  simp only [Edge,Rec,Holds,x,y,typed] at *

theorem no_intruder {r allow ts u v a b} (cap : P455Closure.Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (rec : Rec u r allow a b) (changed : ChangedPair u v a b)
    (isolated : ∀ z, z≠a → z≠b → ¬ Edge u r allow a z ∧ ¬ Edge u r allow b z)
    (z j : Nat) (za : z≠a) (zb : z≠b) : ¬ sees u [(a,0),(z,j),(b,2)] := by
  intro occurs
  obtain ⟨tag,ab,len,tagOk,bit,prof⟩ := rec
  have hr : 0<r := by omega
  let k := [a,b,z]
  let U := select k u
  have capU := select_cap k cap
  have sub : select [a,b] U = select [a,b] u := select_sub k [a,b] u (by simp [k])
  have binary : Rec U r allow a b := ⟨tag,ab,len,tagOk,bit,sub.trans prof⟩
  have record : Edge U r allow a b := .inl binary
  have nonAB := edge_no_links capU ab record
  have none := isolated z za zb
  have zaEdge : ¬Edge U r allow z a := by
    intro h
    exact none.1 ((edge_project k (by simp [k]) (by simp [k])).mp (h.elim Or.inr Or.inl))
  have zbEdge : ¬Edge U r allow z b := by
    intro h
    exact none.2 ((edge_project k (by simp [k]) (by simp [k])).mp (h.elim Or.inr Or.inl))
  have nonAZ : ¬ Link r U a z ∧ ¬ Link r U z a := by
    constructor
    · intro h; exact zbEdge ((twin_edges capU h za.symm ab zb).mp record)
    · intro h; exact zbEdge ((twin_edges capU h za zb ab).mpr record)
  have nonBZ : ¬ Link r U b z ∧ ¬ Link r U z b := by
    have ba : Edge U r allow b a := record.elim Or.inr Or.inl
    constructor
    · intro h; exact zaEdge ((twin_edges capU h zb.symm ab.symm za).mp ba)
    · intro h; exact zaEdge ((twin_edges capU h zb za ab.symm).mpr ba)
  have names (t) (m : t∈U) : t∈k := P455DefectRename.kept m
  have cmp : P455SourceFamilies.Compressed r U := by
    intro i l link
    obtain ⟨ci,cl⟩ := link_counts capU link
    have mi := names i (List.count_pos_iff.mp (ci ▸ hr))
    have ml := names l (List.count_pos_iff.mp (cl ▸ hr))
    simp only [k,List.mem_cons,List.not_mem_nil,or_false] at mi ml
    rcases mi with h|h|h <;> rcases ml with e|e|e <;> subst i <;> subst l <;>
      first | exact not_self hr capU link | exact nonAB.1 link | exact nonAB.2 link |
        exact nonAZ.1 link | exact nonAZ.2 link | exact nonBZ.1 link | exact nonBZ.2 link
  have obs := sees_select k u _ (by simp [k]) occurs
  have st : Structural U r allow := .inr ⟨⟨k,by simp [k],names⟩,a,b,z,j,ab,za,zb,binary,obs⟩
  have eq := P455StructuralReflection.literal_projection hr cap valid k (by simp [k]) st cmp
  have ext := congrArg (select [a,b]) eq
  rw [select_sub k [a,b] u (by simp [k]),select_sub k [a,b] v (by simp [k])] at ext
  exact changed ext

private theorem peel (k : W) {w : W} (x : Nat) (t : W) (eq : select k w=x::t) :
    ∃ l r, w=l++x::r ∧ select k l=[] ∧ select k r=t := by
  induction w with
  | nil => cases eq
  | cons a w ih =>
    by_cases keep : a∈k
    · have ⟨e,tail⟩ := List.cons.inj (show a::select k w=x::t by simpa [select,keep] using eq)
      exact ⟨[],w,by simp [e],rfl,tail⟩
    · obtain ⟨l,r,mid,el,er⟩ := ih (by simpa [select,keep] using eq)
      exact ⟨a::l,r,by simp [mid],by simpa [select,keep] using el,er⟩

private theorem cut (k : W) (p : W) (x : Nat) (t : W) (w : W)
    (eq : select k w=p++x::t) : ∃ m z, w=m++x::z ∧ select k m=p ∧ select k z=t := by
  induction p generalizing w with
  | nil => exact peel k x t eq
  | cons a p ih =>
    obtain ⟨l,r,f,el,er⟩ := peel k a (p++x::t) eq
    have keptA : a∈k := P455DefectRename.kept (keep:=k) (w:=w) (a:=a) (by rw [eq]; simp)
    obtain ⟨m,z,mz,em,ez⟩ := ih r er
    refine ⟨l++a::m,z,?_,?_,ez⟩
    · simp [f,mz,List.append_assoc]
    · rw [select_append,el]; simpa [select,keptA] using congrArg (List.cons a) em

private theorem stamped_three (l p q t : W) (a z b : Nat) :
    sees (l ++ a :: (p ++ z :: (q ++ b :: t)))
      [(a,l.count a),(z,(l++a::p).count z),(b,(l++a::(p++z::q)).count b)] := by
  let n₁ := advance (fun _ => 0) l
  let n₂ := advance (advance n₁ [a]) p
  let n₃ := advance (advance n₂ [z]) q
  have one : n₁ a = l.count a := by simp [n₁,advance]
  have two : n₂ z = (l++a::p).count z := by
    simp [n₁,n₂,advance,List.count_cons,List.count_append,beq_iff_eq]; omega
  have three : n₃ b = (l++a::(p++z::q)).count b := by
    simp [n₁,n₂,n₃,advance,List.count_cons,List.count_append,beq_iff_eq]; omega
  unfold sees events
  rw [← one,← two,← three]
  simp only [stamp_append,stamp]
  have end' : [(b,n₃ b)].Sublist ((b,n₃ b)::stamp (advance n₃ [b]) t) :=
    List.singleton_sublist.mpr List.mem_cons_self
  have qq := end'.trans (List.sublist_append_right (stamp (advance n₂ [z]) q) _)
  have zz := qq.cons₂ (z,n₂ z)
  have pp := zz.trans (List.sublist_append_right (stamp (advance n₁ [a]) p) _)
  exact (pp.cons₂ (a,n₁ a)).trans (List.sublist_append_right _ _)

/-- Absence of the indexed intrusion is exactly strong enough to turn the
    first six projected positions into a literal factor of the source. -/
theorem closed_of_no_intruder {w : W} {a b : Nat} (ab : a≠b)
    (profileStart : ∃ t : W, select [a,b] w=P455Structural.early a b++t)
    (none : ∀ z j, z≠a → z≠b → ¬sees w [(a,0),(z,j),(b,2)]) :
    P455Structural.Closed w a b := by
  obtain ⟨t,eq⟩ := profileStart
  let k := [a,b]
  obtain ⟨l,r,first,l0,rest⟩ := peel k a ([a,b,a,b,b]++t) eq
  obtain ⟨m,z,last,middle,_⟩ := cut k [a,b,a,b] b t r rest
  have ca : l.count a=0 := by
    rw [← select_count k l a (by simp [k]),l0]; rfl
  have cb : l.count b=0 := by
    rw [← select_count k l b (by simp [k]),l0]; rfl
  have two : m.count b=2 := by
    rw [← select_count k m b (by simp [k]),middle]
    simp [List.count_cons,ab,Ne.symm ab]
  have sel : select k m=m := by
    apply List.filter_eq_self.mpr
    intro d mem
    by_cases da : d=a
    · simp [k,da]
    by_cases db : d=b
    · simp [k,db]
    obtain ⟨p,q,ms⟩ := List.append_of_mem mem
    have triple := stamped_three l p q z a d b
    have pos : (l++a::(p++d::q)).count b=2 := by
      rw [← ms]; simp [List.count_cons,ab,Ne.symm ab,cb,two]
    rw [ca,pos] at triple
    apply False.elim (none d ((l++a::p).count d) da db ?_)
    simpa [first,last,ms,List.append_assoc] using triple
  refine ⟨ab,l,z,?_,List.count_eq_zero.mp ca,List.count_eq_zero.mp cb⟩
  have small := sel.symm.trans middle
  simp [first,last,small,P455Structural.early,List.append_assoc]

theorem closed_changed {r allow ts u v a b} (cap : P455Closure.Cap r u)
    (valid : (P455FullSingleton.model r allow ts).Valid u v)
    (rec : Rec u r allow a b) (changed : ChangedPair u v a b)
    (isolated : ∀ z, z≠a → z≠b → ¬ Edge u r allow a z ∧ ¬ Edge u r allow b z) :
    P455Structural.Closed u a b := by
  have ban := no_intruder cap valid rec changed isolated
  obtain ⟨tag,ab,_,_,bit,eq⟩ := rec
  apply closed_of_no_intruder ab _ ban
  exact ⟨_,by simpa [profile,profilePrefix,P455Structural.early,List.append_assoc] using eq⟩

end P455PrivatePhase
