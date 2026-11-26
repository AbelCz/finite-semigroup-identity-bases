import Problem455OtherProjection
import Problem455DefectRename
import Problem455EdgeSource




namespace P455EdgeProjection
open P455Witness P455Paths P455SourceFamilies P455CertificateReach P455PortReflection P455EdgeSource
open P455DefectProjection P455OtherProjection P455DefectRename Problem455.Slots

def candidates (ts : Tiles) (e : EdgeCertificate) : List (Node × Bool) :=
  [(e.a,true),(e.b,true),(e.right,!ts.right e.a.tag),(e.left,!ts.left e.a.tag),
   (e.down,!ts.bottom e.a.tag),(e.up,!ts.top e.a.tag),
   (e.diagonal,!ts.right e.a.tag && !ts.bottom e.a.tag)]

def nodes (ts : Tiles) (e : EdgeCertificate) :=
  ((candidates ts e).filter Prod.snd).map Prod.fst

def names (ts : Tiles) (e : EdgeCertificate) := (nodes ts e).flatMap roles

theorem nodes_exact {ts e n} : n ∈ nodes ts e ↔ Active ts e n := by
  constructor
  · intro h; obtain ⟨⟨j,b⟩,m,rfl⟩ := List.mem_map.mp h
    obtain ⟨cand,bok⟩ := List.mem_filter.mp m
    change b = true at bok; subst b
    simp only [candidates,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,
      true_and,and_true] at cand
    rcases cand with h|h|⟨h,p⟩|⟨h,p⟩|⟨h,p⟩|⟨h,p⟩|⟨h,p⟩ <;> subst j
    · exact .anchor
    · exact .successor
    · exact .right (by simpa using p.symm)
    · exact .left (by simpa using p.symm)
    · exact .down (by simpa using p.symm)
    · exact .up (by simpa using p.symm)
    · have two : ts.right e.a.tag = false ∧ ts.bottom e.a.tag = false := by simpa using p.symm
      exact .diagonal two.1 two.2
  · intro active
    apply List.mem_map.mpr
    refine ⟨(_,true),List.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    cases active <;> simp_all [candidates]

theorem names_exact {ts e x} : x ∈ names ts e ↔ ∃ n, Active ts e n ∧ x ∈ roles n := by
  simp [names,List.mem_flatMap,nodes_exact]

theorem names_bound (ts : Tiles) (e : EdgeCertificate) : (names ts e).length ≤ 14 := by
  have rep (ls : List Node) : (ls.flatMap roles).length = ls.length * 2 := by
    induction ls with
    | nil => rfl
    | cons x ls ih => simp [roles,List.flatMap_cons,ih,Nat.add_mul, Nat.add_comm] at *; omega
  have bound : (nodes ts e).length ≤ 7 := by
    simpa [nodes,candidates] using (List.length_filter_le Prod.snd (candidates ts e))
  rw [names,rep]; omega

theorem covered {ts e n} (ac : Active ts e n) : Covers (names ts e) (roles n) :=
  fun _ h => names_exact.mpr ⟨n,ac,h⟩

theorem saturated {r allow mark u} (cap : P455Closure.Cap r u) (ts : Tiles) (e : EdgeCertificate)
    (ok : Holds r allow mark u (e.query ts)) {x : Nat} (mem : x ∈ names ts e) : u.count x = r := by
  obtain ⟨n,ac,role⟩ := names_exact.mp mem
  have ct := record_counts cap (active_owner cap ts e ok ac).2
  rcases (show x = n.owner ∨ x = n.mate by simpa [roles] using role) with rfl|rfl
  · exact ct.1
  · exact ct.2

private theorem flag {r allow mark u} (keep : W) (b : Bool) (q : Query)
    (transfer : b = true → Holds r allow mark u q → Holds r allow mark (select keep u) q)
    (h : Holds r allow mark u (flagQ b q)) : Holds r allow mark (select keep u) (flagQ b q) := by
  cases b
  · exact True.intro
  · exact transfer rfl h

theorem project_edge {r allow mark u} (ts : Tiles) (e : EdgeCertificate)
    (ok : Holds r allow mark u (e.query ts)) : Holds r allow mark (select (names ts e) u) (e.query ts) := by
  let keep := names ts e
  have ka : Covers keep (roles e.a) := covered .anchor
  have kb : Covers keep (roles e.b) := covered .successor
  have ao := ka e.a.owner (by simp [roles]); have am := ka e.a.mate (by simp [roles])
  have bo := kb e.b.owner (by simp [roles]); have bm := kb e.b.mate (by simp [roles])
  obtain ⟨ma,mb,lc,succ,_⟩ := ok
  refine ⟨select_marked keep _ _ ao am ma,select_marked keep _ _ bo bm mb,?_,?_,True.intro⟩
  · refine ⟨flag keep _ _ (fun b q => ?_) lc.1,flag keep _ _ (fun b q => ?_) lc.2.1,
        flag keep _ _ (fun b q => ?_) lc.2.2.1,flag keep _ _ (fun b q => ?_) lc.2.2.2.1,
        flag keep _ _ (fun b q => ?_) lc.2.2.2.2.1,True.intro⟩
    · exact select_neighbor keep ts e.a e.right .right ka (covered (.right (by simpa using b))) q
    · exact select_neighbor keep ts e.a e.left .left ka (covered (.left (by simpa using b))) q
    · exact select_neighbor keep ts e.a e.down .down ka (covered (.down (by simpa using b))) q
    · exact select_neighbor keep ts e.a e.up .up ka (covered (.up (by simpa using b))) q
    · have pair : ts.right e.a.tag = false ∧ ts.bottom e.a.tag = false := by simpa using b
      have dg := covered (e := e) (.diagonal pair.1 pair.2)
      exact ⟨select_neighbor keep ts e.right e.diagonal .down (covered (.right pair.1)) dg q.1,
        select_neighbor keep ts e.down e.diagonal .right (covered (.down pair.2)) dg q.2⟩
  · unfold chosenSuccessor at succ ⊢
    dsimp only at succ ⊢
    split at succ
    next ret =>
      rw [if_pos ret]
      refine ⟨succ.1,succ.2.1.elim (fun q => .inl (select_port keep _ _ _ ka kb q))
          (fun q => .inr (select_port keep _ _ _ kb ka q)),
        select_order keep _ (by simp [bo,ao]) succ.2.2.1,True.intro⟩
    next other =>
      rw [if_neg other]
      exact ⟨succ.1,select_order keep _ (by simp [bo,ao]) succ.2⟩

def template (ts : Tiles) (e : EdgeCertificate) (u : W) :=
  (select (names ts e) u).map (names ts e).idxOf

/-- The only source assumptions are the cap and an actual 1,0 edge
    certificate in the observed side. The other side is unrestricted.
    Marking the two endpoint records retains the bit of either one. -/
theorem canonical_edge {r allow mark u} (cap : P455Closure.Cap r u) (ts : Tiles) (e : EdgeCertificate)
    (ok : Holds r allow mark u (e.query ts)) :
    let keep := names ts e
    let T := template ts e u
    P455Closure.Cap r T ∧ (∀ x ∈ T, x < 14 ∧ T.count x = r) ∧
      Holds r allow (endpointMarks keep.idxOf e) T ((sendEdge keep.idxOf e).query ts) := by
  let keep := names ts e
  let w := select keep u
  let T := template ts e u
  let d := keep.idxOf
  have hr : 0 < r := by have h : e.a.tag.length + 16 = r := ok.1.2.1; omega
  have sat {x : Nat} (hx : x ∈ keep) : w.count x = r :=
    (select_count keep u x hx).trans (saturated cap ts e ok hx)
  have small (x) (m : x ∈ w) : x ∈ keep := kept m
  have ext : w.map (extend keep) = T := extend_map small
  have cp : P455Closure.Cap r T := ext ▸ cap_rename (extend keep) (extend_inj keep) (select_cap keep cap)
  have ct {x : Nat} (hx : x ∈ keep) : T.count (d x) = r := by
    rw [← ext,show d x = extend keep x by simp [d,extend,hx],count_rename _ (extend_inj keep),sat hx]
  refine ⟨cp,?_,?_⟩
  · intro y hy; obtain ⟨x,xm,rfl⟩ := List.mem_map.mp hy
    exact ⟨Nat.lt_of_lt_of_le (List.idxOf_lt_length (small x xm)) (names_bound ts e),ct (small x xm)⟩
  · let h := fun j => [decode keep j]
    have back : ([] : W) ++ T.flatMap h ++ [] = w := by
      have single (v : W) : v.flatMap h = v.map (decode keep) := by
        induction v with
        | nil => rfl
        | cons a v ih => simp [h,List.flatMap_cons,ih] at *
      simpa only [List.nil_append,List.append_nil,single] using decode_map small
    have uniform (n : Node) (ac : Active ts e n) : UniformOn r T h d (roles n) := by
      intro x hx; have k := covered ac x hx
      exact ⟨ct k,by simp [h,d,decode_idx keep k]⟩
    exact edge_source (mark := mark) (l := []) (k := []) hr (by rw [back]; exact select_cap keep cap)
      ts e uniform (by rw [back]; exact project_edge ts e ok)

end P455EdgeProjection
