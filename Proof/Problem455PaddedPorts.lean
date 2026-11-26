import Problem455RectangleRank
import Problem455Slots



namespace P455PaddedPorts
open P455RectangleRank Problem455.Slots
abbrev W := List Nat

inductive Block where
  | single (i : Nat)
  | pair (i j : Nat)
  deriving DecidableEq

def cells : Block → W
  | .single i => [i]
  | .pair i j => [i,j]

def phase (bs : List Block) := bs.flatMap fun b => cells b ++ cells b
def roles (i : Nat) := [owner i,mate i]
def letters (bs : List Block) := (phase bs).flatMap roles

private theorem singleton_head {i j u : Nat} {p : W} (ne : i≠j)
    (eq : u :: u :: p = [i,j,i,j]) : False := by
  obtain ⟨rfl,e⟩ := List.cons.inj eq
  exact ne (List.cons.inj e).1

private theorem only_pair (bs : List Block) (i j : Nat) (ne : i≠j)
    (obs : select [i,j] (phase bs)=[i,j,i,j]) : Block.pair i j ∈ bs := by
  induction bs with
  | nil => simp [phase,select] at obs
  | cons b bs ih =>
    change select [i,j] ((cells b ++ cells b) ++ phase bs) = _ at obs
    rw [select_append,select_append] at obs
    cases b with
    | single u =>
      by_cases hu : u=i ∨ u=j
      · have su : select [i,j] [u]=[u] := by simp [select,hu]
        simp only [cells,su,List.cons_append,List.nil_append] at obs
        exact (singleton_head ne obs).elim
      · have su : select [i,j] [u]=[] := by simp [select,hu]
        simp only [cells,su,List.nil_append] at obs
        exact List.mem_cons_of_mem _ (ih obs)
    | pair u v =>
      by_cases hu : u=i ∨ u=j <;> by_cases hv : v=i ∨ v=j
      · have sv : select [i,j] [u,v]=[u,v] := by simp [select,hu,hv]
        simp only [cells,sv,List.cons_append,List.nil_append,List.cons.injEq] at obs
        obtain ⟨rfl,rfl,_⟩ := obs
        exact List.mem_cons_self
      · have sv : select [i,j] [u,v]=[u] := by simp [select,hu,hv]
        simp only [cells,sv,List.cons_append,List.nil_append] at obs
        exact (singleton_head ne obs).elim
      · have sv : select [i,j] [u,v]=[v] := by simp [select,hu,hv]
        simp only [cells,sv,List.cons_append,List.nil_append] at obs
        exact (singleton_head ne obs).elim
      · have sv : select [i,j] [u,v]=[] := by simp [select,hu,hv]
        simp only [cells,sv,List.nil_append] at obs
        exact List.mem_cons_of_mem _ (ih obs)

private theorem phase_mem (bs : List Block) (x : Nat) : x∈phase bs ↔ x∈bs.flatMap cells := by
  simp [phase,List.mem_flatMap]

private theorem pair_present {bs : List Block} (nd : (bs.flatMap cells).Nodup)
    (i j : Nat) (present : Block.pair i j ∈ bs) : select [i,j] (phase bs)=[i,j,i,j] := by
  obtain ⟨pre,post,eq⟩ := List.append_of_mem present
  subst bs
  change ((_ ++ (.pair i j :: post)).flatMap cells).Nodup at nd
  simp only [List.flatMap_append,List.flatMap_cons,cells,List.cons_append,List.nil_append] at nd
  have parts := List.pairwise_append.mp nd
  have hits (x : Nat) (m : x∈pre.flatMap cells) : x∉[i,j] := by
    intro e
    have no := parts.2.2 x m x (by simpa using List.mem_append_left (post.flatMap cells) e : x∈i::j::post.flatMap cells)
    exact no rfl
  have ends (x : Nat) (m : x∈post.flatMap cells) : x∉[i,j] := by
    have hi := (List.nodup_cons.mp parts.2.1).1
    have hj := (List.nodup_cons.mp (List.nodup_cons.mp parts.2.1).2).1
    intro e
    rcases (show x=i ∨ x=j by simpa using e) with rfl|rfl
    · exact hi (List.mem_cons_of_mem _ m)
    · exact hj m
  have s1 := select_nil [i,j] (phase pre) (fun x m => hits x ((phase_mem ..).mp m))
  have s2 := select_nil [i,j] (phase post) (fun x m => ends x ((phase_mem ..).mp m))
  change select [i,j] ((pre ++ .pair i j :: post).flatMap _) = _
  rw [List.flatMap_append,List.flatMap_cons,select_append]
  change select [i,j] (phase pre) ++ select [i,j] (([i,j] ++ [i,j]) ++ phase post)=_
  rw [s1,select_append,s2]
  simp [select]

theorem phase_exact {bs : List Block} (nd : (bs.flatMap cells).Nodup)
    (i j : Nat) (ne : i≠j) :
    select [i,j] (phase bs)=[i,j,i,j] ↔ Block.pair i j∈bs :=
  ⟨only_pair bs i j ne,pair_present nd i j⟩

private theorem roles_inj {s t : W} (eq : s.flatMap roles=t.flatMap roles) : s=t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all [roles]
  | cons i s ih =>
    cases t with
    | nil => simp [roles] at eq
    | cons j t =>
      simp only [List.flatMap_cons,roles,List.cons_append,List.nil_append,List.cons.injEq] at eq
      have e : i=j := by have := eq.1; unfold owner at this; omega
      rw [e,ih eq.2.2]

private theorem role_selection (s : W) (i j : Nat) :
    select (roles i ++ roles j) (s.flatMap roles) = (select [i,j] s).flatMap roles := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    by_cases h : a=i ∨ a=j
    · have kept : select (roles i ++ roles j) (roles a)=roles a := by
        rcases h with rfl|rfl <;> simp [roles,select]
      have er : select [i,j] (a::s)=a::select [i,j] s := by simp [select,h]
      simp only [List.flatMap_cons,select_append,kept,ih,er]
    · have hf : a≠i ∧ a≠j := by simpa using h
      have non : ∀ b∈roles a, b∉roles i ++ roles j := by
        intro b m n
        simp only [roles,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at m n
        unfold owner mate at m n
        omega
      have erased := select_nil _ _ non
      have er : select [i,j] (a::s)=select [i,j] s := by simp [select,h]
      simp only [List.flatMap_cons,select_append,erased,ih,er,List.nil_append]

/-- In the literal eight-occurrence projection on the four actual roles,
the oriented interleaving exists exactly for an intended matching edge.
This is independent of block order and permits unmatched boundary cells. -/
theorem literal_phase_exact {bs : List Block} (nd : (bs.flatMap cells).Nodup)
    (i j : Nat) (ne : i≠j) :
    select (roles i ++ roles j) (letters bs) =
      [owner i,mate i,owner j,mate j,owner i,mate i,owner j,mate j] ↔
      Block.pair i j∈bs := by
  unfold letters
  rw [role_selection,← phase_exact nd i j ne]
  change _ = [i,j,i,j].flatMap roles ↔ _
  exact ⟨roles_inj,congrArg (List.flatMap roles)⟩

end P455PaddedPorts
