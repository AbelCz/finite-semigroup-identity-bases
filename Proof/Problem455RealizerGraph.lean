import Problem455EffectiveQ



namespace P455RealizerGraph
open P455EffectiveQ
variable {α : Type} [DecidableEq α]

def joinAt (k : α) (m : List (α × α)) := m ++ m.flatMap fun p =>
  if p.2=k then m.filterMap (fun q => if q.1=k then some (p.1,q.2) else none) else []

theorem mem_joinAt (k a b : α) (m : List (α × α)) :
    (a,b)∈joinAt k m ↔ (a,b)∈m ∨ ((a,k)∈m ∧ (k,b)∈m) := by
  simp only [joinAt,List.mem_append,List.mem_flatMap]
  apply or_congr_right
  constructor
  · rintro ⟨⟨x,y⟩,px,h⟩
    by_cases eq : y=k
    · subst y
      simp [List.mem_filterMap] at h
      obtain ⟨z,w,qz,rfl,rfl,rfl⟩ := h
      exact ⟨px,qz⟩
    · simp [eq] at h
  · rintro ⟨p,q⟩
    refine ⟨(a,k),p,?_⟩
    simp [List.mem_filterMap]
    exact q

def initial (domain : List α) (edge : α → α → Bool) := domain.flatMap fun a =>
  (domain.filter fun b => decide (a=b) || edge a b).map fun b => (a,b)

theorem mem_initial {domain : List α} (edge : α → α → Bool) {a b : α} (ha : a∈domain) (hb : b∈domain) :
    (a,b)∈initial domain edge ↔ a=b ∨ edge a b=true := by
  simp only [initial,List.mem_flatMap,List.mem_map,List.mem_filter,Bool.or_eq_true,decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x,_,y,⟨_,e⟩,rfl,rfl⟩; exact e
  · intro h; exact ⟨a,ha,b,⟨hb,h⟩,rfl,rfl⟩

theorem mem_fold {domain : List α} (e : α → α → Bool) (pivots : List α)
    (hp : ∀ x∈pivots,x∈domain) {a b : α} (ha : a∈domain) (hb : b∈domain) :
    (a,b)∈pivots.foldr joinAt (initial domain e) ↔ P455EffectiveQReach.via e pivots a b=true := by
  induction pivots generalizing a b with
  | nil => simpa [P455EffectiveQReach.via] using mem_initial e ha hb
  | cons k ks ih =>
    have mem := hp k List.mem_cons_self
    have rest : ∀ x∈ks,x∈domain := fun x h => hp x (List.mem_cons_of_mem _ h)
    simp only [List.foldr_cons,mem_joinAt,P455EffectiveQReach.via,Bool.or_eq_true,Bool.and_eq_true,
      ih rest ha hb,ih rest ha mem,ih rest mem hb]

def walk (e : W → W → Bool) (u v : W) :=
  let pivots := words u
  decide ((u,v)∈pivots.foldr joinAt (initial (u::v::pivots) e))

theorem walk_eq (e : W → W → Bool) (u v : W) : walk e u v=walkB e u v := by
  apply Bool.eq_iff_iff.mpr
  simp only [walk,decide_eq_true_eq,walkB]
  exact mem_fold e _ (fun x h => by simp [h]) (by simp) (by simp)

end P455RealizerGraph
