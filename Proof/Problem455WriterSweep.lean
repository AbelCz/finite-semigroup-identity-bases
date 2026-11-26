import Problem455WriterFrontier

namespace P455WriterSweep
open P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine
open P455EffectiveChain P455WriterFrontier

def reach (M : Ordinary g q) (c d : Config g q) := ∃ t, follow M c t=d

theorem trans {M : Ordinary g q} {a b c} (h : reach M a b) (k : reach M b c) : reach M a c := by
  obtain ⟨u,rfl⟩ := h; obtain ⟨v,hv⟩ := k
  exact ⟨u+v,by rw [follow_add,hv]⟩

theorem single {M : Ordinary g q} {c d} (h : once M c=d) : reach M c d := ⟨1,h⟩

def cleanSym (M : Ordinary g q) (O : Alphabet M) (read : Fin g → Option Bool)
    (a : Fin (g+1)) : Fin (g+1) :=
  if a=ink M.marker then ink M.marker else
  if a=fresh g then fresh g else
  (read (eraseTag M.blank a)).elim (fresh g) (fun b => ink (O.bit b))

theorem clean_mark (M : Ordinary g q) (O : Alphabet M) (read) (a) :
    cleanSym M O read a=ink M.marker ↔ a=ink M.marker := by
  have freshNe := Ne.symm (ink_ne_fresh M.marker)
  by_cases h : a=ink M.marker
  · simp [cleanSym,h]
  · simp only [cleanSym,h,↓reduceIte,iff_false]
    split
    · exact freshNe
    · cases read (eraseTag M.blank a) with
      | none => exact freshNe
      | some b => exact fun e => O.away b (ink_inj.mp e)

def control (M : Ordinary g q) (O : Alphabet M) (read : Fin g→Option Bool)
    (s : Fin 3) (a : Fin (g+1)) : Option (Ins (Fin (g+1)) (Fin 3)) :=
  if s=0 then
    if a=ink M.marker then some ⟨1,a,.right⟩ else some ⟨0,a,.left⟩
  else if s=1 then
    if a=fresh g then some ⟨2,a,.left⟩ else some ⟨1,cleanSym M O read a,.right⟩
  else if a=ink M.marker then none else some ⟨2,a,.left⟩

def sweep (M : Ordinary g q) (O : Alphabet M) (read : Fin g→Option Bool) : Ordinary (g+1) 3 where
  marker := ink M.marker
  blank := fresh g
  blank_ne := Ne.symm (ink_ne_fresh _)
  start := 0
  delta := control M O read
  keeps := by
    intro s a i e
    unfold control at e
    split at e <;> split at e
    · cases e; rfl
    · cases e; rfl
    · split at e
      · cases e; rfl
      · cases e; exact clean_mark ..
    · split at e
      · contradiction
      · cases e; rfl
  leftSafe := by
    intro s i e
    simp only [control,if_pos rfl,ink_ne_fresh,↓reduceIte] at e
    split at e
    · cases e; exact Direction.noConfusion
    · split at e
      · cases e; exact Direction.noConfusion
      · contradiction

def mix (src dst : Nat→Fin k) (p i : Nat) := if i<p then dst i else src i

theorem mix_next (src dst : Nat→Fin k) (p) :
    writeAt (mix src dst p) p (dst p)=mix src dst (p+1) := by
  funext i; by_cases e : i=p
  · subst i; simp [writeAt,mix]
  · have same : i<p+1 ↔ i<p := by omega
    simp [writeAt,mix,e,same]

theorem rewind (M : Ordinary g q) (O : Alphabet M) (read) (src : Nat → Fin (g+1))
    (proper : ∀ j, src j=ink M.marker ↔ j=0) (s : Fin 3) (mode : s=0 ∨ s=2) (p) :
    reach (sweep M O read) ⟨src,p,s⟩ ⟨src,0,s⟩ := by
  induction p with
  | zero => exact ⟨0,rfl⟩
  | succ p ih =>
    apply trans _ ih
    apply single
    have ne : src (p+1)≠ink M.marker := fun e => Nat.succ_ne_zero p ((proper _).mp e)
    rcases mode with rfl|rfl <;> simp [once,instruction,sweep,control,ne,write_same,dest]

theorem sweep_run (M : Ordinary g q) (O : Alphabet M) (read) (src dst : Nat → Fin (g+1))
    (n : Nat) (used : ∀ i, i≤n → src i≠fresh g)
    (tailBlank : ∀ i, n<i → src i=fresh g)
    (clean : ∀ i, dst i=cleanSym M O read (src i))
    (p k : Nat) (bound : p+k=n+1) :
    reach (sweep M O read) ⟨mix src dst p,p,1⟩ ⟨dst,n,2⟩ := by
  induction k generalizing p with
  | zero =>
    have e : p=n+1 := by omega
    subst p
    have ne := Ne.symm (ink_ne_fresh M.marker)
    have whole : mix src dst (n+1)=dst := by
      funext i; by_cases le : i<n+1
      · simp [mix,le]
      · have blank := tailBlank i (by omega)
        simp [mix,le,clean i,blank,cleanSym,ne]
    have blank : dst (n+1)=fresh g := by
      rw [clean,tailBlank _ (by omega)]
      simp [cleanSym,ne]
    rw [whole]; apply single
    have stop : instruction (sweep M O read) ⟨dst,n+1,1⟩=some ⟨2,dst (n+1),.left⟩ := by
      simp [instruction,sweep,control,blank]
    rw [once,stop]; simp [write_same,dest]
  | succ k ih =>
    have le : p≤n := by omega
    apply trans _ (ih (p+1) (by omega))
    apply single
    have atp : mix src dst p p=src p := by simp [mix]
    have ins : instruction (sweep M O read) ⟨mix src dst p,p,1⟩=
        some ⟨1,dst p,.right⟩ := by
      simp [instruction,sweep,control,atp,used _ le,clean p]
    rw [once,ins]
    simp [mix_next,dest]

theorem finish (M : Ordinary g q) (O : Alphabet M) (read) (src : Nat→Fin (g+1)) (p n)
    (proper : ∀ j, src j=ink M.marker ↔ j=0)
    (used : ∀ i, i≤n → src i≠fresh g) (tailBlank : ∀ i, n<i → src i=fresh g) :
    let dst := fun j => cleanSym M O read (src j)
    reach (sweep M O read) ⟨src,p,0⟩ ⟨dst,0,2⟩ ∧
    instruction (sweep M O read) ⟨dst,0,2⟩=none := by
  let dst := fun j => cleanSym M O read (src j)
  have mp : ∀ j, dst j=ink M.marker ↔ j=0 := fun j => (clean_mark ..).trans (proper j)
  have origin := (proper 0).mpr rfl
  have start : mix src dst 1=src := by
    funext i; cases i with
    | zero => simp [mix,dst,origin,cleanSym]
    | succ i => simp [mix]
  constructor
  · apply trans (rewind M O read src proper 0 (Or.inl rfl) p)
    have first : reach (sweep M O read) ⟨src,0,0⟩ ⟨mix src dst 1,1,1⟩ := by
      rw [start]; apply single
      have i : instruction (sweep M O read) ⟨src,0,0⟩=some ⟨1,src 0,.right⟩ := by
        simp [instruction,sweep,control,origin]
      rw [once,i]; simp [dest,write_same]
    exact trans first (trans (sweep_run M O read src dst n used tailBlank (fun _ => rfl) 1 n (by omega))
      (rewind M O read dst mp 2 (Or.inr rfl) n))
  · change control M O read 2 (dst 0)=none
    simp [control,(mp 0).mpr rfl]

end P455WriterSweep
