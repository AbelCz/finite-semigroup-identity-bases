import Mathlib.Computability.TMToPartrec

namespace P455MathlibMarker
open Turing

variable {K : Type} {G : K → Type} {L V : Type} [DecidableEq K]

abbrev Track := TM2to1.Γ' K G

def safe : TM1.Stmt (Track (G := G)) L V → Prop
  | .move _ s | .load _ s => safe s
  | .write w s => (∀ a v, (w a v).1 = a.1) ∧ safe s
  | .branch _ p q => safe p ∧ safe q
  | .goto _ | .halt => True

omit [DecidableEq K] in
theorem trNormal_safe (s : TM2.Stmt G L V) : safe (TM2to1.trNormal s) := by
  induction s <;> simp_all [TM2to1.trNormal,safe]

theorem tr_safe (M : L → TM2.Stmt G L V) (q) : safe (TM2to1.tr M q) := by
  cases q with
  | normal => exact trNormal_safe _
  | ret => exact ⟨trNormal_safe _,True.intro⟩
  | go k s q => cases s <;> simp [TM2to1.tr,TM2to1.trStAct,safe]

variable [Inhabited L] [Inhabited V]
variable (M : L → TM1.Stmt (Track (G := G)) L V)

def safeState (q : TM1to0.Λ' M) := ∀ p ∈ q.1, safe p

def preserves (a : Track (G := G)) : TM0.Stmt (Track (G := G)) → Prop
  | .move _ => True
  | .write b => b.1=a.1

variable (hm : ∀ l, safe (M l))
include hm

omit [DecidableEq K] [Inhabited L] [Inhabited V] in
theorem trAux_safe (a : Track (G := G)) (p : TM1.Stmt (Track (G := G)) L V)
    (hp : safe p) (v) :
    safeState M (TM1to0.trAux M a p v).1 ∧ preserves a (TM1to0.trAux M a p v).2 := by
  induction p generalizing v with
  | move _ q => simpa [TM1to0.trAux,safeState,preserves,safe] using hp
  | write w q => exact ⟨fun _ h => Option.some.inj h ▸ hp.2, hp.1 _ _⟩
  | load _ _ ih => exact ih hp _
  | branch b p q ih₁ ih₂ =>
    cases e : b a v <;> simp only [TM1to0.trAux,e,cond] <;> first | exact ih₁ hp.1 v | exact ih₂ hp.2 v
  | goto l => simpa [TM1to0.trAux,safeState,preserves] using hm (l a v)
  | halt => simp [TM1to0.trAux,safeState,preserves]

omit [DecidableEq K] in
theorem guarded {S : Finset (TM1to0.Λ' M)} (hs : TM0.Supports (TM1to0.tr M) ↑S) :
    ∃ U : Finset (TM1to0.Λ' M), TM0.Supports (TM1to0.tr M) ↑U ∧
      ∀ q ∈ U, ∀ a q' b, (TM1to0.tr M) q a = some (q',.write b) → b.1=a.1 := by
  classical
  refine ⟨S.filter (safeState M), ⟨?_,?_⟩,?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨hs.1,by simpa [safeState,TM1to0.instInhabitedΛ'] using hm default⟩
  · rintro ⟨_ | p,v⟩ a q' s step good
    · contradiction
    obtain ⟨mem,safeP⟩ := Finset.mem_filter.mp good
    have hp := safeP p rfl
    have h := (trAux_safe M hm a p hp v).1
    exact Finset.mem_filter.mpr ⟨hs.2 step mem,(congrArg (safeState M) (congrArg Prod.fst (Option.some.inj step))).mp h⟩
  · rintro ⟨_ | p,v⟩ good a q' b step
    · contradiction
    have hp := (Finset.mem_filter.mp good).2 p rfl
    have h := (trAux_safe M hm a p hp v).2
    exact (congrArg (preserves a) (congrArg Prod.snd (Option.some.inj step))).mp h

end P455MathlibMarker
