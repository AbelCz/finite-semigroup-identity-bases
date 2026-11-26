import Problem455CellClassHalting

/- Explicit identity class and first-change obstruction for the literal
   canonical word of each legal rectangle. Arbitrary comparison words,
   all model valuations and all ordinary semigroup rule instances. -/
namespace P455CellClassEndpoints
open P455FirstRewrite P455RectangleRank P455PaddedWord P455PaddedTiles P455CellClassGrid
open P455CellClassHalting P455CellClassSnake P455CellClassRank P455CellClass
open Problem455.Slots
abbrev W := List Nat
variable {n w h : Nat} {M : MachineTable n}

def endpoint (R : Rectangle M w h) (b : Bool) := text h w (widthCode n) (labels R) (constant b)
abbrev monoid (M : MachineTable n) := P455FullSingleton.model (widthCode n+16) (allowed M) (system n)

theorem rank_witness (R : Rectangle M w h) (size : 1<w*h) :
    RankWitness (monoid M) (widthCode n+16) (endpoint R false) (endpoint R true) (List.range (2*(w*h))) := by
  let g := (data R size).geometry
  have l := layout (show 0<widthCode n+16 by omega) g
  have cap := g.phases.capped
  apply P455RectangleRank.witness (by omega) (by omega) _ _ g.names cap (P455ConstantProduct.identity _ l)
    (fun v identity => represent g.names cap g.finalPair identity)
  intro bits valid
  constructor
  · intro i ix yes
    cases val : bits (i+1)
    · have small : i<w*h := by omega
      exact False.elim (no_incident_descent small yes cap (g.finalPair i small) valid
        (descent g.phases bits g.finalPair small ix yes val (g.next i ix)))
    · rfl
  · intro positive yes
    cases val : bits 0
    · have small : w*h-1<w*h := by omega
      exact False.elim (no_incident_descent small yes cap (g.finalPair _ small) valid
        (descent g.phases bits g.finalPair small positive yes val (g.wrap positive)))
    · rfl

theorem constant_identity (R : Rectangle M w h) (size : 1<w*h) :
    (monoid M).Valid (endpoint R false) (endpoint R true) := (rank_witness R size).identity

theorem zero_class (R : Rectangle M w h) (size : 1<w*h) (V : W) :
    (monoid M).Valid (endpoint R false) V ↔ V=endpoint R false ∨ V=endpoint R true := by
  constructor
  · exact (rank_witness R size).two V
  · rintro (rfl|rfl)
    · intro _; rfl
    · exact constant_identity R size

theorem first_changing_rank (R : Rectangle M w h) (size : 1<w*h) {G : W → W → Prop}
    (sound : ∀ u v, G u v → (monoid M).Valid u v) {V : W} (step : Step G (endpoint R false) V)
    (diff : endpoint R false ≠ V) : ∃ u v, G u v ∧ 2*(w*h) ≤ rank u v := by
  simpa using step_rank (by omega) (rank_witness R size)
    (fun _ _ e => P455FirstTesters.tester_rule (P455FirstTesters.valid_left _ _ e)) sound step diff

end P455CellClassEndpoints
