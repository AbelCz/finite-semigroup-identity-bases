import Problem455MathlibCode
import Problem455MathlibMarker

/- The compilation fixes a finite machine before the input. Its exact
   terminal tape equals the same physical encoding of the output list. -/
namespace P455MathlibTM
open Turing PartrecToTM2 P455MathlibCode

abbrev Track := TM2to1.Γ' K' (fun _ => Γ')

instance stackFinite : Fintype K' :=
  ⟨{.main,.rev,.aux,.stack},fun k => by cases k <;> simp⟩

def cell (bottom : Bool) (s : Γ') : Track :=
  (bottom, Function.update (fun _ => none) K'.main (some s))

def image (x : List Bool) : List Track :=
  cell true .cons :: cell false .bit1 :: x.map (fun b => cell false (letter b))

theorem tr_input (x : List Bool) :
    TM2to1.trInit (Γ := fun _ => Γ') K'.main (trList [wire x]) = image x := by
  unfold TM2to1.trInit
  rw [raw_main]
  simp [image,cell,List.map_map,Function.comp_def]

theorem unique_sim {K : Type} {G : K → Type} {L V : Type}
    {u : TM2.Cfg G L V} {a b}
    (ha : TM2to1.TrCfg u a) (hb : TM2to1.TrCfg u b) : a=b := by
  cases ha with
  | mk t ht =>
    cases hb with
    | mk s hs =>
      have eq : t=s := by
        apply ListBlank.ext
        intro n
        funext k
        have h := congrArg (fun z => ListBlank.nth z n) ((ht k).trans (hs k).symm)
        simpa only [ListBlank.nth_map] using h
      subst s
      rfl

private theorem final_config {K : Type} {G : K → Type} {L V : Type}
    {u : TM2.Cfg G L V} {a} (h : TM2to1.TrCfg u a) (val : V) :
    TM2to1.TrCfg ⟨(none : Option L),val,u.stk⟩ ⟨none,val,a.Tape⟩ := by
  cases h with
  | mk t ht => exact .mk t ht

private theorem stack_update (x : List Γ') :
    Function.update (fun _ : K' => ([] : List Γ')) .main x = K'.elim x [] [] [] := by
  funext k
  cases k <;> simp [K'.elim,Function.update]

/-- Finiteness of the actual alphabet, a finite support of reachable
    control labels and full bilateral tape equality at a genuine halt. -/
theorem supported {f : List Bool → List Bool} (hf : Computable f) :
    ∃ (L : Type) (_ : Inhabited L) (M : TM0.Machine Track L) (S : Finset L),
       TM0.Supports M (S : Set L) ∧
       (∀ q ∈ S, ∀ a q' b, M q a = some (q',.write b) → b.1=a.1) ∧
       ∀ x, ∃ q, (⟨q,Tape.mk₁ (image (f x))⟩ : TM0.Cfg Track L) ∈
         Turing.eval (TM0.step M) (TM0.init (image x)) := by
  classical
  obtain ⟨c, hc⟩ := compile hf
  letI : Inhabited PartrecToTM2.Λ' := ⟨trNormal c .halt⟩
  let M₁ := TM2to1.tr PartrecToTM2.tr
  let M₀ := TM1to0.tr M₁
  obtain ⟨S,hs,mark⟩ := P455MathlibMarker.guarded M₁ (P455MathlibMarker.tr_safe _)
    (TM1to0.tr_supports M₁ (TM2to1.tr_supports _ (PartrecToTM2.tr_supports c .halt)))
  refine ⟨_,inferInstance,M₀,S,hs,mark,?_⟩
  intro x
  let v := [wire x]
  let w := [wire (f x)]
  have run : PartrecToTM2.halt w ∈ Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval]
    exact (Part.mem_map_iff _).mpr ⟨_,hc x,rfl⟩
  have e (u : List Nat) : PartrecToTM2.init c u = TM2.init (Λ := PartrecToTM2.Λ') (σ := Option Γ') K'.main (trList u) := by
    simp [PartrecToTM2.init,TM2.init,stack_update]
    rfl
  rw [e] at run
  obtain ⟨b, hb, rb⟩ := Turing.tr_eval (TM2to1.tr_respects PartrecToTM2.tr)
    (TM2to1.trCfg_init (Γ := fun _ : K' => Γ') (Λ := PartrecToTM2.Λ') (σ := Option Γ') K'.main (trList v)) run
  have standard := TM2to1.trCfg_init (Γ := fun _ : K' => Γ') (Λ := PartrecToTM2.Λ') (σ := Option Γ') K'.main (trList w)
  have target := final_config standard (none : Option Γ')
  simp only [TM2.init,stack_update,TM1.init] at target
  have eq := unique_sim hb target
  subst b
  obtain ⟨d, hd, rd⟩ := Turing.tr_eval (TM1to0.tr_respects M₁) rfl rb
  subst d
  refine ⟨(none,none),?_⟩
  simpa only [v,w,tr_input] using rd

end P455MathlibTM
