import Problem455RealizerPrim
namespace P455ClassPrim
open P455EffectiveQ P455GraphPrim

variable {A : Type} [Primcodable A]
abbrev Raw := Option W

theorem live {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {T : A → W} {z : A → Raw} (ht : Primrec T) (hz : Primrec z) :
    Primrec fun a => liveB (e a) (T a) (z a) := by
  let h (a : A) (w : W) := goodB (e a) (T a) w
  have rec : Primrec₂ h :=
    Primrec₂.mk (good (A := A × W) (e := fun q => e q.1)
      (he.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (ht.comp Primrec.fst) Primrec.snd)
  exact (Primrec.option_casesOn hz (Primrec.const false) rec).of_eq
    (fun a => by cases z a <;> rfl)

theorem pairedRec {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {T : A → W} {x y : A → Raw} (ht : Primrec T) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun a => paired (e a) (T a) (x a) (y a) := by
  let inside (a : A) (u v : W) := goodB (e a) (T a) u && goodB (e a) (T a) v && walkB (e a) u v
  have ep : Primrec (fun p : ((A×W)×W)×(W×W) => e p.1.1.1 p.2.1 p.2.2) :=
    he.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have rr : Primrec (fun p : (A×W)×W => inside p.1.1 p.1.2 p.2) :=
    Primrec.and.comp (Primrec.and.comp
      (good (A := (A×W)×W) (e := fun p => e p.1.1) ep (ht.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      (good (A := (A×W)×W) (e := fun p => e p.1.1) ep (ht.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (reachable (A := (A×W)×W) (e := fun p => e p.1.1) ep (Primrec.snd.comp Primrec.fst) Primrec.snd)
  let tail (a : A) (u : W) : Bool := Option.casesOn (y a) false (inside a u)
  have tr : Primrec₂ tail := Primrec₂.mk
    (Primrec.option_casesOn (hy.comp Primrec.fst) (Primrec.const false) rr.to₂)
  exact (Primrec.option_casesOn hx (Primrec.const false) tr).of_eq
    (fun a => by cases x a <;> cases h : y a <;> simp [tail,inside,h,paired])

theorem relation {e : A → W → W → Bool} (he : Primrec (fun x : A×(W×W) => e x.1 x.2.1 x.2.2))
    {T : A → W} {x y : A → Raw} (ht : Primrec T) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun a => relB (e a) (T a) (x a) (y a) :=
  Primrec.or.comp (Primrec.and.comp (Primrec.not.comp (live he ht hx)) (Primrec.not.comp (live he ht hy)))
    (pairedRec he ht hx hy)
end P455ClassPrim
