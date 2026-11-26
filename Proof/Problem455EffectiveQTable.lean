import Problem455EffectiveQMove
import Problem455TableProduct
import Problem455FirstTesters



namespace P455EffectiveQTable
open P455Quotient P455Table P455TableProduct
abbrev W := List Nat

def plainEq (r : Nat) (T : W) : DecidableEq (Q (P455FirstTesters.plain r) T) :=
  P455EffectiveQ.decEq _ (fun _ _ => false) (fun _ _ => by simp [P455FirstTesters.plain]) T

def plainListing (r : Nat) (T : W) := quotientListing (P455FirstTesters.plain r) T (plainEq r T)

def plainOps (r : Nat) (T : W) (cap : Cap r T) :=
  finiteOps (plainListing r T) (quotientModel _ T cap)

def plainPresents (r : Nat) (T : W) (cap : Cap r T) :
    Presents (plainOps r T cap) (quotientModel (P455FirstTesters.plain r) T cap) :=
  presentation .. 

section
variable {tags : List (List Bool)} {marks : Nat → Nat → Bool}
  {allow : List Bool → Prop} {mark : Nat → Nat → Prop}
  (tag_ok : ∀ t,t∈tags ↔ allow t) (mark_ok : ∀ a b,marks a b=true ↔ mark a b)

def markedListing (r : Nat) (T : W) := quotientListing (Problem455Finite.rules r allow mark) T
  (P455EffectiveQMove.markedEq tag_ok mark_ok r T)

def markedOps (r : Nat) (T : W) (cap : Cap r T) :=
  finiteOps (markedListing tag_ok mark_ok r T) (quotientModel _ T cap)

def markedPresents (r : Nat) (T : W) (cap : Cap r T) :
    Presents (markedOps tag_ok mark_ok r T cap) (quotientModel (Problem455Finite.rules r allow mark) T cap) :=
  presentation ..
end
end P455EffectiveQTable
