import Problem455TableProduct

/- These finite catalogues and quotient equalities are plugged into the
   concrete compiler by the output module. Functions here assemble exactly
   the dependent products used in the rank theorem. -/
namespace P455TableFactors
open P455Table P455TableProduct P455FirstRewrite P455Witness P455Paths


abbrev Whole (r : Nat) (allow : Tag → Prop) (ts : Tiles) :=
    P455FirstTesters.Carrier r ×
      ((P455GuardProduct.Carrier r allow ts × P455EdgeProduct.Carrier r allow ts) ×
       (P455BinaryProduct.Carrier r allow × P455StructuralProduct.Carrier r allow))

def components {I : Type} (C : Listing I) (rs : I → P455Quotient.Rules Nat) (ts : I → List Nat)
    (eq : ∀ i, DecidableEq (P455Quotient.Q (rs i) (ts i))) :
    Listing ((i : I) → P455Quotient.Q (rs i) (ts i)) :=
  family C (fun i => quotientListing _ _ (eq i)) (fun i => P455Quotient.zero (rs i) (ts i))

structure Catalogues (r : Nat) (allow : Tag → Prop) (ts : Tiles) where
  primitive : Listing (P455FirstTesters.Index r)
  binary : Listing (P455BinaryProduct.Index r allow)
  structural : Listing (P455StructuralProduct.Index r allow)
  guard : Listing (P455GuardProduct.Index r allow ts)
  edge : Listing (P455EdgeProduct.Index r allow ts)

structure EqualityTests (r : Nat) (allow : Tag → Prop) (ts : Tiles) where
  plain : ∀ T : List Nat, DecidableEq (P455Quotient.Q (P455FirstTesters.plain r) T)
  binary : ∀ i : P455BinaryProduct.Index r allow, DecidableEq (P455Quotient.Q i.R i.T)
  guard : ∀ i : P455GuardProduct.Index r allow ts, DecidableEq (P455Quotient.Q i.R i.T)
  edge : ∀ i : P455EdgeProduct.Index r allow ts, DecidableEq (P455Quotient.Q i.R i.T)

def listing {r allow ts} (C : Catalogues r allow ts) (E : EqualityTests r allow ts) :
    Listing (Whole r allow ts) :=
  pair (components C.primitive (fun _ => P455FirstTesters.plain r) Subtype.val (fun i => E.plain i.val))
    (pair (pair (components C.guard _ _ E.guard) (components C.edge _ _ E.edge))
      (pair (components C.binary _ _ E.binary)
        (components C.structural (fun _ => P455FirstTesters.plain r) _ (fun i => E.plain i.T))))

end P455TableFactors
