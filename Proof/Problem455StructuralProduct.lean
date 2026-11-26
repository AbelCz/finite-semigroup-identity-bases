import Problem455Structural



namespace P455StructuralProduct
open P455Structural P455Witness P455Quotient P455Closure P455Uncrossed
open P455SourceFamilies P455FirstTesters P455FirstRewrite

def templates (r : Nat) := Problem455Finite.wordsUpTo (List.range 4) (4*r)
structure Index (r : Nat) (allow : Tag → Prop) where
  pos : Fin (templates r).length
  cap : P455Closure.Cap r ((templates r).get pos)
  cmp : Compressed r ((templates r).get pos)
  test : Structural ((templates r).get pos) r allow
def Index.T (i : Index r allow) := (templates r).get i.pos
abbrev Carrier (r : Nat) (allow : Tag → Prop) := (i : Index r allow) → Q (plain r) i.T

def product (r : Nat) (allow : Tag → Prop) : Model (Carrier r allow) where
  op := fun x y i => mul (plain r) i.cap (x i) (y i)
  unit := fun i => ofWord (plain r) i.T []
  assoc := fun x y z => funext (fun i => mul_assoc (plain r) i.cap (x i) (y i) (z i))
  oneL := fun x => funext (fun i => (unit_laws (plain r) i.cap (x i)).1)
  oneR := fun x => funext (fun i => (unit_laws (plain r) i.cap (x i)).2)

theorem coordinate (f : Nat → Carrier r allow) (w : List Nat) (i : Index r allow) :
    (product r allow).eval f w i = eval (plain r) i.cap (fun x => f x i) w := by
  induction w with
  | nil => rfl
  | cons x xs ih => exact congrArg (mul (plain r) i.cap (f x i)) ih

theorem identity {r allow} (f : Frame Nat) (l k : List Nat) (x y : Nat)
    (hp : f.p=[x]) (hq : f.q=[y]) (valid : f.Valid r allow (fun _ _ => False)) :
    (product r allow).Valid (side f l k false) (side f l k true) := by
  intro val
  funext i
  rw [coordinate,coordinate]
  exact structural_eval i.cap i.cmp i.test f l k x y hp hq valid _

/-- The actual shared canonical words of the positional gap construction
satisfy the structural subproduct identity for every retained-name list
containing the marked roles. -/
theorem small_identity {r allow} (f : Frame Nat) (l k names : List Nat) (x y : Nat)
    (hx : x ∈ names) (hy : y ∈ names) (hp : f.p=[x]) (hq : f.q=[y])
    (valid : f.Valid r allow (fun _ _ => False)) (bit : Bool)
    (cap : P455Closure.Cap r (side f l k bit)) :
    (product r allow).Valid (P455Compression.small (side f l k false) names)
      (P455Compression.small (side f l k true) names) := by
  obtain ⟨g,L,K,gp,gq,gv,eq,_⟩ :=
    P455CompressedFrame.canonical_pair f l k names hx hy hp hq valid bit cap
  rw [eq,eq]
  exact identity g L K x y gp gq gv

end P455StructuralProduct
