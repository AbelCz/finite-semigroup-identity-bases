import Problem455NumericProduct
import Problem455TableBits
import Mathlib.Computability.Primrec

/- Primitive-recursive numeric product on the standard mathlib encodings
of matrices. The theorem refers to the actual first-order core function. -/
namespace P455NumericProductPrim
open P455Table P455NumericProduct
variable {A : Type} [Primcodable A]

theorem entry' {T : A→Matrix} {i j : A→Nat} (t : Primrec T) (a : Primrec i) (b : Primrec j) :
    Primrec (fun x => entry (T x) (i x) (j x)) := by
  have row := Primrec.option_getD.comp (Primrec.list_getElem?.comp t a) (Primrec.const [])
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp row b) (Primrec.const 0)

theorem grid' {n : A→Nat} {f : A→Nat→Nat→Nat} (dim : Primrec n)
    (elem : Primrec (fun p : (A×Nat)×Nat => f p.1.1 p.1.2 p.2)) :
    Primrec fun x => grid (n x) (f x) := by
  exact Primrec.list_map (Primrec.list_range.comp dim)
    (Primrec₂.mk (Primrec.list_map (Primrec.list_range.comp (dim.comp Primrec.fst)) elem.to₂))

theorem tensor' : Primrec₂ tensor := by
  apply Primrec₂.mk
  apply grid' (Primrec.nat_mul.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))
  let Src := ((Matrix×Matrix)×Nat)×Nat
  have l : Primrec (fun a : Src => a.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have r : Primrec (fun a : Src => a.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have d := Primrec.list_length.comp r
  have i : Primrec (fun a : Src => a.1.2) := Primrec.snd.comp Primrec.fst
  have j : Primrec (fun a : Src => a.2) := Primrec.snd
  exact Primrec.nat_add.comp (entry' r (Primrec.nat_mod.comp i d) (Primrec.nat_mod.comp j d))
    (Primrec.nat_mul.comp (entry' l (Primrec.nat_div.comp i d) (Primrec.nat_div.comp j d)) d)

theorem assemble' : Primrec assemble := by
  exact Primrec.list_foldr (h:=fun (_ : List Matrix) (p : Matrix × Matrix) => tensor p.1 p.2) (Primrec.id (α:=List Matrix)) (Primrec.const P455NumericProduct.singleton)
    (Primrec₂.mk (tensor'.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem unary : Primrec P455TableBits.unary := by
  have bits : Primrec (fun n : Nat => (List.range n).map (fun _ => true)) :=
    Primrec.list_map Primrec.list_range (Primrec₂.const true)
  exact (Primrec.list_append.comp bits (Primrec.const [false])).of_eq (fun _ => by
    simp [P455TableBits.unary,List.map_const'])

theorem row : Primrec P455TableBits.row :=
  Primrec.list_flatMap Primrec.id (unary.comp Primrec.snd).to₂

theorem encode : Primrec P455TableBits.encode :=
  Primrec.list_append.comp (unary.comp Primrec.list_length)
    (Primrec.list_flatMap Primrec.id (row.comp Primrec.snd).to₂)

theorem bits_of_product : Primrec (fun cs => P455TableBits.encode (assemble cs)) :=
  encode.comp assemble'

end P455NumericProductPrim
