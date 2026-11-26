import Problem455WriterBlank
import Mathlib.Computability.Primrec

namespace P455WriterProgram
namespace Cert
open Primrec
variable {X : Type} [Primcodable X]
theorem g' : Primrec g := Primrec.fst
theorem q' : Primrec q := Primrec.fst.comp Primrec.snd
theorem marker' : Primrec marker := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem blank' : Primrec blank := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem start' : Primrec start := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem entries' : Primrec entries := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem get (l : X → List Nat) (hl : Primrec l) (n : Nat) : Primrec fun x => (l x).getD n 0 :=
  (Primrec.list_getD 0).comp hl (Primrec.const n)
theorem incHead' : Primrec incHead :=
  Primrec.list_cons.comp (Primrec.nat_add.comp (get _ Primrec.id 0) (Primrec.const 1)) Primrec.list_tail

theorem readBits' : Primrec readBits := by
  apply Primrec.list_foldr (h:=fun (_ : List Bool) (p : Bool × List Nat) => bif p.1 then incHead p.2 else 0::p.2)
    (Primrec.id (α:=List Bool)) (Primrec.const ([] : List Nat))
  exact (Primrec.cond (Primrec.fst.comp Primrec.snd) (incHead'.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.const 0) (Primrec.snd.comp Primrec.snd))).to₂

theorem drop' (n : Nat) : Primrec fun l : List Nat => l.drop n := by
  induction n with
  | zero => exact Primrec.id
  | succ n ih => exact (Primrec.list_tail.comp ih).of_eq fun l => List.tail_drop

theorem raw' : Primrec raw :=
  (get _ Primrec.id 2).pair ((get _ Primrec.id 3).pair ((get _ Primrec.id 4).pair
    ((get _ Primrec.id 5).pair ((get _ Primrec.id 6).pair (drop' 7)))))

theorem ones : Primrec fun n : Nat => List.replicate n (1 : Nat) :=
  (Primrec.list_map Primrec.list_range (Primrec₂.const 1)).of_eq (fun _ => by simp [List.map_const'])

theorem script' {w : X → List Bool} {a b : X → Nat} (ha : Primrec a) (hb : Primrec b) (hw : Primrec w) :
    Primrec fun x => script (a x) (b x) (w x) :=
  Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_append.comp
    (Primrec.list_map hw (Primrec.nat_add.comp (Primrec.cond Primrec.snd (hb.comp Primrec.fst)
      (ha.comp Primrec.fst)) (Primrec.const 2)).to₂)
    (ones.comp (Primrec.nat_add.comp (Primrec.list_length.comp hw) (Primrec.const 1))))

theorem written' {c m a : X → Nat} (hc : Primrec c) (hm : Primrec m) (ha : Primrec a) :
    Primrec fun x => writtenSymbol (c x) (m x) (a x) :=
  Primrec.ite ((Primrec.nat_lt.comp hc (Primrec.const 2)).or
    ((Primrec.eq.comp ha hm).or (Primrec.eq.comp (Primrec.nat_sub.comp hc (Primrec.const 2)) hm))) ha
    (Primrec.nat_sub.comp hc (Primrec.const 2))

theorem dir' {c m a : X → Nat} (hc : Primrec c) (hm : Primrec m) (ha : Primrec a) :
    Primrec fun x => dir (c x) (m x) (a x) :=
  Primrec.ite (Primrec.eq.comp hc (Primrec.const 1))
    (Primrec.ite (Primrec.eq.comp ha hm) (Primrec.const 1) (Primrec.const 0)) (Primrec.const 2)

theorem instr' {ng z a d : X → Nat} (hg : Primrec ng) (hz : Primrec z) (ha : Primrec a) (hd : Primrec d) :
    Primrec fun x => instr (ng x) (z x) (a x) (d x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.nat_add.comp (Primrec.nat_mul.comp hg hz) ha))) hd

theorem push' : Primrec₂ pushRaw := by
  apply Primrec₂.mk
  have m : Primrec fun p : Nat × Raw => p.2 := Primrec.snd
  have aux : Primrec fun p : (Nat × Raw) × Nat => p.1.2 := m.comp Primrec.fst
  have c : Primrec fun p : (Nat × Raw) × Nat => p.1.1 := Primrec.fst.comp Primrec.fst
  exact (g'.comp m).pair ((Primrec.nat_add.comp (q'.comp m) (Primrec.const 1)).pair
    ((marker'.comp m).pair ((blank'.comp m).pair ((q'.comp m).pair
      (Primrec.list_append.comp (entries'.comp m) (Primrec.list_map (Primrec.list_range.comp (g'.comp m))
        (instr' (g'.comp aux) (start'.comp aux) (written' c (marker'.comp aux) Primrec.snd)
          (dir' c (marker'.comp aux) Primrec.snd)).to₂))))))

theorem blankRaw' : Primrec blankRaw := by
  apply Primrec.list_foldr (h:=fun (_ : List Bool) (p : Nat × Raw) => pushRaw p.1 p.2)
    (script' (get _ readBits' 0) (get _ readBits' 1) Primrec.id) (raw'.comp readBits')
  exact (push'.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

end Cert
end P455WriterProgram
