import Problem455WriterMachineData
import Problem455WriterProgramPrim

namespace P455WriterProgram.Cert
open Primrec
variable {X : Type} [Primcodable X]

theorem unpack' {ng k : X → Nat} (hg : Primrec ng) (hk : Primrec k) : Primrec fun x => unpack (ng x) (k x) := by
  have s := Primrec.nat_sub.comp hk (Primrec.const 1)
  have u := Primrec.nat_div.comp s (Primrec.const 3)
  exact (Primrec.nat_div.comp u hg).pair ((Primrec.nat_mod.comp u hg).pair (Primrec.nat_mod.comp s (Primrec.const 3)))

theorem normalized' {m : X → Raw} {z a : X → Nat} (hm : Primrec m) (hz : Primrec z) (ha : Primrec a) :
    Primrec (fun x => normalizedIns (m x) (z x) (a x)) := by
  have ng := g'.comp hm
  have nq := q'.comp hm
  have k := (Primrec.list_getD 0).comp (entries'.comp hm) (Primrec.nat_add.comp (Primrec.nat_mul.comp hz ng) ha)
  exact Primrec.ite (Primrec.nat_lt.comp hz nq)
    (Primrec.ite (Primrec.eq.comp k (Primrec.const 0)) (nq.pair (ha.pair (Primrec.const 1))) (unpack' ng k))
    (Primrec.ite ((Primrec.eq.comp hz nq).and ((Primrec.eq.comp ha (marker'.comp hm)).not))
      (nq.pair (ha.pair (Primrec.const 0))) ((Primrec.nat_add.comp nq (Primrec.const 1)).pair (ha.pair (Primrec.const 1))))

theorem act' {m : X → Raw} {v : X → Nat} (hm : Primrec m) (hv : Primrec v) :
    Primrec (fun x => act (m x) (v x)) := by
  have ng := g'.comp hm
  have h := Primrec.nat_div.comp hv ng
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) h)
    (Primrec.option_some.comp (normalized' hm (Primrec.nat_sub.comp h (Primrec.const 1)) (Primrec.nat_mod.comp hv ng)))
    (Primrec.const none)

theorem send' {ng a d : X → Nat} {i : X → Triple} (hg : Primrec ng) (ha : Primrec a) (hd : Primrec d) (hi : Primrec i) :
    Primrec (fun x => send (ng x) (a x) (d x) (i x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp hg (Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp hi)) hd)
    (Primrec.nat_add.comp (Primrec.fst.comp hi) (Primrec.const 1)) (Primrec.const 0))) ha

def route (ng sym : Nat) (left right : Bool) (l c r : Option Triple) : Option Nat :=
  if l=none ∧ c=none ∧ r=none then some sym
  else if l≠none ∧ c=none ∧ r=none then some (send ng sym 2 (l.getD (0,0,0)))
  else if l=none ∧ c=none ∧ r≠none then some (send ng sym 0 (r.getD (0,0,0)))
  else if l=none ∧ c≠none ∧ r=none then
    let i := c.getD (0,0,0)
    if (i.2.2=0 ∧ left=true) ∨ (i.2.2=2 ∧ right=true) then none else some (send ng i.2.1 1 i)
  else none

theorem route_eq (n a : Nat) (b f : Bool) (l c r : Option Triple) :
    route n a b f l c r=output n a b f l c r := by cases l <;> cases c <;> cases r <;> rfl

theorem output' {ng a : X → Nat} {bl br : X → Bool} {l c r : X → Option Triple}
    (hg : Primrec ng) (ha : Primrec a) (hb : Primrec bl) (hf : Primrec br) (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) :
    Primrec fun x => output (ng x) (a x) (bl x) (br x) (l x) (c x) (r x) := by
  have L := Primrec.eq.comp hl (Primrec.const none)
  have C := Primrec.eq.comp hc (Primrec.const none)
  have R := Primrec.eq.comp hr (Primrec.const none)
  have i := Primrec.option_getD.comp hc (Primrec.const (0,0,0))
  have D := Primrec.snd.comp (Primrec.snd.comp i)
  have rule : Primrec (fun x => route (ng x) (a x) (bl x) (br x) (l x) (c x) (r x)) :=
    Primrec.ite (L.and (C.and R)) (Primrec.option_some.comp ha) (Primrec.ite (L.not.and (C.and R))
    (Primrec.option_some.comp (send' hg ha (Primrec.const 2) (Primrec.option_getD.comp hl (Primrec.const (0,0,0)))))
    (Primrec.ite (L.and (C.and R.not))
    (Primrec.option_some.comp (send' hg ha (Primrec.const 0) (Primrec.option_getD.comp hr (Primrec.const (0,0,0)))))
    (Primrec.ite (L.and (C.not.and R)) (Primrec.ite
    (((Primrec.eq.comp D (Primrec.const 0)).and (Primrec.eq.comp hb (Primrec.const true))).or
    ((Primrec.eq.comp D (Primrec.const 2)).and (Primrec.eq.comp hf (Primrec.const true)))) (Primrec.const none)
    (Primrec.option_some.comp (send' hg (Primrec.fst.comp (Primrec.snd.comp i)) (Primrec.const 1) i))) (Primrec.const none))))
  exact rule.of_eq (fun _ => route_eq ..)

theorem isNone' {A : Type} [Primcodable A] : Primrec (@Option.isNone A) :=
  (Primrec.not.comp Primrec.option_isSome).of_eq fun o => by cases o <;> rfl

theorem localValue' {m : X → Raw} {l r : X → Option Nat} {c : X → Nat} (hm : Primrec m) (hl : Primrec l)
    (hc : Primrec c) (hr : Primrec r) : Primrec fun x => localValue (m x) (l x) (c x) (r x) :=
  output' (g'.comp hm) (Primrec.nat_mod.comp hc (g'.comp hm)) (isNone'.comp hl) (isNone'.comp hr)
    (Primrec.option_bind hl (act' (hm.comp Primrec.fst) Primrec.snd).to₂) (act' hm hc)
    (Primrec.option_bind hr (act' (hm.comp Primrec.fst) Primrec.snd).to₂)

theorem dimension' : Primrec dimension := Primrec.nat_mul.comp g'
  (Primrec.nat_add.comp (Primrec.nat_add.comp q' (Primrec.const 2)) (Primrec.const 1))
theorem neighbour' : Primrec neighbour := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
  (Primrec.const none) (Primrec.option_some.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem line' {m : X → Raw} {n l c : X → Nat} (hm : Primrec m) (hn : Primrec n) (hl : Primrec l) (hc : Primrec c) :
    Primrec fun x => line (m x) (n x) (l x) (c x) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hn (Primrec.const 1)))
  (localValue' (hm.comp Primrec.fst) (neighbour'.comp (hl.comp Primrec.fst)) (hc.comp Primrec.fst) (neighbour'.comp Primrec.snd)).to₂

theorem slab' {m : X → Raw} {n l : X → Nat} (hm : Primrec m) (hn : Primrec n) (hl : Primrec l) :
    Primrec fun x => slab (m x) (n x) (l x) :=
  Primrec.list_flatMap (Primrec.list_range.comp hn) (line' (hm.comp Primrec.fst) (hn.comp Primrec.fst) (hl.comp Primrec.fst) Primrec.snd).to₂

theorem grid' {m : X → Raw} {n : X → Nat} (hm : Primrec m) (hn : Primrec n) : Primrec fun x => grid (m x) (n x) :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.nat_add.comp hn (Primrec.const 1)))
  (slab' (hm.comp Primrec.fst) (hn.comp Primrec.fst) Primrec.snd).to₂

theorem machineData' : Primrec machineData := by
  have mark := Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd (α:=Raw) (β:=Nat)) (g'.comp Primrec.fst)) (marker'.comp Primrec.fst)
  exact dimension'.pair ((Primrec.list_map (Primrec.list_range.comp dimension') mark.to₂).pair (blank'.pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp g' (Primrec.nat_add.comp start' (Primrec.const 1))) marker').pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp g' (Primrec.nat_add.comp (Primrec.nat_add.comp q' (Primrec.const 1)) (Primrec.const 1))) marker').pair
    (grid' Primrec.id dimension')))))

theorem fromBits' : Primrec fromBits := machineData'.comp blankRaw'

end P455WriterProgram.Cert
