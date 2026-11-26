import Problem455WriterTileRec
import Problem455LiteralMovePrim

namespace P455WriterProfiles
open Problem455.Slots P455WriterTiles P455BinaryEquality
abbrev W := List Nat
abbrev Tags := List (List Bool)
abbrev Candidate := Nat × Nat × List Bool × Bool

variable {A : Type} [Primcodable A]

theorem pairRec {a b : A → Nat} {v : A → Bool} (ha : Primrec a) (hb : Primrec b) (hv : Primrec v) :
    Primrec fun x => pair (a x) (b x) (v x) := by
  let cons := @Primrec.list_cons Nat _
  exact Primrec.ite (Primrec.eq.comp hv (.const true))
    (cons.comp hb (cons.comp ha (.const []))) (cons.comp ha (cons.comp hb (.const [])))

theorem profileRec {a b : A → Nat} {t : A → List Bool} {v : A → Bool}
    (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) (hv : Primrec v) :
    Primrec fun x => profile (a x) (b x) (t x) (v x) := by
  let cons := @Primrec.list_cons Nat _
  have ab := cons.comp ha (cons.comp hb (.const []))
  have fixed := cons.comp ha (cons.comp ha (cons.comp hb (cons.comp ha (cons.comp hb (cons.comp hb (.const []))))))
  have reps := Primrec.list_flatten.comp (replicateRec (.const 5) (cons.comp ha (cons.comp hb ab)))
  have mid : Primrec (fun x => (t x).flatMap (pair (a x) (b x))) := Primrec.list_flatMap ht (Primrec₂.mk (pairRec (A := A × Bool) (ha.comp Primrec.fst) (hb.comp Primrec.fst) Primrec.snd))
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp fixed reps) mid) ab)
    (Primrec.list_append.comp (pairRec ha hb hv) ab)

def candidates (w : W) (ts : Tags) : List Candidate :=
  choices w (choices w (choices ts [false,true]))

def test (r : Nat) (w : W) (c : Candidate) :=
  decide (c.1 ≠ c.2.1 ∧ c.2.2.1.length+16=r ∧ w=profile c.1 c.2.1 c.2.2.1 c.2.2.2)

def isProfile (r : Nat) (ts : Tags) (w : W) := (candidates w ts).any (test r w)

theorem correct {n} (M : P455PaddedTiles.MachineTable n) (r w) :
    isProfile r (P455Enum.tags M) w=true ↔ IsProfile r (P455PaddedTiles.allowed M) w := by
  simp only [isProfile,candidates,choices,List.any_eq_true,List.mem_flatMap,List.mem_map,test,decide_eq_true_eq]
  constructor
  · rintro ⟨_,⟨a,_,_,⟨b,_,_,⟨t,ht,bit,_,rfl⟩,rfl⟩,rfl⟩,hne,hlen,hw⟩
    exact ⟨a,b,t,bit,hne,hlen,P455Enum.mem_tags.mp ht,hw⟩
  · rintro ⟨a,b,t,bit,hne,hlen,ht,hw⟩
    have names : a∈w ∧ b∈w := by rw [hw]; exact P455Enum.profile_names
    refine ⟨(a,b,t,bit),⟨a,names.1,_,⟨b,names.2,_,⟨t,P455Enum.mem_tags.mpr ht,bit,?_,rfl⟩,rfl⟩,rfl⟩,hne,hlen,hw⟩
    cases bit <;> simp

theorem isProfileRec {r : A → Nat} {ts : A → Tags} {w : A → W} (hr : Primrec r) (ht : Primrec ts)
    (hw : Primrec w) : Primrec fun a => isProfile (r a) (ts a) (w a) := by
  apply P455GraphPrim.anyB (choicesRec hw (choicesRec hw (choicesRec ht (.const [false,true]))))
  apply Primrec₂.mk
  have p := Primrec.snd (α := A) (β := Candidate)
  have x := Primrec.fst.comp p
  have y := Primrec.fst.comp (Primrec.snd.comp p)
  have suffix := Primrec.snd.comp (Primrec.snd.comp p)
  have t := Primrec.fst.comp suffix
  have b := Primrec.snd.comp suffix
  exact PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp x y)) <|
    PrimrecPred.and (Primrec.eq.comp (Primrec.nat_add.comp (Primrec.list_length.comp t) (.const 16)) (hr.comp Primrec.fst))
      (Primrec.eq.comp (hw.comp Primrec.fst) (profileRec x y t b))

end P455WriterProfiles
