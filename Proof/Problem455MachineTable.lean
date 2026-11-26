import Problem455MachineLocal
import Problem455PaddedReadback



namespace P455MachineTable
open P455MachineLocal P455PaddedTiles

structure TM (g q : Nat) where
  marker : Fin g
  blank : Fin g
  blank_ne : blank≠marker
  start : Fin q
  accept : Fin q
  distinct : start≠accept
  delta : Fin q→Fin g→Ins (Fin g) (Fin q)
  keeps : ∀ z a,(delta z a).symbol=marker ↔ a=marker
  leftSafe : ∀ z,(delta z marker).dir≠.left
  stationary : delta accept marker=⟨accept,marker,.stay⟩

abbrev C (g q : Nat) := Cell (Fin g) (Fin q)
def headIndex (p : Option (Fin q)) : Nat := match p with | none => 0 | some x => x.val+1

def enc (c : C g q) : Fin (g*(q+1)) :=
  ⟨g*headIndex c.head+c.sym.val,by
    have v := c.sym.isLt
    have z : headIndex c.head ≤ q := by cases hh : c.head with
      | none => simp [headIndex]
      | some s => simp [headIndex]; have := s.isLt; omega
    have m := Nat.mul_le_mul_left g z
    rw [Nat.mul_add,Nat.mul_one]; omega⟩

def dec (M : TM g q) (x : Fin (g*(q+1))) : C g q :=
  let h := x.val/g
  let symbol := x.val%g
  let head := if e : 0<h then some (⟨h-1,by
    have gr := M.marker.isLt
    have pos : 0<g := by omega
    have div := (Nat.div_lt_iff_lt_mul pos).mpr (calc x.val < g*(q+1) := x.isLt
                                                     _ = _ := Nat.mul_comm ..)
    dsimp [h] at *; omega⟩ : Fin q) else none
  ⟨⟨symbol,Nat.mod_lt _ (by have := M.marker.isLt; omega)⟩,head⟩

theorem dec_enc (M : TM g q) (c : C g q) : dec M (enc c)=c := by
  obtain ⟨s,h⟩ := c
  have gpos : 0<g := by have := s.isLt; omega
  cases h with
  | none => simp [dec,enc,headIndex,Nat.div_eq_of_lt s.isLt,Nat.mod_eq_of_lt s.isLt]
  | some p =>
    simp [dec,enc,headIndex,Nat.mul_add_div gpos,Nat.div_eq_of_lt s.isLt,Nat.mul_add_mod,Nat.mod_eq_of_lt s.isLt]

theorem enc_inj (M : TM g q) {a b : C g q} (e : enc a=enc b) : a=b := by
  simpa [dec_enc] using congrArg (dec M) e

def compile (M : TM g q) : MachineTable (g*(q+1)) where
  marker := fun v=>decide ((dec M v).sym=M.marker)
  initial := fun left=>if left then enc ⟨M.marker,some M.start⟩ else enc ⟨M.blank,none⟩
  accept := enc ⟨M.marker,some M.accept⟩
  distinct := by
    intro eq
    have h := congrArg Cell.head (enc_inj M eq)
    exact M.distinct (Option.some.inj h)
  next := fun l c r => (update M.delta (l.map (dec M)) (dec M c) (r.map (dec M))).map enc

structure Config (g q : Nat) where
  tape : Nat→Fin g
  pos : Nat
  state : Fin q

def init (M : TM g q) : Config g q := ⟨(fun i=>if i=0 then M.marker else M.blank),0,M.start⟩

def step (M : TM g q) (c : Config g q) : Config g q :=
  let ins := M.delta c.state (c.tape c.pos)
  ⟨writeAt c.tape c.pos ins.symbol,dest ins.dir c.pos,ins.state⟩

def run (M : TM g q) : Nat→Config g q
  | 0 => init M
  | t+1 => step M (run M t)

def row (M : TM g q) (t x : Nat) := enc (atCell (run M t).tape (run M t).pos (run M t).state x)

theorem marker_iff (M : TM g q) (t x : Nat) : (run M t).tape x=M.marker ↔ x=0 := by
  induction t with
  | zero => by_cases e : x=0 <;> simp [run,init,e,M.blank_ne]
  | succ t ih =>
    change writeAt _ _ _ x=M.marker ↔ x=0
    by_cases e : x=(run M t).pos
    · rw [writeAt,if_pos e,M.keeps,←e]; exact ih
    · simpa [writeAt,e] using ih

theorem head_bound (M : TM g q) (t : Nat) : (run M t).pos ≤ t := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    change dest (_ : Ins (Fin g) (Fin q)).dir (run M t).pos≤t+1
    cases d : (M.delta (run M t).state ((run M t).tape (run M t).pos)).dir <;>
      simp [dest] <;> omega

theorem physical_safe {t w : Nat} (M : TM g q) (wide : t+1<w) :
    ¬ exits (M.delta (run M t).state ((run M t).tape (run M t).pos)).dir w (run M t).pos := by
  intro bad
  rcases bad with ⟨left,at0⟩|⟨_,edge⟩
  · rw [at0,(marker_iff M t 0).mpr rfl] at left
    exact M.leftSafe _ left
  · have := head_bound M t; omega

theorem left_dec (M : TM g q) (t x : Nat) :
    (leftAt (row M t) x).map (dec M)=leftOf (atCell (run M t).tape (run M t).pos (run M t).state) x := by
  by_cases e : x=0 <;> simp [leftAt,leftOf,e,row,dec_enc]

theorem right_dec (M : TM g q) (t x w : Nat) :
    (rightAt (row M t) w x).map (dec M)=rightOf (atCell (run M t).tape (run M t).pos (run M t).state) w x := by
  by_cases e : x+1=w <;> simp [rightAt,rightOf,e,row,dec_enc]

theorem local_value (M : TM g q) (t w x : Nat) (head : (run M t).pos<w)
    (safe : ¬exits (M.delta (run M t).state ((run M t).tape (run M t).pos)).dir w (run M t).pos)
    (hx : x<w) :
    (compile M).next (leftAt (row M t) x) (row M t x) (rightAt (row M t) w x)=some (row M (t+1) x) := by
  change (update M.delta _ (dec M (enc _)) _).map enc=_
  rw [left_dec,right_dec,dec_enc,local_step _ _ _ _ _ head safe _ hx]
  rfl

end P455MachineTable
