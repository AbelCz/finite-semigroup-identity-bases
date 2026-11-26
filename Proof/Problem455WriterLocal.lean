import Problem455WriterNorm
import Problem455WriterTileData

namespace P455WriterProgram
open P455EffectiveMachine P455MachineLocal P455MachineCleanup P455MachineTable P455PaddedTiles

def act (m : Raw) (v : Nat) : Option Triple :=
  if 0<v/(g m) then some (normalizedIns m (v/(g m)-1) (v%(g m))) else none

def send (ng sym d : Nat) (i : Triple) := ng*(if i.2.2=d then i.1+1 else 0)+sym

def output (ng sym : Nat) (left right : Bool) : Option Triple → Option Triple → Option Triple → Option Nat
  | none,none,none => some sym
  | some i,none,none => some (send ng sym 2 i)
  | none,none,some i => some (send ng sym 0 i)
  | none,some i,none => if (i.2.2=0 ∧ left=true) ∨ (i.2.2=2 ∧ right=true) then none
                        else some (send ng i.2.1 1 i)
  | _,_,_ => none

def localValue (m : Raw) (l : Option Nat) (c : Nat) (r : Option Nat) :=
  output (g m) (c%(g m)) l.isNone r.isNone (l.bind (act m)) (act m c) (r.bind (act m))

theorem act_spec (M : Ordinary ng nq) (v : Fin (ng*((nq+2)+1))) :
    act (data M) v.val=(action (normalized M).delta (dec (normalized M) v)).map numIns := by
  unfold act action dec
  by_cases h : 0<v.val/ng
  · simp only [data,g,h,if_pos,dif_pos,Option.map_some]
    apply congrArg some
    have pos : 0<ng := by have := M.marker.isLt; omega
    have bound : v.val/ng<(nq+2)+1 := (Nat.div_lt_iff_lt_mul pos).mpr (Nat.mul_comm ng _ ▸ v.isLt)
    exact normalizedIns_spec M ⟨v.val/ng-1,by omega⟩ ⟨v.val%ng,Nat.mod_lt _ pos⟩
  · simp [data,g,h]

theorem opt_act (M : Ordinary ng nq) (v : Option (Fin (ng*((nq+2)+1)))) :
    (v.map Fin.val).bind (act (data M)) = ((v.map (dec (normalized M))).bind (action (normalized M).delta)).map numIns := by
  cases v with
  | none => rfl
  | some c => exact act_spec M c

theorem send_spec (a : Fin ng) (i : Ins (Fin ng) (Fin ns)) (d : Direction) :
    send ng a.val (dirCode d) (numIns i)=(enc ⟨a,sends i d⟩).val := by
  obtain ⟨z,b,e⟩:=i
  cases e <;> cases d <;> simp [send,numIns,sends,enc,headIndex,dirCode]

theorem output_spec (delta : Fin ns → Fin ng → Ins (Fin ng) (Fin ns))
    (l : Option (C ng ns)) (c : C ng ns) (r : Option (C ng ns)) :
    output ng c.sym.val l.isNone r.isNone ((l.bind (action delta)).map numIns)
      ((action delta c).map numIns) ((r.bind (action delta)).map numIns) =
      ((update delta l c r).map enc).map Fin.val := by
  unfold update
  cases e₁ : l.bind (action delta) with
  | none =>
    cases e₂ : action delta c with
    | none =>
      cases e₃ : r.bind (action delta) with
      | none => simp [output,enc,headIndex]
      | some i => exact congrArg some (send_spec c.sym i .left)
    | some i =>
      cases e₃ : r.bind (action delta) with
      | some j => rfl
      | none =>
        have dl : (numIns i).2.2=0 ↔ i.dir=.left := by cases h : i.dir <;> simp [numIns,h,dirCode]
        have dr : (numIns i).2.2=2 ↔ i.dir=.right := by cases h : i.dir <;> simp [numIns,h,dirCode]
        change (if ((numIns i).2.2=0 ∧ l.isNone=true) ∨ ((numIns i).2.2=2 ∧ r.isNone=true) then none else some (send ng i.symbol.val 1 (numIns i))) = _
        by_cases e : (i.dir=.left ∧ l.isNone=true) ∨ (i.dir=.right ∧ r.isNone=true)
        · simp only [dl,dr,e,if_true]; rfl
        · simp only [dl,dr,e,if_false]
          exact congrArg some (send_spec i.symbol i .stay)
  | some i =>
    cases e₂ : action delta c with
    | some j => cases r.bind (action delta) <;> rfl
    | none =>
      cases e₃ : r.bind (action delta) with
      | none => exact congrArg some (send_spec c.sym i .right)
      | some j => rfl

theorem localValue_spec (M : Ordinary ng nq) (l : Option (Fin (ng*((nq+2)+1)))) (c : Fin (ng*((nq+2)+1)))
    (r : Option (Fin (ng*((nq+2)+1)))) :
    localValue (data M) (l.map Fin.val) c.val (r.map Fin.val) = ((compile (normalized M)).next l c r).map Fin.val := by
  unfold localValue
  rw [opt_act,opt_act,act_spec]
  have em {A B : Type} (f : A → B) (o : Option A) : (o.map f).isNone=o.isNone := by cases o <;> rfl
  simpa only [em] using (output_spec (normalized M).delta
    (l.map (dec (normalized M))) (dec (normalized M) c) (r.map (dec (normalized M))))

end P455WriterProgram
