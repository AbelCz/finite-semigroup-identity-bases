import Problem455EffectiveMachineDiagonal




namespace P455MachineAlphabet
open P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine

def embed (k : Nat) (a : Fin g) : Fin (g+k) := ⟨a.val,by have := a.isLt; omega⟩

theorem embed_inj (k : Nat) (a b : Fin g) : embed k a=embed k b ↔ a=b := by
  constructor
  · intro e; exact Fin.ext (congrArg (@Fin.val (g+k)) e)
  · intro e; rw [e]

def liftIns (k : Nat) (i : Ins (Fin g) (Fin q)) : Ins (Fin (g+k)) (Fin q) :=
  ⟨i.state,embed k i.symbol,i.dir⟩

def enlarged (M : Ordinary g q) (k : Nat) : Ordinary (g+k) q where
  marker := embed k M.marker
  blank := embed k M.blank
  blank_ne := fun h => M.blank_ne ((embed_inj ..).mp h)
  start := M.start
  delta := fun s a => if h : a.val<g then (M.delta s ⟨a,h⟩).map (liftIns k) else none
  keeps := by
    intro s a ins valid
    split at valid
    next h =>
      cases d : M.delta s ⟨a,h⟩ with
      | none => simp [d] at valid
      | some i =>
        obtain rfl : liftIns k i=ins := by simpa [d] using valid
        have old := M.keeps s ⟨a,h⟩ i d
        change embed k i.symbol=embed k M.marker ↔ a=embed k M.marker
        rw [embed_inj,old]
        exact ⟨fun e => Fin.ext (congrArg (@Fin.val g) e),fun e => Fin.ext (congrArg (@Fin.val (g+k)) e)⟩
    next => contradiction
  leftSafe := by
    intro s ins valid
    simp only [embed,dif_pos M.marker.isLt] at valid
    cases d : M.delta s M.marker with
    | none => simp [d] at valid
    | some i =>
      obtain rfl : liftIns k i=ins := by simpa [d] using valid
      exact M.leftSafe s i d

def alphabet (M : Ordinary g q) (A : Alphabet M) (k : Nat) : Alphabet (enlarged M k) where
  bit b := embed k (A.bit b)
  away _ e := A.away _ ((embed_inj ..).mp e)
  ink _ e := A.ink _ ((embed_inj ..).mp e)
  distinct e := A.distinct ((embed_inj ..).mp e)

def configuration (c : Config g q) (k : Nat) : Config (g+k) q :=
  ⟨fun x => embed k (c.tape x),c.pos,c.state⟩

theorem input_config (M : Ordinary g q) (A : Alphabet M) (w : List Bool) (k : Nat) :
    inputConfig (enlarged M k) (alphabet M A k) w=configuration (inputConfig M A w) k := by
  congr 1
  apply congrArg (fun (f : Nat→Fin (g+k)) => Config.mk f 0 M.start)
  funext x
  cases x with
  | zero => rfl
  | succ j =>
    cases e : w[j]? <;> simp [configuration,inputConfig,inputTape,e,alphabet,enlarged,embed]

theorem instruction_eq (M : Ordinary g q) (c : Config g q) (k : Nat) :
    instruction (enlarged M k) (configuration c k)=(instruction M c).map (liftIns k) := by
  simp [instruction,enlarged,configuration,embed,(c.tape c.pos).isLt]

theorem once_eq (M : Ordinary g q) (c : Config g q) (k : Nat) :
    once (enlarged M k) (configuration c k)=configuration (once M c) k := by
  unfold once
  rw [instruction_eq]
  cases d : instruction M c with
  | none => rfl
  | some i =>
    simp only [Option.map_some]
    have tape : writeAt (configuration c k).tape c.pos (embed k i.symbol)=
        fun j => embed k (writeAt c.tape c.pos i.symbol j) := by
      funext j; by_cases eq : j=c.pos <;> simp [configuration,writeAt,eq]
    exact congrArg (fun f => Config.mk f (dest i.dir c.pos) i.state) tape

theorem run_eq (M : Ordinary g q) (A : Alphabet M) (w : List Bool) (k t : Nat) :
    follow (enlarged M k) (inputConfig (enlarged M k) (alphabet M A k) w) t=
      configuration (follow M (inputConfig M A w) t) k := by
  induction t with
  | zero => exact input_config M A w k
  | succ t ih => simpa only [follow,ih] using once_eq M (follow M (inputConfig M A w) t) k

end P455MachineAlphabet
