import Problem455FoldMachine

namespace P455FoldInput
open Turing P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine
open P455FoldWorld P455FoldMachine

structure Wire (Γ : Type) [Inhabited Γ] where
  first : Γ
  second : Γ
  letter : Bool→Γ
  ink : ∀ b, letter b≠default
  distinct : letter false≠letter true
  flag : Γ→Bool
  flags : flag first=true ∧ flag second=false ∧ flag default=false ∧ ∀ b, flag (letter b)=false

variable [Inhabited Γ]

def stream (C : Wire Γ) (x : List Bool) := C.first::C.second::x.map C.letter
def layout (C : Wire Γ) (x : List Bool) : Int→Γ
  | .negSucc _ => default
  | .ofNat 0 => C.first
  | .ofNat 1 => C.second
  | .ofNat (i+2) => (x[i]?).elim default C.letter

theorem nth_stream (C : Wire Γ) (x : List Bool) (i : Int) :
    (Tape.mk₁ (stream C x)).nth i=layout C x i := by
  cases i with
  | negSucc n =>
    change (ListBlank.mk ([] : List Γ)).nth n=default
    simp [ListBlank.nth_mk]
  | ofNat n =>
    change (Tape.mk' _ (ListBlank.mk (stream C x))).nth (n : Int)=_
    rw [Tape.mk'_nth_nat,ListBlank.nth_mk,List.getI_eq_iget_getElem?]
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        simp only [stream,List.getElem?_cons_succ,List.getElem?_map,layout]
        cases x[n]? <;> rfl

theorem marked (C : Wire Γ) (x : List Bool) (p : Int) :
    C.flag (layout C x p)=true ↔ p=0 := by
  obtain ⟨one,two,b,all⟩ := C.flags
  cases p with
  | negSucc n => simp [layout,b]
  | ofNat n =>
    cases n with
    | zero => simp [layout,one]
    | succ n =>
      cases n with
      | zero => simp [layout,two]
      | succ n => cases e : x[n]? <;> simp [layout,e,b,all] <;> omega

def initWorld [Inhabited Q] (C : Wire Γ) (x : List Bool) : World Γ Q :=
  ⟨layout C x,false,0,default⟩

theorem describes_init [Inhabited Q] (C : Wire Γ) (x : List Bool) :
    Describes (initWorld (Q:=Q) C x) (TM0.init (stream C x)) := by
  refine ⟨rfl,fun i => ?_⟩
  simpa [TM0.init,initWorld,pos,coord] using nth_stream C x i

variable [Inhabited Q]
variable (aCode : Sym Γ ≃ Fin g) (sCode : Ctrl Γ Q ≃ Fin r)

def inputAlpha (M : Table Γ Q) (C : Wire Γ) :
    Alphabet (machine aCode sCode M default (C.first,C.second)) where
  bit b := aCode (some (default,C.letter b))
  away _ eq := Option.noConfusion (aCode.injective eq)
  ink b eq := C.ink b (congrArg Prod.snd (Option.some.inj (aCode.injective eq)))
  distinct eq := C.distinct (congrArg Prod.snd (Option.some.inj (aCode.injective eq)))

theorem cell_layout (M : Table Γ Q) (C : Wire Γ) (x : List Bool) :
    (fun j => aCode (cell (layout C x) j))=
      inputTape _ (inputAlpha aCode sCode M C) x := by
  funext j; cases j with
  | zero => rfl
  | succ j =>
    change aCode (some (packed (layout C x) (j+1)))=(x[j]?).elim (aCode (some (default,default)))
        (fun b => aCode (some (default,C.letter b)))
    have left : coord false (j+1)=Int.negSucc j := by simp [coord]; omega
    have right : coord true (j+1)=Int.ofNat (j+2) := by simp [coord]; omega
    simp only [packed,left,right,layout]
    cases x[j]? <;> rfl

theorem initial (M : Table Γ Q) (C : Wire Γ) (x : List Bool) :
    physical aCode sCode (initWorld (Q:=Q) C x)=
      inputConfig _ (inputAlpha aCode sCode M C) x := by
  change (⟨_,0,sCode (default,false,packed (layout C x) 0)⟩ : Config g r)=
    ⟨_,0,sCode (default,false,(C.first,C.second))⟩
  dsimp only [initWorld]
  rw [cell_layout aCode sCode M C x]
  rfl

end P455FoldInput
