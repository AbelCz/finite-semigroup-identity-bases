import Problem455EffectiveMachinePrefix
import Problem455Decision

/- The finite input script, its tape contents, and the blank-input reduction
from the unconditional diagonal problem on ordinary binary-input machines. -/
namespace P455EffectiveWriter
open P455EffectiveMachine P455EffectivePrefix P455MachineLocal P455MachineCleanup P455MachineTable

def dataEnv (M : Ordinary g q) (A : Alphabet M) (word : List Bool) (p : Nat) : Env g :=
  ⟨inputTape M A word,p⟩

theorem input_fresh (M : Ordinary g q) (A : Alphabet M) (w : List Bool) :
    inputTape M A w (w.length+1)=M.blank := by simp [inputTape,List.getElem?_eq_none (Nat.le_refl w.length)]

theorem input_away (M : Ordinary g q) (A : Alphabet M) (w : List Bool) (k : Nat) :
    inputTape M A w (k+1)≠M.marker := by
  change (w[k]?).elim M.blank A.bit ≠ M.marker
  cases w[k]? with
  | none => exact M.blank_ne
  | some b => exact A.away b

theorem tape_snoc (M : Ordinary g q) (A : Alphabet M) (w : List Bool) (b : Bool) :
    writeAt (inputTape M A w) (w.length+1) (A.bit b)=inputTape M A (w++[b]) := by
  funext i
  cases i with
  | zero => simp [writeAt,inputTape]
  | succ j =>
    by_cases lt : j<w.length
    · have ne : j≠w.length := by omega
      simp [writeAt,ne,inputTape,List.getElem?_append_left lt]
    · have le : w.length≤j := by omega
      by_cases eq : j=w.length
      · subst j
        simp [writeAt,inputTape,List.getElem?_append_right]
      · have lt' : w.length<j := by omega
        have dead : w.length+1≤j := by omega
        have all : (w++[b]).length≤j := by simpa using dead
        simp [writeAt,eq,inputTape,List.getElem?_eq_none le,List.getElem?_eq_none all]

theorem push_bit (M : Ordinary g q) (A : Alphabet M) (p) (b) :
    effect M.marker (.putRight (A.bit b)) (dataEnv M A p (p.length+1))=
      dataEnv M A (p++[b]) ((p++[b]).length+1) := by
  simp [effect,dataEnv,write,motion,dest,input_fresh,M.blank_ne,A.away,tape_snoc]

theorem put_many (M : Ordinary g q) (A : Alphabet M) (w p : List Bool) :
    perform M.marker (w.map (fun b => Cmd.putRight (A.bit b))) (dataEnv M A p (p.length+1))=
    dataEnv M A (p++w) ((p++w).length+1) := by
  induction w generalizing p with
  | nil => simp [perform]
  | cons b ws ih =>
    change perform M.marker (ws.map (fun b => Cmd.putRight (A.bit b)))
      (effect M.marker (.putRight (A.bit b)) (dataEnv M A p (p.length+1))) = _
    rw [push_bit,ih]
    simp

theorem rewind (M : Ordinary g q) (A : Alphabet M) (w : List Bool) (k n : Nat) :
    perform M.marker (List.replicate n (.left : Cmd g)) (dataEnv M A w (k+n))=dataEnv M A w k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change perform M.marker (List.replicate n .left)
      (effect M.marker .left (dataEnv M A w (k+n+1))) = _
    have one : effect M.marker .left (dataEnv M A w (k+n+1))=dataEnv M A w (k+n) := by
      simp [effect,dataEnv,write,motion,dest,input_away,write_same]
    rw [one,ih]

def writer (M : Ordinary g q) (A : Alphabet M) (w : List Bool) : List (Cmd g) :=
  Cmd.right :: ((w.map (fun b => Cmd.putRight (A.bit b))) ++ List.replicate (w.length+1) .left)

theorem written (M : Ordinary g q) (A : Alphabet M) (w : List Bool) :
    perform M.marker (writer M A w) (dataEnv M A [] 0)=dataEnv M A w 0 := by
  have start : effect M.marker .right (dataEnv M A [] 0)=dataEnv M A [] 1 := by
    simp [effect,dataEnv,motion,write,dest,write_same]
  simp only [writer,perform,List.foldl_cons,List.foldl_append,start]
  change perform M.marker (List.replicate (w.length+1) .left)
    (perform M.marker (w.map (fun b => Cmd.putRight (A.bit b))) (dataEnv M A [] (([] : List Bool).length+1)))=_
  rw [put_many]
  simp only [List.nil_append]
  simpa using rewind M A w 0 (w.length+1)

def blankize (M : Ordinary g q) (A : Alphabet M) (w : List Bool) := install M (writer M A w)

theorem blankize_iff (M : Ordinary g q) (A : Alphabet M) (w : List Bool) :
    (∃ t, stopped (blankize M A w).2 t) ↔ HALT M (inputConfig M A w) := by
  let e := dataEnv M A [] 0
  let cs := writer M A w
  let N := (install M cs).2
  have initial : config₀ N = e.start N := by
    have m : N.marker=M.marker := installed_marker M cs
    have b : N.blank=M.blank := installed_blank M cs
    have f : (fun j => if j=0 then N.marker else N.blank) = inputTape M A [] := by
      funext j; cases j <;> simp [inputTape,m,b]
    simp [config₀,e,Env.start,dataEnv,f]
  exact (blank_halts N).symm.trans (initial ▸ (install_iff M cs e).trans (by
    change HALT M ((perform M.marker (writer M A w) (dataEnv M A [] 0)).start M) ↔ _
    rw [written]; rfl))

def diagonalInput (P : Ordinary g q) (B : Alphabet P) := blankize P B (selfBits P B)

theorem diagonal_input_iff (P : Ordinary g q) (B : Alphabet P) :
    (∃ t, stopped (diagonalInput P B).2 t) ↔ SelfHalt P B := blankize_iff P B _

theorem diagonal_basis (P : Ordinary g q) (B : Alphabet P) :
    P455Global.HasBasis (P455MachineReduction.model (diagonalInput P B).2) ↔ ¬SelfHalt P B :=
  (P455Decision.ordinary_equivalence _).trans (not_congr (diagonal_input_iff P B))

end P455EffectiveWriter
