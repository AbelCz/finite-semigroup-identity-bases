import Problem455EffectiveMachineRelabel

/- A single concrete writer suffices for every numerical-table decider,
without any requirement tying their work alphabets or bit conventions. -/
namespace P455RelabeledChain
open P455MachineLocal P455MachineCleanup P455MachineTable P455EffectiveMachine
open P455EffectiveChain P455EffectiveRelabel

def writerEmb (W : Ordinary g q) (O : Alphabet W) (h : Nat) : Emb g (4+g+h) :=
  common W O (base:=4) (by decide) (by omega)

def readerEmb (g : Nat) (D : Ordinary h r) (B : Alphabet D) : Emb h (4+g+h) :=
  common D B (base:=4+g) (by omega) (by omega)

theorem marker_agrees (W : Ordinary g q) (O : Alphabet W) (D : Ordinary h r) (B : Alphabet D) :
    (expand W (writerEmb W O h)).marker=(expand D (readerEmb g D B)).marker := by
  apply Fin.ext
  exact (mark_number W O 4).trans (mark_number D B (4+g)).symm

theorem tapes_agree (W : Ordinary g q) (O : Alphabet W) (D : Ordinary h r) (B : Alphabet D) (w : List Bool) :
    (fun j => (writerEmb W O h).enc (inputTape W O w j))=
      inputTape (expand D (readerEmb g D B)) (alpha D B (readerEmb g D B)) w := by
  funext j; rw [input_tape]; apply Fin.ext
  cases j with
  | zero => exact (mark_number W O 4).trans (mark_number D B (4+g)).symm
  | succ j =>
    cases eq : w[j]? with
    | none => simpa only [inputTape,eq,Option.elim_none] using
        (blank_number W O 4).trans (blank_number D B (4+g)).symm
    | some b => simpa only [inputTape,eq,Option.elim_some] using
        (bit_number W O 4 b).trans (bit_number D B (4+g) b).symm

def combined (W : Ordinary g q) (O : Alphabet W) (D : Ordinary h r) (B : Alphabet D) :
    Ordinary (4+g+h) (q+r) :=
  chain (expand W (writerEmb W O h)) (expand D (readerEmb g D B)) (marker_agrees W O D B)

def inputs (W : Ordinary g q) (A O : Alphabet W) (D : Ordinary h r) (B : Alphabet D) :
    Alphabet (combined W O D B) :=
  P455EffectiveChain.liftAlphabet _ _ _ (alpha W A (writerEmb W O h))

theorem expands_delivery (W : Ordinary g q) (A O : Alphabet W) (D : Ordinary h r) (B : Alphabet D) {x y}
    (writing : Delivers W A x W O y) :
    Delivers (expand W (writerEmb W O h)) (alpha W A (writerEmb W O h)) x
      (expand D (readerEmb g D B)) (alpha D B (readerEmb g D B)) y := by
  obtain ⟨t,stopped,pos,tape⟩ := writing
  refine ⟨t,?_⟩
  simp only [exp_run]
  constructor
  · rw [exp_instruction,stopped]; rfl
  · refine ⟨pos,?_⟩
    change (fun j => (writerEmb W O h).enc ((follow W (inputConfig W A x) t).tape j))=_
    rw [tape]; exact tapes_agree W O D B y

/-- Physical composition on one one-sided tape. The writer may use two
different bit alphabets for input and output. The reader's original
alphabet and final-state convention are unrestricted. The fresh common
alphabet and all transition tables are computed from the two programs. -/
theorem answers_combined (W : Ordinary g q) (A O : Alphabet W) (D : Ordinary h r)
    (B : Alphabet D) (ans : Fin r→Bool) {x y b}
    (writing : Delivers W A x W O y) (reading : Answers D B ans y b) :
    Answers (combined W O D B) (inputs W A O D B) (out q ans) x b :=
  answers_chain _ _ (marker_agrees W O D B) _ _ ans
    (expands_delivery W A O D B writing) (exp_answers D B (readerEmb g D B) reading)

end P455RelabeledChain
