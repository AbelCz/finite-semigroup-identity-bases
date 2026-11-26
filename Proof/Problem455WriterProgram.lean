import Problem455MachineParseSelf





namespace P455WriterProgram
open P455EffectiveMachine P455MachineLocal P455MachineCleanup P455EffectivePrefix P455EffectiveWriter

abbrev Raw := Nat × Nat × Nat × Nat × Nat × List Nat
abbrev g (m : Raw) := m.1
abbrev q (m : Raw) := m.2.1
abbrev marker (m : Raw) := m.2.2.1
abbrev blank (m : Raw) := m.2.2.2.1
abbrev start (m : Raw) := m.2.2.2.2.1
abbrev entries (m : Raw) := m.2.2.2.2.2

def incHead (l : List Nat) := (l.getD 0 0 + 1)::l.tail
def readBits (bits : List Bool) : List Nat :=
  bits.foldr (fun b l => bif b then incHead l else 0::l) []

theorem read_one (n : Nat) (b : List Bool) : readBits (unary n ++ b)=n::readBits b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change incHead (readBits (unary n ++ b)) = _
    rw [ih]; rfl

theorem read_many (nums : List Nat) (b : List Bool) :
    readBits (nums.flatMap unary ++ b)=nums++readBits b := by
  induction nums with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.append_assoc,read_one,ih,List.cons_append]

def rowData (M : Ordinary g0 q0) := (quote M).rows.toList.flatMap (fun row => row.toList.map (entryCode g0))
def data (M : Ordinary g0 q0) : Raw := (g0,q0,M.marker.val,M.blank.val,M.start.val,rowData M)

theorem read_self (M : Ordinary g0 q0) (A : Alphabet M) :
    readBits (selfBits M A) =
      (A.bit false).val::(A.bit true).val::g0::q0::M.marker.val::M.blank.val::M.start.val::rowData M := by
  have hn : readBits []=[] := rfl
  have h := read_many (quote M).numerals []
  simpa [selfBits,List.append_assoc,read_one,Code.bits,Code.numerals,quote,rowData,hn] using
    congrArg (fun l => (A.bit false).val::(A.bit true).val::l) h

def raw (w : List Nat) : Raw := (w.getD 2 0,w.getD 3 0,w.getD 4 0,w.getD 5 0,w.getD 6 0,w.drop 7)

theorem raw_self (M : Ordinary g0 q0) (A : Alphabet M) :
    raw (readBits (selfBits M A))=data M := by rw [read_self]; rfl

/-- 0 means right, 1 means left, and 2+a writes a then moves right. -/
def script (a b : Nat) (w : List Bool) :=
  0 :: (w.map (fun x => (bif x then b else a)+2) ++ List.replicate (w.length+1) 1)

def cmdCode : Cmd g0 → Nat
  | .right => 0
  | .left => 1
  | .putRight v => v.val+2

theorem script_spec (M : Ordinary g0 q0) (A : Alphabet M) (w : List Bool) :
    script (A.bit false).val (A.bit true).val w = (writer M A w).map cmdCode := by
  simp only [script,writer,List.map_cons,List.map_append,List.map_replicate,List.map_map,cmdCode]
  congr 2
  apply List.map_congr_left
  intro b _; cases b <;> rfl

def writtenSymbol (c m a : Nat) := if c<2 ∨ a=m ∨ c-2=m then a else c-2
def dir (c m a : Nat) := if c=1 then (if a=m then 1 else 0) else 2
def instr (g z a d : Nat) := 1+3*(g*z+a)+d

def pushRaw (c : Nat) (m : Raw) : Raw :=
  (g m,q m+1,marker m,blank m,q m,
   entries m ++ (List.range (g m)).map fun a =>
     instr (g m) (start m) (writtenSymbol c (marker m) a) (dir c (marker m) a))

def blankRaw (bits : List Bool) :=
  let l := readBits bits
  (script (l.getD 0 0) (l.getD 1 0) bits).foldr pushRaw (raw l)

end P455WriterProgram
