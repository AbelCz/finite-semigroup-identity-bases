import Problem455WriterMachineData

namespace P455WriterProgram
open P455EffectiveMachine P455MachineLocal P455MachineCleanup P455MachineTable

def fromCodeBits (bits : List Bool) := machineData (raw (0::0::readBits bits))

theorem nums_code (C : Code ng nq) : readBits C.bits=C.numerals := by
  have h := read_many C.numerals []
  have he : readBits []=[] := rfl
  simpa [Code.bits,he] using h

theorem quote_machine (C : Code ng nq) (safe : C.Safe) : quote (C.machine safe)=C := by
  cases C with
  | mk m b s r =>
    unfold quote
    apply congrArg (fun rows => Code.mk m b s rows)
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [quote,Code.machine,Code.read,Vector.get]

theorem fromCodeBits_spec (C : Code ng nq) (safe : C.Safe) :
    P455WriterTiles.Models (fromCodeBits C.bits) (compile (normalized (C.machine safe))) := by
  have e : raw (0::0::readBits C.bits)=data (C.machine safe) := by
    rw [nums_code]; unfold data rowData; rw [quote_machine]; rfl
  unfold fromCodeBits; rw [e]; exact machineData_models _

end P455WriterProgram
