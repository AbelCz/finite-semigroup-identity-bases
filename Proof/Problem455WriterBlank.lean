import Problem455WriterProgram

namespace P455WriterProgram
open P455EffectiveMachine P455MachineLocal P455MachineCleanup P455EffectivePrefix P455EffectiveWriter

theorem indices_ofFn {α : Type} (f : Fin n → α) :
    (Vector.ofFn f).toList = (List.finRange n).map f := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [Vector.toList_ofFn]

def row (M : Ordinary g0 q0) (z : Fin q0) :=
  (List.finRange g0).map (fun a => entryCode g0 (M.delta z a))

theorem rows_spec (M : Ordinary g0 q0) : rowData M = (List.finRange q0).flatMap (row M) := by
  simp only [rowData,quote,indices_ofFn,List.flatMap_map,Function.comp_def,List.map_map]
  rfl

theorem cols (n : Nat) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp); intros; simp

theorem code_write (cmd : Cmd g0) (m a : Fin g0) :
    writtenSymbol (cmdCode cmd) m.val a.val = (write m cmd a).val := by
  cases cmd with
  | right => simp [writtenSymbol,cmdCode,write]
  | left => simp [writtenSymbol,cmdCode,write]
  | putRight v =>
    simp only [writtenSymbol,cmdCode,Nat.add_sub_cancel,write]
    by_cases ea : a=m <;> by_cases ev : v=m <;> simp_all [Fin.ext_iff] <;> omega

theorem code_motion (cmd : Cmd g0) (m a : Fin g0) :
    dir (cmdCode cmd) m.val a.val=dirCode (motion m cmd a) := by
  cases cmd with
  | right => rfl
  | left => by_cases ea : a=m <;> simp_all [dir,cmdCode,motion,dirCode,Fin.ext_iff]
  | putRight v => simp [dir,cmdCode,motion,dirCode]

theorem entry_lift (i : Option (Ins (Fin g0) (Fin q0))) :
    entryCode g0 (i.map liftIns) = entryCode g0 i := by cases i <;> rfl

theorem push_data (M : Ordinary g0 q0) (c : Cmd g0) :
    pushRaw (cmdCode c) (data M)=data (push M c) := by
  have low (s : Fin q0) : row (push M c) s.castSucc=row M s := by
    unfold row; apply List.map_congr_left
    intro a _
    change entryCode _ ((push M c).delta (P455EffectivePrefix.old s) a)=_
    rw [old_ins,entry_lift]
  have top : row (push M c) (Fin.last q0)=
      (List.range g0).map (fun a => instr g0 M.start.val (writtenSymbol (cmdCode c) M.marker.val a)
        (dir (cmdCode c) M.marker.val a)) := by
    unfold row
    rw [cols]; simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left; intro a _
    change entryCode _ ((push M c).delta (head q0) a)=_
    rw [head_ins,code_write,code_motion]; rfl
  have content : rowData (push M c)=rowData M++
      (List.range g0).map (fun a => instr g0 M.start.val (writtenSymbol (cmdCode c) M.marker.val a)
        (dir (cmdCode c) M.marker.val a)) := by
    rw [rows_spec,rows_spec,List.finRange_succ_last]
    simp [List.flatMap_append,List.flatMap_map,Function.comp_def,low,top]
  exact congrArg (fun xs => (g0,q0+1,M.marker.val,M.blank.val,q0,xs)) content.symm

theorem install_data (M : Ordinary g0 q0) (cs : List (Cmd g0)) :
    (cs.map cmdCode).foldr pushRaw (data M)=data (install M cs).2 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons,List.foldr_cons,ih,push_data,install]

theorem blank_self (M : Ordinary g0 q0) (A : Alphabet M) :
    blankRaw (selfBits M A)=data (diagonalInput M A).2 := by
  dsimp only [blankRaw]
  rw [raw_self]
  have eq := read_self M A
  rw [eq]
  change (script (A.bit false).val (A.bit true).val (selfBits M A)).foldr pushRaw (data M)=_
  rw [script_spec,install_data]
  rfl

end P455WriterProgram
