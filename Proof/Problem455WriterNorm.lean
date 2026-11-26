import Problem455WriterBlank

namespace P455WriterProgram
open P455EffectiveMachine P455MachineLocal P455MachineCleanup

theorem flat_lookup {A B : Type} (f : A → List B) (k : Nat) (len : ∀ x, (f x).length = k)
    (xs : List A) (i j : Nat) (hi : i < xs.length) (hj : j < k) :
    (xs.flatMap f)[i*k+j]? = (f xs[i])[j]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.flatMap_cons,Nat.zero_mul,Nat.zero_add,List.getElem_cons_zero]
              exact List.getElem?_append_left (by simpa [len] using hj)
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      simp only [List.flatMap_cons,Nat.succ_mul,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [len]; omega),len]
      rw [show i*k+k+j-k=i*k+j by omega]; exact ih i hi'

theorem stored (M : Ordinary ng nq) (z : Fin nq) (a : Fin ng) :
    (entries (data M)).getD (z.val*ng+a.val) 0=entryCode ng (M.delta z a) := by
  change (rowData M).getD _ 0=_
  rw [List.getD_eq_getElem?_getD,rows_spec,flat_lookup (row M) ng (by intro; simp [row])
       _ _ _ (by simp) a.isLt]
  simp only [row,List.getElem_finRange,List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

abbrev Triple := Nat × Nat × Nat
def numIns (i : Ins (Fin ng) (Fin nq)) : Triple := (i.state.val,i.symbol.val,dirCode i.dir)
def unpack (ng k : Nat) : Triple := (((k-1)/3)/ng, ((k-1)/3)%ng, (k-1)%3)

theorem unpack_some (i : Ins (Fin ng) (Fin nq)) : unpack ng (entryCode ng (some i))=numIns i := by
  have hp : 0<ng := by have := i.symbol.isLt; omega
  have hd : dirCode i.dir<3 := by cases i.dir <;> decide
  have hp₁ : (1+3*(ng*i.state.val+i.symbol.val)+dirCode i.dir)-1=3*(ng*i.state.val+i.symbol.val)+dirCode i.dir := by omega
  simp [unpack,entryCode,hp₁,Nat.mul_add_div (by decide : 0<3),Nat.div_eq_of_lt hd,Nat.mul_add_mod,
    Nat.mod_eq_of_lt hd,Nat.mul_add_div hp,Nat.div_eq_of_lt i.symbol.isLt,Nat.mod_eq_of_lt i.symbol.isLt,numIns]

def normalizedIns (m : Raw) (z a : Nat) : Triple :=
  if z<q m then
    let k := (entries m).getD (z*g m+a) 0
    if k=0 then (q m,a,1) else unpack (g m) k
  else if z=q m ∧ a≠marker m then (q m,a,0) else (q m+1,a,1)

theorem normalizedIns_spec (M : Ordinary ng nq) (z : Fin (nq+2)) (a : Fin ng) :
    normalizedIns (data M) z.val a.val=numIns (trans M z a) := by
  by_cases h : z.val<nq
  · let s : Fin nq := ⟨z.val,h⟩
    have E := stored M s a
    change (entries (data M)).getD (z.val*ng+a.val) 0=_ at E
    simp only [normalizedIns,P455MachineCleanup.trans,q,data,g,if_pos h,dif_pos h] at *
    rw [E]
    cases e : M.delta s a with
    | none => simp [s] at e; simp [e,entryCode,numIns,cleanState,dirCode]
    | some i =>
      have N : entryCode ng (some i)≠0 := by simp [entryCode] <;> omega
      rw [if_neg N,unpack_some]; simp [s] at e; simp [e,numIns,extend,old]
  · by_cases k : z.val=nq <;> by_cases e : a=M.marker <;>
      simp [normalizedIns,data,P455MachineCleanup.trans,q,g,marker,entries,h,k,e,Fin.ext_iff.mp, numIns,cleanState,acceptState,dirCode,← Fin.ext_iff]

end P455WriterProgram
