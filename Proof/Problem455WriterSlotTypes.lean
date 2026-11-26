import Problem455WriterEdgeTypes
import Problem455WriterProfiles
namespace P455WriterSlots
open P455Witness
open P455WriterTiles (choicesRec map_choices choices)
variable {A : Type} [Primcodable A]

abbrev ContactData := (Tag × Bool) ⊕ (Fin 5 × Bool)
def contactCode : ContactChoice ≃ ContactData where
  toFun | .record t b => .inl (t,b) | .port p b => .inr (p,b)
  invFun | .inl (t,b) => .record t b | .inr (p,b) => .port p b
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨_,_⟩|⟨_,_⟩ <;> rfl
instance : Primcodable ContactChoice := Primcodable.ofEquiv _ contactCode
theorem contactCodeRec : Primrec contactCode := Primrec.of_equiv

def defectCode : SlotDefect ≃ Nat ⊕ W where
  toFun | .deficient a => .inl a | .overflow xs => .inr xs
  invFun | .inl a => .deficient a | .inr xs => .overflow xs
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl
instance : Primcodable SlotDefect := Primcodable.ofEquiv _ defectCode
theorem defectCodeRec : Primrec defectCode := Primrec.of_equiv

abbrev SlotData := Node × Bool × Bool × List (Nat × ContactChoice) × Nat × SlotDefect
def slotCode : SlotCertificate ≃ SlotData where
  toFun s := (s.anchor,s.bit,s.startAtMate,s.steps,s.terminalIndex,s.defect)
  invFun | (a,b,m,p,i,d) => ⟨a,b,m,p,i,d⟩
  left_inv a := by cases a; rfl
  right_inv _ := rfl
instance : Primcodable SlotCertificate := Primcodable.ofEquiv _ slotCode
theorem slotCodeRec : Primrec slotCode := Primrec.of_equiv

theorem choicesRec' {ts : A → List Tag} (ht : Primrec ts) :
    Primrec fun a => P455Enum.choices (ts a) := by
  let b := [false,true]
  let f := fun s : Tag × Bool => contactCode.symm (Sum.inl s)
  let g := fun s : Fin 5 × Bool => contactCode.symm (Sum.inr s)
  have hf : Primrec f := (Primrec.of_equiv_symm (e:=contactCode)).comp Primrec.sumInl
  have hg : Primrec g := (Primrec.of_equiv_symm (e:=contactCode)).comp Primrec.sumInr
  have h1 := Primrec.list_map (choicesRec ht (.const b)) (hf.comp Primrec.snd).to₂
  have h2 : Primrec (fun _ : A => (choices (P455Enum.fins 5).list b).map g) := Primrec.const _
  apply (Primrec.list_append.comp h1 h2).of_eq
  intro a
  simp only [map_choices,P455Enum.choices,b,P455Enum.bools,f,g,contactCode,Equiv.coe_fn_symm_mk]

theorem stepsRec {w : A → W} {ts : A → List Tag} (hw : Primrec w) (ht : Primrec ts) :
    Primrec fun a => P455Enum.steps (w a) (ts a) := choicesRec hw (choicesRec' ht)

theorem defectsRec {w : A → W} (hw : Primrec w) :
    Primrec fun a => P455Enum.defects (w a) := by
  have f : Primrec SlotDefect.deficient := (Primrec.of_equiv_symm (e:=defectCode)).comp Primrec.sumInl
  have g : Primrec SlotDefect.overflow := (Primrec.of_equiv_symm (e:=defectCode)).comp Primrec.sumInr
  exact Primrec.list_append.comp (Primrec.list_map hw (f.comp Primrec.snd).to₂)
    (Primrec.list_map (P455GraphPrim.wordsUpTo.comp hw (.const 5)) (g.comp Primrec.snd).to₂)

theorem slotsRec {w : A → W} {ts : A → List Tag} (hw : Primrec w) (ht : Primrec ts) :
    Primrec fun a => P455Enum.slots (w a) (ts a) := by
  let bs := P455Enum.bools.list
  have h := choicesRec (P455WriterEdge.poolRec hw ht) (choicesRec (.const bs)
    (choicesRec (.const bs) (choicesRec (P455GraphPrim.wordsUpTo.comp (stepsRec hw ht) (.const 6))
    (choicesRec (.const (List.range 12)) (defectsRec hw)))))
  apply (Primrec.list_map h ((Primrec.of_equiv_symm (e:=slotCode)).comp Primrec.snd).to₂).of_eq
  intro a
  simp only [map_choices,P455Enum.slots,bs,choices,List.map_flatMap,List.map_map,Function.comp_def,
    slotCode,Equiv.coe_fn_symm_mk]

end P455WriterSlots
