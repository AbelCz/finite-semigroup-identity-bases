import Problem455Encoded
import Problem455MachineParseSelf




namespace P455RawReduction
open P455FirstRewrite P455Table P455TableSemantics P455TableBits P455Encoded
open P455EffectiveMachine P455MachineCleanup P455MachineParse P455EffectiveWriter

def singleton : FiniteOps := ⟨1,0,fun _ _ => 0⟩
def trivialModel : Model Unit := ⟨fun _ _ => (),(),by intros; rfl,fun _ => rfl,fun _ => rfl⟩
def singletonPresents : Presents singleton trivialModel := by
  unfold singleton
  exact ⟨fun _ => (),fun i j _ => Subsingleton.elim i j,fun _ => ⟨0,rfl⟩,rfl,fun _ _ => rfl⟩

theorem singleton_based : HasBasis (matrix singleton) := by
  apply (basis_iff singletonPresents).mpr
  let rules : List (W×W) := [([0],[1])]
  refine ⟨rules,?_,?_⟩
  · intro u v mem
    have same : (u,v)=([0],[1]) := List.mem_singleton.mp mem
    cases same
    exact ⟨by decide,by decide,fun _ => rfl⟩
  · intro u v un vn _
    let h : Nat → W := fun x => if x=0 then u else v
    refine .snoc (.refl u) ⟨[0],[1],[],[],h,.inl (by simp [rules]),by decide,by decide,?_,?_,?_⟩
    · intro x; by_cases e : x=0 <;> simp [h,e,un,vn]
    · simp [h]
    · simp [h]

def parseBlank (bits : List Bool) : Option RawOrdinary := do
  let ⟨g,q,c⟩ ← parseCode bits
  let M ← c.decode
  return ⟨g,q,M⟩

theorem parseBlank_quote (M : Ordinary g q) :
    parseBlank (quote M).bits=some ⟨g,q,M⟩ := by
  simp [parseBlank,code_roundtrip,quote_decode]

def realizesHalt : Option RawOrdinary → Prop
  | none => False
  | some ⟨_,_,M⟩ => ∃ t, stopped M t

def makeTable : Option RawOrdinary → Matrix
  | none => matrix singleton
  | some ⟨_,_,M⟩ => output M

theorem makeTable_laws (source : Option RawOrdinary) :
    SemigroupTable (makeTable source) ∧ HasUnit (makeTable source) := by
  rcases source with _|⟨_,_,M⟩
  · exact output_laws singletonPresents
  · exact output_monoid M

theorem makeTable_basis (source : Option RawOrdinary) :
    HasBasis (makeTable source) ↔ ¬ realizesHalt source := by
  rcases source with _|⟨_,_,M⟩
  · exact ⟨fun _ => id,fun _ => singleton_based⟩
  · exact finite_basis_iff M

def blankTable (bits : List Bool) := makeTable (parseBlank bits)
def blankBits (bits : List Bool) := encode (blankTable bits)
def diagonalTable (bits : List Bool) := makeTable (blankSource bits)
def diagonalBits (bits : List Bool) := encode (diagonalTable bits)

theorem bit_roundtrip (source : Option RawOrdinary) :
    parse (encode (makeTable source))=some (makeTable source) := by
  rcases source with _|⟨_,_,M⟩
  · exact matrix_roundtrip _
  · exact quoted_encoded M

/-- For every raw input, the output bytes parse as an associative monoid
    table and give the claimed answer on the ordinary semigroup signature. -/
theorem exact_blank (bits : List Bool) :
    parse (blankBits bits)=some (blankTable bits) ∧
    SemigroupTable (blankTable bits) ∧ HasUnit (blankTable bits) ∧
    (HasBasis (blankTable bits) ↔ ¬ realizesHalt (parseBlank bits)) :=
  ⟨bit_roundtrip _,(makeTable_laws _).1,(makeTable_laws _).2,makeTable_basis _⟩

theorem blank_matrix_iso (M : Ordinary g q) :
    blankTable (quote M).bits = matrix (ops M) ∧
      Nonempty (Presents (ops M) (P455MachineReduction.model M)) :=
  ⟨by simp [blankTable,parseBlank_quote,makeTable,output],⟨presents M⟩⟩

theorem exact_self (M : Ordinary g q) (A : Alphabet M) :
    HasBasis (diagonalTable (selfBits M A)) ↔ ¬SelfHalt M A := by
  rw [diagonalTable,blankSource_self,makeTable,finite_basis_iff,diagonal_input_iff]

end P455RawReduction
