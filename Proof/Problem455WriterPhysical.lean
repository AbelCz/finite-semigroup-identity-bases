import Problem455WriterSweep
import Problem455TableDecision

namespace P455WriterPhysical
open P455MachineLocal P455MachineTable P455MachineCleanup P455EffectiveMachine
open P455EffectiveChain P455WriterFrontier P455WriterSweep

/-- A finite-control producer may halt anywhere and leave arbitrary work on every track.
    Projecting cell j+1 has to recover the optional j-th output bit. -/
def Projects (M : Ordinary g q) (A : Alphabet M) (read : Fin g → Option Bool)
    (x y : List Bool) : Prop :=
  ∃ t, let c := follow M (inputConfig M A x) t
       instruction M c=none ∧ ∀ j, read (c.tape (j+1)) = y[j]?

def writer (M : Ordinary g q) (O : Alphabet M) (read : Fin g → Option Bool) :=
  chain (monitor M) (sweep M O read) rfl

def bits (M : Ordinary g q) (O : Alphabet M) (read : Fin g → Option Bool) (A : Alphabet M) :
    Alphabet (writer M O read) := liftAlphabet (monitor M) (sweep M O read) rfl (alphabet M A)

theorem cleanup (M : Ordinary g q) (A O : Alphabet M) (read : Fin g → Option Bool)
    (empty : read M.blank=none) {x y} (hx : Projects M A read x y) :
    Delivers (writer M O read) (bits M O read A) x (writer M O read) (bits M O read O) y := by
  obtain ⟨t,halt,raw⟩ := hx
  let c := follow M (inputConfig M A x) t
  change instruction M c=none at halt
  change ∀ j, read (c.tape (j+1))=y[j]? at raw
  obtain ⟨n,ok,run⟩ := simulates M A x t
  change Good M c n at ok
  let src := tape n c.tape
  have proper : ∀ j, src j=ink M.marker ↔ j=0 := by
    intro j; by_cases le : j≤n
    · simp [src,tape,le,ink_inj,ok.2.2]
    · have ne : j≠0 := by omega
      simp [src,tape,le,ne,Ne.symm (ink_ne_fresh M.marker)]
  have used : ∀ i, i≤n → src i≠fresh g := by
    intro i le; simp [src,tape,le,ink_ne_fresh]
  have virgin : ∀ i, n<i → src i=fresh g := by
    intro i lt; simp [src,tape,Nat.not_le_of_lt lt]
  let dst := fun j => cleanSym M O read (src j)
  let W := writer M O read
  let B := bits M O read O
  have output : dst=inputTape W B y := by
    funext j; cases j with
    | zero =>
      change cleanSym M O read (src 0)=ink M.marker
      simp [cleanSym,(proper 0).mpr rfl]
    | succ j =>
      change cleanSym M O read (src (j+1))=(y[j]?).elim (fresh g) (fun b => ink (O.bit b))
      have ne := fun h => Nat.succ_ne_zero j ((proper _).mp h)
      by_cases le : j+1≤n
      · have e : src (j+1)=ink (c.tape (j+1)) := by simp [src,tape,le]
        simp [cleanSym,ne,e,ink_ne_fresh,raw,show ink (c.tape (j+1))≠ink M.marker from e ▸ ne]
      · have b := ok.2.1 (j+1) (Nat.lt_of_not_ge le)
        have v := virgin _ (Nat.lt_of_not_ge le)
        have nodata : y[j]?=none := (raw j).symm.trans (b ▸ empty)
        simp [cleanSym,v,nodata,Ne.symm (ink_ne_fresh M.marker)]
  let L := monitor M
  let R := sweep M O read
  let ci := inputConfig L (alphabet M A) x
  change follow L ci t=liftCfg n c at run
  have ended : instruction L (follow L ci t)=none := by rw [run,ins_eq M ok,halt]; rfl
  obtain ⟨j,stop,before⟩ := earliest (fun j => instruction L (follow L ci j)=none) t ended
  have same := (unique_halt L ci stop ended).trans run
  have ci_eq : inputConfig W (bits M O read A) x=rename (left 3) ci := rfl
  have switch : follow W (inputConfig W (bits M O read A) x) (j+1)=
      rename (right q) (⟨src,c.pos,0⟩ : Config (g+1) 3) := by
    rw [ci_eq,follow]
    change once (chain L R rfl) (follow (chain L R rfl) (rename (left 3) ci) j)=_
    rw [follows_left L R rfl ci j before,shift_control L R rfl _ stop,same]
    rfl
  obtain ⟨⟨k,ex⟩,endR⟩ := finish M O read src c.pos n proper used virgin
  change follow R ⟨src,c.pos,0⟩ k=⟨dst,0,2⟩ at ex
  have final : follow W (inputConfig W (bits M O read A) x) (j+1+k)=
      rename (right q) (⟨dst,0,2⟩ : Config (g+1) 3) := by
    rw [follow_add,switch]
    exact (follows_right L R rfl _ k).trans (congrArg (rename (right q)) ex)
  refine ⟨j+1+k,?_⟩
  dsimp only
  rw [final]
  refine ⟨?_,rfl,output⟩
  change (chain L R rfl).delta (right q 2) (dst 0)=none
  change R.delta 2 (dst 0)=none at endR
  simp [chain,right_delta,endR]

/-- Construction on a single producer, uniform in every input. -/
theorem writer_exists (M : Ordinary g q) (A O : Alphabet M) (read : Fin g → Option Bool)
    (empty : read M.blank=none)
    (allCodes : ∀ {k s} (P : Ordinary k s) (B : Alphabet P),
      ∃ X : P455Table.FiniteOps,
        Nonempty (P455Table.Presents X (P455MachineReduction.model (P455EffectiveWriter.diagonalInput P B).2))
        ∧ Projects M A read (selfBits P B) (P455TableBits.encode (P455Table.matrix X))) :
    P455TableDecision.PresentationWriterExists := by
  refine ⟨_,_,writer M O read,bits M O read A,bits M O read O,?_⟩
  intro k s P B
  obtain ⟨X,iso,h⟩ := allCodes P B
  exact ⟨X,iso,cleanup M A O read empty h⟩

end P455WriterPhysical
