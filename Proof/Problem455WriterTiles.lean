import Problem455WriterTileData
import Problem455PrimitivePrim
import Mathlib.Data.List.FinRange

/- Primitive-recursive tag enumeration for the literal numerical local rule. -/
namespace P455WriterTiles
open P455PaddedTiles

abbrev TileData := Bool × Bool × Bool × Bool × Bool × Bool × Nat × Nat × Nat × Nat

def raw (p : Tile n) : TileData :=
  (p.left,p.right,p.top,p.bottom,p.oddRow,p.oddColumn,letter p.l,p.c.val,letter p.r,p.b.val)

def choices (xs : List X) (ys : List Y) : List (X × Y) :=
  xs.flatMap fun x => ys.map fun y => (x,y)

theorem map_choices (xs : List X) (ys : List Y) (f : X×Y → Z) :
    (choices xs ys).map f = xs.flatMap fun x => ys.map fun y => f (x,y) := by
  simp only [choices,List.map_flatMap,List.map_map,Function.comp_def]

theorem choicesRec {A X Y : Type} [Primcodable A] [Primcodable X] [Primcodable Y]
    {xs : A → List X} {ys : A → List Y} (hx : Primrec xs) (hy : Primrec ys) :
    Primrec fun a => choices (xs a) (ys a) := by
  apply Primrec.list_flatMap hx
  apply Primrec₂.mk
  apply Primrec.list_map (hy.comp Primrec.fst)
  exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

def options (n : Nat) := 0 :: (List.range n).map Nat.succ
def pool (n : Nat) : List TileData :=
  let b := [false,true]
  let s := List.range n
  let o := options n
  choices b (choices b (choices b (choices b (choices b (choices b (choices o (choices s (choices o s))))))))

theorem optionsRec : Primrec options :=
  Primrec.list_cons.comp (.const 0) (Primrec.list_map Primrec.list_range (Primrec.succ.comp Primrec.snd).to₂)

theorem poolRec : Primrec pool := by
  have b : Primrec (fun _ : Nat => [false,true]) := Primrec.const _
  have o := optionsRec
  have s := Primrec.list_range
  exact choicesRec b (choicesRec b (choicesRec b (choicesRec b (choicesRec b (choicesRec b
    (choicesRec o (choicesRec s (choicesRec o s))))))))

theorem map_raw (n : Nat) : ((P455Enum.tiles n).list.map raw) = pool n := by
  have op : options n = (P455Enum.options (P455Enum.fins n)).list.map letter := by
    simp only [options,P455Enum.options,P455Enum.fins,List.map_cons,List.map_map,letter]
    rw [←List.map_coe_finRange,List.map_map]
    rfl
  unfold pool
  rw [op,←List.map_coe_finRange]
  simp only [P455Enum.tiles,P455Enum.bools,P455Enum.fins,choices,List.map_flatMap,List.map_map,
    List.flatMap_map,List.flatMap_assoc,Function.comp_def,raw]

def tokenN (n k : Nat) := digit (n+1) k

def rawCode (n : Nat) (p : TileData) :=
  p.1 :: p.2.1 :: p.2.2.1 :: p.2.2.2.1 :: p.2.2.2.2.1 :: p.2.2.2.2.2.1 ::
    (tokenN n p.2.2.2.2.2.2.1 ++ (tokenN n (p.2.2.2.2.2.2.2.1+1) ++
      (tokenN n p.2.2.2.2.2.2.2.2.1 ++ tokenN n (p.2.2.2.2.2.2.2.2.2+1))))

theorem code_raw (p : Tile n) : rawCode n (raw p) = code p := rfl

def eligible (D : MachineData) (p : TileData) : Prop :=
  let (left,right,top,bottom,oddRow,oddColumn,l,c,r,b) := p
  update D l c r = some b ∧ left=decide (l=0) ∧ right=decide (r=0) ∧ marker D c=left ∧
  (left=true → oddColumn=false) ∧ (top=true → oddRow=false ∧ c=initial D left) ∧
  (bottom=true → left=true → c=accept D)

instance eligibleDec (D : MachineData) (p : TileData) : Decidable (eligible D p) := by
  unfold eligible; infer_instance

theorem eligible_raw {D : MachineData} {M : MachineTable n} (h : Models D M) (p : Tile n) :
    eligible D (raw p) ↔ Admitted M p := by
  have none (s : Option (Fin n)) : decide (letter s=0) = s.isNone := by
    cases s <;> simp [letter]
  have step : (M.next p.l p.c p.r).map Fin.val = some p.b.val ↔ M.next p.l p.c p.r = some p.b := by
    cases e : M.next p.l p.c p.r <;> simp [Fin.ext_iff]
  simp only [eligible,raw,Admitted,h.step,h.marks,h.start,h.final,none,step,Fin.ext_iff]

def tags (D : MachineData) := ((pool (size D)).filter (eligible D)).map (rawCode (size D))

theorem tags_correct {D : MachineData} {M : MachineTable n} (h : Models D M) :
    tags D = P455Enum.tags M := by
  unfold tags P455Enum.tags
  rw [h.dim,←map_raw,List.filter_map,List.map_map]
  have same : ((P455Enum.tiles n).list.filter (fun p => decide (eligible D (raw p)))) =
      ((P455Enum.tiles n).list.filter (Admitted M)) := by
    apply List.filter_congr
    intro p _
    exact Bool.eq_iff_iff.mpr (by simpa using eligible_raw h p)
  simpa only [Function.comp_def,code_raw] using congrArg (List.map code) same

end P455WriterTiles
