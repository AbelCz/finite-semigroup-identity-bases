import Problem455CellClassPadded
import Problem455PaddedOrders
import Problem455PaddedSnake
import Problem455PortUnique

/- Recover exact directional neighbors in the literal rectangle word.
   Coordinates and type tags are inferred for arbitrary records. -/
namespace P455CellClassGrid
open P455RectangleRank P455PaddedMatchings P455PaddedTiles P455PaddedWord P455Witness
open P455CellClassClean P455CellClassFrames P455SlotSaturation P455GridRows Problem455.Slots
noncomputable section
variable {n w h : Nat} {M : MachineTable n}

def labels (R : Rectangle M w h) := tagAt w R.tag

theorem label_at (R : Rectangle M w h) {y x : Nat} (_hy : y<h) (hx : x<w) :
    labels R (idAt w y x) = R.tag y x := tag_id R.tag hx

def zero (R : Rectangle M w h) := text h w (widthCode n) (labels R) (constant false)
def cell (R : Rectangle M w h) (y x : Nat) := node (labels R) (idAt w y x)
abbrev H (R : Rectangle M w h) := Holds (widthCode n+16) (allowed M) noMark (zero R)

theorem coordinates {R : Rectangle M w h} {y x : Nat} (hy : y<h) (hx : x<w) :
    (cell R y x).tag = R.tag y x := label_at R hy hx

def literal_phases (R : Rectangle M w h) (size : 1<w*h) :
    Phases (widthCode n+16) (allowed M) (w*h) (middle h w (widthCode n) (labels R)) (tail (w*h)) := by
  have yes (i : Nat) (ix : i<w*h) : allowed M (labels R i) := by
    obtain ⟨y,hy,x,hx,rfl⟩ := id_covers ix
    rw [label_at R hy hx]; exact R.eligible y hy x hx
  exact P455CellClassPadded.phases size (labels R) (fun i ix => by
    obtain ⟨tile,eq,_⟩ := yes i ix; rw [← eq,code_length]) yes

theorem cell_typed (R : Rectangle M w h) (size : 1<w*h) {i : Nat} (ix : i<w*h) :
    H R (typedNode (node (labels R) i)) := typed_cell (literal_phases R size) (constant false) ix noMark

theorem any_record (R : Rectangle M w h) (size : 1<w*h) (u : Node) (read : H R (typedNode u)) :
    ∃ y<h, ∃ x<w,u=cell R y x := by
  obtain ⟨i,ix,own,mate⟩ := record_roles (constant false) (P455CellClassPadded.names size _ _)
    (P455CellClass.canonical_final _) u read
  have equal := P455PortUnique.node_unique u (node (labels R) i) own mate read (cell_typed R size ix)
  obtain ⟨y,hy,x,hx,eq⟩ := id_covers ix
  exact ⟨y,hy,x,hx,by simpa [cell,eq] using equal⟩

structure Orders (R : Rectangle M w h) : Prop where
  early : ∀ i<w*h,∀ j<w*h,i≠j → H R (earlyDisjoint (P455PaddedPorts.roles i) (P455PaddedPorts.roles j))
  column : ∀ y<h,∀ x, x+1<w → H R (earlier (owner (idAt w y x)) (13+widthCode n)
      (owner (idAt w y (x+1))) (13+widthCode n))
  first : ∀ i j, i<j → j<w*h → H R (earlier (owner i) 0 (owner j) 0)

theorem orders (R : Rectangle M w h) (size : 1<w*h) : Orders R :=
  ⟨fun _ hi _ hj ne => early_groups size (labels R) (constant false) (allowed M) noMark ne hi hj,
   fun _ hy _ slope => column_order size (labels R) (constant false) (allowed M) noMark hy slope,
   fun _ _ lt hj => first_owner size (labels R) (constant false) (allowed M) noMark lt hj⟩

theorem port {R : Rectangle M w h} (size : 1<w*h) (ord : Orders R) (p : Fin 5) {i j}
    (lt : i<w*h) (jt : j<w*h) (ne : i≠j) :
    H R (orientedPort p.val (node (labels R) i) (node (labels R) j)) ↔
      P455PaddedPorts.Block.pair i j ∈ matching h w p.val := by
  have iff := port_iff (k:=widthCode n) size (labels R) (constant false) (allowed M) noMark p ne lt jt
  exact ⟨fun r => (iff.mp r).2.2.2,fun yes => iff.mpr
    ⟨cell_typed R size lt,cell_typed R size jt,ord.early i lt j jt ne,yes⟩⟩

private theorem codeLen (R : Rectangle M w h) {y x : Nat} (hy : y<h) (hx : x<w) :
    (cell R y x).tag.length=widthCode n := by
  obtain ⟨tile,eq,_⟩ := R.eligible y hy x hx; rw [coordinates hy hx,← eq,code_length]

theorem right_iff (R : Rectangle M w h) (size : 1<w*h) (ord : Orders R) {y x v z : Nat}
    (hy : y<h) (hx : x<w) (hv : v<h) (hz : z<w) :
    H R (rightward (system n) (cell R y x) (cell R v z)) ↔ y=v ∧ x+1=z := by
  let i := idAt w y x
  let j := idAt w v z
  have li : i<w*h := id_bound hy hx
  have lj : j<w*h := id_bound hv hz
  have col : (system n).oddColumn (cell R y x).tag=odd x := (coordinates hy hx) ▸ (R.flags y hy x hx).2.2.2.2.2
  let p : Fin 5 := ⟨if odd x then 1 else 0,by split <;> decide⟩
  have matchId : matching h w p.val=horizontal h w (odd x) := by cases e : odd x <;> simp [p,matching,e]
  have edges : H R (orientedPort p.val (cell R y x) (cell R v z)) → i≠j →
      P455PaddedPorts.Block.pair i j ∈ horizontal h w (odd x) := by
    intro read ne; rw [← matchId]; exact (port size ord p li lj ne).mp read
  constructor
  · rintro ⟨horiz,read,_,_⟩
    have ne : i≠j := by
      intro eq; obtain ⟨rfl,rfl⟩ := id_inj hx hz eq
      obtain ⟨a,b,pa,pb,good⟩ := horiz
      have same := code_inj (pa.trans pb.symm)
      exact good.2.2.2.2.2.1 (congrArg Tile.oddColumn same)
    rw [col] at read
    obtain ⟨Y,_,X,Xp,_,e1,e2⟩ := (horizontal_edge ..).mp (edges read ne)
    obtain ⟨yy,xx⟩ := id_inj hx (show X<w by omega) e1
    obtain ⟨vv,zz⟩ := id_inj hz Xp e2
    omega
  · rintro ⟨rfl,rfl⟩
    have ne : i≠j := fun eq => by obtain ⟨_,err⟩ := id_inj hx hz eq; omega
    have has : P455PaddedPorts.Block.pair i j ∈ horizontal h w (odd x) :=
      (horizontal_edge ..).mpr ⟨y,hy,x,hz,rfl,rfl,rfl⟩
    have read := (port size ord p li lj ne).mpr (matchId ▸ has)
    refine ⟨?_,?_,?_,True.intro⟩
    · change (system n).horizontal _ _; rw [coordinates hy hx,coordinates hy hz]; exact R.right y hy x hz
    · change H R (orientedPort _ _ _); rw [col]; exact read
    · rw [codeLen R hy hx]; exact ord.column y hy x hz

theorem down_iff (R : Rectangle M w h) (size : 1<w*h) (ord : Orders R) {y x v z : Nat}
    (hy : y<h) (hx : x<w) (hv : v<h) (hz : z<w) :
    H R (downward (system n) (cell R y x) (cell R v z)) ↔ y+1=v ∧ x=z := by
  let i := idAt w y x
  let j := idAt w v z
  have li : i<w*h := id_bound hy hx
  have lj : j<w*h := id_bound hv hz
  have row : (system n).oddRow (cell R y x).tag=odd y := (coordinates hy hx) ▸ (R.flags y hy x hx).2.2.2.2.1
  let p : Fin 5 := ⟨if odd y then 3 else 2,by split <;> decide⟩
  have matchId : matching h w p.val=vertical h w (odd y) := by cases e : odd y <;> simp [p,matching,e]
  constructor
  · rintro ⟨vert,read⟩
    have ne : i≠j := by
      intro eq; obtain ⟨rfl,rfl⟩ := id_inj hx hz eq
      obtain ⟨a,b,pa,pb,good⟩ := vert
      have same := code_inj (pa.trans pb.symm)
      exact good.2.2.2.2.2.1 (congrArg Tile.oddRow same)
    rw [row] at read
    have has := (port size ord p li lj ne).mp read
    rw [matchId] at has
    obtain ⟨X,_,Y,Yp,_,e1,e2⟩ := (vertical_edge ..).mp has
    obtain ⟨yy,xx⟩ := id_inj hx (by assumption) e1
    obtain ⟨vv,zz⟩ := id_inj hz (by assumption) e2
    omega
  · rintro ⟨rfl,rfl⟩
    have ne : i≠j := fun eq => by obtain ⟨err,_⟩ := id_inj hx hz eq; omega
    have has : P455PaddedPorts.Block.pair i j ∈ vertical h w (odd y) :=
      (vertical_edge ..).mpr ⟨x,hx,y,hv,rfl,rfl,rfl⟩
    refine ⟨?_,?_⟩
    · change (system n).vertical _ _; rw [coordinates hy hx,coordinates hv hx]; exact R.down y hv x hx
    · change H R (orientedPort _ _ _); rw [row]; exact (port size ord p li lj ne).mpr (matchId ▸ has)

theorem functional {R : Rectangle M w h} (size : 1<w*h) (ord : Orders R) :
    Ports (widthCode n+16) (allowed M) (system n) (zero R) := by
  intro a rec d b c nb nc
  obtain ⟨y,hy,x,hx,rfl⟩ := any_record R size a rec
  obtain ⟨v,hv,z,hz,rfl⟩ := any_record R size b (P455Paths.neighbor_target_record nb)
  obtain ⟨s,hs,q,hq,rfl⟩ := any_record R size c (P455Paths.neighbor_target_record nc)
  have positions : v=s ∧ z=q := by
    cases d with
    | right =>
      have := (right_iff R size ord hy hx hv hz).mp nb
      have := (right_iff R size ord hy hx hs hq).mp nc
      omega
    | left =>
      have := (right_iff R size ord hv hz hy hx).mp nb
      have := (right_iff R size ord hs hq hy hx).mp nc
      omega
    | down =>
      have := (down_iff R size ord hy hx hv hz).mp nb
      have := (down_iff R size ord hy hx hs hq).mp nc
      omega
    | up =>
      have := (down_iff R size ord hv hz hy hx).mp nb
      have := (down_iff R size ord hs hq hy hx).mp nc
      omega
  rw [positions.1,positions.2]

end
end P455CellClassGrid
