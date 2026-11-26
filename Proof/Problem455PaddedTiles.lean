import Problem455Witness




namespace P455PaddedTiles
open P455Witness

structure Tile (n : Nat) where
  left : Bool
  right : Bool
  top : Bool
  bottom : Bool
  oddRow : Bool
  oddColumn : Bool
  l : Option (Fin n)
  c : Fin n
  r : Option (Fin n)
  b : Fin n
  deriving DecidableEq

def digit (n k : Nat) : Tag := List.replicate k true ++ List.replicate (n-k) false
def letter : Option (Fin n) → Nat
  | none => 0
  | some a => a.val+1
def token {n : Nat} (s : Option (Fin n)) := digit (n+1) (letter s)
def code (p : Tile n) : Tag :=
  p.left :: p.right :: p.top :: p.bottom :: p.oddRow :: p.oddColumn ::
    (token p.l ++ (token (some p.c) ++ (token p.r ++ token (some p.b))))
def widthCode (n : Nat) := 6+4*(n+1)

private theorem token_length (s : Option (Fin n)) : (token s).length=n+1 := by
  have lim : letter s ≤ n+1 := by cases s with
    | none => simp [letter]
    | some a => simp only [letter]; have := a.isLt; omega
  simp [token,digit]; omega

theorem code_length (p : Tile n) : (code p).length = widthCode n := by
  simp [code,widthCode,token_length]; omega

private theorem token_inj {a b : Option (Fin n)} (eq : token a = token b) : a=b := by
  have ct := congrArg (List.count true) eq
  have zero (k : Nat) : (List.replicate k false).count true=0 := by
    apply List.count_eq_zero.mpr
    intro m
    have := List.eq_of_mem_replicate m
    contradiction
  simp [token,digit,zero] at ct
  cases a <;> cases b <;> simp_all [letter,Fin.ext_iff]

theorem code_inj {p q : Tile n} (eq : code p = code q) : p=q := by
  cases p with
  | mk l r t b row col ll cc rr bb =>
    cases q with
    | mk l' r' t' b' row' col' ll' cc' rr' bb' =>
      simp only [code,List.cons.injEq] at eq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,eq⟩ := eq
      obtain ⟨e1,e⟩ := List.append_inj eq ((token_length _).trans (token_length _).symm)
      obtain ⟨e2,e⟩ := List.append_inj e ((token_length _).trans (token_length _).symm)
      obtain ⟨e3,e4⟩ := List.append_inj e ((token_length _).trans (token_length _).symm)
      have z1 := token_inj e1; have z2 := Option.some.inj (token_inj e2)
      have z3 := token_inj e3; have z4 := Option.some.inj (token_inj e4)
      subst_vars; rfl

/-- Local alphabet of center symbols, including all possible head marks.
Undefined entries reject forbidden triples, including a head leaving the tape. -/
structure MachineTable (n : Nat) where
  marker : Fin n → Bool
  initial : Bool → Fin n
  accept : Fin n
  distinct : initial true ≠ accept
  next : Option (Fin n) → Fin n → Option (Fin n) → Option (Fin n)

def Admitted (M : MachineTable n) (p : Tile n) :=
  M.next p.l p.c p.r = some p.b ∧
  p.left = p.l.isNone ∧ p.right = p.r.isNone ∧ M.marker p.c = p.left ∧
  (p.left=true → p.oddColumn=false) ∧
  (p.top=true → p.oddRow=false ∧ p.c=M.initial p.left) ∧
  (p.bottom=true → p.left=true → p.c=M.accept)

def allowed (M : MachineTable n) (tag : Tag) := ∃ p, code p=tag ∧ Admitted M p

def Horizontal (p q : Tile n) :=
  p.right=false ∧ q.left=false ∧ p.top=q.top ∧ p.bottom=q.bottom ∧
  p.oddRow=q.oddRow ∧ p.oddColumn≠q.oddColumn ∧ q.l=some p.c ∧ p.r=some q.c

def Vertical (p q : Tile n) :=
  p.bottom=false ∧ q.top=false ∧ p.left=q.left ∧ p.right=q.right ∧
  p.oddColumn=q.oddColumn ∧ p.oddRow≠q.oddRow ∧ p.b=q.c

def system (n : Nat) : Tiles where
  horizontal := fun x y => ∃ p q : Tile n, code p=x ∧ code q=y ∧ Horizontal p q
  vertical := fun x y => ∃ p q : Tile n, code p=x ∧ code q=y ∧ Vertical p q
  left := fun t => t[0]?.getD false
  right := fun t => t[1]?.getD false
  top := fun t => t[2]?.getD false
  bottom := fun t => t[3]?.getD false
  oddRow := fun t => t[4]?.getD false
  oddColumn := fun t => t[5]?.getD false

def leftAt (row : Nat → Fin n) (x : Nat) := if x=0 then none else some (row (x-1))
def rightAt (row : Nat → Fin n) (w x : Nat) := if x+1=w then none else some (row (x+1))
def odd (i : Nat) : Bool := decide (i%2=1)

/-- Finite accepting trace through row s on w cells. The final local update
is checked once, including at both flagged boundaries. -/
structure Run (M : MachineTable n) (w s : Nat) where
  positive : 0<w
  rows : Nat → Nat → Fin n
  start : ∀ x, x<w → rows 0 x=M.initial (decide (x=0))
  marks : ∀ y, y≤s → ∀ x, x<w → M.marker (rows y x)=decide (x=0)
  steps : ∀ y, y<s → ∀ x, x<w →
    M.next (leftAt (rows y) x) (rows y x) (rightAt (rows y) w x)=some (rows (y+1) x)
  accept : rows s 0=M.accept
  stutter : ∀ x, x<w →
    M.next (leftAt (rows s) x) (rows s x) (rightAt (rows s) w x)=some (rows s x)

variable {n w s : Nat} {M : MachineTable n}

theorem positive_time (R : Run M w s) : 0<s := by
  cases s with
  | zero =>
    have z := (R.start 0 R.positive).symm.trans R.accept
    exact False.elim (M.distinct (by simpa using z))
  | succ => omega

def tileAt (R : Run M w s) (extra y x : Nat) : Tile n where
  left := decide (x=0)
  right := decide (x+1=w)
  top := decide (y=0)
  bottom := decide (y=s+extra)
  oddRow := odd y
  oddColumn := odd x
  l := leftAt (R.rows (min y s)) x
  c := R.rows (min y s) x
  r := rightAt (R.rows (min y s)) w x
  b := R.rows (min (y+1) s) x

theorem admits_tile (R : Run M w s) (extra y x : Nat) (hx : x<w) :
    Admitted M (tileAt R extra y x) := by
  refine ⟨?_,?_,?_,R.marks _ (Nat.min_le_right ..) _ hx,?_,?_,?_⟩
  · by_cases h : y<s
    · simpa [tileAt,Nat.min_eq_left (by omega : y≤s),Nat.min_eq_left (by omega : y+1≤s)] using R.steps y h x hx
    · simpa [tileAt,Nat.min_eq_right (by omega : s≤y),Nat.min_eq_right (by omega : s≤y+1)] using R.stutter x hx
  · by_cases e : x=0 <;> simp [tileAt,leftAt,e]
  · by_cases e : x+1=w <;> simp [tileAt,rightAt,e]
  · intro h; have e : x=0 := of_decide_eq_true h; simp [tileAt,odd,e]
  · intro h; have e : y=0 := of_decide_eq_true h; simpa [tileAt,odd,e] using R.start x hx
  · intro a b
    have ey : y=s+extra := of_decide_eq_true a
    have ex : x=0 := of_decide_eq_true b
    simpa [tileAt,ex,ey,Nat.min_eq_right (by omega : s≤s+extra)] using R.accept

private theorem opposite (x : Nat) : odd x ≠ odd (x+1) := by
  unfold odd
  by_cases e : x%2=1
  · have f : (x+1)%2 ≠ 1 := by omega
    simp [e,f]
  · have f : (x+1)%2 = 1 := by omega
    simp [e,f]

theorem horizontal (R : Run M w s) (extra y x : Nat) (hx : x+1<w) :
    Horizontal (tileAt R extra y x) (tileAt R extra y (x+1)) := by
  refine ⟨?_,?_,rfl,rfl,rfl,opposite _,?_,?_⟩
  · simp [tileAt,show x+1≠w by omega]
  · simp [tileAt]
  · simp [tileAt,leftAt]
  · simp [tileAt,rightAt,show x+1≠w by omega]

theorem vertical (R : Run M w s) (extra y x : Nat) (hy : y<s+extra) :
    Vertical (tileAt R extra y x) (tileAt R extra (y+1) x) := by
  refine ⟨?_,?_,rfl,rfl,rfl,opposite _,rfl⟩
  · simp [tileAt,show y≠s+extra by omega]
  · simp [tileAt]

structure Rectangle (M : MachineTable n) (width height : Nat) where
  positiveW : 0<width
  positiveH : 0<height
  tag : Nat → Nat → Tag
  eligible : ∀ y, y<height → ∀ x, x<width → allowed M (tag y x)
  flags : ∀ y, y<height → ∀ x, x<width →
    (system n).left (tag y x)=decide (x=0) ∧ (system n).right (tag y x)=decide (x+1=width) ∧
    (system n).top (tag y x)=decide (y=0) ∧ (system n).bottom (tag y x)=decide (y+1=height) ∧
    (system n).oddRow (tag y x)=odd y ∧ (system n).oddColumn (tag y x)=odd x
  right : ∀ y, y<height → ∀ x, x+1<width → (system n).horizontal (tag y x) (tag y (x+1))
  down : ∀ y, y+1<height → ∀ x, x<width → (system n).vertical (tag y x) (tag (y+1) x)

def rectangle (R : Run M w s) (extra : Nat) : Rectangle M w (s+extra+1) where
  positiveW := R.positive
  positiveH := by omega
  tag := fun y x => code (tileAt R extra y x)
  eligible := fun y _ x hx => ⟨_,rfl,admits_tile R extra y x hx⟩
  flags := by
    intro y _ x _
    simp [system,code,tileAt]
  right := fun y _ x hx => ⟨_,_,rfl,rfl,horizontal R extra y x hx⟩
  down := fun y hy x _ => ⟨_,_,rfl,rfl,vertical R extra y x (by omega)⟩

/-- The same tag alphabet, tag length and tile relations work at every
bound. Width one is allowed. The construction pads time alone. -/
theorem unbounded (R : Run M w s) (k : Nat) :
    ∃ h, 1<h ∧ k<2*(w*h) ∧ Nonempty (Rectangle M w h) := by
  have time := positive_time R
  let h := s+k+1
  have hw : 1≤w := R.positive
  have size : h ≤ w*h := by simpa using Nat.mul_le_mul_right h hw
  exact ⟨h,by dsimp [h]; omega,by dsimp [h] at *; omega,⟨rectangle R k⟩⟩

end P455PaddedTiles
