import Problem455PaddedMatchings


namespace P455PaddedMatchings
open P455PaddedTiles

def rowEnd (w y x : Nat) : Prop := if odd y then x=0 else x+1=w

def Next (w y x v z : Nat) : Prop :=
  (odd y=false ∧ v=y ∧ z=x+1) ∨
  (odd y=true ∧ v=y ∧ z+1=x) ∨
  (v=y+1 ∧ z=x ∧ rowEnd w y x)

theorem odd_succ (y : Nat) : odd (y+1)= !odd y := by
  by_cases e : y%2=1
  · simp [odd,e,show (y+1)%2≠1 by omega]
  · simp [odd,e,show (y+1)%2=1 by omega]

theorem first_id (w : Nat) : idAt w 0 0=0 := by simp [idAt,odd]

theorem end_id {w y x : Nat} (hx : x<w) (endRow : rowEnd w y x) :
    idAt w y x+1=w*(y+1) := by
  cases par : odd y <;> simp [rowEnd,par] at endRow <;> simp [idAt,par,Nat.mul_add] <;> omega

theorem down_id {w y x : Nat} (hx : x<w) (endRow : rowEnd w y x) :
    idAt w (y+1) x=idAt w y x+1 := by
  rw [end_id hx endRow]
  cases par : odd y <;> simp [rowEnd,par] at endRow <;> simp [idAt,odd_succ,par] <;> omega

theorem stepping {w h i : Nat} (bound : i+1<w*h) :
    ∃ y<h, ∃ x<w, ∃ v<h, ∃ z<w, idAt w y x=i ∧ idAt w v z=i+1 ∧ Next w y x v z := by
  obtain ⟨y,hy,x,hx,eq⟩ := id_covers (show i<w*h by omega)
  refine ⟨y,hy,x,hx,?_⟩
  by_cases b : rowEnd w y x
  · have jy : y+1<h := by
      by_cases strict : y+1<h
      · exact strict
      · have e : y+1=h := by omega
        have endPos := end_id hx b
        rw [e,eq] at endPos; omega
    exact ⟨y+1,jy,x,hx,eq,(down_id hx b).trans (congrArg (·+1) eq),.inr (.inr ⟨rfl,rfl,b⟩)⟩
  · cases par : odd y with
    | false =>
      simp [rowEnd,par] at b
      refine ⟨y,hy,x+1,by omega,eq,?_,.inl ⟨par,rfl,rfl⟩⟩
      simp [idAt,par] at eq ⊢; omega
    | true =>
      simp [rowEnd,par] at b
      refine ⟨y,hy,x-1,by omega,eq,?_,.inr (.inl ⟨par,rfl,by omega⟩)⟩
      simp [idAt,par] at eq ⊢; omega

theorem last_cell {w h : Nat} (pos : 0<w*h) :
    ∃ y<h, ∃ x<w, y+1=h ∧ rowEnd w y x ∧ idAt w y x=w*h-1 := by
  have wy : 0<w := by cases w with | zero => simp at pos | succ => omega
  have hy : 0<h := by cases h with | zero => simp at pos | succ => omega
  let y := h-1
  let x := if odd y then 0 else w-1
  have hx : x<w := by dsimp [x]; split <;> omega
  have b : rowEnd w y x := by cases p : odd y <;> simp [rowEnd,x,p] <;> omega
  have e : y+1=h := by dsimp [y]; omega
  have z := end_id hx b
  rw [e] at z
  exact ⟨y,by dsimp [y]; omega,x,hx,e,b,by omega⟩

def decodeRow (w i : Nat) := i/w
def decodeCol (w i : Nat) := if odd (decodeRow w i) then w-1-(i%w) else i%w

theorem decode_id {w y x : Nat} (hx : x<w) :
    decodeRow w (idAt w y x)=y ∧ decodeCol w (idAt w y x)=x := by
  have wt : 0<w := by omega
  have off : (if odd y then w-1-x else x)<w := by split <;> omega
  have yr : decodeRow w (idAt w y x)=y := by
    simp [decodeRow,idAt,Nat.mul_add_div wt,Nat.div_eq_of_lt off]
  refine ⟨yr,?_⟩
  unfold decodeCol
  rw [yr]
  simp only [idAt,Nat.mul_add_mod,Nat.mod_eq_of_lt off]
  cases p : odd y <;> simp <;> omega

def tagAt (w : Nat) (tile : Nat→Nat→List Bool) (i : Nat) :=
  tile (decodeRow w i) (decodeCol w i)

theorem tag_id (tile : Nat→Nat→List Bool) {w y x : Nat} (hx : x<w) :
    tagAt w tile (idAt w y x)=tile y x := by simp [tagAt,(decode_id hx).1,(decode_id hx).2]

end P455PaddedMatchings
