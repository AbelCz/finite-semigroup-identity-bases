import Problem455Finite



namespace P455EffectiveQReach
open P455Quotient
variable {α : Type} [DecidableEq α]

def via (edge : α → α → Bool) : List α → α → α → Bool
  | [], x, y => decide (x=y) || edge x y
  | z::zs, x, y => via edge zs x y || (via edge zs x z && via edge zs z y)

private theorem initial (e : α → α → Bool) (s : List α) {a b : α} (h : a=b ∨ e a b=true) :
    via e s a b = true := by
  induction s with
  | nil => simpa [via] using h
  | cons z zs ih => simp [via,ih]

private theorem splice (e : α → α → Bool) (s : List α) {a b c : α} (mem : b∈s)
    (p : via e s a b=true) (q : via e s b c=true) : via e s a c=true := by
  induction s generalizing a b c with
  | nil => simp at mem
  | cons z zs ih =>
    simp only [via,Bool.or_eq_true,Bool.and_eq_true] at p q ⊢
    rcases List.mem_cons.mp mem with rfl|tail
    · exact Or.inr ⟨p.elim id (·.1),q.elim id (·.2)⟩
    · rcases p with p|⟨px,py⟩ <;> rcases q with q|⟨qx,qy⟩
      · exact .inl (ih tail p q)
      · exact .inr ⟨ih tail p qx,qy⟩
      · exact .inr ⟨px,ih tail py q⟩
      · exact .inr ⟨px,qy⟩

theorem sound {rel : α → α → Prop} (e : α → α → Bool) (ok : ∀ x y,e x y=true → rel x y)
    (s : List α) {a b : α} (h : via e s a b = true) : Walk rel a b := by
  induction s generalizing a b with
  | nil =>
    simp only [via,Bool.or_eq_true,decide_eq_true_eq] at h
    rcases h with rfl|h
    · exact .refl _
    · exact .snoc (.refl _) (ok _ _ h)
  | cons z zs ih =>
    simp only [via,Bool.or_eq_true,Bool.and_eq_true] at h
    exact h.elim ih (fun ⟨p,q⟩ => (ih p).trans (ih q))

theorem complete {rel : α → α → Prop} (e : α → α → Bool) (ok : ∀ x y,rel x y → e x y=true)
    (s : List α) {a b : α} (cover : ∀ x, Walk rel a x → x∈s) (p : Walk rel a b) :
    via e s a b = true := by
  induction p with
  | refl => exact initial _ _ (.inl rfl)
  | snoc p step ih => exact splice _ _ (cover _ p) ih (initial _ _ (.inr (ok _ _ step)))

end P455EffectiveQReach
