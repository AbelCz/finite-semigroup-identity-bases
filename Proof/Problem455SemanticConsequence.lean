import Problem455StatementAudit




namespace P455SemanticConsequence
open P455BinaryTerms P455PureSemigroup

def ev (mul : A → A → A) (f : Nat → A) : Term → A
  | .var i => f i
  | .mul s t => mul (ev mul f s) (ev mul f t)

def satisfies (mul : A → A → A) (s t : Term) :=
  ∀ f : Nat → A, ev mul f s=ev mul f t

def entails (R : Term → Term → Prop) (s t : Term) :=
  ∀ (A : Type) (mul : A → A → A), (∀ u v, R u v → satisfies mul u v) → satisfies mul s t

theorem ev_sub (mul : A → A → A) (f : Nat → A) (g : Nat → Term) (s : Term) :
    ev mul f (inst g s)=ev mul (fun i => ev mul f (g i)) s := by
  induction s <;> simp_all [inst,ev]

theorem sound {R s t} (h : Equational R s t) : entails R s t := by
  intro A mul models
  induction h with
  | refl => exact fun _ => rfl
  | gen g => exact models _ _ g
  | symm _ ih => exact fun f => (ih f).symm
  | trans _ _ ih ik => exact fun f => (ih f).trans (ik f)
  | mul _ _ ih ik => intro f; simp only [ev,ih f,ik f]
  | subst g _ ih => intro f; rw [ev_sub,ev_sub]; exact ih _

def relation (R : Term → Term → Prop) : Setoid Term where
  r := Equational R
  iseqv := ⟨fun t => .refl t, fun h => .symm h,fun h k => .trans h k⟩

abbrev Free (R) := Quotient (relation R)

def cls (R) (t : Term) : Free R := Quotient.mk _ t

def product (R) (a b : Free R) : Free R :=
  Quotient.liftOn₂ a b (fun u v => cls R (.mul u v))
    (fun _ _ _ _ h k => Quotient.sound (Equational.mul h k))

theorem ev_class (R) (g : Nat → Term) (t) :
    ev (product R) (fun i => cls R (g i)) t=cls R (inst g t) := by
  induction t <;> simp_all [ev,inst]; rfl

theorem free_model (R) (s t) (h : R s t) : satisfies (product R) s t := by
  intro f
  let g i := Classical.choose (Quotient.exists_rep (f i))
  have eq : f=fun i => cls R (g i) := funext fun i => (Classical.choose_spec (Quotient.exists_rep (f i))).symm
  rw [eq, ev_class, ev_class]
  exact Quotient.sound (Equational.subst g (.gen h))

theorem id_inst (t : Term) : inst Term.var t=t := by induction t <;> simp_all [inst]

theorem complete {R s t} (h : entails R s t) : Equational R s t := by
  have e := h (Free R) (product R) (free_model R) (fun i => cls R (.var i))
  have eq : cls R s=cls R t := by simpa only [ev_class,id_inst] using e
  exact Quotient.exact eq

theorem iff_semantic (R) (s t) : Equational R s t ↔ entails R s t := ⟨sound,complete⟩

theorem public_basis {T : P455Table.Matrix} (ok : P455TableSemantics.SemigroupTable T) :
    Basis T ↔ ∃ R : List (Term × Term), ∀ s t,
      (∀ f : Nat → Fin T.length, P455StatementAudit.val ok f s=P455StatementAudit.val ok f t) ↔
      entails (fun u v => (u,v) ∈ R) s t := by
  rw [P455StatementAudit.exact_basis ok]
  simp only [iff_semantic]

end P455SemanticConsequence
