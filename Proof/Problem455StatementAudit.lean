import Problem455TableDecision



namespace P455StatementAudit
open P455Table P455TableSemantics P455BinaryTerms P455BinaryBasis P455PureSemigroup

def product (T : Matrix) (valid : SemigroupTable T) (a b : Fin T.length) : Fin T.length :=
  ⟨entry T a b,entry_lt valid a.isLt b.isLt⟩

def val {T : Matrix} (ok : SemigroupTable T) (f : Nat → Fin T.length) : Term → Fin T.length
  | .var x => f x
  | .mul s t => product T ok (val ok f s) (val ok f t)

theorem eval_fin {T : Matrix} (ok : SemigroupTable T) (f : Nat → Fin T.length) (s : Term) :
    (val ok f s).val=eval T (fun x => (f x).val) s := by
  induction s <;> simp_all [val,eval,product]

theorem assignments {T : Matrix} (ok : SemigroupTable T) (s t : Term) :
    ValidTerm T s t ↔ ∀ f : Nat → Fin T.length, val ok f s=val ok f t := by
  constructor
  · intro all f
    apply Fin.ext
    rw [eval_fin,eval_fin]
    exact all _ (fun x => (f x).isLt)
  · intro h f bounded
    let g (i : Nat) : Fin T.length := ⟨f i,bounded i⟩
    simpa only [eval_fin,g] using congrArg Fin.val (h g)

theorem substitution {T : Matrix} (ok : SemigroupTable T) (g : Nat → Term)
    (f : Nat → Fin T.length) (s : Term) :
    val ok f (inst g s) = val ok (fun x => val ok f (g x)) s := by
  induction s <;> simp_all [inst,val]

theorem soundness {T : Matrix} (ok : SemigroupTable T) {G : Term → Term → Prop}
    (laws : ∀ {a b}, G a b → ValidTerm T a b) {s t} (p : Equational G s t) :
    ValidTerm T s t := by
  apply (assignments ok _ _).mpr
  induction p with
  | refl => exact fun _ => rfl
  | gen h => exact (assignments ok _ _).mp (laws h)
  | symm _ ih => exact fun f => (ih f).symm
  | trans _ _ ih ik => exact fun f => (ih f).trans (ik f)
  | mul _ _ ih ik => intro f; simp only [val,ih f,ik f]
  | subst g _ ih => intro f; rw [substitution,substitution]; exact ih _

/-- Exact equality between the identities holding in a semigroup and the
    ordinary consequences of one finite list of two-sided equations. -/
theorem exact_basis {T : Matrix} (ok : SemigroupTable T) :
    Basis T ↔ ∃ R : List (Term × Term), ∀ s t,
      (∀ f : Nat → Fin T.length, val ok f s=val ok f t) ↔
      Equational (fun u v => (u,v) ∈ R) s t := by
  constructor
  · rintro ⟨R,truth,complete⟩
    exact ⟨R,fun s t => ⟨fun h => complete s t ((assignments ok s t).mpr h),
      fun pf => (assignments ok s t).mp (soundness ok (fun h => truth _ _ h) pf)⟩⟩
  · rintro ⟨R,exactness⟩
    exact ⟨R,fun s t h => (assignments ok _ _).mpr ((exactness _ _).mpr (.gen h)),
      fun s t h => (exactness _ _).mp ((assignments ok s t).mp h)⟩

theorem encoding_inj {S T : Matrix} (s : SemigroupTable S) (t : SemigroupTable T)
    (h : P455TableBits.encode S=P455TableBits.encode T) : S=T := by
  have x := P455TableBits.roundtrip (fun r hr => (s.2.1 r hr).1)
  have y := P455TableBits.roundtrip (fun r hr => (t.2.1 r hr).1)
  exact Option.some.inj (x.symm.trans ((congrArg P455TableBits.parse h).trans y))

end P455StatementAudit
