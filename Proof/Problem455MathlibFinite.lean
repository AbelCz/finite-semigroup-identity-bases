import Problem455MathlibTM

namespace P455MathlibFinite
open Turing P455MathlibTM

/-- The states really form a finite type. Every instruction writing on
    the tape preserves its Boolean marker track, on all symbols. -/
theorem finite_machine {f : List Bool → List Bool} (hf : Computable f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q) (M : TM0.Machine Track Q),
       (∀ q a q' b, M q a = some (q',.write b) → b.1=a.1) ∧
       ∀ x, ∃ q, (⟨q,Tape.mk₁ (image (f x))⟩ : TM0.Cfg Track Q) ∈
         Turing.eval (TM0.step M) (TM0.init (image x)) := by
  classical
  obtain ⟨L,I,M,S,hs,guard,run⟩ := supported hf
  let Q := {q : L // q ∈ S}
  letI : Inhabited Q := ⟨⟨default,hs.1⟩⟩
  let pick (q : L) : Q := if h : q ∈ S then ⟨q,h⟩ else default
  have proj (q : L) (h : q ∈ S) : (pick q).val = q := by simp [pick,h]
  let sym : PointedMap Track Track := ⟨id,rfl⟩
  let N := M.map sym sym pick Subtype.val
  refine ⟨Q,inferInstance,inferInstance,N,?_,?_⟩
  · intro q a q' b step
    change (M q.val a).map (Prod.map pick (TM0.Stmt.map sym)) = _ at step
    obtain ⟨⟨r,s⟩,hr,he⟩ := Option.map_eq_some_iff.mp step
    cases s with
    | move d =>
      change (pick r, TM0.Stmt.move d) = (q',TM0.Stmt.write b) at he
      cases he
    | write z =>
      change (pick r,TM0.Stmt.write z) = (q',TM0.Stmt.write b) at he
      have eq : z=b := TM0.Stmt.write.inj (congrArg Prod.snd he)
      exact eq ▸ guard q.val q.property a r z hr
  · intro x
    obtain ⟨r,stop⟩ := run x
    have sim := TM0.Machine.map_respects M sym sym (⟨pick,Subtype.ext (proj _ hs.1)⟩ : PointedMap L Q)
      Subtype.val hs (fun _ => rfl) proj
    have lift (q : L) (xs : List Track) :
        TM0.Cfg.map sym pick (⟨q,Tape.mk₁ xs⟩ : TM0.Cfg Track L) = ⟨pick q,Tape.mk₁ xs⟩ := by
      simp [TM0.Cfg.map,Tape.map_mk₁,sym]
    have eq : TM0.Cfg.map sym pick (TM0.init (Λ := L) (image x)) = TM0.init (Λ := Q) (image x) := by
      unfold TM0.init
      rw [lift]
      exact congrArg (fun q => TM0.Cfg.mk q (Tape.mk₁ (image x))) (Subtype.ext (proj _ hs.1))
    obtain ⟨b,⟨_,equ⟩,ok⟩ := Turing.tr_eval sim ⟨hs.1,eq⟩ stop
    subst b
    rw [lift] at ok
    exact ⟨_,ok⟩

end P455MathlibFinite
