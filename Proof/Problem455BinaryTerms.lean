import Problem455TableSemantics

/- A free-semigroup word and a binary multiplication term describe the
   same identity modulo associativity. There is no constant constructor. -/
namespace P455BinaryTerms
open P455FirstRewrite P455Table P455TableSemantics

inductive Term where
  | var (i : Nat)
  | mul (s t : Term)
  deriving DecidableEq

def flat : Term → W
  | .var i => [i]
  | .mul s t => flat s ++ flat t

theorem nonempty (t : Term) : flat t≠[] := by induction t <;> simp_all [flat]

def fromHead (x : Nat) : W → Term
  | [] => .var x
  | y::w => .mul (.var x) (fromHead y w)

def fromWord : W → Term
  | [] => .var 0
  | x::xs => fromHead x xs

@[simp] theorem flat_head (x : Nat) (w : W) : flat (fromHead x w)=x::w := by
  induction w generalizing x with
  | nil => rfl
  | cons y ys ih => simp [fromHead,flat,ih]

theorem flat_from {w : W} (ne : w≠[]) : flat (fromWord w)=w := by
  cases w with | nil => contradiction | cons x xs => exact flat_head _ _

def inst (f : Nat → Term) : Term → Term
  | .var i => f i
  | .mul s t => .mul (inst f s) (inst f t)

theorem flat_inst (f : Nat → Term) (t : Term) :
    flat (inst f t)=(flat t).flatMap (fun i => flat (f i)) := by
  induction t <;> simp_all [inst,flat,List.flatMap_append]

/-- Ordinary equational deduction in semigroups. The associativity
    constructor is the instance of one three-variable binary identity. -/
inductive Proof (G : Term → Term → Prop) : Term → Term → Prop
  | refl (x) : Proof G x x
  | symm : Proof G x y → Proof G y x
  | trans : Proof G x y → Proof G y z → Proof G x z
  | gen : G x y → Proof G x y
  | mul : Proof G x y → Proof G z t → Proof G (.mul x z) (.mul y t)
  | subst (f) : Proof G x y → Proof G (inst f x) (inst f y)
  | assoc (x y z) : Proof G (.mul (.mul x y) z) (.mul x (.mul y z))

private theorem join (G) (a : Nat) (A : W) (b : Nat) (B : W) :
    Proof G (.mul (fromHead a A) (fromHead b B)) (fromHead a (A++b::B)) := by
  induction A generalizing a with
  | nil => exact .refl _
  | cons x xs ih => exact .trans (.assoc _ _ _) (.mul (.refl _) (ih x))

theorem norm (G) (x : Term) : Proof G x (fromWord (flat x)) := by
  induction x with
  | var x => exact .refl _
  | mul s t hs ht =>
    apply Proof.trans (.mul hs ht)
    obtain ⟨a,A,ea⟩ := List.exists_cons_of_ne_nil (nonempty s)
    obtain ⟨b,B,eb⟩ := List.exists_cons_of_ne_nil (nonempty t)
    simp only [flat,ea,eb,fromWord,List.cons_append]
    exact join G a A b B

theorem assoc_eq (G) {s t : Term} (e : flat s=flat t) : Proof G s t :=
  (norm G s).trans (e.symm ▸ (norm G t).symm)

def frame (l r : W) (t : Term) : Term :=
  let left := if l=[] then t else .mul (fromWord l) t
  if r=[] then left else .mul left (fromWord r)

theorem flat_frame (l r : W) (t : Term) : flat (frame l r t)=l++flat t++r := by
  by_cases a : l=[] <;> by_cases b : r=[] <;> simp [frame,a,b,flat,flat_from]

theorem proof_frame {G} (l r : W) {x y} (e : Proof G x y) :
    Proof G (frame l r x) (frame l r y) := by
  by_cases a : l=[] <;> by_cases b : r=[] <;> simp [frame,a,b] <;>
    first | exact e | exact .mul (.refl _) e | exact .mul e (.refl _)
          | exact .mul (.mul (.refl _) e) (.refl _)

theorem step_in_terms {G : W → W → Prop} {H} (rules : ∀ u v, G u v → Proof H (fromWord u) (fromWord v))
    {a b : W} (step : Step G a b) : Proof H (fromWord a) (fromWord b) := by
  obtain ⟨u,v,l,r,h,rule,un,vn,ne,rfl,rfl⟩ := step
  let f (i : Nat) := fromWord (h i)
  have fold (w : W) (wn : w≠[]) : flat (frame l r (inst f (fromWord w)))=l++w.flatMap h++r := by
    have ef : (fun i => flat (f i))=h := funext fun i => flat_from (ne i)
    rw [flat_frame,flat_inst,flat_from wn,ef]
  have align (w : W) (wn : w≠[]) :
      Proof H (fromWord (l++w.flatMap h++r)) (frame l r (inst f (fromWord w))) := by
    have pos : l++w.flatMap h++r≠[] := by rw [←fold w wn]; exact nonempty _
    exact assoc_eq H ((flat_from pos).trans (fold w wn).symm)
  have middle : Proof H (fromWord u) (fromWord v) :=
    rule.elim (fun m => rules _ _ m) (fun m => (rules _ _ m).symm)
  exact (align u un).trans ((proof_frame l r (.subst f middle)).trans (align v vn).symm)

theorem words_to_terms {G : W → W → Prop} {H} (rules : ∀ u v, G u v → Proof H (fromWord u) (fromWord v))
    {a b : W} (path : Derives G a b) : Proof H (fromWord a) (fromWord b) := by
  induction path with
  | refl => exact .refl _
  | snoc _ e ih => exact ih.trans (step_in_terms rules e)

theorem terms_to_words {G : W → W → Prop} {H} (rules : ∀ u v, H u v → Derives G (flat u) (flat v))
    {a b} (path : Proof H a b) : Derives G (flat a) (flat b) := by
  induction path with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm (fun e => P455ReductionBoundary.sym_step e)
  | trans _ _ ih ik => exact ih.trans ik
  | gen e => exact rules _ _ e
  | @mul x y z t _ _ ih ik =>
    exact (by simpa using P455Prefix.context_derives [] (flat z) ih :
      Derives G (flat x++flat z) (flat y++flat z)).trans
      (by simpa using P455Prefix.context_derives (flat y) [] ik)
  | subst f _ ih =>
    simp only [flat_inst]
    exact P455Prefix.substitute_deduction _ (fun i => nonempty (f i)) ih
  | assoc x y z => simp [flat,List.append_assoc,P455Quotient.Walk.refl]

end P455BinaryTerms
