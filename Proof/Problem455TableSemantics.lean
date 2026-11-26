import Problem455Table



namespace P455TableSemantics
open P455Table P455FirstRewrite

def SemigroupTable (T : Matrix) : Prop :=
  0<T.length ∧ (∀ row∈T, row.length=T.length ∧ ∀ a∈row, a<T.length) ∧
  ∀ a b c, a<T.length → b<T.length → c<T.length →
    entry T (entry T a b) c=entry T a (entry T b c)

def HasUnit (T : Matrix) := ∃ u<T.length, ∀ i<T.length, entry T u i=i ∧ entry T i u=i

theorem output_laws {A : Type} {X : FiniteOps} {M : Model A} (p : Presents X M) :
    SemigroupTable (matrix X) ∧ HasUnit (matrix X) := by
  have assoc (a b c : Fin X.size) : X.mul (X.mul a b) c=X.mul a (X.mul b c) := by
    apply p.inj
    simp only [p.mul_eq,M.assoc]
  refine ⟨⟨by simpa using Nat.lt_of_le_of_lt (Nat.zero_le _) X.one.isLt,
    by simpa only [matrix_length] using square X,?_⟩,?_⟩
  · intro a b c ha hb hc
    let i : Fin X.size := ⟨a,by simpa using ha⟩
    let j : Fin X.size := ⟨b,by simpa using hb⟩
    let k : Fin X.size := ⟨c,by simpa using hc⟩
    change entry _ (entry _ i j) k=entry _ i (entry _ j k)
    simp only [matrix_entry]
    exact congrArg Fin.val (assoc i j k)
  · refine ⟨X.one.val,by simp,?_⟩
    intro i hi
    let j : Fin X.size := ⟨i,by simpa using hi⟩
    change entry _ X.one j=j.val ∧ entry _ j X.one=j.val
    simp only [matrix_entry]
    constructor
    · exact congrArg Fin.val (p.inj _ _ (by rw [p.mul_eq,p.one_eq,M.oneL]))
    · exact congrArg Fin.val (p.inj _ _ (by rw [p.mul_eq,p.one_eq,M.oneR]))

def value (T : Matrix) (f : Nat → Nat) : Nat → List Nat → Nat
  | a, [] => f a
  | a, b::w => entry T (f a) (value T f b w)

def wordValue (T : Matrix) (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a::w => value T f a w

def Valid (T : Matrix) (u v : List Nat) := ∀ f : Nat → Nat, (∀ x, f x<T.length) →
    wordValue T f u=wordValue T f v

def HasBasis (T : Matrix) := ∃ rules : List (List Nat × List Nat),
    (∀ u v, (u,v)∈rules → u≠[] ∧ v≠[] ∧ Valid T u v) ∧
    ∀ u v, u≠[] → v≠[] → Valid T u v → Derives (fun a b => (a,b)∈rules) u v

def code (X : FiniteOps) (f : Nat → Fin X.size) : Nat → List Nat → Fin X.size
  | x, [] => f x
  | x, y::ys => X.mul (f x) (code X f y ys)

theorem read_code (X : FiniteOps) (f : Nat → Fin X.size) (x : Nat) (w : List Nat) :
    value (matrix X) (fun a => (f a).val) x w=(code X f x w).val := by
  induction w generalizing x with
  | nil => rfl
  | cons y ys ih => exact (congrArg (entry _ (f x).val) (ih y)).trans (matrix_entry X _ _)

theorem decode_code {X : FiniteOps} {M : Model A} (p : Presents X M) (f : Nat → Fin X.size)
    (x : Nat) (w : List Nat) : p.decode (code X f x w)=M.eval (fun a => p.decode (f a)) (x::w) := by
  induction w generalizing x with
  | nil => simp [code,Model.eval,M.oneR]
  | cons y ys ih =>
    change p.decode (X.mul _ _)=M.op _ _
    rw [p.mul_eq,ih]

theorem valid_iff {X : FiniteOps} {M : Model A} (p : Presents X M) (u v : List Nat)
    (un : u≠[]) (vn : v≠[]) : Valid (matrix X) u v ↔ M.Valid u v := by
  obtain ⟨a,U,rfl⟩ := List.exists_cons_of_ne_nil un
  obtain ⟨b,V,rfl⟩ := List.exists_cons_of_ne_nil vn
  constructor
  · intro h g
    let f (i : Nat) := Classical.choose (p.surj (g i))
    have counts := h (fun x => (f x).val) (fun i => by simp)
    change value _ _ _ _=value _ _ _ _ at counts
    rw [read_code,read_code] at counts
    have E := congrArg p.decode (Fin.ext counts)
    rw [decode_code,decode_code] at E
    have fg : (fun i => p.decode (f i))=g := funext fun i => Classical.choose_spec (p.surj (g i))
    simpa only [fg] using E
  · intro h g bounded
    let f (i : Nat) : Fin X.size := ⟨g i,by simpa using bounded i⟩
    change value _ (fun i => (f i).val) _ _=value _ (fun i => (f i).val) _ _
    rw [read_code,read_code]
    exact congrArg Fin.val (p.inj _ _ ((decode_code p f a U).trans
      ((h (fun i => p.decode (f i))).trans (decode_code p f b V).symm)))

theorem basis_iff {X : FiniteOps} {M : Model A} (p : Presents X M) :
    HasBasis (matrix X) ↔ P455Global.HasBasis M := by
  constructor <;> rintro ⟨rules,sound,complete⟩ <;> refine ⟨rules,?_,?_⟩
  · intro u v m; obtain ⟨a,b,s⟩ := sound u v m
    exact ⟨a,b,(valid_iff p u v a b).mp s⟩
  · intro u v a b s; exact complete u v a b ((valid_iff p u v a b).mpr s)
  · intro u v m; obtain ⟨a,b,s⟩ := sound u v m
    exact ⟨a,b,(valid_iff p u v a b).mpr s⟩
  · intro u v a b s; exact complete u v a b ((valid_iff p u v a b).mp s)

end P455TableSemantics
