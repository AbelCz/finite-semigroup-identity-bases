import Problem455ConstantProduct



namespace P455CellClassBinary
open Problem455.Slots P455Witness P455FirstTesters P455FirstRewrite P455MarkedRank
open P455BinaryEquality P455BinaryProduct P455SlotSaturation P455ProfileComponent
abbrev W := List Nat

theorem exact_counts {r allow ts U V} (cap : P455Quotient.Cap r U)
    (h : (P455FullSingleton.model r allow ts).Valid U V) (x : Nat) :
    U.count x = V.count x := by
  have ct := (tester_rule (valid_left _ _ h)).unary x
  have bd := cap x
  omega

private theorem named {r allow ts U V} (h : (P455FullSingleton.model r allow ts).Valid U V)
    (i : P455BinaryProduct.Index r allow) (f : Nat → W) :
    P455Quotient.ofWord i.R i.T (U.flatMap f) = P455Quotient.ofWord i.R i.T (V.flatMap f) := by
  have idBin := ((valid_pair ..).mp (((valid_pair ..).mp ((valid_pair ..).mp h).2).2)).1
  let g (a : Nat) (j : P455BinaryProduct.Index r allow) := P455Quotient.ofWord j.R j.T (f a)
  have eq := congrFun (idBin g) i
  rw [eval_at,eval_at,P455Quotient.eval_rep i.R i.bound _ U f (fun _ _ => rfl),
    P455Quotient.eval_rep i.R i.bound _ V f (fun _ _ => rfl)] at eq
  exact eq

private theorem encoding (i j : Nat) (ne : i ≠ j) (U : W) :
    let E := U.flatMap (code i j)
    (∀ x ∈ E, x=0 ∨ x=1) ∧ E.count 0 = U.count i ∧ E.count 1 = U.count j ∧
    E.length = U.count i + U.count j ∧ E.map (fun z => if z=0 then i else j) = select [i,j] U := by
  induction U with
  | nil => simp [select]
  | cons a U ih =>
    obtain ⟨names,lo,hi,len,back⟩ := ih
    by_cases ai : a=i <;> by_cases aj : a=j <;>
      simp_all [List.flatMap_cons,code,List.count_cons,select,List.mem_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] <;> exact names

/-- A change of two-name projection in a capped word is necessarily the
    change of the single bit of one admitted binary profile. Either input
    name can be its owner. All other names of V are unrestricted. -/
theorem changed {r allow ts U V} (cap : P455Quotient.Cap r U)
    (h : (P455FullSingleton.model r allow ts).Valid U V) {x y : Nat} (ne : x ≠ y)
    (diff : select [x,y] U ≠ select [x,y] V) :
    ∃ a b tag bit, ((a=x ∧ b=y) ∨ (a=y ∧ b=x)) ∧ tag.length+16=r ∧ allow tag ∧
      select [x,y] U = profile a b tag bit ∧ select [x,y] V = profile a b tag (!bit) := by
  classical
  let f := code x y
  let T := U.flatMap f
  let S := V.flatMap f
  let d := fun z : Nat => if z=0 then x else y
  obtain ⟨names,c0,c1,len,decU⟩ := encoding x y ne U
  obtain ⟨_,_,_,_,decV⟩ := encoding x y ne V
  change T.map d = _ at decU
  change S.map d = _ at decV
  have neq : T ≠ S := fun same => diff (decU.symm.trans ((congrArg (List.map d) same).trans decV))
  change T.length = U.count x + U.count y at len
  have capT : P455Quotient.Cap r T := by
    intro z; by_cases mem : z ∈ T
    · rcases names z mem with rfl|rfl
      · exact c0 ▸ cap x
      · exact c1 ▸ cap y
    · simp [List.count_eq_zero.mpr mem]
  have capV : P455Quotient.Cap r V := fun i => (exact_counts cap h i) ▸ cap i
  have pr (a b : Nat) (w : W) : proj a b w = select [a,b] w := by simp [proj,select]
  have pos (a b : Nat) (dif : proj a b U ≠ proj a b V) :
      0 < U.count a ∧ 0 < U.count b := by
    obtain ⟨ea,eb⟩ := (tester_rule (valid_left _ _ h)).binary cap capV a b dif
    rcases Nat.eq_zero_or_pos r with zero|positive
    · have empty (u : W) (cp : P455Quotient.Cap r u) : u=[] := by
        cases u with
        | nil => rfl
        | cons z w => have := cp z; simp [zero] at this
      exact False.elim (dif (by rw [empty U cap, empty V capV]))
    · exact ⟨ea ▸ positive,eb ▸ positive⟩
  obtain ⟨px,py⟩ := pos x y (by simpa only [pr] using diff)
  have covered := Problem455Finite.covered [0,1] (2*r) T (by have := cap x; have := cap y; omega)
    (fun z m => by simpa using names z m)
  obtain ⟨n,en⟩ := List.get_of_mem covered
  let i : P455BinaryProduct.Index r allow := ⟨n,decide (IsProfile r allow T),en.symm ▸ capT,by
    rw [en]; exact ⟨.inr ⟨c0 ▸ px,c1 ▸ py⟩,decide_eq_true_iff⟩⟩
  have iT : i.T = T := en
  have ip : i.prof = decide (IsProfile r allow T) := rfl
  have same := named h i f
  change P455Quotient.ofWord i.R i.T T = P455Quotient.ofWord i.R i.T S at same
  have ps : IsProfile r allow T := by
    apply Classical.byContradiction
    intro no
    have rr : i.R = plain r := by simp [P455BinaryProduct.Index.R,ip,no]
    rw [iT,rr] at same
    have ok : P455Quotient.Good (plain r) T T := ⟨T,.refl _,[],[],by simp⟩
    have path := ((P455Quotient.same_nonzero_class _ ok).mp same).2
    exact neq (path.transport (P := fun z => T=z) rfl (fun bad _ => False.elim bad))
  have rr : i.R = rules r allow noMark := by simp [P455BinaryProduct.Index.R,ip,ps]
  rw [iT,rr] at same
  obtain ⟨a,b,tag,bit,ab,tl,ok,et⟩ := ps
  have live : P455Quotient.Good (rules r allow noMark) T T := ⟨T,.refl _,[],[],by simp⟩
  have path := ((P455Quotient.same_nonzero_class _ live).mp same).2
  rw [et] at path
  obtain ⟨v,es⟩ := (variants ab tl ok bit S).mp path
  have opp : v = !bit := by cases v <;> cases bit <;> simp_all
  have az := names a (show a ∈ T by simp [et,profile,profilePrefix])
  have bz := names b (show b ∈ T by simp [et,profile,profilePrefix])
  refine ⟨d a,d b,tag,bit,?_,tl,ok,?_,?_⟩
  · rcases az with h1|h1 <;> rcases bz with h2|h2 <;> simp_all [d]
  · exact decU.symm.trans ((congrArg (List.map d) et).trans (P455ContactReflection.map_profile ..))
  · rw [← decV,es,opp,P455ContactReflection.map_profile]

end P455CellClassBinary
