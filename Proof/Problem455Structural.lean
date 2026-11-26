import Problem455StructuralWords

 
namespace P455Structural
open P455Witness P455Quotient P455Closure P455Uncrossed Problem455.Slots
open P455SourceFamilies P455FirstTesters

private theorem image_edge (h : Nat → W) (x a b : Nat)
    (pos : 0 < Problem455Swap.bigram a b (h x)) (u : W) :
    u.count x ≤ Problem455Swap.bigram a b (u.flatMap h) := by
  induction u with
  | nil => simp [Problem455Swap.bigram]
  | cons z u ih =>
    simp only [List.flatMap_cons,Problem455Swap.bigram_append]
    by_cases e : z=x
    · subst z; simp [List.count_cons]; omega
    · simp [List.count_cons,e]; omega

private theorem singleton_in_template {r : Nat} {T p q u : W} {h : Nat → W} {x : Nat}
    (eq : T = p ++ u.flatMap h ++ q) (cap : P455Closure.Cap r T) (cmp : Compressed r T)
    (cx : u.count x = r) (nonempty : h x ≠ []) : ∃ a, h x = [a] := by
  cases z : h x with
  | nil => exact False.elim (nonempty z)
  | cons a t =>
    cases t with
    | nil => exact ⟨a,rfl⟩
    | cons b t =>
      have pair : 0 < Problem455Swap.bigram a b (h x) := by
        rw [z]; simp [Problem455Swap.bigram,Problem455Swap.hit]; omega
      have base := image_edge h x a b pair u
      have low : r ≤ Problem455Swap.bigram a b T := by
        rw [eq,Problem455Swap.bigram_append,Problem455Swap.bigram_append]; omega
      have top := Problem455Swap.out_bound a b (b+1) (by omega) T
      rw [Problem455BlockBridge.occ_count] at top
      have high := cap a
      exact False.elim (cmp a b (by unfold Problem455Swap.Link; omega))

private theorem image_count {r : Nat} (h : Nat → W) (u : W) (x a : Nat)
    (c : u.count x = r) (img : h x = [a]) : r ≤ (u.flatMap h).count a := by
  have h := P455DonorInterval.split_contributions h u x a
  simp [img,c] at h
  omega

/-- Under any substitution, a live factor in a structural tester gives
literal equality of the two substituted words. All other images may be
empty or arbitrarily long and may use shared names. -/
theorem structural_factor {r T allow} (cap : P455Closure.Cap r T) (cmp : Compressed r T)
    (stest : Structural T r allow) (f : Frame Nat) (l k : W) (bit : Bool) (x y : Nat)
    (hp : f.p = [x]) (hq : f.q = [y]) (valid : f.Valid r allow (fun _ _ => False))
    (h : Nat → W) (fac : Factor ((side f l k bit).flatMap h) T) :
    (side f l k bit).flatMap h = (side f l k (!bit)).flatMap h := by
  obtain ⟨pre,post,eq⟩ := fac
  have eqCore : T = (pre ++ l.flatMap h) ++ (f.core bit).flatMap h ++ (k.flatMap h ++ post) := by
    simpa [side,List.flatMap_append,List.append_assoc] using eq
  have count (z : Nat) (role : z = x ∨ z = y) : (f.core bit).count z = r := by
    have has : z ∈ f.p ∨ z ∈ f.q := by simpa [hp,hq] using role
    have orig := valid.2.2.2.2.2.2.2 z has
    cases bit with
    | false => exact orig
    | true => exact (f.count_core z true).trans orig
  have commute : h x ++ h y = h y ++ h x := by
    by_cases nx : h x = []
    · simp [nx]
    by_cases ny : h y = []
    · simp [ny]
    obtain ⟨a,ax⟩ := singleton_in_template eqCore cap cmp (count x (.inl rfl)) nx
    obtain ⟨b,by'⟩ := singleton_in_template eqCore cap cmp (count y (.inr rfl)) ny
    by_cases ab : a=b
    · simp [ax,by',ab]
    exfalso
    apply structural_excludes_closed stest
    let L := pre ++ l.flatMap h
    have fresh (z s : Nat) (kind : z=x ∨ z=y) (im : h z = [s]) : s ∉ L := by
      have bound := cap s
      rw [eqCore] at bound
      have ct := image_count h (f.core bit) z s (count z kind) im
      apply List.count_eq_zero.mp
      dsimp [L]
      simp only [List.count_append] at bound ⊢
      omega
    let tail := f.mid ++ f.beforeMutable ++ f.pair bit ++ f.beforeFinalP ++ f.p ++ f.beforeFinalQ ++ f.q
    have shape : f.core bit = f.early ++ tail := by simp [Frame.core,tail,List.append_assoc]
    refine ⟨ab,L,tail.flatMap h ++ (k.flatMap h ++ post),?_,fresh x a (.inl rfl) ax,fresh y b (.inr rfl) by'⟩
    rw [eqCore,shape]
    simp [L,Frame.early,hp,hq,List.flatMap_append,List.flatMap_cons,ax,by',List.append_assoc,early]
  cases bit <;>
    simp only [side,Frame.core,Frame.pair,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true,hp,hq,List.append_nil] <;>
    rw [commute]

private theorem plain_factor {r : Nat} {T u : W} (g : Good (plain r) T u) : Factor u T := by
  obtain ⟨v,walk,fac⟩ := g
  have e : T=v := by induction walk with
                      | refl => rfl
                      | snoc _ impossible _ => exact False.elim impossible
  exact e ▸ fac

/-- Universal equality in the actual Rees factor monoid of each structural
template. Zero evaluations, either live orientation and arbitrary good
representatives are handled through the quotient evaluation. -/
theorem structural_eval {r T allow} (cap : P455Closure.Cap r T) (cmp : Compressed r T)
    (stest : Structural T r allow) (f : Frame Nat) (l k : W) (x y : Nat)
    (hp : f.p=[x]) (hq : f.q=[y]) (valid : f.Valid r allow (fun _ _ => False))
    (val : Nat → Q (plain r) T) :
    eval (plain r) cap val (side f l k false) = eval (plain r) cap val (side f l k true) := by
  classical
  apply Classical.byContradiction
  intro d
  let R := plain r
  have live : ∃ b : Bool, eval R cap val (side f l k b) ≠ zero R T := by
    by_cases nz : eval R cap val (side f l k false) ≠ zero R T
    · exact ⟨false,nz⟩
    · exact ⟨true,fun eq => d ((Classical.not_not.mp nz).trans eq.symm)⟩
  obtain ⟨b,nz⟩ := live
  let u := side f l k b
  have existsRep (a : Nat) (ha : a ∈ u) :=
    nonzero_representative R (val a) (live_inputs R cap val _ nz a ha)
  let h (a : Nat) := if yes : a ∈ u then (existsRep a yes).choose else []
  have rep (a) (mem : a ∈ u) : ofWord R T (h a) = val a := by
    simpa only [h,dif_pos mem] using (existsRep a mem).choose_spec.2
  have original := eval_rep R cap val u h rep
  have separated := structural_factor cap cmp stest f l k b x y hp hq valid h
    (plain_factor ((nonzero_iff R).mp (original ▸ nz)))
  have other := eval_rep R cap val (side f l k (!b)) h
    (fun a ha => rep a ((same_letters f l k b a).mpr ha))
  have done := original.trans ((congrArg (ofWord R T) separated).trans other.symm)
  cases b
  · exact d done
  · exact d done.symm

end P455Structural
