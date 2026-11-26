import Problem455Uncrossed
import Problem455Compression



namespace P455CompressedFrame
open P455Closure P455Compression P455Uncrossed

private theorem prepend_cut (a x : Nat) (cs tail : List Piece) :
    prependOutside a (cs ++ .literal x :: tail) =
      prependOutside a cs ++ .literal x :: tail := by
  cases cs with
  | nil => rfl
  | cons p cs => cases p <;> rfl

private theorem pieces_cut (names u v : W) (x : Nat) (hx : x ∈ names) :
    pieces names (u ++ x :: v) = pieces names u ++ .literal x :: pieces names v := by
  induction u with
  | nil => simp [pieces,hx]
  | cons a u ih =>
    by_cases k : a ∈ names
    · simp [pieces,k,ih]
    · simp [pieces,k,ih,prepend_cut]

private theorem code_append (n : Nat) (p q : List Piece) :
    code n (p ++ q) = code n p ++ code (n+p.length) q := by
  induction p generalizing n with
  | nil => simp [code]
  | cons e p ih => cases e <;> simp [code,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private def enc (names : W) (n : Nat) (w : W) := code n (pieces names w)
private def span (names w : W) := (pieces names w).length
private theorem enc_cut {names : W} {x : Nat} (hx : x ∈ names) (n : Nat) (u v : W) :
    enc names n (u ++ x :: v) = enc names n u ++ x :: enc names (n+span names u+1) v := by
  simp only [enc,span,pieces_cut _ _ _ _ hx,code_append,code]

private theorem enc_cons {names : W} {x : Nat} (hx : x ∈ names) (n : Nat) (v : W) :
    enc names n (x :: v) = x :: enc names (n+1) v := by simp [enc,pieces,hx,code]

private def pick (x y : Nat) (b : Bool) := if b then y else x
private def middleWord (x y : Nat) (es : List (W × Bool)) : W :=
  es.flatMap fun e => e.1 ++ [pick x y e.2]

private def encodeMiddle (names : W) (n : Nat) : List (W × Bool) → List (W × Bool)
  | [] => []
  | (u,b)::es => (enc names n u,b) :: encodeMiddle names (n+span names u+1) es

private def finish (names : W) (n : Nat) : List (W × Bool) → Nat
  | [] => n
  | (u,_)::es => finish names (n+span names u+1) es

private theorem enc_middle {names : W} {x y : Nat} (hx : x ∈ names) (hy : y ∈ names)
    (n : Nat) (es : List (W × Bool)) (tail : W) :
    enc names n (middleWord x y es ++ tail) =
      middleWord x y (encodeMiddle names n es) ++ enc names (finish names n es) tail := by
  induction es generalizing n with
  | nil => simp [middleWord,encodeMiddle,finish]
  | cons e es ih =>
    obtain ⟨gap,b⟩ := e
    have hk : pick x y b ∈ names := by cases b <;> simp [pick,hx,hy]
    change enc names n (((gap ++ [pick x y b]) ++ middleWord x y es) ++ tail) =
      (((enc names n gap ++ [pick x y b]) ++ middleWord x y (encodeMiddle names _ es)) ++
      enc names (finish names _ es) tail)
    simp only [List.append_assoc,List.singleton_append,enc_cut hk,ih,List.cons_append,List.nil_append]

private theorem mid_tags (names : W) (n : Nat) (es : List (W × Bool)) :
    (encodeMiddle names n es).map Prod.snd = es.map Prod.snd := by
  induction es generalizing n with
  | nil => rfl
  | cons e es ih => cases e; simp [encodeMiddle,ih]

private theorem singleton_mid (f : Frame Nat) {x y : Nat} (hp : f.p = [x]) (hq : f.q = [y]) :
    f.mid = middleWord x y f.middle := by
  unfold Frame.mid middleWord
  congr 1
  funext e
  cases e.2 <;> simp [hp,hq,pick]

private def firstSuffix (f : Frame Nat) (l : W) (x y : Nat) :=
  l ++ [x,x,y,x,y,y] ++ middleWord x y f.middle ++ f.beforeMutable

private def lastSuffix (f : Frame Nat) (k : W) (x y : Nat) :=
  f.beforeFinalP ++ x :: (f.beforeFinalQ ++ y :: k)

private theorem literal_pair (f : Frame Nat) (l k : W) {x y : Nat} (hp : f.p = [x])
    (hq : f.q = [y]) (b : Bool) :
    side f l k b = firstSuffix f l x y ++ pick x y b :: pick x y (!b) :: lastSuffix f k x y := by
  cases b <;> simp [side,Frame.core,Frame.early,Frame.pair,firstSuffix,lastSuffix,hp,hq,
    singleton_mid f hp hq,pick,List.append_assoc]

private theorem sum_append (a b : W) : (a++b).sum = a.sum+b.sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih,Nat.add_assoc]

private theorem same_base (f : Frame Nat) (l k names : W) {x y : Nat} (hp : f.p = [x])
    (hq : f.q = [y]) (b : Bool) :
    base (side f l k b) names = base (side f l k false) names := by
  cases b <;> simp [literal_pair f l k hp hq,base,sum_append,pick,Nat.add_comm,
    Nat.add_left_comm,Nat.add_assoc]

private def make (f : Frame Nat) (names : W) (x y head : Nat) : Frame Nat :=
  let n := finish names head f.middle
  let p := n+span names f.beforeMutable+2
  { pHead := x, pTail := [], qInit := [], qLast := y, tag := f.tag,
    middle := encodeMiddle names head f.middle, beforeMutable := enc names n f.beforeMutable,
    beforeFinalP := enc names p f.beforeFinalP,
    beforeFinalQ := enc names (p+span names f.beforeFinalP+1) f.beforeFinalQ }

private theorem enc_frame (f : Frame Nat) (l k names : W) {x y : Nat} (hx : x ∈ names)
    (hy : y ∈ names) (hp : f.p = [x]) (hq : f.q = [y]) (start : Nat) :
    let head := start+span names l+6
    let n := finish names head f.middle
    let p := n+span names f.beforeMutable+2
    let q := p+span names f.beforeFinalP+1
    let g := make f names x y head
    ∀ b, enc names start (side f l k b) =
      side g (enc names start l) (enc names (q+span names f.beforeFinalQ+1) k) b := by
  dsimp only
  intro b
  let head := start+span names l+6
  let g := make f names x y head
  have gp : g.p = [x] := rfl
  have gq : g.q = [y] := rfl
  change _ = side g _ _ b
  cases b <;>
    simp only [literal_pair f l k hp hq,literal_pair g _ _ gp gq,firstSuffix,lastSuffix,
      pick,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      List.append_assoc,List.cons_append,List.nil_append] <;>
    rw [enc_cut hx,enc_cons hx,enc_cons hy,enc_cons hx,enc_cons hy,enc_cons hy,
      enc_middle hx hy] <;>
    first
    | rw [enc_cut hx,enc_cons hy,enc_cut hx,enc_cut hy]
    | rw [enc_cut hy,enc_cons hx,enc_cut hx,enc_cut hy]
  all_goals rfl

private theorem lookup_congr (pre p q : List Piece)
    (same : ∀ n, lookup n p = lookup n q) (n : Nat) :
    lookup n (pre ++ p) = lookup n (pre ++ q) := by
  induction pre generalizing n with
  | nil => exact same n
  | cons c cs ih =>
    cases c with
    | literal a => exact ih (n+1)
    | gap w => funext a; simp [lookup,congrFun (ih (n+1)) a]

/-- Both smaller words use the same expansion, including corresponding gap
    variables on either side of the mutable pair. -/
theorem same_expansion (f : Frame Nat) (l k names : W) {x y : Nat} (hx : x ∈ names)
    (hy : y ∈ names) (hp : f.p = [x]) (hq : f.q = [y]) (b : Bool) :
    expand (side f l k b) names = expand (side f l k false) names := by
  unfold expand
  rw [same_base f l k names hp hq b]
  cases b with
  | false => rfl
  | true =>
    rw [literal_pair f l k hp hq true,literal_pair f l k hp hq false]
    simp only [pick,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true,
      pieces_cut _ _ _ _ hx,pieces_cut _ _ _ _ hy,pieces,hx,hy,if_true]
    apply lookup_congr
    intro n
    rfl

/-- For any common retained list containing x and y, both canonical shorter
    words form one common valid literal singleton frame with equal contexts.
    Its one expansion simultaneously recovers the two original words. -/
theorem canonical_pair {r allow} (f : Frame Nat) (l k names : W) {x y : Nat}
    (hx : x ∈ names) (hy : y ∈ names) (hp : f.p = [x]) (hq : f.q = [y])
    (valid : f.Valid r allow (fun _ _ => False)) (origBit : Bool)
    (cap : Cap r (side f l k origBit)) :
    ∃ (g : Frame Nat) (left right : W),
      g.p = [x] ∧ g.q = [y] ∧ g.Valid r allow (fun _ _ => False) ∧
      (∀ b, small (side f l k b) names = side g left right b) ∧
      (∀ b, (side g left right b).flatMap (expand (side f l k origBit) names) = side f l k b) := by
  let start := base (side f l k false) names
  let head := start+span names l+6
  let n := finish names head f.middle
  let p := n+span names f.beforeMutable+2
  let q := p+span names f.beforeFinalP+1
  let g := make f names x y head
  let left := enc names start l
  let right := enc names (q+span names f.beforeFinalQ+1) k
  have gp : g.p = [x] := rfl
  have gq : g.q = [y] := rfl
  have eq (b : Bool) : small (side f l k b) names = side g left right b := by
    unfold small
    rw [same_base f l k names hp hq b]
    exact enc_frame f l k names hx hy hp hq start b
  have bound : Cap r (side g left right origBit) := by
    rw [← eq]
    apply (canonical (side f l k origBit) names).small_cap (by have := valid.1; omega)
    rw [recover]
    exact cap
  have v : g.Valid r allow (fun _ _ => False) := by
    apply g.valid_of_capped_shape valid.1 valid.2.1 _ _ _ _ _ origBit left right bound
    · exact (mid_tags names head f.middle).trans valid.2.2.1
    · simpa only [gp,← hp] using valid.2.2.2.1
    · simpa only [gq,← hq] using valid.2.2.2.2.1
    · simpa only [gp,gq,← hp,← hq] using valid.2.2.2.2.2.1
    · simp
  refine ⟨g,left,right,gp,gq,v,eq,?_⟩
  intro b
  rw [← eq,(same_expansion f l k names hx hy hp hq origBit).trans
    (same_expansion f l k names hx hy hp hq b).symm]
  exact recover _ _

end P455CompressedFrame
