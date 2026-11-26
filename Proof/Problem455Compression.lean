import Problem455Retained




namespace P455Compression
open P455Witness P455Retained

inductive Piece where
  | literal (a : Nat)
  | gap (w : W)
  deriving DecidableEq

def body : Piece → W | .literal a => [a] | .gap w => w

def prependOutside (a : Nat) : List Piece → List Piece
  | .gap w :: tail => .gap (a::w) :: tail
  | cs => .gap [a] :: cs

def pieces (names : W) : W → List Piece
  | [] => []
  | a :: u =>
    let rest := pieces names u
    if a ∈ names then .literal a :: rest else prependOutside a rest

def good (names : W) : Piece → Prop
  | .literal a => a ∈ names
  | .gap w => w ≠ [] ∧ ∀ a ∈ w, a ∉ names

/-- Adjacency of gap pieces is prohibited; with good and exact decoding this
    expresses maximality of every omitted run, also at the two ends. -/
def noTouch : List Piece → Prop
  | .gap _ :: .gap _ :: _ => False
  | _ :: tail => noTouch tail
  | [] => True

private theorem prepend_body (a : Nat) (cs : List Piece) :
    (prependOutside a cs).flatMap body = a :: cs.flatMap body := by
  cases cs with
  | nil => rfl
  | cons p tail => cases p <;> rfl

theorem decoded (names u : W) : (pieces names u).flatMap body = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    by_cases c : a ∈ names
    · simp [pieces,c,body,ih]
    · simp [pieces,c,prepend_body,ih]

private theorem prepend_good {a : Nat} {cs : List Piece} {names : W} (ha : a ∉ names)
    (all : ∀ c ∈ cs, good names c) : ∀ c ∈ prependOutside a cs, good names c := by
  cases cs with
  | nil => simp [prependOutside,good,ha]
  | cons p tail =>
    cases p with
    | literal b => simp [prependOutside,good,ha] at *; exact all
    | gap w =>
      have h := all (.gap w) (by simp)
      simp only [good] at h
      simp only [prependOutside,List.forall_mem_cons,good,List.cons_ne_nil,not_false_eq_true,true_and]
      exact ⟨⟨by simp,ha,h.2⟩,fun c hc => all c (by simp [hc])⟩

theorem pieces_good (names u : W) : ∀ c ∈ pieces names u, good names c := by
  induction u with
  | nil => simp [pieces]
  | cons a u ih =>
    by_cases k : a ∈ names
    · simp only [pieces,if_pos k,List.forall_mem_cons]
      exact ⟨k,ih⟩
    · simpa only [pieces,if_neg k] using prepend_good k ih

private theorem prepend_sep {cs : List Piece} (a : Nat) (ok : noTouch cs) :
    noTouch (prependOutside a cs) := by
  cases cs with
  | nil => exact True.intro
  | cons p tail =>
    cases p with
    | literal b => exact ok
    | gap w => cases tail with
      | nil => exact True.intro
      | cons p' rest => cases p' <;> exact ok

theorem maximal (names u : W) : noTouch (pieces names u) := by
  induction u with
  | nil => exact True.intro
  | cons a u ih =>
    by_cases k : a ∈ names
    · simpa only [pieces,if_pos k,noTouch] using ih
    · simpa only [pieces,if_neg k] using prepend_sep a ih

/-- The numerical bound counts even retained names not occurring in u. -/
def base (u names : W) := u.sum + names.sum + 1

private theorem le_sum {a : Nat} {w : W} (ha : a ∈ w) : a ≤ w.sum := by
  induction w with
  | nil => simp at ha
  | cons b w ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp ha with h|h
    · omega
    · have := ih h; omega

def code : Nat → List Piece → W
  | _,[] => []
  | n,.literal a :: cs => a :: code (n+1) cs
  | n,.gap _ :: cs => n :: code (n+1) cs

def lookup : Nat → List Piece → Nat → W
  | _,[],a => [a]
  | n,.literal _ :: cs,a => lookup (n+1) cs a
  | n,.gap w :: cs,a => if a=n then w else lookup (n+1) cs a

def small (u names : W) := code (base u names) (pieces names u)
def expand (u names : W) := lookup (base u names) (pieces names u)

private theorem low_fixed (cs : List Piece) (a n : Nat) (low : a < n) :
    lookup n cs a = [a] := by
  induction cs generalizing n with
  | nil => rfl
  | cons p cs ih =>
    cases p <;> simp [lookup,show a ≠ n by omega,ih (n+1) (by omega)]

private theorem low_kept (cs : List Piece) (names : W)
    (all : ∀ c ∈ cs, good names c) (a n : Nat) (low : a < n) (use : a ∈ code n cs) :
    a ∈ names := by
  induction cs generalizing n with
  | nil => cases use
  | cons c cs ih =>
    have rest := ih (fun c hc => all c (by simp [hc])) (n+1) (by omega)
    cases c with
    | literal b =>
      rcases List.mem_cons.mp use with eq|mem
      · obtain rfl := eq; exact all (.literal a) (by simp)
      · exact rest mem
    | gap w =>
      rcases List.mem_cons.mp use with eq|mem
      · omega
      · exact rest mem

private theorem decode_code (cs : List Piece) (names : W) (n : Nat)
    (all : ∀ c ∈ cs, good names c) (large : ∀ a ∈ names, a < n) :
    (code n cs).flatMap (lookup n cs) = cs.flatMap body := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih =>
    have goodTail (p) (hp : p ∈ cs) : good names p := all _ (by simp [hp])
    have tail := ih (n+1) goodTail (fun a ha => by have := large a ha; omega)
    cases c with
    | literal a =>
      have low := large a (all (.literal a) (by simp))
      simp [code,lookup,low_fixed cs a (n+1) (by omega),body,tail]
    | gap w =>
      have miss : n ∉ code (n+1) cs := by
        intro h
        have := large n (low_kept cs names goodTail n (n+1) (by omega) h)
        omega
      have eq : (code (n+1) cs).flatMap (lookup n (.gap w :: cs)) =
          (code (n+1) cs).flatMap (lookup (n+1) cs) := by
        simp only [List.flatMap_def]
        apply congrArg List.flatten
        exact List.map_congr_left (fun a ha => by
          have dif : a ≠ n := fun d => miss (d ▸ ha)
          simp [lookup,dif])
      change lookup n (.gap w::cs) n ++ (code (n+1) cs).flatMap _ = w ++ cs.flatMap body
      rw [eq,tail]
      simp [lookup]

private theorem gap_code (cs : List Piece) (names : W) (n : Nat)
    (all : ∀ c ∈ cs, good names c) (large : ∀ a ∈ names, a < n) :
    ∀ g ∈ code n cs, g ∉ names →
    (code n cs).count g = 1 ∧ lookup n cs g ≠ [] ∧ ∀ a ∈ lookup n cs g, a ∉ names := by
  induction cs generalizing n with
  | nil => simp [code]
  | cons c cs ih =>
    intro g use outside
    have goodTail (p) (hp : p ∈ cs) : good names p := all _ (by simp [hp])
    have tail := ih (n+1) goodTail (fun a ha => by have := large a ha; omega) g
    cases c with
    | literal a =>
      have dif : g ≠ a := fun d => outside (d ▸ all (.literal a) (by simp))
      have occurs : g ∈ code (n+1) cs := by simpa [code,dif] using use
      simpa [code,lookup,List.count_cons,dif,Ne.symm dif] using tail occurs outside
    | gap w =>
      by_cases same : g=n
      · subst g
        have miss : n ∉ code (n+1) cs := fun u =>
          outside (low_kept cs names goodTail n (n+1) (by omega) u)
        have gw := all (.gap w) (by simp)
        simpa [code,lookup,List.count_cons,List.count_eq_zero.mpr miss,good] using gw
      · have occurs : g ∈ code (n+1) cs := by simpa [code,same] using use
        simpa [code,lookup,List.count_cons,same,Ne.symm same] using tail occurs outside

theorem recover (u names : W) : (small u names).flatMap (expand u names) = u :=
  (decode_code (pieces names u) names (base u names) (pieces_good names u)
    (fun a h => by have := le_sum h; unfold base; omega)).trans (decoded names u)

theorem canonical (u names : W) : Expansion (small u names) (expand u names) (fun a => a ∈ names) where
  literal x _ kept := low_fixed _ _ _ (by have := le_sum kept; unfold base; omega)
  gaps := gap_code (pieces names u) names (base u names) (pieces_good names u)
    (fun a h => by have := le_sum h; unfold base; omega)

/-- Every generated gap name lies outside the original alphabet. -/
theorem gap_fresh (u names : W) (g : Nat) (use : g ∈ small u names) (unkept : g ∉ names) : g ∉ u := by
  intro orig
  apply unkept
  apply low_kept (pieces names u) names (pieces_good names u) g (base u names) _ use
  have := le_sum orig
  unfold base; omega

theorem counts_retained (u names : W) (x : Nat) (hx : x ∈ names) :
    (small u names).count x = u.count x := by
  have c := (canonical u names).count_eq (small u names) (fun _ h => h) x hx
  rw [recover] at c
  exact c.symm

end P455Compression
