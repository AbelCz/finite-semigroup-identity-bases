import Problem455EffectiveQTable
/- Raw first-order quotient tables. Each row is labeled by one canonical
   raw representative. The dense table itself contains only naturals. -/
namespace P455EffectiveQRaw
open P455Quotient P455EffectiveQ P455Table P455TableProduct
abbrev Raw := Option W

def distinctRaw (rel : Raw → Raw → Bool) : List Raw → List Raw
  | [] => []
  | a::xs => if xs.any (rel a) then distinctRaw rel xs else a::distinctRaw rel xs

def labels (e : W → W → Bool) (T : W) :=
  distinctRaw (relB e T) (none :: (words T).map some)

def index (e : W → W → Bool) (T : W) (x : Raw) :=
  (labels e T).findIdx fun y => relB e T x y

def rows (e : W → W → Bool) (T : W) :=
  (labels e T).map fun a => (labels e T).map fun b => index e T (mulRaw a b)



theorem same (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) (a b : Raw) : relB e T a b=true ↔ cls R T a=cls R T b :=
  (rel_iff R e correct T a b).trans ⟨fun h => Quotient.sound (s := setoid R T) h,fun h => Quotient.exact h⟩

theorem map_distinct (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) (xs : List Raw) :
    (distinctRaw (relB e T) xs).map (cls R T) =
    @distinct (Q R T) (P455EffectiveQ.decEq R e correct T) (xs.map (cls R T)) := by
  letI := P455EffectiveQ.decEq R e correct T
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have test : xs.any (relB e T a)=true ↔ cls R T a ∈ xs.map (cls R T) := by
      simp only [List.any_eq_true,List.mem_map,same R e correct]
      exact exists_congr fun x => and_congr_right fun _ => eq_comm
    by_cases hx : cls R T a∈xs.map (cls R T)
    · simp [distinctRaw,distinct,hx,test.mpr hx,ih]
    · have neg : xs.any (relB e T a)=false := Bool.eq_false_iff.mpr (fun h => hx (test.mp h))
      simp [distinctRaw,distinct,hx,neg,ih]

theorem map_labels (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) : (labels e T).map (cls R T) =
    @distinct _ (P455EffectiveQ.decEq R e correct T) (Problem455Finite.carrier R T) := by
  simpa [labels,Problem455Finite.carrier,words,zero,ofWord,Function.comp_def] using
    map_distinct R e correct T (none :: (words T).map some)

theorem all_labels (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) (q : Q R T) : q ∈ (labels e T).map (cls R T) := by
  letI := P455EffectiveQ.decEq R e correct T
  rw [map_labels R e correct]
  exact (mem_distinct _ _).mpr (Problem455Finite.carrier_complete R T q)

theorem labels_nodup (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) : ((labels e T).map (cls R T)).Nodup := by
  letI := P455EffectiveQ.decEq R e correct T
  rw [map_labels R e correct]
  exact nodup_distinct _

def number (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) (x : Raw) : Fin (labels e T).length :=
  ⟨index e T x,by
    apply List.findIdx_lt_length_of_exists
    obtain ⟨y,ym,eq⟩ := List.mem_map.mp (all_labels R e correct T (cls R T x))
    exact ⟨y,ym,(same R e correct T ..).mpr eq.symm⟩⟩

theorem decode_number (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) (x : Raw) : cls R T ((labels e T).get (number R e correct T x))=cls R T x := by
  apply ((same R e correct T ..).mp _).symm
  exact List.findIdx_getElem (w := (number R e correct T x).isLt)

def ops (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) : FiniteOps where
  size := (labels e T).length
  one := number R e correct T (some [])
  mul i j := number R e correct T (mulRaw ((labels e T).get i) ((labels e T).get j))

def presentation (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) (cap : Cap R.r T) : Presents (ops R e correct T) (quotientModel R T cap) where
  decode i := cls R T ((labels e T).get i)
  one_eq := decode_number R e correct T (some [])
  mul_eq i j := decode_number R e correct T _
  inj i j eq := by
    apply Fin.ext
    let xs := (labels e T).map (cls R T)
    have il : i.val < xs.length := by simpa only [xs,List.length_map] using (show i.val < (labels e T).length from i.isLt)
    have jl : j.val < xs.length := by simpa only [xs,List.length_map] using (show j.val < (labels e T).length from j.isLt)
    apply List.getElem?_inj (xs := xs) il (labels_nodup R e correct T)
    change xs[i.val]? = xs[j.val]?
    rw [List.getElem?_eq_getElem il,List.getElem?_eq_getElem jl]
    exact congrArg some (by simpa [xs] using eq)
  surj a := by
    obtain ⟨v,vm,h⟩ := List.mem_map.mp (all_labels R e correct T a)
    obtain ⟨i,hi,atI⟩ := List.getElem_of_mem vm
    exact ⟨⟨i,hi⟩,(congrArg (cls R T) atI).trans h⟩

private theorem tabulate (xs : List α) (f : α → β) :
    (List.finRange xs.length).map (fun i => f (xs.get i))=xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i lt rt; simp

theorem matrix_eq (R : Rules Nat) (e : W → W → Bool) (correct : ∀ u v,e u v=true ↔ R.step u v) (T : W) : matrix (ops R e correct T)=rows e T := by
  unfold matrix rows ops
  change (List.finRange (labels e T).length).map (fun i => (List.finRange (labels e T).length).map
    (fun j => index e T (mulRaw ((labels e T).get i) ((labels e T).get j)))) = _
  let n := labels e T
  let row (a : Raw) := n.map fun b => index e T (mulRaw a b)
  have inner (i : Fin n.length) : (List.finRange n.length).map
      (fun j => index e T (mulRaw (n.get i) (n.get j))) = row (n.get i) :=
    tabulate n (fun b => index e T (mulRaw (n.get i) b))
  exact (List.map_congr_left (fun i _ => inner i)).trans (tabulate n row)

end P455EffectiveQRaw
