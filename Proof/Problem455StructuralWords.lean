import Problem455FirstTesters
import Problem455CompressedFrame




namespace P455Structural
open P455Witness P455Quotient P455Closure P455Uncrossed Problem455.Slots
open P455SourceFamilies P455FirstTesters
abbrev W := List Nat

def Rec (T : W) (r : Nat) (allow : Tag → Prop) (a b : Nat) :=
  ∃ tag, Holds r allow (fun _ _ => False) T (.record a b tag)
def Edge (T : W) (r : Nat) (allow : Tag → Prop) (a b : Nat) :=
  Rec T r allow a b ∨ Rec T r allow b a
def Width (k : Nat) (T : W) := ∃ C : W, C.length ≤ k ∧ ∀ x ∈ T, x ∈ C
def Overlap (T : W) (r : Nat) (allow : Tag → Prop) :=
  ∃ o p q, o ≠ p ∧ o ≠ q ∧ p ≠ q ∧ Edge T r allow o p ∧ Edge T r allow o q
def Intrusion (T : W) (r : Nat) (allow : Tag → Prop) :=
  ∃ o p z j, o ≠ p ∧ z ≠ o ∧ z ≠ p ∧ Rec T r allow o p ∧ sees T [(o,0),(z,j),(p,2)]
def Structural (T : W) (r : Nat) (allow : Tag → Prop) :=
  (Width 4 T ∧ Overlap T r allow) ∨ (Width 3 T ∧ Intrusion T r allow)
def early (a b : Nat) : W := [a,a,b,a,b,b]
def Closed (T : W) (a b : Nat) :=
  a ≠ b ∧ ∃ L R : W, T = L ++ early a b ++ R ∧ a ∉ L ∧ b ∉ L

private theorem only_z (x z : Nat) (L : W) (nx : x ∉ L) :
    select [x,z] L = List.replicate (L.count z) z := by
  induction L with
  | nil => rfl
  | cons c t ih =>
    have nt : x ∉ t := fun h => nx (List.mem_cons_of_mem _ h)
    have cx : c ≠ x := fun e => nx (e ▸ List.mem_cons_self)
    by_cases cz : c = z <;> simp_all [select,List.count_cons,List.replicate_succ]

private theorem early_projection {a b x z : Nat} {T : W} (closed : Closed T a b)
    (inPair : x = a ∨ x = b) (outside : z ≠ a ∧ z ≠ b) :
    ∃ n R, select [x,z] T = List.replicate n z ++ [x,x,x] ++ R := by
  obtain ⟨ab,L,R,rfl,na,nb⟩ := closed
  refine ⟨L.count z,select [x,z] R,?_⟩
  rcases inPair with rfl|rfl <;> rw [select_append,select_append,only_z _ _ _ (by assumption)] <;>
    simp [select,early,ab,Ne.symm ab,Ne.symm outside.1,Ne.symm outside.2]

private theorem not_record_tail {x z : Nat} (xz : x ≠ z) (n : Nat) (tail : W) (tag : Tag) (bit : Bool) :
    List.replicate n z ++ [x,x,x] ++ tail ≠ profile x z tag bit ∧
    List.replicate n z ++ [x,x,x] ++ tail ≠ profile z x tag bit := by
  cases n with
  | zero => simp [profile,profilePrefix,xz]
  | succ n =>
    cases n with
    | zero => simp [profile,profilePrefix,xz,Ne.symm xz,List.replicate_succ]
    | succ n =>
      cases n with
      | zero => simp [profile,profilePrefix,xz,Ne.symm xz,List.replicate_succ]
      | succ n => simp [profile,profilePrefix,xz,Ne.symm xz,List.replicate_succ]

theorem no_external_record {r allow a b T} (closed : Closed T a b) {x z : Nat}
    (inside : x = a ∨ x = b) (out : z ≠ a ∧ z ≠ b) : ¬ Edge T r allow x z := by
  obtain ⟨n,tail,eq⟩ := early_projection closed inside out
  have nz : x ≠ z := by omega
  rintro (⟨t,_,_,_,bit,profileEq⟩|⟨t,_,_,_,bit,profileEq⟩)
  · exact (not_record_tail nz n tail t bit).1 (eq.symm.trans profileEq)
  · exact (not_record_tail nz n tail t bit).2 (eq.symm.trans ((select_pair_symm x z T).symm.trans profileEq))

private theorem early_bound {T : W} {a b o p z j : Nat} (closed : Closed T a b)
    (oi : o=a ∨ o=b) (pi' : p=a ∨ p=b) (out : z ≠ a ∧ z ≠ b) :
    ¬ sees T [(o,0),(z,j),(p,2)] := by
  obtain ⟨ab,L,R,rfl,na,nb⟩ := closed
  intro obs
  have no : o ∉ L := oi.elim (fun e => e ▸ na) (fun e => e ▸ nb)
  have cp : (early a b).count p = 3 := by
    rcases pi' with rfl|rfl <;> simp [early,List.count_cons,ab,Ne.symm ab]
  let inner := (events (early a b)).map (shift (fun x => L.count x))
  let right := stamp (fun x => L.count x + (early a b).count x) R
  have h : [(o,0),(z,j),(p,2)].Sublist (events L ++ (inner ++ right)) := by
    simpa only [sees,events_of_factor,inner,right] using obs
  have nl : (o,0) ∉ events L := fun m => no (stamped_mem_label _ _ _ m)
  have nr : (p,2) ∉ right := by
    intro m
    have low := (P455ContactGeometry.stamp_range (fun x => L.count x + (early a b).count x) R m).1
    omega
  have strip {α : Type} (x : α) (pat u v : List α) (nx : x ∉ u)
      (sub : (x::pat).Sublist (u++v)) : (x::pat).Sublist v := by
    induction u with
    | nil => exact sub
    | cons c u ih =>
      cases sub with
      | cons _ s => exact ih (fun m => nx (List.mem_cons_of_mem _ m)) s
      | cons₂ => exact False.elim (nx List.mem_cons_self)
  have h1 := (strip _ _ _ _ nl h).reverse
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at h1
  have h2 := (strip _ _ right.reverse inner.reverse (by simpa using nr) h1).reverse
  have mid : (z,j) ∈ inner := by simpa using h2.subset (show (z,j) ∈ ([(p,2),(z,j),(o,0)] : List Event).reverse by simp)
  obtain ⟨e,me,eq⟩ := List.mem_map.mp mid
  have ze : e.1 = z := congrArg Prod.fst eq
  have is := stamped_mem_label _ _ _ me
  simp [early,ze,out.1,out.2] at is

private theorem rec_mem {T r allow a b} (h : Rec T r allow a b) : a ∈ T ∧ b ∈ T := by
  obtain ⟨t,_,_,_,bit,eq⟩ := h
  have f (x : Nat) (hx : x=a ∨ x=b) : x ∈ T := by
    have mm : x ∈ profile a b t bit := by rcases hx with rfl|rfl <;> simp [profile,profilePrefix]
    rw [← eq] at mm
    exact (List.mem_filter.mp mm).1
  exact ⟨f a (.inl rfl),f b (.inr rfl)⟩

private theorem edge_mem {T r allow a b} (h : Edge T r allow a b) : a ∈ T ∧ b ∈ T :=
  h.elim rec_mem (fun q => (rec_mem q).symm)

private theorem closed_mem {T a b} (h : Closed T a b) : a ∈ T ∧ b ∈ T := by
  obtain ⟨_,l,t,rfl,_,_⟩ := h
  simp [early]

private theorem separated_core {T r allow a b o p} (c : Closed T a b) (edge : Edge T r allow o p) :
    (o=a ∨ o=b) ↔ (p=a ∨ p=b) := by
  constructor
  · intro h
    apply Classical.byContradiction; intro n
    exact no_external_record c h ⟨fun e => n (.inl e),fun e => n (.inr e)⟩ edge
  · intro h
    apply Classical.byContradiction; intro n
    exact no_external_record c h ⟨fun e => n (.inl e),fun e => n (.inr e)⟩ edge.symm



theorem structural_excludes_closed {r allow T a b} (stest : Structural T r allow) (c : Closed T a b) : False := by
  obtain ⟨ma,mb⟩ := closed_mem c
  have ab := c.1
  rcases stest with ⟨⟨C,len,Cmem⟩,o,p,q,op,oq,pq,e1,e2⟩|⟨⟨C,len,Cmem⟩,o,p,z,j,op,zo,zp,rec',seen⟩
  · have linkP := separated_core c e1
    have linkQ := separated_core c e2
    by_cases h : o=a ∨ o=b
    · have hp := linkP.mp h; have hq := linkQ.mp h; omega
    · have A := edge_mem e1; have B := edge_mem e2
      have uniq : [a,b,o,p,q].Nodup := by simp [List.nodup_cons]; omega
      have sub (x) (m : x ∈ [a,b,o,p,q]) : x ∈ C := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at m
        rcases m with rfl|rfl|rfl|rfl|rfl <;> apply Cmem <;> simp_all
      have := P455FirstRewrite.size_le uniq sub
      simp at this; omega
  · have link := separated_core c (Or.inl rec' : Edge T r allow o p)
    by_cases h : o=a ∨ o=b
    · have hp := link.mp h
      apply early_bound c h hp _ seen
      omega
    · have A := rec_mem rec'
      have uniq : [a,b,o,p].Nodup := by simp [List.nodup_cons]; omega
      have sub (x) (m : x ∈ [a,b,o,p]) : x ∈ C := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at m
        rcases m with rfl|rfl|rfl|rfl <;> apply Cmem <;> simp_all
      have := P455FirstRewrite.size_le uniq sub
      simp at this; omega

end P455Structural
