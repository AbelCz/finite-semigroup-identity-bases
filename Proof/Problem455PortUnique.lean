import Problem455GridRows
import Problem455ActualGuards

/- The one-mark guards genuinely give uniqueness of an entire target
   record, including its tag. The graph may therefore use nodes, not
   merely the unordered set of their two variable names. -/
namespace P455PortUnique
open P455Witness P455Paths P455SourceFamilies P455CrossedSupport P455SlotSaturation
open P455SingletonEvaluation P455ActualGuards P455GuardProduct P455PortReflection Problem455.Slots
abbrev W := List Nat

private theorem tag_unique {a b : Nat} (ne : a ≠ b) (s t : Tag) (p q : W)
    (len : s.length=t.length) (eq : s.flatMap (pair a b) ++ p = t.flatMap (pair a b) ++ q) : s=t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons x s ih =>
    cases t with
    | nil => simp at len
    | cons y t =>
      have lk : s.length=t.length := by simpa using len
      cases x <;> cases y <;> simp [List.flatMap_cons,pair,List.append_assoc,ne,Ne.symm ne] at eq ⊢
      all_goals exact ih _ lk eq

theorem node_unique {r allow mark w} (a b : Node) (own : a.owner=b.owner) (mate : a.mate=b.mate)
    (oa : Holds r allow mark w (typedNode a)) (ob : Holds r allow mark w (typedNode b)) : a=b := by
  obtain ⟨x,y,s⟩ := a; obtain ⟨z,t,v⟩ := b
  dsimp at own mate; subst z; subst t
  obtain ⟨ne,len,_,i,hi⟩ := oa
  obtain ⟨_,len',_,j,hj⟩ := ob
  change s.length+16=r at len; change v.length+16=r at len'
  have e : profile x y s i = profile x y v j := hi.symm.trans hj
  let pre := [x,x,y,x,y,y] ++ (List.replicate 5 [x,y,x,y]).flatten
  let post := fun bit => [x,y] ++ (pair x y bit ++ [x,y])
  have eq : pre ++ (s.flatMap (pair x y) ++ post i) = pre ++ (v.flatMap (pair x y) ++ post j) := by
    simpa only [pre,post,profile,profilePrefix,List.append_assoc] using e
  have := tag_unique ne s v _ _ (by omega) (List.append_cancel_left eq)
  cases this; rfl

theorem functional {r allow mark ts u₀ w v x y} (cap₀ : P455Closure.Cap r u₀)
    (valid : (product r allow ts).Valid u₀ w) (changed : select [x,y] u₀ ≠ select [x,y] w)
    (path : P455Quotient.Walk (P455Closure.Move r allow noMark) u₀ v)
    (cmp : Compressed r v) (n : Node) (side : Matches n x y)
    (rec : Holds r allow mark v (typedNode n)) : P455GridRows.Functional r allow mark v ts n := by
  intro dir a b nb nc
  obtain ⟨ne,len,tag,bit,proj⟩ := rec
  have anchor : Holds r allow (markNode n) v (markedNode n bit) := ⟨ne,len,tag,.inl ⟨rfl,rfl⟩,proj⟩
  have roleeq (k : Bool) : roleOf k a = roleOf k b := by
    apply Classical.byContradiction; intro d
    let f : FunctionalityCertificate := ⟨n,bit,a,b,dir,k⟩
    exact no_guard cap₀ valid changed path (.func f) side
      ⟨anchor,neighbor_remark nb,neighbor_remark nc,compressed_separates cmp d,True.intro⟩
  exact node_unique a b (roleeq false) (roleeq true) (neighbor_target_record nb) (neighbor_target_record nc)

end P455PortUnique
