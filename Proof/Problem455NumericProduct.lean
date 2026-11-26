import Problem455TableSemantics

/- A first-order direct-product serializer. Runtime values are solely
natural numbers, lists of numbers and matrices. -/
namespace P455NumericProduct
open P455Table P455FirstRewrite P455FirstTesters

def grid (n : Nat) (f : Nat → Nat → Nat) : Matrix :=
  (List.range n).map fun i => (List.range n).map fun j => f i j

def tensor (T U : Matrix) : Matrix :=
  let d := U.length
  grid (T.length*d) (fun i j => entry U (i%d) (j%d) + entry T (i/d) (j/d)*d)

def singleton : Matrix := [[0]]

def assemble (factors : List Matrix) : Matrix := factors.foldr tensor singleton

def pack (i : Fin n) (j : Fin m) : Fin (n*m) := ⟨j.val+i.val*m,by
  have h := Nat.mul_le_mul_right m i.isLt
  rw [Nat.succ_mul] at h
  have v := j.isLt; omega⟩

def major (hm : 0<m) (k : Fin (n*m)) : Fin n := ⟨k.val/m,(Nat.div_lt_iff_lt_mul hm).mpr k.isLt⟩
def minor (hm : 0<m) (k : Fin (n*m)) : Fin m := ⟨k.val%m,Nat.mod_lt _ hm⟩

theorem major_pack (hm : 0<m) (i : Fin n) (j : Fin m) : major hm (pack i j)=i := by
  apply Fin.ext
  simp [major,pack,Nat.add_mul_div_right _ _ hm,Nat.div_eq_of_lt j.isLt]

theorem minor_pack (hm : 0<m) (i : Fin n) (j : Fin m) : minor hm (pack i j)=j := by
  apply Fin.ext; simp [minor,pack,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt j.isLt]

theorem pack_parts (hm : 0<m) (k : Fin (n*m)) : pack (major hm k) (minor hm k)=k := by
  apply Fin.ext
  change k.val%m+k.val/m*m=k.val
  rw [Nat.mul_comm (k.val/m) m,Nat.mod_add_div]

def positive (Y : FiniteOps) : 0<Y.size := Nat.lt_of_le_of_lt (Nat.zero_le _) Y.one.isLt

def prodOps (X Y : FiniteOps) : FiniteOps :=
  ⟨X.size*Y.size,pack X.one Y.one,fun i j =>
    pack (X.mul (major (positive Y) i) (major (positive Y) j))
      (Y.mul (minor (positive Y) i) (minor (positive Y) j))⟩

def prodPresents {M : Model A} {N : Model B} {X Y} (p : Presents X M) (q : Presents Y N) :
    Presents (prodOps X Y) (combine M N) where
  decode k := (p.decode (major (positive Y) k),q.decode (minor (positive Y) k))
  inj i j eq := by
    have u := p.inj _ _ (congrArg Prod.fst eq)
    have v := q.inj _ _ (congrArg Prod.snd eq)
    calc i = pack (major (positive Y) i) (minor (positive Y) i) := (pack_parts ..).symm
         _ = pack (major (positive Y) j) (minor (positive Y) j) := by rw [u,v]
         _ = j := pack_parts ..
  surj := by
    rintro ⟨a,b⟩
    obtain ⟨i,hi⟩ := p.surj a; obtain ⟨j,hj⟩ := q.surj b
    exact ⟨pack i j,by simp [major_pack,minor_pack,hi,hj]⟩
  one_eq := by simp [prodOps,major_pack,minor_pack,combine,p.one_eq,q.one_eq]
  mul_eq := by intro i j; simp [prodOps,major_pack,minor_pack,combine,p.mul_eq,q.mul_eq]

theorem tensor_matrix (X Y : FiniteOps) :
    tensor (matrix X) (matrix Y)=matrix (prodOps X Y) := by
  apply List.ext_getElem (by simp [tensor,grid,prodOps])
  intro i hi _
  have ib : i<X.size*Y.size := by simpa [tensor,grid] using hi
  let a : Fin (X.size*Y.size) := ⟨i,ib⟩
  apply List.ext_getElem (by simp [tensor,grid,matrix,prodOps])
  intro j hj _
  have jb : j<X.size*Y.size := by simpa [tensor,grid,matrix] using hj
  let b : Fin (X.size*Y.size) := ⟨j,jb⟩
  have l := matrix_entry X (major (positive Y) a) (major (positive Y) b)
  have r := matrix_entry Y (minor (positive Y) a) (minor (positive Y) b)
  simp only [major,minor,a,b] at l r
  simp only [tensor,grid,matrix_length,List.getElem_map,List.getElem_range]
  rw [l,r]
  simp only [matrix,List.getElem_map,List.getElem_finRange]
  rfl

def unitOps : FiniteOps := ⟨1,0,fun _ _ => 0⟩
def unitModel : Model Unit where
  op _ _ := ()
  unit := ()
  assoc _ _ _ := rfl
  oneL _ := rfl
  oneR _ := rfl

def unitPresents : Presents unitOps unitModel where
  decode _ := ()
  inj i j _ := Fin.ext (by have a := i.isLt; have b := j.isLt; change i.val<1 at a; change j.val<1 at b; omega)
  surj _ := ⟨⟨0,Nat.zero_lt_one⟩,rfl⟩
  one_eq := rfl
  mul_eq _ _ := rfl

/-- This specification is used only in the proof, not in the serializer. -/
def Represents (T : Matrix) (M : Model A) := ∃ X, T=matrix X ∧ Nonempty (Presents X M)

theorem represents_tensor {M : Model A} {N : Model B} {T U} (a : Represents T M) (b : Represents U N) :
    Represents (tensor T U) (combine M N) := by
  obtain ⟨X,rfl,⟨p⟩⟩ := a; obtain ⟨Y,rfl,⟨q⟩⟩ := b
  exact ⟨prodOps X Y,tensor_matrix _ _,⟨prodPresents p q⟩⟩

structure Coordinate where
  carrier : Type
  model : Model carrier
  raw : Matrix

def carrier : List Coordinate → Type
  | [] => Unit
  | c::cs => c.carrier × carrier cs

def family : (cs : List Coordinate) → Model (carrier cs)
  | [] => unitModel
  | c::cs => combine c.model (family cs)

/-- This holds for the full list with multiplicities, including empty and
singleton families. The raw fold depends only on the lists of numbers. -/
theorem assemble_represents (cs : List Coordinate)
    (ok : ∀ c∈cs,Represents c.raw c.model) : Represents (assemble (cs.map Coordinate.raw)) (family cs) := by
  induction cs with
  | nil => exact ⟨unitOps,rfl,⟨unitPresents⟩⟩
  | cons c cs ih =>
    exact represents_tensor (ok c List.mem_cons_self) (ih (fun z hz => ok z (List.mem_cons_of_mem _ hz)))

end P455NumericProduct
