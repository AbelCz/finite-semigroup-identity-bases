import Problem455WriterEdgePorts
import Problem455WriterEdgeCatalogue

set_option maxHeartbeats 30000
namespace P455WriterEdge
open P455Witness P455PaddedTiles P455WriterQueryLeaves

def whenB (b p : Bool) := if b then p else true

theorem when_ok {e : Env} {v : Bool} {z : Query} (b : Bool) (h : v=true ↔ Holds e.1 allow mark w z) :
    whenB b v=true ↔ Holds e.1 allow mark w (flagQ b z) := by cases b <;> simp [whenB,flagQ,Holds,h]

def localB (env : Env) (n : Nat) (e : EdgeCertificate) :=
  let a := e.a
  let ts := system n
  whenB (!ts.right a.tag) (rightB env n a e.right) &&
    (whenB (!ts.left a.tag) (rightB env n e.left a) &&
    (whenB (!ts.bottom a.tag) (downB env n a e.down) &&
    (whenB (!ts.top a.tag) (downB env n e.up a) &&
     whenB (!ts.right a.tag && !ts.bottom a.tag) (downB env n e.right e.diagonal && rightB env n e.down e.diagonal))))

theorem local_ok (h : ModelsEnv env r allow mark w) (n) (e : EdgeCertificate) :
    localB env n e=true ↔ Holds r allow mark w (localCert (system n) e) := by
  have flag {v : Bool} {z : Query} (b : Bool) (hv : v=true ↔ Holds r allow mark w z) :
      whenB b v=true ↔ Holds r allow mark w (flagQ b z) := by cases b <;> simp [whenB,flagQ,Holds,hv]
  have diag : (downB env n e.right e.diagonal && rightB env n e.down e.diagonal)=true ↔
      Holds r allow mark w (.both (downward (system n) e.right e.diagonal) (rightward (system n) e.down e.diagonal)) := by
    simp only [Bool.and_eq_true,down_ok h,right_ok h]; rfl
  simp only [localB,Bool.and_eq_true,flag _ (right_ok h ..),flag _ (down_ok h ..),flag _ diag]
  simp only [localCert,allQ,Holds,and_true]

def chosenB (env : Env) (n : Nat) (e : EdgeCertificate) :=
  let a := e.a; let b := e.b; let ts := system n
  if endOfRow ts a && ts.bottom a.tag then
    (ts.top b.tag && ts.left b.tag && !ts.oddRow b.tag && !ts.oddColumn b.tag) &&
    ((port env 4 a b || port env 4 b a) && order2 env b.owner 0 a.owner 0)
  else
    let next := if endOfRow ts a then e.down else if ts.oddRow a.tag then e.left else e.right
    decide (next=b) && order2 env a.owner 0 b.owner 0

theorem chosen_ok (h : ModelsEnv env r allow mark w) (n) (e : EdgeCertificate) :
    chosenB env n e=true ↔ Holds r allow mark w (chosenSuccessor (system n) e) := by
  dsimp only [chosenB,chosenSuccessor]
  split <;> simp only [allQ,Holds,Bool.and_eq_true,Bool.or_eq_true,port_ok h,order2,order_ok h,
    earlier,decide_eq_true_eq,and_true]

def queryB (env : Env) (n : Nat) (e : EdgeCertificate) :=
  nodeMarked env e.a true && (nodeMarked env e.b false && (localB env n e && chosenB env n e))

theorem query_ok (h : ModelsEnv env r allow mark w) (n) (e : EdgeCertificate) :
    queryB env n e=true ↔ Holds r allow mark w (e.query (system n)) := by
  simp only [queryB,Bool.and_eq_true,nodeMarked,marked_ok h,local_ok h,chosen_ok h]
  simp only [EdgeCertificate.query,allQ,Holds,markedNode,and_true]

def sameNames (xs ys : List Nat) := xs.all (fun x => decide (x∈ys)) && ys.all (fun y => decide (y∈xs))
theorem same_ok (xs ys : List Nat) : sameNames xs ys=true ↔ ∀ x, x∈xs ↔ x∈ys := by
  simp only [sameNames,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  exact ⟨fun ⟨f,g⟩ x => ⟨f x,g x⟩, fun h => ⟨fun x => (h x).1,fun y => (h y).2⟩⟩

def env (r : Nat) (ts : List (List Bool)) (w : List Nat) (k : Quad) : Env := (r,ts,[(k.1,k.2.1),(k.2.2.1,k.2.2.2)],w)
def tests (r n : Nat) (ts : List (List Bool)) (w : List Nat) (k : Quad) :=
  P455EffectiveQMove.capB r w && (P455Enum.certificates w ts).any fun e =>
    decide (e.a.owner=k.1 ∧ e.a.mate=k.2.1 ∧ e.b.owner=k.2.2.1 ∧ e.b.mate=k.2.2.2) &&
    (sameNames w (P455EdgeProjection.names (system n) e) && queryB (env r ts w k) n e)

theorem tests_ok (M : MachineTable n) (hr : 0<r) (w k) :
    tests r n (P455Enum.tags M) w k=true ↔ ValidKey M r w k := by
  have h : ModelsEnv (env r (P455Enum.tags M) w k) r (allowed M)
      (P455EdgeProduct.marks k.1 k.2.1 k.2.2.1 k.2.2.2) w :=
    ⟨rfl,fun _ => P455Enum.mem_tags,fun _ _ => by rcases k with ⟨a,b,c,d⟩; simp [env,P455EdgeProduct.marks],rfl,hr⟩
  simp only [tests,Bool.and_eq_true,P455EffectiveQMove.cap_iff,List.any_eq_true,decide_eq_true_eq,
    same_ok,query_ok h,ValidKey]
  constructor
  · rintro ⟨cap,e,_,⟨a,b,c,d⟩,ns,hq⟩; exact ⟨cap,e,a,b,c,d,ns,hq⟩
  · rintro ⟨cap,e,a,b,c,d,ns,hq⟩
    obtain ⟨z,za,zb,ne,zq,hz⟩ := P455CatalogueBounds.bounded_edge cap (P455Enum.tags M)
      (fun _ ht => P455Enum.mem_tags.mpr ht) e hq
    exact ⟨cap,z,P455Enum.bounded_mem z hz,⟨za ▸ a,za ▸ b,zb ▸ c,zb ▸ d⟩,ne ▸ ns,zq⟩

def edges (r n : Nat) (ts : List (List Bool)) := family r (tests r n ts)

theorem edges_correct (M : MachineTable n) (hr : 0<r) : edges r n (P455Enum.tags M)=
    P455Packed.names (P455Encoded.useCover (P455Enum.edge hr M)) P455Packed.twoSpec :=
  family_correct M hr _ (tests_ok M hr)

end P455WriterEdge
