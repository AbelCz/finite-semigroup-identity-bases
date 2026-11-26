import Problem455WriterEdgeSearch
import Problem455WriterQueryLeaves
import Problem455WriterAdjacency

set_option maxHeartbeats 25000
namespace P455WriterEdge
open P455Witness P455PaddedTiles P455WriterQueryLeaves

abbrev roles (a : Node) := [a.owner,a.mate]
def order2 (e : Env) (a i b j : Nat) := order e [(a,i),(b,j)]
def nodeRecord (e : Env) (a : Node) := record e a.owner a.mate a.tag
def nodeMarked (e : Env) (a : Node) (bit : Bool) := marked e a.owner a.mate a.tag bit

def port (e : Env) (p : Nat) (a b : Node) :=
  let i := 3+2*p
  nodeRecord e a && (nodeRecord e b && (P455WriterQueryLeaves.earlyDisjoint e (roles a) (roles b) &&
    order e [(a.owner,i),(a.mate,i),(b.owner,i),(b.mate,i),(a.owner,i+1),(a.mate,i+1),(b.owner,i+1),(b.mate,i+1)]))

theorem port_ok (h : ModelsEnv e r allow mark w) (p a b) :
    port e p a b=true ↔ Holds r allow mark w (orientedPort p a b) := by
  simp only [port,nodeRecord,Bool.and_eq_true,record_ok h,earlyDisjoint_ok h,order_ok h]
  change (_ ∧ (_ ∧ (_ ∧ _))) ↔ (_ ∧ (_ ∧ (_ ∧ (_ ∧ True))))
  exact Iff.intro (fun ⟨a,b,c,d⟩ => ⟨a,b,c,d,trivial⟩) (fun ⟨a,b,c,d,_⟩=>⟨a,b,c,d⟩)

def rightB (e : Env) (n : Nat) (a b : Node) :=
  P455WriterTiles.horizontal n a.tag b.tag && (port e (if (system n).oddColumn a.tag then 1 else 0) a b &&
    order2 e a.owner (13+a.tag.length) b.owner (13+a.tag.length))
def downB (e : Env) (n : Nat) (a b : Node) :=
  P455WriterTiles.vertical n a.tag b.tag && port e (if (system n).oddRow a.tag then 3 else 2) a b

def neighborB (e : Env) (n : Nat) (a b : Node) : Dir → Bool
  | .right => rightB e n a b | .left => rightB e n b a | .down => downB e n a b | .up => downB e n b a

theorem right_ok (h : ModelsEnv e r allow mark w) (n a b) : rightB e n a b=true ↔ Holds r allow mark w (rightward (system n) a b) := by
  simp only [rightB,order2,Bool.and_eq_true,P455WriterTiles.horizontal_correct,port_ok h,order_ok h]
  exact Iff.intro (fun ⟨a,b,c⟩=>⟨a,b,c,trivial⟩) (fun ⟨a,b,c,_⟩=>⟨a,b,c⟩)
theorem down_ok (h : ModelsEnv e r allow mark w) (n a b) : downB e n a b=true ↔ Holds r allow mark w (downward (system n) a b) := by
  simp only [downB,Bool.and_eq_true,P455WriterTiles.vertical_correct,port_ok h]; rfl
theorem neighbor_ok (h : ModelsEnv e r allow mark w) (n a b d) : neighborB e n a b d=true ↔ Holds r allow mark w (neighbor (system n) a b d) := by
  cases d with
  | right => exact right_ok h n a b
  | left => exact right_ok h n b a
  | down => exact down_ok h n a b
  | up => exact down_ok h n b a

def role (b : Bool) (a : Node) := if b then a.mate else a.owner
def funcB (e : Env) (n : Nat) (f : FunctionalityCertificate) :=
  nodeMarked e f.anchor f.bit && (neighborB e n f.anchor f.b f.dir && (neighborB e n f.anchor f.c f.dir &&
    separate e (role f.distinguishMate f.b) (role f.distinguishMate f.c)))

theorem func_ok (h : ModelsEnv e r allow mark w) (n f) : funcB e n f=true ↔ Holds r allow mark w (f.query (system n)) := by
  simp only [funcB,nodeMarked,Bool.and_eq_true,marked_ok h,neighbor_ok h,separate_ok h]
  exact Iff.intro (fun ⟨a,b,c,d⟩=>⟨a,b,c,d,trivial⟩) (fun ⟨a,b,c,d,_⟩=>⟨a,b,c,d⟩)

def funcAccept (e : Env) (n a b : Nat) :=
  (P455Enum.functionalities e.2.2.2 e.2.1).any fun f => decide (f.anchor.owner=a ∧ f.anchor.mate=b) && funcB e n f

theorem funcAccept_ok (M : MachineTable n) (h : ModelsEnv e r (allowed M) mark w) (tags : e.2.1=P455Enum.tags M) (a b) :
    funcAccept e n a b=true ↔ ∃ f : FunctionalityCertificate, f.anchor.owner=a ∧ f.anchor.mate=b ∧ Holds r (allowed M) mark w (f.query (system n)) := by
  simp only [funcAccept,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,func_ok h,h.word,tags]
  constructor
  · rintro ⟨f,_,⟨ha,hb⟩,hf⟩; exact ⟨f,ha,hb,hf⟩
  · rintro ⟨f,ha,hb,hf⟩; exact ⟨f,P455Enum.func_mem M f hf,⟨ha,hb⟩,hf⟩

end P455WriterEdge
