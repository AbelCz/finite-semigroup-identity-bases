import Problem455SourceTheorem





set_option maxRecDepth 4096

namespace P455OverflowExample
open Problem455.Slots P455Witness P455Paths P455ContactLift P455SourceFamilies
open Problem455Swap

def occupants : W := [2,3,4,5,6]
def src : W :=
  let profileWord := profile 0 1 [] false
  profileWord.take 8 ++ occupants ++ profileWord.drop 8 ++
    (List.replicate 14 occupants).flatten ++ occupants.reverse
def h (x : Nat) : W := if x = 0 then [0,7] else [x]
def template : W := [8] ++ src.flatMap h ++ [9]
def allow (tag : Tag) : Prop := tag = []
def mark (a b : Nat) : Prop := a = 1 ∧ b = 0
def cert : SlotCertificate := {
  anchor := ⟨0,1,[]⟩
  bit := false
  startAtMate := false
  steps := [(1,.record [] false)]
  terminalIndex := 3
  defect := .overflow occupants
}
def color (a : Nat) := if a = 7 then 0 else a

private theorem link_mem {w : W} {a b : Nat} (lk : Link 16 w a b) : a ∈ w ∧ b ∈ w := by
  have lo := out_bound a b (b+1) (by omega) w
  have hi := in_bound a (a+1) b (by omega) w
  have sub := tail_occ_le b w
  simp only [Problem455BlockBridge.occ_count] at lo hi sub
  unfold Link at lk
  constructor <;> apply List.count_pos_iff.mp <;> omega

private theorem all_source (a : Nat) (ha : a ∈ src) : src.count a = 16 :=
  (by decide : ∀ b ∈ src, src.count b = 16) a ha

theorem cap : P455Closure.Cap 16 template := by
  intro a
  by_cases mem : a ∈ template
  · have bound := (by decide : ∀ c ∈ template, c < 10) a mem
    have cts : ∀ b : Fin 10, template.count b.val ≤ 16 := by decide
    exact cts ⟨a,bound⟩
  · rw [List.count_eq_zero.mpr mem]; decide

set_option maxRecDepth 4096 in
private theorem same_color {a b : Nat} (lk : Link 16 template a b) : color a = color b := by
  obtain ⟨ma,mb⟩ := link_mem lk
  have bound : ∀ c ∈ template, c < 10 := by decide
  have table : ∀ x y : Fin 10, bigram x.val y.val template = 16 → color x.val = color y.val := by decide
  exact table ⟨a,bound a ma⟩ ⟨b,bound b mb⟩ lk

private theorem block_color {a b : Nat} (same : SameBlock 16 template a b) : color a = color b := by
  suffices h : ∀ {x y}, Problem455Swap.Joined (Link 16 template) x y → color x = color y from h same.2.2
  intro x y chain
  induction chain with
  | refl => rfl
  | extend path edge ih =>
    rcases edge with f|b
    · exact ih.trans (same_color f)
    · exact ih.trans (same_color b).symm

set_option maxRecDepth 4096 in
theorem compressed_source : Compressed 16 src := by
  intro a b lk
  obtain ⟨ma,mb⟩ := link_mem lk
  have bound : ∀ c ∈ src, c < 7 := by decide
  have table : ∀ x y : Fin 7, bigram x.val y.val src ≠ 16 := by decide
  exact table ⟨a,bound a ma⟩ ⟨b,bound b mb⟩ lk

set_option maxRecDepth 4096 in
theorem initial : Holds 16 allow mark template (cert.query 16) := by
  have proj : select [0,1] template = profile 0 1 [] false := by decide
  have marked : Holds 16 allow mark template (markedNode cert.anchor false) :=
    ⟨by decide,rfl,rfl,.inr ⟨rfl,rfl⟩,proj⟩
  have rec : Holds 16 allow mark template (contact 16 0 1 (.record [] false)) :=
    ⟨by decide,rfl,rfl,false,proj⟩
  have distinguish : (1 :: occupants).Pairwise (fun a b => color a ≠ color b) := by decide
  have sep := distinguish.imp (fun diff eq => diff (block_color eq))
  have hits : ∀ b ∈ occupants, template.count b = 16 ∧
      sees template [(1,3),(b,0),(1,4)] := by unfold sees; decide
  refine ⟨marked,by change 1 ≤ 6; decide,⟨rec,?_⟩,True.intro⟩
  exact ⟨rfl,(P455TerminalTransfer.block_separation _).mpr sep,
         (allQ_iff _).mpr (by
           intro q hq; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
           obtain ⟨ct,occ⟩ := hits b hb
           exact ⟨ct,by simp [cert,slotStart],⟨0,occ⟩⟩),True.intro⟩

theorem seed : Supplies src h 16 0 (picked cert) := ⟨by decide,by decide⟩
theorem guarded : Guard 16 allow mark src 0 6 := guard_uniform all_source

theorem crossed : (0 ∈ h 0 ∧ 1 ∈ h 1) ∧ ((h 0).length = 2 ∧ mark 1 0) ∧
    src.take 6 = [0,0,1,0,1,1] ∧ template.length = (src.flatMap h).length + 2 := by unfold mark; decide

theorem mutable_pair :
    src = src.take 33 ++ [0,1] ++ src.drop 35 ∧
      (src.take 33).count 0 = 14 ∧ (src.take 33).count 1 = 14 := by decide

theorem source_certificate : let s' := sendSlot (donor src h 16) cert
    Holds 16 allow (markNode s'.anchor) src (s'.query 16) := by
  have lit := slot_source (l := [8]) (k := [9]) (by decide : 0 < 16) cap cert initial seed guarded
  exact lit.2.2.2 compressed_source

theorem evaluation_live :
    P455Quotient.eval (rules 16 allow mark) cap (fun a => P455Quotient.ofWord (rules 16 allow mark) template (h a)) src
      ≠ P455Quotient.zero (rules 16 allow mark) template := by
  rw [P455Quotient.eval_rep (rules 16 allow mark) cap _ src h (fun _ _ => rfl)]
  apply (P455Quotient.nonzero_iff _).mpr
  exact ⟨template,.refl _,[8],[9],rfl⟩

/-- Nonvacuity of the integrated original-word theorem for a positively
    seeded actual overflow tester and a nonempty contact route. Here every
    source variable is uniform, so the retained expansion is the identity. -/
theorem original_gadget_witness (ts : Tiles) :
    let c := Certificate.slot cert
    let d := donor src h 16
    ∃ z l k, P455Quotient.Variant (rules 16 allow mark) template z ∧
      z = l ++ src.flatMap h ++ k ∧ Holds 16 allow mark z (c.query 16 ts) ∧
      Holds 16 allow (P455SourceTheorem.sourceMarks d c) src
        ((P455SourceTheorem.transferred d c).query 16 ts) := by
  let ident := fun x : Nat => [x]
  have expand : P455Retained.Expansion src ident (fun _ => True) :=
    ⟨fun _ _ _ => rfl,fun _ _ f => (f True.intro).elim⟩
  have identity : src.flatMap ident = src := by simp [ident]
  have original : P455OriginalWalk.OriginalGuard 16 allow mark (src.flatMap ident) (fun _ => True) 0 6 := by
    rw [identity]
    intro x near
    exact ⟨True.intro,fun i slot y occupied => ⟨True.intro,guarded x near i slot y occupied⟩⟩
  have smallCap : P455Closure.Cap 16 src := by
    intro a
    by_cases use : a ∈ src
    · rw [all_source a use]; decide
    · rw [List.count_eq_zero.mpr use]; decide
  have top := P455SourceTheorem.arbitrary_reps_original_gadget
    (r := 16) (T := template) (allow := allow) (mark := mark)
    cap (fun a => P455Quotient.ofWord (rules 16 allow mark) template (h a)) src h
    (fun _ _ => rfl) evaluation_live ts (.slot cert) initial false false 0 (by decide)
    seed expand (identity.symm ▸ smallCap) original
  obtain ⟨z,l,k,path,eq,out,_,query,_⟩ := top
  rw [identity] at query
  exact ⟨z,l,k,path,eq,out,query compressed_source⟩

end P455OverflowExample
