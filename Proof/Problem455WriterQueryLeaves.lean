import Problem455WriterBlockTest

namespace P455WriterQueryLeaves
open P455WriterTiles P455WriterProfiles P455WriterObservations Problem455.Slots
open P455Witness (Query Holds Tag Marking)
abbrev Env := Nat × Tags × List (Nat×Nat) × W

structure ModelsEnv (e : Env) (r : Nat) (allow : Tag → Prop) (mark : Marking) (w : W) : Prop where
  lim : e.1=r
  tags : ∀ t, t∈e.2.1 ↔ allow t
  marks : ∀ a b, (a,b)∈e.2.2.1 ↔ mark a b
  word : e.2.2.2=w
  pos : 0<r

def matched (e : Env) (a b : Nat) (t : Tag) (bit : Bool) :=
  decide (select [a,b] e.2.2.2=profile a b t bit)
def good (e : Env) (a b : Nat) (t : Tag) := decide (a≠b ∧ t.length+16=e.1 ∧ t∈e.2.1)
def record (e : Env) (a b : Nat) (t : Tag) := good e a b t && (matched e a b t false || matched e a b t true)
def marked (e : Env) (a b : Nat) (t : Tag) (bit : Bool) :=
  good e a b t && decide ((a,b)∈e.2.2.1 ∨ (b,a)∈e.2.2.1) && matched e a b t bit
def order (e : Env) (pat : List Event) :=
  pat.all (fun p => decide (p.2 ≠ e.1-2)) && decide (sees e.2.2.2 pat)
def separate (e : Env) (a b : Nat) := !(P455WriterBlocks.same e.1 e.2.2.2 a b)
def earlyBefore (e : Env) (xs ys : W) :=
  (choices xs ys).all fun p => order e [(p.1,2),(p.2,0)]
def earlyDisjoint (e : Env) (xs ys : W) := earlyBefore e xs ys || earlyBefore e ys xs

variable {e : Env} {r : Nat} {allow : Tag → Prop} {mark : Marking} {w : W}

theorem record_ok (h : ModelsEnv e r allow mark w) (a b t) :
    record e a b t=true ↔ Holds r allow mark w (.record a b t) := by
  simp only [record,good,matched,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,h.lim,h.word,h.tags,Holds,typed]
  constructor
  · rintro ⟨⟨ne,len,ok⟩,u|v⟩
    · exact ⟨ne,len,ok,false,u⟩
    · exact ⟨ne,len,ok,true,v⟩
  · rintro ⟨ne,len,ok,bit,z⟩
    exact ⟨⟨ne,len,ok⟩,by cases bit <;> simp_all⟩

theorem marked_ok (h : ModelsEnv e r allow mark w) (a b t bit) :
    marked e a b t bit=true ↔ Holds r allow mark w (.markedBit a b t bit) := by
  simp only [marked,good,matched,Bool.and_eq_true,decide_eq_true_eq,h.lim,h.word,h.tags,h.marks,Holds,and_assoc]

theorem order_ok (h : ModelsEnv e r allow mark w) (pat) :
    order e pat=true ↔ Holds r allow mark w (.order pat) := by
  simp only [order,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,h.lim,h.word,Holds]

theorem separate_ok (h : ModelsEnv e r allow mark w) (a b) :
    separate e a b=true ↔ Holds r allow mark w (.separate a b) := by
  simp only [separate,Bool.not_eq_true',Holds,h.lim,h.word,←P455WriterBlocks.same_ok h.pos]
  cases P455WriterBlocks.same r w a b <;> simp

theorem earlyBefore_ok (h : ModelsEnv e r allow mark w) (xs ys) :
    earlyBefore e xs ys=true ↔ Holds r allow mark w (P455Witness.earlyBefore xs ys) := by
  rw [P455PortReflection.earlyBefore_iff]
  simp only [earlyBefore,choices,List.all_eq_true,List.mem_flatMap,List.mem_map]
  constructor
  · intro t a ha b hb
    exact (order_ok h _).mp (t (a,b) ⟨a,ha,b,hb,rfl⟩)
  · rintro t _ ⟨a,ha,b,hb,rfl⟩
    exact (order_ok h _).mpr (t a ha b hb)

theorem earlyDisjoint_ok (h : ModelsEnv e r allow mark w) (xs ys) :
    earlyDisjoint e xs ys=true ↔ Holds r allow mark w (P455Witness.earlyDisjoint xs ys) := by
  simp only [earlyDisjoint,Bool.or_eq_true,earlyBefore_ok h,P455Witness.earlyDisjoint,Holds]

variable {A X : Type} [Primcodable A] [Primcodable X]
theorem memRec [DecidableEq X] {x : A → X} {l : A → List X} [inst : ∀ a, Decidable (x a∈l a)]
    (hx : Primrec x) (hl : Primrec l) : Primrec fun a => @decide _ (inst a) := by
  have v := P455GraphPrim.anyB hl
    ((Primrec.eq.comp (hx.comp (Primrec.fst (β := X))) Primrec.snd).to₂)
  apply Primrec.of_eq v
  intro a
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

theorem limRec {f : A → Env} (hf : Primrec f) : Primrec fun x => (f x).1 := Primrec.fst.comp hf
theorem tagsRec {f : A → Env} (hf : Primrec f) : Primrec fun x => (f x).2.1 := Primrec.fst.comp (Primrec.snd.comp hf)
theorem marksRec {f : A → Env} (hf : Primrec f) : Primrec fun x => (f x).2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hf))
theorem wordRec {f : A → Env} (hf : Primrec f) : Primrec fun x => (f x).2.2.2 :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf))

theorem matchedRec {f : A → Env} {a b : A → Nat} {t : A → Tag} {v : A → Bool}
    (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) (hv : Primrec v) :
    Primrec fun x => matched (f x) (a x) (b x) (t x) (v x) :=
  Primrec.eq.comp (selectRec (Primrec.list_cons.comp ha (Primrec.list_cons.comp hb (.const []))) (wordRec hf))
    (profileRec ha hb ht hv)

theorem goodRec {f : A → Env} {a b : A → Nat} {t : A → Tag}
    (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) :
    Primrec fun x => good (f x) (a x) (b x) (t x) :=
  PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp ha hb))
    (PrimrecPred.and (Primrec.eq.comp (Primrec.nat_add.comp (Primrec.list_length.comp ht) (.const 16)) (limRec hf))
      (memRec ht (tagsRec hf)))

theorem recordRec {f : A → Env} {a b : A → Nat} {t : A → Tag}
    (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) :
    Primrec fun x => record (f x) (a x) (b x) (t x) :=
  Primrec.and.comp (goodRec hf ha hb ht)
    (Primrec.or.comp (matchedRec hf ha hb ht (.const false)) (matchedRec hf ha hb ht (.const true)))

theorem markedRec {f : A → Env} {a b : A → Nat} {t : A → Tag} {v : A → Bool}
    (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) (hv : Primrec v) :
    Primrec fun x => marked (f x) (a x) (b x) (t x) (v x) :=
  Primrec.and.comp (Primrec.and.comp (goodRec hf ha hb ht)
    (PrimrecPred.or (memRec (Primrec.pair ha hb) (marksRec hf)) (memRec (Primrec.pair hb ha) (marksRec hf))))
    (matchedRec hf ha hb ht hv)

theorem orderRec {f : A → Env} {p : A → List Event} (hf : Primrec f) (hp : Primrec p) :
    Primrec fun a => order (f a) (p a) := by
  apply Primrec.and.comp _ (seesRec (wordRec hf) hp)
  apply P455FramePrim.allB hp
  exact (PrimrecPred.not (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
    (Primrec.nat_sub.comp ((limRec hf).comp Primrec.fst) (.const 2)))).to₂

theorem separateRec {f : A → Env} {a b : A → Nat} (hf : Primrec f) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun x => separate (f x) (a x) (b x) :=
  Primrec.not.comp (P455WriterBlocks.sameRec (limRec hf) (wordRec hf) ha hb)

theorem earlyBeforeRec {f : A → Env} {xs ys : A → W} (hf : Primrec f) (hx : Primrec xs) (hy : Primrec ys) :
    Primrec fun a => earlyBefore (f a) (xs a) (ys a) := by
  apply P455FramePrim.allB (choicesRec hx hy)
  apply Primrec₂.mk
  exact orderRec (hf.comp Primrec.fst) (Primrec.list_cons.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) (.const 2))
    (Primrec.list_cons.comp (Primrec.pair (Primrec.snd.comp Primrec.snd) (.const 0)) (.const [])))

theorem earlyDisjointRec {f : A → Env} {xs ys : A → W} (hf : Primrec f) (hx : Primrec xs) (hy : Primrec ys) :
    Primrec fun a => earlyDisjoint (f a) (xs a) (ys a) :=
  Primrec.or.comp (earlyBeforeRec hf hx hy) (earlyBeforeRec hf hy hx)

end P455WriterQueryLeaves
