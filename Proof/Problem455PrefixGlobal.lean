import Problem455PrefixLinkInvariance

 
namespace P455Prefix
open P455FirstRewrite P455Quotient

/-- Unconditional from validity in the fixed monoid. The original endpoints
    reduce by small steps to a common prefix on a common nonempty expansion
    of a capped, compressed valid identity. Every deduction between those
    compressed words yields an ordinary deduction of the original identity. -/
theorem normalized_compressed {r allow ts} (hr : 0 < r) {u v : Word}
    (valid : (P455FullSingleton.model r allow ts).Valid u v) :
    ∃ A B : Word, ∃ h : Nat → Word,
      (∀ z, h z ≠ []) ∧ Cap r A ∧ Cap r B ∧
      P455SourceFamilies.Compressed r A ∧ P455SourceFamilies.Compressed r B ∧
      (P455FullSingleton.model r allow ts).Valid A B ∧
      A.flatMap h = residual (highNames r u) u ∧ B.flatMap h = residual (highNames r u) v ∧
      Derives (Steps r allow ts) u (headPowers r (highNames r u) ++ A.flatMap h) ∧
      Derives (Steps r allow ts) v (headPowers r (highNames r u) ++ B.flatMap h) ∧
      (∀ k, Derives (fun p q => (P455FullSingleton.model r allow ts).Valid p q ∧ rank p q ≤ k) A B →
        Derives (fun p q => (P455FullSingleton.model r allow ts).Valid p q ∧
          rank p q ≤ max k (2*(r+2)+1)) u v) := by
  obtain ⟨left,right,cu,_,suffixID,_⟩ := arbitrary_prefix valid
  obtain ⟨A,B,h,non,hu,hv,ca,cb,idAB,cmpA,cmpB⟩ := compressed_instance hr _ _ cu suffixID
  refine ⟨A,B,h,non,ca,cb,cmpA,cmpB,idAB,hu,hv,?_,?_,?_⟩
  · rw [hu]; exact left
  · rw [hv]; exact right
  · intro k walk
    apply reassemble valid
    simpa only [hu,hv] using substitute_deduction h non walk

end P455Prefix
