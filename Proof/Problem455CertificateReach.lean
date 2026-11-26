import Problem455GadgetPaths




namespace P455CertificateReach
open P455Witness P455Paths

inductive Active (ts : Tiles) (e : EdgeCertificate) : Node → Prop
  | anchor : Active ts e e.a
  | successor : Active ts e e.b
  | right : ts.right e.a.tag = false → Active ts e e.right
  | left : ts.left e.a.tag = false → Active ts e e.left
  | down : ts.bottom e.a.tag = false → Active ts e e.down
  | up : ts.top e.a.tag = false → Active ts e e.up
  | diagonal : ts.right e.a.tag = false → ts.bottom e.a.tag = false → Active ts e e.diagonal

private theorem role_near {r allow mark w n label} (rec : V r allow mark w (typedNode n))
    (role : label = n.owner ∨ label = n.mate) : Near r allow mark w n.owner label 1 := by
  rcases role with h|h
  · simpa [h] using (near_self (r := r) (allow := allow) (mark := mark) (w := w) n.owner 1)
  · exact h ▸ (record_pair rec).1

theorem functionality_reach {r allow mark w} (cap : P455Closure.Cap r w)
    (ts : Tiles) (f : FunctionalityCertificate) (ok : V r allow mark w (f.query ts))
    {n : Node} {label : Nat} (node : n = f.anchor ∨ n = f.b ∨ n = f.c)
    (role : label = n.owner ∨ label = n.mate) : Near r allow mark w f.anchor.owner label 2 := by
  rcases node with h|h|h <;> subst n
  · exact near_mono (role_near (marked_typed ok.1) role) (by decide)
  · have port := ok.2.1
    exact near_trans (neighbor_paths cap f.dir port).1 (role_near (neighbor_target_record port) role)
  · have port := ok.2.2.1
    exact near_trans (neighbor_paths cap f.dir port).1 (role_near (neighbor_target_record port) role)

private theorem on_guard {r allow mark w b q} (hb : b = false)
    (h : V r allow mark w (flagQ (!b) q)) : V r allow mark w q := by
  simpa [flagQ,hb] using h

private theorem local_right {r allow mark w ts e} (h : V r allow mark w (localCert ts e))
    (b : ts.right e.a.tag = false) : V r allow mark w (rightward ts e.a e.right) :=
  on_guard b h.1
private theorem local_left {r allow mark w ts e} (h : V r allow mark w (localCert ts e))
    (b : ts.left e.a.tag = false) : V r allow mark w (rightward ts e.left e.a) :=
  on_guard b h.2.1
private theorem local_down {r allow mark w ts e} (h : V r allow mark w (localCert ts e))
    (b : ts.bottom e.a.tag = false) : V r allow mark w (downward ts e.a e.down) :=
  on_guard b h.2.2.1
private theorem local_up {r allow mark w ts e} (h : V r allow mark w (localCert ts e))
    (b : ts.top e.a.tag = false) : V r allow mark w (downward ts e.up e.a) :=
  on_guard b h.2.2.2.1
private theorem local_square {r allow mark w ts e} (h : V r allow mark w (localCert ts e))
    (b : ts.right e.a.tag = false) (d : ts.bottom e.a.tag = false) :
    V r allow mark w (downward ts e.right e.diagonal) ∧
    V r allow mark w (rightward ts e.down e.diagonal) := by
  have sq := h.2.2.2.2.1
  simpa [flagQ,b,d,V,Holds] using sq

/-- Either the selected local neighbor is the second endpoint, or the
    certificate contains an actual return port in one of its two orientations. -/
theorem successor_joined {r allow mark w} {ts : Tiles} {e : EdgeCertificate} (cap : P455Closure.Cap r w)
    (ok : V r allow mark w (e.query ts)) : Joined r allow mark w e.a e.b := by
  have lc := ok.2.2.1
  have succ := ok.2.2.2.1
  unfold chosenSuccessor at succ
  dsimp only at succ
  split at succ
  next ret =>
    rcases succ.2.1 with f|b
    · exact port_joined cap 4 (by decide) f
    · exact (port_joined cap 4 (by decide) b).symm
  next noReturn =>
    have eq := succ.1
    cases row : endOfRow ts e.a with
    | true =>
      have bottom : ts.bottom e.a.tag = false := by simpa [row] using noReturn
      have target : e.down = e.b := by simpa [row] using eq
      exact target ▸ down_paths cap (local_down lc bottom)
    | false =>
      cases odd : ts.oddRow e.a.tag with
      | true =>
        have left : ts.left e.a.tag = false := by simpa [endOfRow,odd] using row
        have target : e.left = e.b := by simpa [row,odd] using eq
        exact target ▸ (right_paths cap (local_left lc left)).symm
      | false =>
        have right : ts.right e.a.tag = false := by simpa [endOfRow,odd] using row
        have target : e.right = e.b := by simpa [row,odd] using eq
        exact target ▸ right_paths cap (local_right lc right)

theorem active_owner {r allow mark w} (cap : P455Closure.Cap r w)
    (ts : Tiles) (e : EdgeCertificate) (ok : V r allow mark w (e.query ts))
    {n : Node} (active : Active ts e n) :
    Near r allow mark w e.a.owner n.owner 2 ∧ V r allow mark w (typedNode n) := by
  have lc := ok.2.2.1
  cases active with
  | anchor => exact ⟨near_self _ _,marked_typed ok.1⟩
  | successor => exact ⟨near_mono (successor_joined cap ok).1 (by decide),marked_typed ok.2.1⟩
  | right b =>
    have p := local_right lc b
    exact ⟨near_mono (right_paths cap p).1 (by decide),neighbor_target_record (d := .right) p⟩
  | left b =>
    have p := local_left lc b
    exact ⟨near_mono (right_paths cap p).2 (by decide),neighbor_target_record (d := .left) p⟩
  | down b =>
    have p := local_down lc b
    exact ⟨near_mono (down_paths cap p).1 (by decide),neighbor_target_record (d := .down) p⟩
  | up b =>
    have p := local_up lc b
    exact ⟨near_mono (down_paths cap p).2 (by decide),neighbor_target_record (d := .up) p⟩
  | diagonal rr dd =>
    have p := local_right lc rr
    have q := (local_square lc rr dd).1
    exact ⟨near_trans (right_paths cap p).1 (down_paths cap q).1,neighbor_target_record (d := .down) q⟩

/-- For either endpoint owner, every role genuinely used in the specified
    edge certificate is within four actual record/port contacts. -/
theorem edge_reach {r allow mark w} (cap : P455Closure.Cap r w)
    (ts : Tiles) (e : EdgeCertificate) (ok : V r allow mark w (e.query ts))
    {n : Node} {label : Nat} (active : Active ts e n) (role : label = n.owner ∨ label = n.mate) :
    Near r allow mark w e.a.owner label 4 ∧ Near r allow mark w e.b.owner label 4 := by
  obtain ⟨reach,rec⟩ := active_owner cap ts e ok active
  have first := near_trans reach (role_near rec role)
  exact ⟨near_mono first (by decide),near_trans (successor_joined cap ok).2 first⟩

end P455CertificateReach
