import InPlaceOrDisjointBuffer

open Aeneas Aeneas.Std Aeneas.SepLogic Aeneas.Std.WP Result

namespace in_place_or_disjoint_buffer

/-- `new_in_place` hands over the slots of `buffer`; its back function ends the `as_mut_ptr`
borrow, turning the slots back into the slice. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_in_place.spec {T : Type} (buffer : Slice T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_in_place buffer
      ⦃ (b, back) => ⌜b.len = buffer.len ∧ b.src = b.dst.retype ∧
        ∀ b', back b' = Slice.end_as_mut_ptr buffer b.dst⌝ ∗ b.dst ↦* buffer.val ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_in_place
  step*
  exact ⟨rfl, fun _ => as_mut_ptr_back_post⟩

/-- `new_disjoint` hands over the slots of `src` and `dst`; its back function ends both
`as_mut_ptr` borrows. -/
@[step]
theorem InPlaceOrDisjointBuffer.new_disjoint.spec {T : Type} (src dst : Slice T)
    (h : src.length = dst.length) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.new_disjoint src dst
      ⦃ (b, back) => ⌜b.len = src.len ∧ ∀ b', back b' = (do
          let s ← Slice.end_as_mut_ptr src b.src.retype
          let d ← Slice.end_as_mut_ptr dst b.dst
          ok (s, d))⌝ ∗ b.src ↦* src.val ∗ b.dst ↦* dst.val ⦄ := by
  unfold InPlaceOrDisjointBuffer.new_disjoint
  step*
  subst_vars
  have : ((RawPtr.retype p : ConstRawPtr T).retype : MutRawPtr T) = p := rfl
  apply (WP.ispec_ok _).2
  iframe

@[step]
theorem InPlaceOrDisjointBuffer.impl.len.spec {T : Type} (self : InPlaceOrDisjointBuffer T) :
    ⦃ emp ⦄ InPlaceOrDisjointBuffer.impl.len self ⦃ r => ⌜r = self.len⌝ ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.len
  step*

@[step]
theorem InPlaceOrDisjointBuffer.impl.src.spec {T : Type} (self : InPlaceOrDisjointBuffer T)
    (vs : List T) (h : self.len.val = vs.length) :
    ⦃ self.src ↦* vs ⦄ InPlaceOrDisjointBuffer.impl.src self
      ⦃ (s, back) => ⌜s.val = vs ∧ back = self.src.reviveRange vs⌝ ∗ self.src ↦† vs.length ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.src
  step*

@[step]
theorem InPlaceOrDisjointBuffer.impl.dst.spec {T : Type} (self : InPlaceOrDisjointBuffer T)
    (vs : List T) (h : self.len.val = vs.length) :
    ⦃ self.dst ↦* vs ⦄ InPlaceOrDisjointBuffer.impl.dst self
      ⦃ (s, back, _) => ⌜s.val = vs⌝ ∗ self.dst ↦† vs.length ∗
        ⌜∀ s', s'.length = vs.length →
          ⦃ self.dst ↦† vs.length ⦄ back s' ⦃ b => ⌜b = self⌝ ∗ self.dst ↦* s'.val ⦄⌝ ⦄ := by
  unfold InPlaceOrDisjointBuffer.impl.dst
  step*
  refine ⟨vs_post, fun s' hs' => ?_⟩
  subst from_raw_parts_mut_back_post
  rw [← h]
  step*

theorem zero_first_in_place.spec (buf : Slice U8) (h : 0 < buf.length) :
    ⦃ emp ⦄ zero_first_in_place buf ⦃ r => ⌜r = (buf.len, buf.set 0#usize 0#u8)⌝ ⦄ := by
  unfold zero_first_in_place
  step*
  rw [b_post2]
  step with Slice.end_as_mut_ptr.spec buf b.dst (d.set 0#usize 0#u8).val (by simp [d_post])
  step*
  exact ⟨by simp [i_post, b1_post, b_post], Slice.ext _ _ (by simp [buf1_post, d_post])⟩

theorem copy_first.spec (src dst : Slice U8) (h : src.length = dst.length)
    (h0 : 0 < src.length) :
    ⦃ emp ⦄ copy_first src dst ⦃ r => ⌜r = (src, dst.set 0#usize (src.val[0]'h0))⌝ ⦄ := by
  unfold copy_first
  step*
  rw [src_back_post]
  step with RawPtr.reviveRange.spec_len b.src src.val dst.length (by simp [h])
  step*
  rw [b_post1]
  step*
  exact ⟨Slice.ext _ _ s_post, Slice.ext _ _ (by simp [d_post, s1_post])⟩

theorem increment_first_in_place.spec (buf : Slice U8) (h : 0 < buf.length) :
    ⦃ emp ⦄ increment_first_in_place buf
      ⦃ r => ⌜r = buf.set 0#usize (core.num.U8.wrapping_add (buf.val[0]'h) 1#u8)⌝ ⦄ := by
  unfold increment_first_in_place
  step*
  rw [src_back_post, b_post1]
  step with RawPtr.reviveRange.spec_len (RawPtr.retype b.dst) buf.val buf.val.length rfl
  step*
  rw [b_post2]
  step with Slice.end_as_mut_ptr.spec buf b.dst s2.val (by simp [s2_post, s1_post])
  apply Slice.ext
  rw [r_post, s2_post, i_post, x_post, List.getElem_of_eq s_post]
  simp [s1_post]

end in_place_or_disjoint_buffer
