import Max2SAT.Counts.Adjustments

/-! The manuscript's explicit slice lemma: the count adjustment retains
the diagonal correction, and its allowance bounds either orientation. -/
namespace Max2SAT.Counts

theorem count_slice_identity (F : Formula n) (hF : wellFormed F)
    (β : ℚ) (h : ℕ) (x : Assignment n) (hx : ones x=h) (t : Fin n) :
    (countGain F β h t).eval x=scoreGain F t x+β*bit (x t) := by
  rw [countGain_eval F β h t x hF,hx]
  ring

theorem count_slice_comparison (F : Formula n) (hF : wellFormed F)
    (β : ℚ) (h : ℕ) (x : Assignment n) (hx : ones x=h) (t : Fin n) (p : Bool) :
    direction p*(countGain F β h t).eval x-|β|≤direction p*scoreGain F t x := by
  rw [count_slice_identity F hF β h x hx t]
  have hb := le_abs_self β
  have hn := neg_le_abs β
  cases p <;> cases x t <;> simp only [direction,bit_false,bit_true] <;> norm_num <;> linarith

end Max2SAT.Counts
