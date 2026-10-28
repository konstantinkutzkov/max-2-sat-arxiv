import Max2SAT.Random.AbsoluteGains

/-! Deterministic clipping and first-moment estimates in Lemma
`lem:counts-profile`. The convex concentration step is not assumed or
proved here. All probability statements use an exact finite fair-bit law. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- An arbitrary constant shift cannot lower the first absolute moment
of a symmetric signed sum. -/
theorem shifted_absolute_mean (a : ι → ℝ) (b : ℝ) :
    Real.sqrt ((∑ i, (a i)^2)/3) ≤
      expect (fairBits ι) (fun z => |b+∑ i, sign (z i)*a i|) := by
  have ht := expect_mono (fairBits ι) (fun z =>
    abs_sub (b+∑ i, sign (z i)*a i) (b-∑ i, sign (z i)*a i))
  have he : ∀ z : ι → Bool,
      |(b+∑ i, sign (z i)*a i)-(b-∑ i, sign (z i)*a i)| =
        |∑ i, sign (z i)*a i| * 2 := by
    intro z
    rw [show (b+∑ i, sign (z i)*a i)-(b-∑ i, sign (z i)*a i) =
      (∑ i, sign (z i)*a i)*2 by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  simp_rw [he] at ht
  rw [expect_mul_const, expect_add] at ht
  have hs := signed_sum_symmetric a (fun v => |b+v|)
  simp only [←sub_eq_add_neg] at hs
  rw [hs] at ht
  exact (signed_sum_absolute a).trans (by linarith)

/-- The half-sized row fluctuation has the exact lower bound used for
the conditional gap, uniformly in the linear coefficient. -/
theorem row_gap_mean (a : ι → ℝ) (b : ℝ) :
    Real.sqrt ((∑ i, (a i)^2)/3)/2 ≤
      expect (fairBits ι) (fun z => |b+(∑ i, sign (z i)*a i)/2|) := by
  have h := shifted_absolute_mean a (2*b)
  have he : ∀ z : ι → Bool,
      |2*b+∑ i, sign (z i)*a i| = |b+(∑ i, sign (z i)*a i)/2| * 2 := by
    intro z
    rw [show 2*b+∑ i, sign (z i)*a i =
      (b+(∑ i, sign (z i)*a i)/2)*2 by ring, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
  simp_rw [he] at h
  rw [expect_mul_const] at h
  linarith

/-- Clipping a gap whose constant part is small costs at most this
quadratic amount. Here z is the unscaled signed row sum. -/
theorem small_shift_clipping (b z M : ℝ) (hM : 0<M) (hb : |b|≤M/2) :
    |b+z/2|-z^2/(8*M) ≤ min |b+z/2| M := by
  apply le_min
  · exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))
  · have ht := abs_add_le b (z/2)
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    have hs := sq_nonneg (|z|-2*M)
    have hd : |z|/2-M/2 ≤ z^2/(8*M) := by
      apply (le_div_iff₀ (by positivity : 0<8*M)).2
      nlinarith [sq_abs z]
    linarith

/-- A large constant part supplies M/4 unless the fluctuation pays for
it in squared energy. This avoids counting exceptional indices. -/
theorem large_shift_clipping (b z M : ℝ) (hM : 0<M) (hb : M/2 < |b|) :
    M/4-z^2/M ≤ min |b+z/2| M := by
  by_cases hz : |z|≤M/2
  · have ht := abs_sub (b+z/2) (z/2)
    rw [add_sub_cancel_right, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    have hn : 0≤z^2/M := div_nonneg (sq_nonneg _) hM.le
    apply le_min <;> linarith
  · have hs : M^2/4≤z^2 := by nlinarith [sq_abs z, abs_nonneg z]
    have hd : M/4≤z^2/M := (le_div_iff₀ hM).2 (by nlinarith)
    exact (sub_nonpos.mpr hd).trans (le_min (abs_nonneg _) hM.le)

/-- The convex comparison statistic in the common-gap proof. -/
def gapProxy (H z : κ → ℝ) (M : ℝ) : ℝ :=
  ∑ t, if |H t|≤M/2 then |H t+z t/2| else M/4

/-- A deterministic bound, slightly sharper than the 9/8 loss used in
the manuscript. No independence between rows is needed. -/
theorem clipped_sum_lower (H z : κ → ℝ) (M E : ℝ) (hM : 0<M)
    (henergy : (∑ t, (z t)^2)≤E) :
    gapProxy H z M-E/M ≤ ∑ t, min |H t+z t/2| M := by
  have hp : ∀ t, (if |H t|≤M/2 then |H t+z t/2| else M/4)-(z t)^2/M ≤
      min |H t+z t/2| M := by
    intro t
    split_ifs with ht
    · have h := small_shift_clipping (H t) (z t) M hM ht
      have hd : (z t)^2/(8*M)≤(z t)^2/M := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) hM
        linarith
      linarith
    · exact large_shift_clipping (H t) (z t) M hM (lt_of_not_ge ht)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hp t)
  rw [Finset.sum_sub_distrib, ←Finset.sum_div] at hs
  exact (sub_le_sub_left (div_le_div_of_nonneg_right henergy hM.le) _).trans hs

/-- Expected size of the proxy. The row bound is exactly the condition
that the large-shift contribution M/4 covers the first-moment target. -/
theorem gap_proxy_mean (H : κ → ℝ) (L : κ → ι → ℝ) (M : ℝ)
    (hrow : ∀ t, Real.sqrt ((∑ w, (L t w)^2)/3)/2≤M/4) :
    (∑ t, Real.sqrt ((∑ w, (L t w)^2)/3))/2 ≤
      expect (fairBits ι) (fun x => gapProxy H
        (fun t => ∑ w, sign (x w)*L t w) M) := by
  unfold gapProxy
  rw [expect_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : |H t|≤M/2
  · simp only [ite_eq_left ht]
    exact row_gap_mean (L t) (H t)
  · simp only [ite_eq_right ht, expect_const]
    exact hrow t

end
end Max2SAT.Counts
