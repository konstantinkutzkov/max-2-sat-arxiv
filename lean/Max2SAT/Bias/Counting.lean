import Max2SAT.Bias.Hybrid
import Max2SAT.Bias.Parameters

/-! The manuscript's general candidate-count lemma (lem:bias_count).
It uses the total initial gap and the squared occurrence counts directly. -/
namespace Max2SAT.Bias
open FairCoin
noncomputable section

theorem gap_mass_probability (F : Formula n) (hF : wellFormed F)
    (hQ : 0 < ∑ i : Fin n, (B F i : ℝ)^2) :
    probability n (admissible F (initialPreference F) (branchingSet F)) ≤
      Real.exp (-(gapMass F Finset.univ : ℝ)^2 /
        (512 * ∑ i : Fin n, (B F i : ℝ)^2)) := by
  let Q := ∑ i : Fin n, (B F i : ℝ)^2
  let G := (gapMass F Finset.univ : ℝ)
  let a := (∑ i ∈ branchingSet F, |(gap F i : ℝ)|) / 4
  have hV : (∑ i : Fin n, (2 * (B F i : ℝ))^2) = 4 * Q := by
    simp only [Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hv : 0 < ∑ i : Fin n, (2 * (B F i : ℝ))^2 := by
    rw [hV]
    exact mul_pos (by norm_num) hQ
  have hG : 0 ≤ G := by
    dsimp [G]
    rw [gapMass_real]
    positivity
  have hm : G ≤ 2 * (gapMass F (branchingSet F) : ℝ) := by
    dsimp [G]
    exact_mod_cast branchingSet_mass F
  rw [gapMass_real] at hm
  have ha : G / 8 ≤ a := by dsimp [a]; linarith
  have hs : (G / 8)^2 ≤ a^2 := by nlinarith
  have hratio : G^2 / (512 * Q) ≤ a^2 / (8 * Q) := calc
    _ = (G / 8)^2 / (8 * Q) := by ring
    _ ≤ a^2 / (8 * Q) := div_le_div_of_nonneg_right hs (by positivity)
  apply le_trans (admissible_probability F (branchingSet F) hF hv)
  apply Real.exp_le_exp.mpr
  rw [hV]
  change -a^2 / (2 * (4 * Q)) ≤ -G^2 / (512 * Q)
  have he : 2 * (4 * Q) = 8 * Q := by ring
  rw [he]
  simpa only [neg_div] using neg_le_neg hratio

theorem gap_mass_output_count (F : Formula n) (hF : wellFormed F)
    (hQ : 0 < ∑ i : Fin n, (B F i : ℝ)^2) :
    ((Hybrid.outputs F (initialPreference F) (branchingSet F)).length : ℝ) ≤
      (2 : ℝ)^n * Real.exp (-(gapMass F Finset.univ : ℝ)^2 /
        (512 * ∑ i : Fin n, (B F i : ℝ)^2)) := by
  rw [Hybrid.output_count]
  have hp := gap_mass_probability F hF hQ
  rw [probability_eq_count] at hp
  have hn : (0 : ℝ) < 2^n := by positivity
  have hc := (div_le_iff₀ hn).mp hp
  simpa only [mul_comm] using hc

end
end Max2SAT.Bias
