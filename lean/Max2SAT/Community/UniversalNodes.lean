import Max2SAT.Community.FamilyParameters

/-! A uniform exhaustive bound absorbs the finitely many small input sizes.
This bound concerns actual search calls; arithmetic costs remain separate. -/
namespace Max2SAT.Community
noncomputable section
open Counts
variable {n r : ℕ}
set_option maxHeartbeats 1000000

def searchPolynomial (n r : ℕ) : ℝ := (2*(n:ℝ)^3+4*n+3)^r*(2+14*n)

theorem discovery_direction_bound (F : Formula n) (r : ℕ) (i : Fin r) :
    ∑ t, ((discoverFormula r F).direction i t:ℝ)^2≤1 := by
  unfold discoverFormula
  split
  · exact (frame_direction_unit _ _ _ (computed_frame_orthogonal _) i).le
  · simp

theorem all_runs_coarse (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) (hK : ∀ g∈guesses, PrefixSearch.Stable (K g) P) :
    (Runs.nodeCount guesses K P:ℝ)≤guesses.length*(2+2*n)*(2:ℝ)^n := by
  classical
  have hp (g : ι) : FairCoin.probability n (fun x => (K g x).Holds x)≤1 := by
    unfold FairCoin.probability
    rw [←FairCoin.average_const n 1]
    apply FairCoin.average_mono
    intro x
    split <;> norm_num
  have h := all_runs_nodes_of_probability guesses K P hK 1 (fun g _ => hp g)
  have hcard : P.card≤n := by simpa using Finset.card_le_univ P
  have hpow : (2:ℝ)^(P.card+1)≤2*(2:ℝ)^n := by
    rw [pow_succ,mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcard) (by norm_num)
  have hinside : (2:ℝ)^(P.card+1)+2*n*(2:ℝ)^n*1≤(2+2*n)*(2:ℝ)^n := by nlinarith
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg (α:=ℝ) guesses.length))

theorem search_polynomial_bounds (n r : ℕ) :
    2+2*(n:ℝ)≤searchPolynomial n r ∧
      (2*(n:ℝ)^3+3)^r*(2+2*n)≤searchPolynomial n r ∧
      (4*(n:ℝ)+3)^r*(2+14*n)≤searchPolynomial n r := by
  have hn : 0≤(n:ℝ) := by positivity
  have hn3 : 0≤(n:ℝ)^3 := by positivity
  have hp : 1≤(2*(n:ℝ)^3+4*n+3)^r := one_le_pow₀ (by nlinarith)
  unfold searchPolynomial
  refine ⟨by nlinarith,?_,?_⟩
  · gcongr <;> nlinarith
  · gcongr; nlinarith

theorem community_nodes_coarse (F : Formula n) (prepare : Formula n → Representation n r)
    (hv : ∀ i, ∑ t, ((prepare F).direction i t:ℝ)^2≤1) :
    (communityNodes F prepare:ℝ)≤searchPolynomial n r*(2:ℝ)^n := by
  classical
  have hpoly := search_polynomial_bounds n r
  have hex : (Regular.independentNodes (∅ : Finset (Fin n)):ℝ)≤searchPolynomial n r*(2:ℝ)^n := by
    rw [Regular.independent_nodes_exact,Finset.card_empty,Nat.sub_zero]
    have hh : ((2^(n+1)-1:ℕ):ℝ)≤(2:ℝ)^(n+1) := by exact_mod_cast Nat.sub_le (2^(n+1)) 1
    have hp : (2:ℝ)≤searchPolynomial n r := by nlinarith [hpoly.1,Nat.cast_nonneg (α:=ℝ) n]
    exact hh.trans (by rw [pow_succ,mul_comm]; exact mul_le_mul_of_nonneg_right hp (by positivity))
  unfold communityNodes
  split
  · exact hex
  · rename_i hn
    dsimp only
    split
    · exact hex
    · split
      · have h := all_runs_coarse (countGuesses n 0)
          (countBudget F 0 (roundPrefix (twoRound n) 2) (twoRound n)) _
          (fun _ _ => comparison_stable _ _ _ _ (round_prefix_closed _ _))
        simp only [countGuesses,ite_true,List.length_singleton,Nat.cast_one,one_mul] at h
        exact h.trans (mul_le_mul_of_nonneg_right hpoly.1 (by positivity))
      · have h := all_runs_coarse
          (projectionGrids (prepare F).direction (fun _ => cappedSpacing n (prepare F).trialSpacing))
          (projectionBudget F (prepare F).coefficient (prepare F).direction
            (fun _ => cappedSpacing n (prepare F).trialSpacing) (roundPrefix (twoRound n) 2) (twoRound n)) _
          (fun _ _ => comparison_stable _ _ _ _ (round_prefix_closed _ _))
        have hc := capped_grid_size (prepare F).direction (prepare F).trialSpacing (by omega : 1≤n) hv
        change (projectionNodes F (prepare F):ℝ)≤_ at h
        apply h.trans
        have hh := mul_le_mul_of_nonneg_right hc (show 0≤2+2*(n:ℝ) by positivity)
        exact mul_le_mul_of_nonneg_right (hh.trans hpoly.2.1) (by positivity)

theorem diagonalized_nodes_coarse (F : Formula n) (r : ℕ) (g : ℚ) :
    (diagonalizedNodes F r g:ℝ)≤searchPolynomial n r*(2:ℝ)^n := by
  unfold diagonalizedNodes computedNodes
  apply community_nodes_coarse
  intro i
  change (∑ t, ((discoverFormula r F).direction i t:ℝ)^2)≤1
  exact discovery_direction_bound F r i

theorem discovery_base_bounds (g : ℚ) (χ : ℝ) (hg : 0<g) (hχ : 1≤χ) :
    1≤exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)) ∧
      exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ))<2 := by
  constructor
  · apply Real.one_le_exp_iff.mpr
    exact (by positivity : (0:ℝ)≤(1/2)*Real.log 2).trans (le_max_left _ _)
  · exact exponential_base_lt_two _ _ (by norm_num)
      (round_rate_pos 2 (by omega) (1/2) (g:ℝ) (400*χ) (by norm_num)
        (by exact_mod_cast hg) (by positivity))

theorem small_size_nodes (F : Formula n) (r N : ℕ) (g : ℚ) (c : ℝ)
    (hn : n<N) (hc : 1≤c) :
    (diagonalizedNodes F r g:ℝ)≤(2:ℝ)^N*searchPolynomial n r*c^n := by
  have hpow : (2:ℝ)^n≤(2:ℝ)^N := pow_le_pow_right₀ (by norm_num) (by omega)
  have hc' : 1≤c^n := one_le_pow₀ hc
  have hp : 0≤searchPolynomial n r := by unfold searchPolynomial; positivity
  apply (diagonalized_nodes_coarse F r g).trans
  have hh := mul_le_mul_of_nonneg_left hpow hp
  have hh' := mul_le_mul_of_nonneg_left hc' (show 0≤(2:ℝ)^N*searchPolynomial n r by positivity)
  nlinarith

end
end Max2SAT.Community
