import Max2SAT.Community.Computed

/-! The zero-coefficient branch and the full search under deterministic
quality conditions. Numerical discovery is still a separate obligation. -/
namespace Max2SAT.Community
noncomputable section
open Counts
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}

theorem zero_count_gain (F : Formula n) (b : ℕ) (t : Fin n) :
    countGain F 0 b t=gainExpr F t := by
  cases he : gainExpr F t
  simp [countGain,Affine.add,Affine.scale,Affine.shift,he]

theorem zero_count_nodes (F : Formula n) (hF : wellFormed F) (hn : 4≤n)
    (g K D : ℝ) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hN : ‖interactionMatrix (gainExpr F)‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      crossProfile (interactionMatrix (gainExpr F)) (secondRound n) (firstRound n)) :
    (Runs.nodeCount (countGuesses n 0)
      (countBudget F 0 (roundPrefix (twoRound n) 2) (twoRound n))
      (roundPrefix (twoRound n) 2):ℝ)≤
      (2+14*n)*(exponentialBase (1/2) (roundRate 2 (1/2) g K))^n := by
  have hp : 0<(roundPrefix (twoRound n) 2).card := by rw [two_round_prefix_card]; omega
  have h := round_runs_nodes (countGuesses n 0) (fun b => countGain F 0 b)
    (twoRound n) 2 (by omega) two_round_order two_round_range hp
    (fun b _ => countGain_symmetric F hF 0 b)
    (fun b _ => countGain_diagonal F hF 0 b)
    (fun _ => 0) (by simp) (1/2) g K D (by norm_num) (by norm_num) hg hK hD
    two_round_size
    (by intro b _; simpa only [show countGain F 0 b=gainExpr F from funext (zero_count_gain F b)] using hN)
    (by
      intro b _
      simpa only [show countGain F 0 b=gainExpr F from funext (zero_count_gain F b),two_round_profile] using hprofile)
    (by simp; positivity)
  have he : countBudget F 0 (roundPrefix (twoRound n) 2) (twoRound n)=
      (fun b => comparisonBudget (countGain F 0 b) (fun _ => 0) (roundPrefix (twoRound n) 2) (twoRound n)) := by
    funext b
    simp [countBudget]
  rw [he]
  convert h.1 using 1
  norm_num [countGuesses]
  left
  ring

/-- The runtime bound no longer requires positive coefficient mass. -/
theorem computed_nodes_of_quality (F : Formula n) (discover : Formula n → Representation n r)
    (g : ℚ) (K : ℝ) (hF : wellFormed F) (hn : 4≤n) (hg : 0<g) (hK : 0<K)
    (hD : 0<remainderEnergy F (discover F))
    (hv : ∀ k, ∑ t, ((discover F).direction k t:ℝ)^2≤1)
    (hbudget : (coefficientMass (discover F):ℝ)≤(g:ℝ)*n*Real.sqrt (remainderEnergy F (discover F):ℝ)/64)
    (hN : ‖interactionMatrix (projectionGain F (discover F).coefficient (discover F).direction (fun _ => 0))‖^2≤
      K*(remainderEnergy F (discover F):ℝ))
    (hprofile : 4*Real.sqrt 3*((g:ℝ)*n*Real.sqrt (remainderEnergy F (discover F):ℝ))≤
      crossProfile (interactionMatrix (projectionGain F (discover F).coefficient (discover F).direction (fun _ => 0)))
        (secondRound n) (firstRound n)) :
    (computedNodes F g discover:ℝ)≤(4*(n:ℝ)+3)^r*(2+14*n)*
      (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) K))^n ∧
      exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) K)<2 := by
  by_cases hΛ:coefficientMass (discover F)=0
  · have he : projectionGain F (discover F).coefficient (discover F).direction (fun _ => 0)=gainExpr F :=
      funext (zero_coefficients_gain F (discover F) hΛ _)
    rw [he] at hN hprofile
    have hb := zero_count_nodes F hF hn g K (remainderEnergy F (discover F))
      (by exact_mod_cast hg) hK (by exact_mod_cast hD) hN hprofile
    have hnid : computedNodes F g discover=
      Runs.nodeCount (countGuesses n 0) (countBudget F 0 (roundPrefix (twoRound n) 2) (twoRound n))
        (roundPrefix (twoRound n) 2) := by
      have hD' : remainderEnergy F (withComputedSpacing F g (discover F))≠0 := ne_of_gt hD
      have hΛ' : coefficientMass (withComputedSpacing F g (discover F))=0 := hΛ
      simp only [computedNodes,communityNodes,show ¬n<4 by omega,ite_false,hD',hΛ',ite_true]
    rw [hnid]
    refine ⟨hb.trans ?_,exponential_base_lt_two _ _ (by norm_num)
      (round_rate_pos 2 (by omega) (1/2) g K (by norm_num) (by exact_mod_cast hg) hK)⟩
    have hpow : 1≤(4*(n:ℝ)+3)^r := one_le_pow₀ (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    have hnon : 0≤(2+14*(n:ℝ))*(exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) K))^n :=
      mul_nonneg (by positivity) (pow_nonneg (Real.exp_pos _).le _)
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hpow hnon
  · exact computed_positive_nodes F discover g K hF hn hg hK hD
      (lt_of_le_of_ne (coefficient_mass_nonneg _) (Ne.symm hΛ)) hv hbudget hN hprofile

end
end Max2SAT.Community
