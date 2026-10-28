import Max2SAT.Counts.VerifiedNodes
import Max2SAT.Counts.GuessInvariance
import Max2SAT.Counts.GridBounds

/-! Formula-level instantiations. All guesses have the same interaction
matrix. Count preprocessing preserves it, so hypotheses concern the input. -/
namespace Max2SAT.Counts
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}

theorem interaction_matrix_of_coeff_eq (H G : Fin n → Affine n)
    (h : ∀ t w, (H t).coeff w=(G t).coeff w) :
    interactionMatrix H=interactionMatrix G := by
  funext t w
  simp only [interactionMatrix,h]

theorem projection_round_nodes (F : Formula n) (hF : wellFormed F)
    (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ)
    (hδ : ∀ i, 0≤δ i) (guesses : List (Fin r → ℚ))
    (round : Fin n → ℕ) (k : ℕ) (hk : 2≤k)
    (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : ((roundPrefix round k).card:ℝ)≤τ*n)
    (hN : ‖interactionMatrix (projectionGain F lam v (fun _ => 0))‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : roundPrefix round k,
        Real.sqrt (∑ w, (earlierRow (projectionGain F lam v (fun _ => 0)) round t w)^2))
    (hslack : (∑ t∈roundPrefix round k, (allowance lam v δ t : ℝ))≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount guesses (projectionBudget F lam v δ (roundPrefix round k) round)
      (roundPrefix round k) : ℝ)≤
      guesses.length*(2+2*n*(3+2*k))*(exponentialBase τ (roundRate k τ g K))^n ∧
      exponentialBase τ (roundRate k τ g K)<2 := by
  apply round_runs_nodes guesses (projectionGain F lam v) round k hk horder hround hP
    (fun b _ => projectionGain_symmetric F hF lam v b)
    (fun b _ => projectionGain_diagonal F hF lam v b)
    (allowance lam v δ) (fun t _ => allowance_nonneg lam v δ hδ t)
    τ g K D hτ hτ1 hg hK hD hsize _ _ hslack
  · intro b _
    rw [interaction_matrix_of_coeff_eq _ _ (projection_coeff_independent F lam v b (fun _ => 0))]
    exact hN
  · intro b _
    simpa only [earlier_rows_of_coeff_eq _ _
      (projection_coeff_independent F lam v b (fun _ => 0))] using hprofile

theorem projection_sequential_nodes (F : Formula n) (hF : wellFormed F)
    (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ)
    (hδ : ∀ i, 0≤δ i) (guesses : List (Fin r → ℚ))
    (P : Finset (Fin n)) (hr : EarlierInPrefix P (fun i => i.val)) (hP : 0<P.card)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : (P.card:ℝ)≤τ*n)
    (hN : ‖sequentialMatrix (projectionGain F lam v (fun _ => 0)) P‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : P, Real.sqrt (∑ w,
        (earlierRow (projectionGain F lam v (fun _ => 0)) (fun i => i.val) t w)^2))
    (hslack : (∑ t∈P, (allowance lam v δ t : ℝ))≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount guesses (projectionBudget F lam v δ P (fun i => i.val)) P : ℝ)≤
      guesses.length*(2+6*n)*(exponentialBase τ (sequentialRate τ g K))^n ∧
      exponentialBase τ (sequentialRate τ g K)<2 := by
  apply sequential_runs_nodes guesses (projectionGain F lam v) P hr hP
    (fun b _ => projectionGain_symmetric F hF lam v b)
    (fun b _ => projectionGain_diagonal F hF lam v b)
    (allowance lam v δ) (fun t _ => allowance_nonneg lam v δ hδ t)
    τ g K D hτ hτ1 hg hK hD hsize _ _ hslack
  · intro b _
    rw [sequential_matrix_of_coeff_eq _ _ (projection_coeff_independent F lam v b (fun _ => 0))]
    exact hN
  · intro b _
    simpa only [earlier_rows_of_coeff_eq _ _
      (projection_coeff_independent F lam v b (fun _ => 0))] using hprofile

theorem count_round_nodes (F : Formula n) (hF : wellFormed F) (β : ℚ)
    (round : Fin n → ℕ) (k : ℕ) (hk : 2≤k)
    (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : ((roundPrefix round k).card:ℝ)≤τ*n)
    (hN : ‖interactionMatrix (countGain F β 0)‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : roundPrefix round k, Real.sqrt (∑ w, (earlierRow (countGain F β 0) round t w)^2))
    (hslack : (roundPrefix round k).card*|(β:ℝ)|≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount (countGuesses n β)
      (countBudget (preprocess F).1 β (roundPrefix round k) round) (roundPrefix round k) : ℝ)≤
      (n+1)*(2+2*n*(3+2*k))*(exponentialBase τ (roundRate k τ g K))^n ∧
      exponentialBase τ (roundRate k τ g K)<2 := by
  have hG := (preprocess_finished F hF).1
  have h := round_runs_nodes (countGuesses n β) (countGain (preprocess F).1 β)
    round k hk horder hround hP
    (fun b _ => countGain_symmetric _ hG β b) (fun b _ => countGain_diagonal _ hG β b)
    (fun _ => |β|) (fun _ _ => abs_nonneg β) τ g K D hτ hτ1 hg hK hD hsize
    (by
      intro b _
      rw [interaction_matrix_of_coeff_eq _ _ (count_coeff_preprocess F hF β b 0)]
      exact hN)
    (by
      intro b _
      simpa only [earlier_rows_of_coeff_eq _ _ (count_coeff_preprocess F hF β b 0)] using hprofile)
    (by simpa using hslack)
  refine ⟨h.1.trans ?_,h.2⟩
  have hl : ((countGuesses n β).length:ℝ)≤n+1 := by exact_mod_cast (count_guesses_length (n:=n) β)
  have hb : 0≤(exponentialBase τ (roundRate k τ g K))^n :=
    pow_nonneg (Real.exp_pos _).le n
  gcongr

end
end Max2SAT.Counts
