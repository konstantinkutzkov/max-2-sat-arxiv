import Max2SAT.Counts.ProgramBounds

namespace Max2SAT.Counts
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}

theorem grid_round_nodes (F : Formula n) (hF : wellFormed F)
    (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ) (δ : ℚ) (hδ : 0<δ)
    (hv : ∀ i, ∑ t, (v i t:ℝ)^2≤1)
    (round : Fin n → ℕ) (k : ℕ) (hk : 2≤k)
    (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : ((roundPrefix round k).card:ℝ)≤τ*n)
    (hN : ‖interactionMatrix (projectionGain F lam v (fun _ => 0))‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : roundPrefix round k,
        Real.sqrt (∑ w, (earlierRow (projectionGain F lam v (fun _ => 0)) round t w)^2))
    (hslack : (∑ i, |(lam i:ℝ)| * ((δ:ℝ)*Real.sqrt n+1))≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount (projectionGrids v (fun _ => δ))
      (projectionBudget F lam v (fun _ => δ) (roundPrefix round k) round)
      (roundPrefix round k) : ℝ)≤
      (2*Real.sqrt n/(δ:ℝ)+3)^r*(2+2*n*(3+2*k))*
        (exponentialBase τ (roundRate k τ g K))^n ∧
      exponentialBase τ (roundRate k τ g K)<2 := by
  have hs := (prefix_allowance_bound lam v δ hδ.le hv (roundPrefix round k)).trans hslack
  push_cast at hs
  have h := projection_round_nodes F hF lam v (fun _ => δ) (fun _ => hδ.le)
    (projectionGrids v (fun _ => δ)) round k hk horder hround hP τ g K D
    hτ hτ1 hg hK hD hsize hN hprofile hs
  refine ⟨h.1.trans ?_,h.2⟩
  have hl := projection_grid_card_bound v δ hδ hv
  have hb : 0≤(exponentialBase τ (roundRate k τ g K))^n := pow_nonneg (Real.exp_pos _).le n
  gcongr

theorem grid_sequential_nodes (F : Formula n) (hF : wellFormed F)
    (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ) (δ : ℚ) (hδ : 0<δ)
    (hv : ∀ i, ∑ t, (v i t:ℝ)^2≤1)
    (P : Finset (Fin n)) (hr : EarlierInPrefix P (fun i => i.val)) (hP : 0<P.card)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : (P.card:ℝ)≤τ*n)
    (hN : ‖sequentialMatrix (projectionGain F lam v (fun _ => 0)) P‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : P, Real.sqrt (∑ w,
        (earlierRow (projectionGain F lam v (fun _ => 0)) (fun i => i.val) t w)^2))
    (hslack : (∑ i, |(lam i:ℝ)| * ((δ:ℝ)*Real.sqrt n+1))≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount (projectionGrids v (fun _ => δ))
      (projectionBudget F lam v (fun _ => δ) P (fun i => i.val)) P : ℝ)≤
      (2*Real.sqrt n/(δ:ℝ)+3)^r*(2+6*n)*
        (exponentialBase τ (sequentialRate τ g K))^n ∧
      exponentialBase τ (sequentialRate τ g K)<2 := by
  have hs := (prefix_allowance_bound lam v δ hδ.le hv P).trans hslack
  push_cast at hs
  have h := projection_sequential_nodes F hF lam v (fun _ => δ) (fun _ => hδ.le)
    (projectionGrids v (fun _ => δ)) P hr hP τ g K D
    hτ hτ1 hg hK hD hsize hN hprofile hs
  refine ⟨h.1.trans ?_,h.2⟩
  have hl := projection_grid_card_bound v δ hδ hv
  have hb : 0≤(exponentialBase τ (sequentialRate τ g K))^n := pow_nonneg (Real.exp_pos _).le n
  gcongr

end
end Max2SAT.Counts
