import Max2SAT.Regular.Encoding
import Max2SAT.Regular.Rounds
import Max2SAT.Regular.Parameters
import Max2SAT.Regular.Spectral

namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ}

def countNodes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (d : ℕ) : ℕ :=
  Counts.Runs.nodeCount (Counts.countGuesses n (correction n d))
    (Counts.countBudget (preprocess (formula G units)).1 (correction n d)
      (Counts.roundPrefix (Counts.twoRound n) 2) (Counts.twoRound n))
    (Counts.roundPrefix (Counts.twoRound n) 2)

def countResult (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (d : ℕ) : Option (ℤ × Assignment n) :=
  Counts.countResult (formula G units) (correction n d)
    (Counts.roundPrefix (Counts.twoRound n) 2) (Counts.twoRound n)

theorem count_result_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (d : ℕ) :
    ∃ q x, countResult G units d=some (q,x) ∧ q=score (formula G units) x ∧
      ∀ y, score (formula G units) y≤q :=
  Counts.countResult_correct _ _ _ _ (formula_wellFormed G units) (Counts.round_prefix_closed _ _)

/-- All analytic hypotheses of the two-round theorem are discharged from
regularity, the stated eigenvalue bound, density, and explicit size bounds. -/
theorem high_degree_nodes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (hreg : G.IsRegularOfDegree d)
    (L ε : ℝ) (hL : 1≤L) (he : 0<ε) (he1 : ε≤1/2)
    (hn : 80≤n) (hsize : 2≤ε*n) (hdensity : (d:ℝ)≤(1-ε)*n)
    (hdegree : 64*L^2≤(d:ℝ)) (hlarge : 128≤(gapConstant ε)^2*ε*n)
    (hspec : EigenBound G d (L*Real.sqrt d)) :
    (countNodes G units d:ℝ)≤(n+1)*(2+14*n)*
      (Counts.exponentialBase (1/2) (Counts.roundRate 2 (1/2) (gapConstant ε) (normConstant L ε)))^n ∧
    Counts.exponentialBase (1/2) (Counts.roundRate 2 (1/2) (gapConstant ε) (normConstant L ε))<2 := by
  have hn2 : 2≤n := by omega
  have hd0 : 0<d := by
    have : (0:ℝ)<d := by nlinarith
    exact_mod_cast this
  have hdn : d≤n-1 := by
    let v : Fin n := ⟨0,by omega⟩
    have h := G.degree_lt_card_verts v
    rw [hreg v,Fintype.card_fin] at h
    omega
  have hscale := (large_degree_scale L hL hdegree).2
  have hLd : L*Real.sqrt d<(d:ℝ) := by
    have : (0:ℝ)<d := by exact_mod_cast hd0
    linarith
  have hcenter := centered_norm_of_eigenvalues G d hreg (L*Real.sqrt d) (by positivity) hLd hspec
  have he' : ε≤1 := by linarith
  have hrow := row_energy_bounds hn2 ε he he' hsize hdensity
  have hD : 0<rowEnergy n d := by
    have : (0:ℝ)<d := by exact_mod_cast hd0
    nlinarith [mul_pos he this]
  have hnorm := regular_norm_bound G hn2 hdn ε L he he' hL hsize hdensity hdegree hcenter
  have hedges := actual_round_edge_lower G hn (L*Real.sqrt d) (by positivity) hscale hcenter
  have hprofile := profile_from_edges G hn2 hreg hd0 ε he he' hsize hdensity
    (firstRound n) (secondRound n) rounds_disjoint hedges
  have hprofile' := regular_profile_bound ε he (rowEnergy n d) _ hrow.2 hprofile
  have hcoeff : ∀ t w, ((Counts.countGain (formula G units) (correction n d) 0 t).coeff w:ℝ)=
      corrected G d t w := by
    intro t w
    exact congrFun (congrFun (count_matrix_formula G units d) t) w
  rw [←actual_round_profile G _ hcoeff] at hprofile'
  have hslack := regular_allowance_bound hn2 (by omega : d≤n) ε (gapConstant ε)
    (rowEnergy n d) he (gap_constant_pos he) hD.le hrow.1 hlarge
  have h := Counts.count_two_round_nodes (formula G units) (formula_wellFormed G units)
    (correction n d) hn2 (gapConstant ε) (normConstant L ε) (rowEnergy n d)
    (gap_constant_pos he) (norm_constant_pos hL he) hD
    (by rw [count_matrix_formula]; exact hnorm) hprofile' hslack
  exact h

end
end Max2SAT.Regular
