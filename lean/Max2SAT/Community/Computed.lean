import Max2SAT.Community.Runtime
import Max2SAT.Community.RationalRoot

/-! Plug the actual rational square-root spacing into the search wrapper.
Only discovery of the rational directions remains a callback. -/
namespace Max2SAT.Community
open Counts
variable {n r : ℕ}

def withComputedSpacing (F : Formula n) (g : ℚ) (d : Representation n r) : Representation n r :=
  {d with trialSpacing := computedSpacing n g (remainderEnergy F d) (coefficientMass d)}

def computedSearch (F : Formula n) (g : ℚ) (discover : Formula n → Representation n r) :
    Option (Assignment n) := communitySearch F (fun G => withComputedSpacing G g (discover G))

def computedResult (F : Formula n) (g : ℚ) (discover : Formula n → Representation n r) :
    Option (ℤ × Assignment n) := communityResult F (fun G => withComputedSpacing G g (discover G))

def computedNodes (F : Formula n) (g : ℚ) (discover : Formula n → Representation n r) : ℕ :=
  communityNodes F (fun G => withComputedSpacing G g (discover G))

theorem computed_result_correct (F : Formula n) (g : ℚ) (discover : Formula n → Representation n r)
    (hF : wellFormed F) :
    ∃ q x, computedResult F g discover=some (q,x) ∧ q=score F x ∧ ∀ y, score F y≤q :=
  community_result_correct F _ hF

theorem computed_grid_size (F : Formula n) (g : ℚ) (d : Representation n r) (hn : 1≤n)
    (hv : ∀ k, ∑ t, (d.direction k t:ℝ)^2≤1) :
    ((projectionGrids d.direction (fun _ => cappedSpacing n (withComputedSpacing F g d).trialSpacing)).length:ℝ)≤
      (2*(n:ℝ)^3+3)^r := capped_grid_size d.direction _ hn hv

open scoped Matrix.Norms.L2Operator in
/-- Actual node bound for the computed-spacing branch. The hypotheses on
approximation quality remain explicit, rather than being hidden in the
formal preprocessing callback. -/
theorem computed_positive_nodes (F : Formula n) (discover : Formula n → Representation n r)
    (g : ℚ) (K : ℝ) (hF : wellFormed F) (hn : 4≤n) (hg : 0<g) (hK : 0<K)
    (hD : 0<remainderEnergy F (discover F)) (hΛ : 0<coefficientMass (discover F))
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
  have hs := computed_spacing_bounds n g _ _ (by omega) hg hD hΛ
  have h := projection_phase_nodes F (withComputedSpacing F g (discover F)) hF hn g K
    (remainderEnergy F (discover F)) (by exact_mod_cast hg) hK (by exact_mod_cast hD)
    hv (by exact_mod_cast hΛ) hbudget hs.1 hs.2 hN hprofile
  have hnodes : computedNodes F g discover=projectionNodes F (withComputedSpacing F g (discover F)) := by
    apply community_positive_nodes F _ hn
    · exact ne_of_gt hD
    · exact ne_of_gt hΛ
  rw [hnodes]
  exact h

end Max2SAT.Community
