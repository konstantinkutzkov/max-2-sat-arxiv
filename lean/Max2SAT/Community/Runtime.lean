import Max2SAT.Community.Algorithm
import Max2SAT.Community.Rounds
import Max2SAT.Community.Energy
import Max2SAT.Community.Noise

/-! Runtime of the capped projection phase, under explicit deterministic
matrix/profile hypotheses. These are the obligations of the discovery
analysis; this module does not assert that every approximation meets them. -/
namespace Max2SAT.Community
noncomputable section
open Counts
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}
set_option maxHeartbeats 800000

theorem coefficient_mass_cast (d : Representation n r) :
    (coefficientMass d:ℝ)=∑ k, |(d.coefficient k:ℝ)| := by simp [coefficientMass]

theorem remainder_energy_cast (F : Formula n) (d : Representation n r) :
    (remainderEnergy F d:ℝ)=matrixEnergy (interactionMatrix (projectionGain F d.coefficient d.direction (fun _ => 0))) := by
  rw [matrix_energy_sum]
  simp [remainderEnergy,interactionMatrix]

/-- No probability assertion appears here: this checks that the computed
spacing, cap, allowance and actual recursive node count fit the proved
count/projection theorem. -/
theorem projection_phase_nodes (F : Formula n) (d : Representation n r)
    (hF : wellFormed F) (hn : 4≤n) (g K D : ℝ)
    (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hv : ∀ k, ∑ t, (d.direction k t:ℝ)^2≤1)
    (hΛ : 0<(coefficientMass d:ℝ))
    (hbudget : (coefficientMass d:ℝ)≤g*n*Real.sqrt D/64)
    (hδlo : g*Real.sqrt (n*D)/(128*(coefficientMass d:ℝ))≤(d.trialSpacing:ℝ))
    (hδhi : (d.trialSpacing:ℝ)≤g*Real.sqrt (n*D)/(64*(coefficientMass d:ℝ)))
    (hN : ‖interactionMatrix (projectionGain F d.coefficient d.direction (fun _ => 0))‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      crossProfile (interactionMatrix (projectionGain F d.coefficient d.direction (fun _ => 0)))
        (secondRound n) (firstRound n)) :
    (projectionNodes F d:ℝ)≤(4*(n:ℝ)+3)^r*(2+14*n)*
      (exponentialBase (1/2) (roundRate 2 (1/2) g K))^n ∧
      exponentialBase (1/2) (roundRate 2 (1/2) g K)<2 := by
  have hlow := spacing_from_allowance n g D _ _ (by omega) hg hD hΛ hbudget hδlo
  have hinactive := capped_spacing_inactive d.trialSpacing (by omega : 2≤n) hlow
  have hslack := spacing_allowance n g D _ _ hg.le hD.le hΛ hbudget hδhi
  have hδp := capped_spacing_pos d.trialSpacing (by omega : 0<n)
  have hp : 0<(roundPrefix (twoRound n) 2).card := by rw [two_round_prefix_card]; omega
  have hallow : (∑ t∈roundPrefix (twoRound n) 2,
      (allowance d.coefficient d.direction (fun _ => cappedSpacing n d.trialSpacing) t:ℝ))≤
      g*n*Real.sqrt D/8 := by
    have h := prefix_allowance_bound d.coefficient d.direction _ hδp.le hv (roundPrefix (twoRound n) 2)
    push_cast at h
    rw [hinactive] at h ⊢
    have he : (∑ k, |(d.coefficient k:ℝ)| * ((d.trialSpacing:ℝ)*Real.sqrt n+1))=
        (coefficientMass d:ℝ)*((d.trialSpacing:ℝ)*Real.sqrt n+1) := by
      rw [coefficient_mass_cast,Finset.sum_mul]
    rw [he] at h
    have hnon : 0≤g*n*Real.sqrt D := by positivity
    linarith
  have h := projection_round_nodes F hF d.coefficient d.direction
    (fun _ => cappedSpacing n d.trialSpacing) (fun _ => hδp.le)
    (projectionGrids d.direction (fun _ => cappedSpacing n d.trialSpacing))
    (twoRound n) 2 (by omega) two_round_order two_round_range hp
    (1/2) g K D (by norm_num) (by norm_num) hg hK hD two_round_size hN
    (by simpa only [two_round_profile] using hprofile) hallow
  have hc := useful_grid_size d.direction d.trialSpacing (by omega : 2≤n) hv hlow
  have hbase : 0≤(exponentialBase (1/2) (roundRate 2 (1/2) g K))^n :=
    pow_nonneg (Real.exp_pos _).le _
  refine ⟨?_,h.2⟩
  apply h.1.trans
  convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc
    (show 0≤(2+14*(n:ℝ)) by positivity)) hbase using 1; ring

/-- The positive-mass branch of the full wrapper has exactly this node count. -/
theorem community_positive_nodes (F : Formula n) (prepare : Formula n → Representation n r)
    (hn : 4≤n) (hD : remainderEnergy F (prepare F)≠0) (hΛ : coefficientMass (prepare F)≠0) :
    communityNodes F prepare=projectionNodes F (prepare F) := by
  simp [communityNodes,show ¬n<4 by omega,hD,hΛ]

/-- This is the numerical target after deterministic perturbation, with the
revised norm constant 400*chi and the unchanged choice of g. -/
theorem discovery_structural_conditions (H : Fin n → Affine n)
    (X E : Matrix (Fin n) (Fin n) ℝ) (ν χ g : ℝ)
    (hn : 100≤n) (hν : 0<ν) (hχ : 1≤χ) (hg : 0<g)
    (hgu : g≤1/(256*Real.sqrt χ))
    (heq : interactionMatrix H=X+offDiagonal E)
    (hraw : (99/100:ℝ)*n*((n:ℝ)-1)*ν≤(frobenius X)^2 ∧
      (frobenius X)^2≤(101/100:ℝ)*χ*n*((n:ℝ)-1)*ν)
    (hrows : ∀ i∈secondRound n, (99/100:ℝ)*(firstRound n).card*ν≤
      ∑ j∈firstRound n, (X i j)^2)
    (hE : frobenius E≤(1/100:ℝ)*n*Real.sqrt ν)
    (hnorm : ‖interactionMatrix H‖≤18*Real.sqrt (n*χ*ν)) :
    0<matrixEnergy (interactionMatrix H) ∧
    ‖interactionMatrix H‖^2≤400*χ*matrixEnergy (interactionMatrix H) ∧
    4*Real.sqrt 3*(g*n*Real.sqrt (matrixEnergy (interactionMatrix H)))≤
      crossProfile (interactionMatrix H) (secondRound n) (firstRound n) := by
  have henergy := remainder_energy_bounds X E ν χ hn hν.le hχ hraw hE
  rw [←heq] at henergy
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hD : 0<matrixEnergy (interactionMatrix H) := (by positivity :
    (0:ℝ)<(9/10)*n*ν).trans_le henergy.1
  have hs := round_sizes (n:=n) (by omega : 20≤n)
  have hprofile := corrected_profile_lower X E (secondRound n) (firstRound n) ν hν.le hs.2 hs.1 hrows hE
  rw [←heq] at hprofile
  refine ⟨hD,?_,?_⟩
  · exact discovery_operator_constant _ ν χ _ hν.le (by linarith) henergy.1 hnorm
  · exact (discovery_profile_target ν χ _ g hν.le hχ hD.le hg.le hgu henergy.2).trans hprofile

end
end Max2SAT.Community
