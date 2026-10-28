import Max2SAT.Community.CoefficientBudget
import Max2SAT.Community.RepresentationMatrix
import Max2SAT.Community.RandomEvent

/-! Connect the actual formula, computed representation and search to the
proved noise event. ApproximationGuarantees lists intermediate numerical
conditions, derived for the actual construction in ComputedDiscovery. -/
namespace Max2SAT.Community
noncomputable section
open Counts FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ} {α : Type*} [Fintype α]
set_option maxHeartbeats 1000000

/-- Intermediate claims about a numerical representation. ComputedDiscovery
proves them for the constructed frame; they are not external assumptions. -/
structure ApproximationGuarantees (F : Formula n) (d : Representation n r)
    (A X : Matrix (Fin n) (Fin n) ℝ) (B₀ ζ ν : ℝ) : Prop where
  directions_unit : ∀ k, ∑ t, (d.direction k t:ℝ)^2≤1
  diagonal_entries : ∀ k, (d.coefficient k:ℝ)=
    ∑ t, (d.direction k t:ℝ)*(∑ w, interactionMatrix (gainExpr F) t w*(d.direction k w:ℝ))
  truncation : ‖interactionMatrix (gainExpr F)-representationMatrix d‖≤‖X‖+B₀+2*ζ
  frobenius_error : frobenius (A-representationMatrix d)≤(1/100:ℝ)*n*Real.sqrt ν

/-- All search-quality hypotheses are derived from the raw noise event,
original mean/size bounds and the explicitly listed numerical guarantees. -/
theorem computed_nodes_on_event (F : Formula n) (discover : Formula n → Representation n r)
    (A : Matrix (Fin n) (Fin n) ℝ) (z : Edge n → ℝ) (g : ℚ) (ν χ μ B₀ ζ : ℝ)
    (hF : wellFormed F) (hn : 100≤n) (hg : 0<g) (hν : 0<ν) (hχ : 1≤χ)
    (hμ : 0≤μ) (hB : 0≤B₀) (hζ : 0≤ζ)
    (hgu : (g:ℝ)≤1/(256*Real.sqrt χ))
    (hmodel : interactionMatrix (gainExpr F)=A+pairMatrix z-Matrix.diagonal (fun i => A i i))
    (hA : ‖A‖≤μ*n) (hdiag : ∀ i, |A i i|≤B₀)
    (hBsmall : B₀≤Real.sqrt (n*χ*ν)) (hζsmall : ζ≤Real.sqrt (n*χ*ν))
    (hmean : (256*r*μ)^2≤(g:ℝ)^2*n*ν)
    (hsize : 1792*r*Real.sqrt χ≤(g:ℝ)*n)
    (hraw : rawGood z ν χ)
    (hQ : ApproximationGuarantees F (discover F) A (pairMatrix z) B₀ ζ ν) :
    (computedNodes F g discover:ℝ)≤(4*(n:ℝ)+3)^r*(2+14*n)*
      (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n ∧
      exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ))<2 := by
  let H := projectionGain F (discover F).coefficient (discover F).direction (fun _ => 0)
  have heq : interactionMatrix H=pairMatrix z+offDiagonal (A-representationMatrix (discover F)) := by
    rw [show interactionMatrix H=offDiagonal (interactionMatrix (gainExpr F)-representationMatrix (discover F)) from
      representation_remainder F (discover F) hF]
    exact remainder_identity _ _ _ _ hmodel (pair_matrix_diagonal z)
  have hnoise : ‖pairMatrix z‖+B₀≤7*Real.sqrt (n*χ*ν) := by
    nlinarith [hraw.2,Real.sqrt_nonneg (n*χ*ν)]
  have hrem := remainder_operator_bound _ A (representationMatrix (discover F)) (pairMatrix z)
    B₀ ζ hB hζ hmodel hdiag hQ.truncation
  have hnorm : ‖interactionMatrix H‖≤18*Real.sqrt (n*χ*ν) := by
    have he := representation_remainder F (discover F) hF
    change ‖interactionMatrix H‖≤_ 
    rw [he]
    linarith [hrem.1]
  have hrawE := raw_good_energy z ν χ (by omega) hraw
  have hs := discovery_structural_conditions H (pairMatrix z) (A-representationMatrix (discover F))
    ν χ g hn hν hχ (by exact_mod_cast hg) hgu heq hrawE hraw.1.2 hQ.frobenius_error hnorm
  have henergy := remainder_energy_bounds (pairMatrix z) (A-representationMatrix (discover F))
    ν χ hn hν.le hχ hrawE hQ.frobenius_error
  rw [←heq] at henergy
  have hD : 0<remainderEnergy F (discover F) := by
    have he := remainder_energy_cast F (discover F)
    rw [←he] at hs
    exact_mod_cast hs.1
  have hbudget := coefficient_budget_from_matrix _ A (pairMatrix z) (discover F)
    μ ν χ g (matrixEnergy (interactionMatrix H)) B₀ hμ hν.le (by linarith)
    (by exact_mod_cast hg.le) hB hQ.directions_unit hQ.diagonal_entries hmodel hA hdiag
    hnoise henergy.1 hmean hsize
  have he := remainder_energy_cast F (discover F)
  rw [←he] at hbudget hs
  exact computed_nodes_of_quality F discover g (400*χ) hF (by omega) hg (by positivity)
    hD hQ.directions_unit hbudget hs.2.1 hs.2.2

/-- The probabilistic assembly is complete conditional on the numerical
routine's stated guarantees on the good noise event. ComputedDiscovery
subsequently supplies these guarantees for the actual rational routine. -/
theorem discovered_search_probability
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (input : (Edge n → α) → Formula n) (discover : Formula n → Representation n r)
    (A : Matrix (Fin n) (Fin n) ℝ) (g : ℚ) (B ν χ μ B₀ ζ : ℝ)
    (hn : 100≤n) (hg : 0<g) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hμ : 0≤μ) (hB₀ : 0≤B₀) (hζ : 0≤ζ)
    (hgu : (g:ℝ)≤1/(256*Real.sqrt χ))
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤n*ν)
    (hF : ∀ x, wellFormed (input x))
    (hmodel : ∀ x, interactionMatrix (gainExpr (input x))=
      A+pairMatrix (fun e => X e (x e))-Matrix.diagonal (fun i => A i i))
    (hA : ‖A‖≤μ*n) (hdiag : ∀ i, |A i i|≤B₀)
    (hBsmall : B₀≤Real.sqrt (n*χ*ν)) (hζsmall : ζ≤Real.sqrt (n*χ*ν))
    (hmean : (256*r*μ)^2≤(g:ℝ)^2*n*ν)
    (hsize : 1792*r*Real.sqrt χ≤(g:ℝ)*n)
    (hQ : ∀ x, 0<(product p).mass x → rawGood (fun e => X e (x e)) ν χ →
      ApproximationGuarantees (input x) (discover (input x)) A (pairMatrix (fun e => X e (x e))) B₀ ζ ν) :
    1-1/(n:ℝ)≤prob (product p) (fun x =>
      (computedNodes (input x) g discover:ℝ)≤(4*(n:ℝ)+3)^r*(2+14*n)*
        (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n) ∧
      exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ))<2 := by
  refine ⟨?_,exponential_base_lt_two _ _ (by norm_num)
    (round_rate_pos 2 (by omega) (1/2) g (400*χ) (by norm_num) (by exact_mod_cast hg) (by positivity))⟩
  apply (discovery_noise_probability bvh ledoux p X (by omega) B ν χ hB hν hχ hm hb hv hd).trans
  apply prob_mono_support
  intro x hx hraw
  exact (computed_nodes_on_event (input x) discover A _ g ν χ μ B₀ ζ (hF x) hn hg hν hχ
    hμ hB₀ hζ hgu (hmodel x) hA hdiag hBsmall hζsmall hmean hsize hraw (hQ x hx hraw)).1

end
end Max2SAT.Community
