import Max2SAT.Community.FamilyRuntime
import Max2SAT.Community.SBMVariance

/-! The hidden-community runtime theorem on the original Bernoulli product
law. The input to the algorithm is only the observed formula and fixed
class parameters. Unit clauses may be any function of the sampled graph. -/
namespace Max2SAT.Community
noncomputable section
open Counts FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
variable {n k : ℕ}
set_option maxHeartbeats 1000000

def sbmLaw (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ)
    (h0 : ∀ a b, 0≤π a b) (h1 : ∀ a b, π a b≤1) : Law (Edge n → Bool) :=
  product (fun e => IndependentPairs.bernoulli (blockProbability group π e)
    (h0 (group e.val.1) (group e.val.2)) (h1 (group e.val.1) (group e.val.2)))

theorem sbm_density_transfer (n : ℕ) (C v : ℝ) (hn : 100≤n) (hC : 0≤C)
    (hd : 5*C*Real.log n≤n*v) : C*((2:ℝ)^2*Real.log n+2^2+2^2)≤n*(4*v) := by
  have hn100 : (100:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hlog : (1/2:ℝ)≤Real.log n := by
    have hh := Real.one_sub_inv_le_log_of_pos hn0
    have hi : 1/(n:ℝ)≤1/2 := (div_le_iff₀ hn0).mpr (by linarith)
    rw [one_div] at hi
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog hC]

theorem sbm_probability_from_density
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) Bool)
    (N : ℕ) (χ : ℝ) (g : ℚ) (hg : 0<g) (hχ : 1≤χ)
    (hgu : (g:ℝ)≤1/(256*Real.sqrt χ))
    (hN : 100≤N) (hkN : k≤N) (hcorrection : 5120000*k*χ≤(N:ℝ))
    (hsize : 1792*k*Real.sqrt χ≤(g:ℝ)*N)
    (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ) (hπ : π.IsSymm)
    (h0 : ∀ a b, 0≤π a b) (h1 : ∀ a b, π a b≤1)
    (units : (Edge n → Bool) → List (Literal n)) (v : ℝ) (hv : 0<v)
    (hvar : ∀ a b, v≤π a b*(1-π a b) ∧ π a b*(1-π a b)≤χ*v)
    (hd : 5*discoveryConstant k χ g*Real.log n≤n*v) :
    1-1/(n:ℝ)≤prob (sbmLaw group π h0 h1) (fun x =>
      (diagonalizedNodes (sampledFormula x (units x)) k g:ℝ)≤(2:ℝ)^N*searchPolynomial n k*
        (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n) := by
  by_cases hn:n<N
  · have hh (x : Edge n → Bool) := small_size_nodes (sampledFormula x (units x)) k N g _ hn
      (discovery_base_bounds g χ hg hχ).1
    simp only [hh,prob_true]
    have hnon : 0≤1/(n:ℝ) := by positivity
    linarith
  · have hn100 : 100≤n := hN.trans (by omega)
    have hC : 0≤discoveryConstant k χ g := by linarith [(discovery_constant_bounds k χ g hχ).1]
    apply discovery_probability_from_density bvh ledoux k N χ g hg hχ hgu hN hkN hcorrection hsize
      _ (fun e => centeredCut (blockProbability group π e))
      (fun x => sampledFormula x (units x)) (blockMean group π) 2 (4*v) 2 2
      (by norm_num) (by positivity) (by norm_num) (by norm_num)
      (block_mean_hermitian group π hπ) (block_mean_rank group π)
    · intro e; exact centered_cut_mean _ _ _
    · intro e b _; exact centered_cut_bound _ (h0 _ _) (h1 _ _) b
    · intro e
      dsimp only [blockProbability]
      simp only [centered_cut_variance]
      have hh := hvar (group e.val.1) (group e.val.2)
      constructor <;> nlinarith [hh.1,hh.2]
    · exact sbm_density_transfer n _ v hn100 hC hd
    · intro x; exact sampled_formula_wellFormed x (units x)
    · intro x; exact sampled_formula_model group π hπ x (units x)
    · exact block_mean_norm group π h0 h1
    · intro i; exact block_mean_entry_bound group π h0 h1 i i

/-- The paper's SBM theorem at the explicit recursive-call level. The
constants and rational algorithm parameter are fixed before n, the
partition, probabilities, observed graph, and added units are supplied. -/
theorem sbm_family (k : ℕ) (hk : 1≤k) (χ : ℝ) (hχ : 1≤χ) :
    ∃ g : ℚ, ∃ C K c : ℝ, 0<g ∧ 0<C ∧ 0<K ∧ 1≤c ∧ c<2 ∧
      ∀ (n : ℕ), External.BandeiraVanHandel n → External.LedouxUpperTail (Edge n) Bool →
      ∀ (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ) (_hπ : π.IsSymm)
        (h0 : ∀ a b, 0≤π a b) (h1 : ∀ a b, π a b≤1)
        (units : (Edge n → Bool) → List (Literal n)),
      0<minBlockVariance (by omega : 0<k) π →
      maxBlockVariance (by omega : 0<k) π≤χ*minBlockVariance (by omega : 0<k) π →
      C*Real.log n≤n*minBlockVariance (by omega : 0<k) π →
      1-1/(n:ℝ)≤prob (sbmLaw group π h0 h1) (fun x =>
        (diagonalizedNodes (sampledFormula x (units x)) k g:ℝ)≤K*searchPolynomial n k*c^n) := by
  obtain ⟨g,hg,_,hgu⟩ := rational_discovery_parameter χ hχ
  obtain ⟨N,hN,hkN,hcorrection,hsize⟩ := discovery_family_threshold k χ g hg
  have hb := discovery_base_bounds g χ hg hχ
  refine ⟨g,5*discoveryConstant k χ g,2^N,
    exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)),hg,?_,by positivity,hb.1,hb.2,?_⟩
  · have hC := (discovery_constant_bounds k χ g hχ).1
    nlinarith
  · intro n bvh ledoux group π hπ h0 h1 units hv hratio hd
    apply sbm_probability_from_density bvh ledoux N χ g hg hχ hgu hN hkN hcorrection hsize
      group π hπ h0 h1 units _ hv _ hd
    intro a b
    have h := block_variance_bounds (by omega : 0<k) π a b
    exact ⟨h.1,h.2.trans hratio⟩

end
end Max2SAT.Community
