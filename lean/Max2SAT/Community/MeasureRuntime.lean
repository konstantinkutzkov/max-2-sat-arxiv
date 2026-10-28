import Max2SAT.Community.FamilyRuntime
import Max2SAT.Community.MeasureNoise

/-! Discovery for the original integer-valued random input on an arbitrary
probability space. The noise event controls every formula with those binary
interactions, so added units may depend on the draw and on extra randomness. -/
namespace Max2SAT.Community
noncomputable section
open Counts FiniteLaw RandomInput IndependentPairs MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
set_option maxHeartbeats 1000000

theorem pair_mean_decomposition (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (z : Edge n → ℝ) :
    pairMatrix z=A+pairMatrix (fun e => z e-A e.val.1 e.val.2)-
      Matrix.diagonal (fun i => A i i) := by
  ext i j
  have hs : A j i=A i j := by simpa using hA.apply i j
  rcases lt_trichotomy i j with h|rfl|h
  · simp [pairMatrix,h,ne_of_lt h]
  · simp [pairMatrix]
  · simp [pairMatrix,h,not_lt.mpr h.le,ne_of_gt h,hs]

theorem integer_discovery_event_from_density
    (bvh : External.BandeiraVanHandel n)
    (ledoux : ∀ (α : Type) [Fintype α], External.LedouxUpperTail (Edge n) α)
    (r N : ℕ) (χ : ℝ) (g : ℚ) (hg : 0<g) (hχ : 1≤χ)
    (hgu : (g:ℝ)≤1/(256*Real.sqrt χ))
    (hN : 100≤N) (hrN : r≤N) (hcorrection : 5120000*r*χ≤(N:ℝ))
    (hsize : 1792*r*Real.sqrt χ≤(g:ℝ)*N)
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]
    (J : Edge n → Ω → ℤ) (hJ : ∀ e, Measurable (J e)) (hi : iIndepFun J μ₀)
    (input : Ω → Formula n) (A : Matrix (Fin n) (Fin n) ℝ)
    (B ν μ B₀ : ℝ) (hB : 1≤B) (hν : 0<ν) (hμ : 0≤μ) (hB₀ : 0≤B₀)
    (hAsym : A.IsHermitian) (hr : A.rank≤r)
    (hm : ∀ e, (∫ ω, (J e ω:ℝ) ∂μ₀)=A e.val.1 e.val.2)
    (hb : ∀ e, ∀ᵐ ω ∂μ₀, |(J e ω:ℝ)-A e.val.1 e.val.2|≤B)
    (hv : ∀ e, ν≤variance (fun ω => (J e ω:ℝ)) μ₀ ∧
      variance (fun ω => (J e ω:ℝ)) μ₀≤χ*ν)
    (hd : discoveryConstant r χ g*(B^2*Real.log n+B₀^2+μ^2)≤n*ν)
    (hF : ∀ ω, wellFormed (input ω))
    (hmodel : ∀ ω, interactionMatrix (gainExpr (input ω))=pairMatrix (fun e => (J e ω:ℝ)))
    (hA : ‖A‖≤μ*n) (hdiag : ∀ i, |A i i|≤B₀) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1-1/(n:ℝ)≤μ₀.real E ∧ ∀ ω∈E,
      (diagonalizedNodes (input ω) r g:ℝ)≤(2:ℝ)^N*searchPolynomial n r*
        (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n := by
  have hbase := discovery_base_bounds g χ hg hχ
  by_cases hn:n<N
  · refine ⟨Set.univ,MeasurableSet.univ,?_,fun ω _ =>
      small_size_nodes (input ω) r N g _ hn hbase.1⟩
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one]
    have hnon : 0≤1/(n:ℝ) := by positivity
    linarith
  · have hNn : N≤n := by omega
    have hNn' : (N:ℝ)≤n := by exact_mod_cast hNn
    have hns : 100≤n := hN.trans hNn
    have hc := discovery_density_conditions n r χ B ν μ B₀ g hns hχ hB hg hd
    have hnoise := integer_noise_probability bvh ledoux μ₀ J hJ hi
      (fun e => A e.val.1 e.val.2) B ν χ (by omega) (by linarith) hν hχ hm hb hv hc.1
    refine ⟨{ω | rawGood (fun e => (J e ω:ℝ)-A e.val.1 e.val.2) ν χ},
      integer_event_measurable J hJ
        (fun z => rawGood (fun e => (z e:ℝ)-A e.val.1 e.val.2) ν χ),hnoise,?_⟩
    intro ω hraw
    have hmodel' := (hmodel ω).trans (pair_mean_decomposition A hAsym (fun e => (J e ω:ℝ)))
    have hQ := computed_discovery_guarantees (input ω) r (hrN.trans hNn) A _ B₀ ν χ
      (hF ω) hAsym hr hB₀ hν.le (by linarith) hmodel' hdiag hraw.2 hc.2.1 hc.2.2.1
      (hcorrection.trans hNn')
    have hnode := (computed_nodes_on_event (input ω) (discoverFormula r) A _ g ν χ μ B₀
      (1/(n:ℝ)^4) (hF ω) hns hg hν hχ hμ hB₀ (by positivity) hgu hmodel' hA hdiag
      hc.2.1 hc.2.2.1 hc.2.2.2
      (hsize.trans (mul_le_mul_of_nonneg_left hNn' (by exact_mod_cast hg.le))) hraw hQ).1
    change (diagonalizedNodes (input ω) r g:ℝ)≤_ at hnode
    have hp : 0≤(exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n :=
      pow_nonneg (Real.exp_pos _).le _
    have hm' := mul_le_mul_of_nonneg_right (search_polynomial_bounds n r).2.2 hp
    have hC : 1≤(2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hpoly : 0≤searchPolynomial n r := by unfold searchPolynomial; positivity
    have hscale := mul_le_mul_of_nonneg_right hC (mul_nonneg hpoly hp)
    exact hnode.trans (hm'.trans (by simpa only [one_mul,mul_assoc] using hscale))

/-- Fixed class parameters precede every original probability space, size,
coefficient distribution, hidden mean, and choice of added unit clauses. -/
theorem integer_discovery_family (r : ℕ) (χ : ℝ) (hχ : 1≤χ) :
    ∃ g : ℚ, ∃ C K c : ℝ, 0<g ∧ 0<C ∧ 0<K ∧ 1≤c ∧ c<2 ∧
      ∀ (n : ℕ), External.BandeiraVanHandel n →
      (∀ (α : Type) [Fintype α], External.LedouxUpperTail (Edge n) α) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]
        (J : Edge n → Ω → ℤ),
      (∀ e, Measurable (J e)) → iIndepFun J μ₀ →
      ∀ (input : Ω → Formula n) (A : Matrix (Fin n) (Fin n) ℝ) (B ν μ B₀ : ℝ),
      1≤B → 0<ν → 0≤μ → 0≤B₀ → A.IsHermitian → A.rank≤r →
      (∀ e, (∫ ω, (J e ω:ℝ) ∂μ₀)=A e.val.1 e.val.2) →
      (∀ e, ∀ᵐ ω ∂μ₀, |(J e ω:ℝ)-A e.val.1 e.val.2|≤B) →
      (∀ e, ν≤variance (fun ω => (J e ω:ℝ)) μ₀ ∧ variance (fun ω => (J e ω:ℝ)) μ₀≤χ*ν) →
      C*(B^2*Real.log n+B₀^2+μ^2)≤n*ν →
      (∀ ω, wellFormed (input ω)) →
      (∀ ω, interactionMatrix (gainExpr (input ω))=pairMatrix (fun e => (J e ω:ℝ))) →
      ‖A‖≤μ*n → (∀ i, |A i i|≤B₀) →
      ∃ E : Set Ω, MeasurableSet E ∧ 1-1/(n:ℝ)≤μ₀.real E ∧ ∀ ω∈E,
        (diagonalizedNodes (input ω) r g:ℝ)≤K*searchPolynomial n r*c^n := by
  obtain ⟨g,hg,_,hgu⟩ := rational_discovery_parameter χ hχ
  obtain ⟨N,hN,hrN,hcorrection,hsize⟩ := discovery_family_threshold r χ g hg
  have hb := discovery_base_bounds g χ hg hχ
  refine ⟨g,discoveryConstant r χ g,2^N,
    exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)),hg,?_,by positivity,hb.1,hb.2,?_⟩
  · linarith [(discovery_constant_bounds r χ g hχ).1]
  · intro n bvh ledoux Ω _ μ₀ _ J hJ hi input A B ν μ B₀ hB hν hμ hB₀ hAsym hr hm hbound hv hd hF hmodel hA hdiag
    exact integer_discovery_event_from_density bvh ledoux r N χ g hg hχ hgu
      hN hrN hcorrection hsize μ₀ J hJ hi input A B ν μ B₀ hB hν hμ hB₀ hAsym hr
      hm hbound hv hd hF hmodel hA hdiag

end
end Max2SAT.Community
