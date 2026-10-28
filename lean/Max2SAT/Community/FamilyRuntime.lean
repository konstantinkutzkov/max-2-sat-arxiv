import Max2SAT.Community.UniversalNodes

/-! The asymptotic discovery hypothesis supplies the explicit conditions,
with a fixed multiplier absorbing all bounded input sizes. -/
namespace Max2SAT.Community
noncomputable section
open Counts FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} [Fintype α]
set_option maxHeartbeats 1000000

theorem discovery_probability_from_density
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (r N : ℕ) (χ : ℝ) (g : ℚ) (hg : 0<g) (hχ : 1≤χ)
    (hgu : (g:ℝ)≤1/(256*Real.sqrt χ))
    (hN : 100≤N) (hrN : r≤N) (hcorrection : 5120000*r*χ≤(N:ℝ))
    (hsize : 1792*r*Real.sqrt χ≤(g:ℝ)*N)
    (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (input : (Edge n → α) → Formula n) (A : Matrix (Fin n) (Fin n) ℝ)
    (B ν μ B₀ : ℝ) (hB : 1≤B) (hν : 0<ν) (hμ : 0≤μ) (hB₀ : 0≤B₀)
    (hAsym : A.IsHermitian) (hr : A.rank≤r)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : discoveryConstant r χ g*(B^2*Real.log n+B₀^2+μ^2)≤n*ν)
    (hF : ∀ x, wellFormed (input x))
    (hmodel : ∀ x, interactionMatrix (gainExpr (input x))=
      A+pairMatrix (fun e => X e (x e))-Matrix.diagonal (fun i => A i i))
    (hA : ‖A‖≤μ*n) (hdiag : ∀ i, |A i i|≤B₀) :
    1-1/(n:ℝ)≤prob (product p) (fun x =>
      (diagonalizedNodes (input x) r g:ℝ)≤(2:ℝ)^N*searchPolynomial n r*
        (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n) := by
  have hbase := discovery_base_bounds g χ hg hχ
  by_cases hn:n<N
  · have hh (x : Edge n → α) := small_size_nodes (input x) r N g _ hn hbase.1
    simp only [hh,prob_true]
    have hnon : 0≤1/(n:ℝ) := by positivity
    linarith
  · have hNn : N≤n := by omega
    have hNn' : (N:ℝ)≤n := by exact_mod_cast hNn
    have hns : 100≤n := hN.trans hNn
    have hc := discovery_density_conditions n r χ B ν μ B₀ g hns hχ hB hg hd
    have h := diagonalized_search_probability bvh ledoux p X input r (hrN.trans hNn) A g B ν χ μ B₀
      hns hg (by linarith) hν hχ hμ hB₀ hAsym hr hgu hm hb hv hc.1 hF hmodel hA hdiag
      hc.2.1 hc.2.2.1 hc.2.2.2
      (hsize.trans (mul_le_mul_of_nonneg_left hNn' (by exact_mod_cast hg.le)))
      (hcorrection.trans hNn')
    apply h.1.trans
    apply prob_mono_support
    intro x _ hx
    have hp : 0≤(exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n :=
      pow_nonneg (Real.exp_pos _).le _
    have hm' := mul_le_mul_of_nonneg_right (search_polynomial_bounds n r).2.2 hp
    have hC : 1≤(2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hpoly : 0≤searchPolynomial n r := by unfold searchPolynomial; positivity
    have hscale := mul_le_mul_of_nonneg_right hC (mul_nonneg hpoly hp)
    exact hx.trans (hm'.trans (by simpa only [one_mul,mul_assoc] using hscale))

/-- Fixed class parameters yield one rational search parameter, density
threshold, multiplier, and exponential base, uniformly over all input sizes
and finite independent-pair laws. No hidden mean is supplied to the search. -/
theorem discovery_family (r : ℕ) (χ : ℝ) (hχ : 1≤χ) :
    ∃ g : ℚ, ∃ C K c : ℝ, 0<g ∧ 0<C ∧ 0<K ∧ 1≤c ∧ c<2 ∧
      ∀ (n : ℕ) (α : Type) [Fintype α],
      External.BandeiraVanHandel n → External.LedouxUpperTail (Edge n) α →
      ∀ (p : Edge n → Law α) (X : Edge n → α → ℝ)
        (input : (Edge n → α) → Formula n) (A : Matrix (Fin n) (Fin n) ℝ)
        (B ν μ B₀ : ℝ),
      1≤B → 0<ν → 0≤μ → 0≤B₀ → A.IsHermitian → A.rank≤r →
      (∀ e, expect (p e) (X e)=0) →
      (∀ e x, 0<(p e).mass x → |X e x|≤B) →
      (∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧ expect (p e) (fun x => (X e x)^2)≤χ*ν) →
      C*(B^2*Real.log n+B₀^2+μ^2)≤n*ν →
      (∀ x, wellFormed (input x)) →
      (∀ x, interactionMatrix (gainExpr (input x))=
        A+pairMatrix (fun e => X e (x e))-Matrix.diagonal (fun i => A i i)) →
      ‖A‖≤μ*n → (∀ i, |A i i|≤B₀) →
      1-1/(n:ℝ)≤prob (product p) (fun x =>
        (diagonalizedNodes (input x) r g:ℝ)≤K*searchPolynomial n r*c^n) := by
  obtain ⟨g,hg,_,hgu⟩ := rational_discovery_parameter χ hχ
  obtain ⟨N,hN,hrN,hcorrection,hsize⟩ := discovery_family_threshold r χ g hg
  have hb := discovery_base_bounds g χ hg hχ
  refine ⟨g,discoveryConstant r χ g,2^N,
    exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)),hg,?_,by positivity,hb.1,hb.2,?_⟩
  · linarith [(discovery_constant_bounds r χ g hχ).1]
  · intro n α _ bvh ledoux p X input A B ν μ B₀ hB hν hμ hB₀ hAsym hr hm hbound hv hd hF hmodel hA hdiag
    exact discovery_probability_from_density bvh ledoux r N χ g hg hχ hgu hN hrN hcorrection hsize
      p X input A B ν μ B₀ hB hν hμ hB₀ hAsym hr hm hbound hv hd hF hmodel hA hdiag

end
end Max2SAT.Community
