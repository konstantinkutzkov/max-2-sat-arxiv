import Max2SAT.IndependentPairs.MatrixRowMoments
import Max2SAT.IndependentPairs.MatrixTail
import Max2SAT.IndependentPairs.MatrixParameters

/-! The independent-pair operator-norm estimate, conditional only on the two
explicitly cited published results. All input, moment and numerical checks
for this estimate are proved in the development. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
variable {n : ℕ} {α : Type*} [Fintype α]

theorem independent_pair_norm_tail
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ)
    (hn : 2≤n) (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 0<χ)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hdensity : (10^9:ℝ)*B^2*Real.log n≤n*χ*ν) :
    prob (product p) (fun x => (290/100:ℝ)*Real.sqrt (n*χ*ν)<
      ‖upperMatrix T (fun e => X e (x e))‖)≤1/(n:ℝ)^3 := by
  have hn0 : 0<n := by omega
  have hnp : (0:ℝ)<n := by exact_mod_cast hn0
  have hscale : 0<(n:ℝ)*χ*ν := by positivity
  have hparams := matrix_parameter_bounds n B (n*χ*ν) hn hB hdensity
  have he : -(1/100:ℝ)^2*n*χ*ν/(8*B^2)= -(n*χ*ν)/(80000*B^2) := by ring
  have herr : (4*n*B^2)*(n*Real.exp (-(1/100:ℝ)^2*n*χ*ν/(8*B^2)))≤
      (2/100:ℝ)*n*χ*ν := by
    rw [he]
    simpa only [mul_assoc] using hparams.2.1
  have hrows := copy_row_moment_bounds p X T B ν χ hB hν hχ hm hb hv herr
  have hmean := upper_expect_289 bvh hn0 p X T B (n*χ*ν) hB.le hscale.le hm hb
    (by simpa only [mul_assoc] using hrows.1)
    (by simpa only [mul_assoc] using hrows.2) hparams.1
  have htail := upper_norm_tail ledoux p X T B ((1/100)*Real.sqrt (n*χ*ν)) hB
    (by positivity) hb
  have hsub := prob_mono_support (product p)
    (fun x => (290/100:ℝ)*Real.sqrt (n*χ*ν)<‖upperMatrix T (fun e => X e (x e))‖)
    (fun x => expect (product p) (fun y => ‖upperMatrix T (fun e => X e (y e))‖)+
      (1/100)*Real.sqrt (n*χ*ν)<‖upperMatrix T (fun e => X e (x e))‖)
    (by intro x _ hx; linarith)
  have hexp : -((1/100:ℝ)*Real.sqrt (n*χ*ν))^2/(8*B^2)=
      -(n*χ*ν)/(80000*B^2) := by
    rw [mul_pow,Real.sq_sqrt hscale.le]; ring
  rw [hexp] at htail
  exact hsub.trans (htail.trans hparams.2.2)

/-- The same norm event with the proposition's original density condition,
including its supplied-mean size term. -/
theorem independent_pair_norm_from_paper
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ)
    (hn : 2≤n) (B ν χ τ σ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hτ : 0<τ) (hτ1 : τ<1)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hdensity : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2)≤n*ν) :
    prob (product p) (fun x => (290/100:ℝ)*Real.sqrt (n*χ*ν)<
      ‖upperMatrix T (fun e => X e (x e))‖)≤1/(n:ℝ)^3 :=
  independent_pair_norm_tail bvh ledoux p X T hn B ν χ hB hν (by linarith) hm hb hv
    (matrix_density_from_paper n B ν χ τ σ hn hν.le hχ hτ hτ1 hdensity)

/-- Join the norm event to the already checked scalar event under the same
product law. Correlations between these events do not affect the union bound. -/
theorem scalar_operator_event
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ)
    (hn : 100≤n) (B ν χ a : ℝ) (S : Finset (Fin n))
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (ha : 0<a)
    (haSmall : a*B≤2*(χ*ν)) (haShift : a≤(1/1000:ℝ)*Real.sqrt ν)
    (haNorm : n*a≤(2/1000:ℝ)*Real.sqrt (n*χ*ν))
    (hS : ∀ t∈S, 0<t.val)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hdensity : (10^9:ℝ)*B^2*Real.log n≤n*χ*ν) :
    prob (product p) (fun x => ¬(
      scalarGood (fun e => X e (x e)) ν χ a S ∧
      ‖upperMatrix T (fun e => X e (x e)-empiricalMean (fun e => X e (x e)))‖^2≤
        9*χ*pairEnergy (fun e => X e (x e)-empiricalMean (fun e => X e (x e)))))≤
      scalarFailureBound n B ν χ a S+1/(n:ℝ)^3 := by
  have hscalar := scalar_event_probability p X (by omega) B ν χ a S hB hν hχ ha
    haSmall haShift hS hm hb hv
  have hnorm := independent_pair_norm_tail bvh ledoux p X T (by omega) B ν χ
    hB hν (by linarith) hm hb (fun e => (hv e).2) hdensity
  have hsub := prob_mono_support (product p)
    (fun x => ¬(scalarGood (fun e => X e (x e)) ν χ a S ∧
      ‖upperMatrix T (fun e => X e (x e)-empiricalMean (fun e => X e (x e)))‖^2≤
        9*χ*pairEnergy (fun e => X e (x e)-empiricalMean (fun e => X e (x e)))))
    (fun x => ¬scalarGood (fun e => X e (x e)) ν χ a S ∨
      (290/100:ℝ)*Real.sqrt (n*χ*ν)<‖upperMatrix T (fun e => X e (x e))‖) (by
      intro x _ hx
      by_contra hh
      have hg : scalarGood (fun e => X e (x e)) ν χ a S := by tauto
      have hr : ‖upperMatrix T (fun e => X e (x e))‖≤(290/100:ℝ)*Real.sqrt (n*χ*ν) := by
        by_contra h; exact hh (Or.inr (lt_of_not_ge h))
      apply hx
      refine ⟨hg,?_⟩
      apply operator_energy_bound T _ _ χ ν hn (by linarith) hν.le hg.2.1.1
      have hs := upper_matrix_shift_bound T (fun e => X e (x e)) (empiricalMean (fun e => X e (x e)))
      have hδ := mul_le_mul_of_nonneg_left hg.1 (Nat.cast_nonneg (α:=ℝ) n)
      linarith)
  exact hsub.trans ((prob_union_le _ _ _).trans (add_le_add hscalar hnorm))

end
end Max2SAT.IndependentPairs
