import Max2SAT.IndependentPairs.MatrixExpectation
import Max2SAT.IndependentPairs.ScalarEvent

/-! Apply Ledoux's published upper-tail theorem to the actual matrix map.
Empirical centering is a deterministic perturbation; its entries are never
assumed independent. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} [Fintype α]

theorem upper_norm_tail (ext : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ) (B r : ℝ)
    (hB : 0<B) (hr : 0<r) (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B) :
    prob (product p) (fun x =>
      expect (product p) (fun y => ‖upperMatrix T (fun e => X e (y e))‖)+r <
        ‖upperMatrix T (fun e => X e (x e))‖)≤Real.exp (-r^2/(8*B^2)) :=
  ext p X (fun z => ‖upperMatrix T z‖) B r hB hr hb
    (upper_matrix_convex T) (upper_matrix_lipschitz T)

/-- Tail after an arbitrary deterministic or sampled common shift.
The shift may depend on all entries, and no extra independence is used. -/
theorem shifted_upper_norm_tail (ext : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ)
    (δ : (Edge n → α) → ℝ) (B r a M q : ℝ)
    (hB : 0<B) (hr : 0<r) (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hm : expect (product p) (fun x => ‖upperMatrix T (fun e => X e (x e))‖)≤M)
    (hδ : prob (product p) (fun x => a < |δ x|)≤q) :
    prob (product p) (fun x => M+r+n*a <
      ‖upperMatrix T (fun e => X e (x e)-δ x)‖)≤q+Real.exp (-r^2/(8*B^2)) := by
  have hsub := prob_mono_support (product p)
    (fun x => M+r+n*a < ‖upperMatrix T (fun e => X e (x e)-δ x)‖)
    (fun x => a < |δ x| ∨
      expect (product p) (fun y => ‖upperMatrix T (fun e => X e (y e))‖)+r <
        ‖upperMatrix T (fun e => X e (x e))‖) (by
      intro x _ hx
      by_contra h
      push Not at h
      have hs := upper_matrix_shift_bound T (fun e => X e (x e)) (δ x)
      have ha := mul_le_mul_of_nonneg_left h.1 (Nat.cast_nonneg (α:=ℝ) n)
      linarith [h.2])
  exact hsub.trans ((prob_union_le _ _ _).trans
    (add_le_add hδ (upper_norm_tail ext p X T B r hB hr hb)))

/-- Convert the norm estimate to the K=9*chi energy normalization. -/
theorem operator_energy_bound (T : ℕ) (z : Edge n → ℝ) (D χ ν : ℝ)
    (hn : 100≤n) (hχ : 0≤χ) (hν : 0≤ν)
    (hD : (98/100:ℝ)*((n:ℝ)-1)*ν≤D)
    (hR : ‖upperMatrix T z‖≤(2902/1000:ℝ)*Real.sqrt (n*χ*ν)) :
    ‖upperMatrix T z‖^2≤9*χ*D := by
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hR
  rw [mul_pow,Real.sq_sqrt (by positivity)] at hsq
  have hnr : (100:ℝ)≤n := by exact_mod_cast hn
  have hd := mul_le_mul_of_nonneg_left hD hχ
  have hn' := mul_le_mul_of_nonneg_right hnr (mul_nonneg hχ hν)
  nlinarith

end
end Max2SAT.IndependentPairs
