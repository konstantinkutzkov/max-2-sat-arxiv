import Max2SAT.Community.RationalFrame
import Max2SAT.Community.TopSelection
import Max2SAT.Community.DiscoveryBridge

/-! Derive the search's approximation guarantees from the actual rational
frame. JacobiParameters and FrameResidual construct this frame with a
small residual; TopSelection computes the largest-entry selection. -/
namespace Max2SAT.Community
open Counts
open scoped Matrix.Norms.L2Operator
variable {n r : ℕ}
set_option maxHeartbeats 1000000

def formulaMatrix (F : Formula n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (gainExpr F i).coeff j

/-- Compute the retained columns and coefficients from a rational frame.
The spacing field is subsequently replaced by withComputedSpacing. -/
def sortedFrameRepresentation (F : Formula n) (Q : Matrix (Fin n) (Fin n) ℚ)
    (hrn : r≤n) : Representation n r :=
  frameRepresentation (formulaMatrix F) Q (topSelection (frameDiagonal (formulaMatrix F) Q) hrn)

noncomputable section

theorem formula_matrix_cast (F : Formula n) :
    realMatrix (formulaMatrix F)=interactionMatrix (gainExpr F) := rfl

/-- The explicit size cutoff used for the low-rank mean correction. -/
theorem rank_correction_small (A : Matrix (Fin n) (Fin n) ℝ) (d : Representation n r)
    (ν χ : ℝ) (hν : 0≤ν) (hχ : 0≤χ) (hA : A.IsHermitian) (hr : A.rank≤r)
    (hsize : 5120000*r*χ≤(n:ℝ))
    (herror : ‖A-representationMatrix d‖≤16*Real.sqrt (n*χ*ν)) :
    frobenius (A-representationMatrix d)≤(1/100:ℝ)*n*Real.sqrt ν := by
  have h := (correction_frobenius A d hA hr).trans
    (mul_le_mul_of_nonneg_left herror (Real.sqrt_nonneg (2*r)))
  apply h.trans
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤(2:ℝ)*r),
    Real.sq_sqrt (by positivity : 0≤(n:ℝ)*χ*ν),Real.sq_sqrt hν]
  have hb := mul_le_mul_of_nonneg_right hsize (show 0≤(n:ℝ)*ν by positivity)
  nlinarith

theorem model_distance (J A X : Matrix (Fin n) (Fin n) ℝ) (B₀ : ℝ)
    (hB : 0≤B₀) (hmodel : J=A+X-Matrix.diagonal (fun i => A i i))
    (hdiag : ∀ i, |A i i|≤B₀) : ‖J-A‖≤‖X‖+B₀ := by
  have hd : ‖Matrix.diagonal (fun i => A i i)‖≤B₀ := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hB).mpr (fun i => by simpa only [Real.norm_eq_abs] using hdiag i)
  have he : J-A=X-Matrix.diagonal (fun i => A i i) := by rw [hmodel]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hd)

/-- All four previously explicit search guarantees follow from rational
orthogonality, largest-entry selection, and the diagonalization residual. -/
theorem frame_approximation_guarantees (F : Formula n)
    (Q : Matrix (Fin n) (Fin n) ℚ) (selected : Fin r ↪ Fin n)
    (A X : Matrix (Fin n) (Fin n) ℝ) (B₀ ζ ν χ : ℝ)
    (hQ : Q.transpose*Q=1) (hA : A.IsHermitian) (hr : A.rank≤r)
    (hB : 0≤B₀) (hζ : 0≤ζ) (hν : 0≤ν) (hχ : 0≤χ)
    (hmodel : interactionMatrix (gainExpr F)=A+X-Matrix.diagonal (fun i => A i i))
    (hdiag : ∀ i, |A i i|≤B₀)
    (htop : ∀ i∈Finset.univ.map selected, ∀ j∉Finset.univ.map selected,
      |frameDiagonal (formulaMatrix F) Q j|≤|frameDiagonal (formulaMatrix F) Q i|)
    (happrox : frobenius (interactionMatrix (gainExpr F)-
      Unitary.conjStarAlgAut ℝ _ (realOrthogonal Q hQ)
        (Matrix.diagonal (fun i => (frameDiagonal (formulaMatrix F) Q i:ℝ))))≤ζ)
    (hnoise : ‖X‖≤(58/10:ℝ)*Real.sqrt (n*χ*ν))
    (hBsmall : B₀≤Real.sqrt (n*χ*ν)) (hζsmall : ζ≤Real.sqrt (n*χ*ν))
    (hsize : 5120000*r*χ≤(n:ℝ)) :
    ApproximationGuarantees F (frameRepresentation (formulaMatrix F) Q selected) A X B₀ ζ ν := by
  let d := frameRepresentation (formulaMatrix F) Q selected
  have htrunc : ‖interactionMatrix (gainExpr F)-representationMatrix d‖≤‖X‖+B₀+2*ζ := by
    rw [show representationMatrix d=_ from frame_matrix_eq (formulaMatrix F) Q selected hQ]
    have h := spectral_truncation_from_frobenius (interactionMatrix (gainExpr F)) A
      (realOrthogonal Q hQ) (fun i => (frameDiagonal (formulaMatrix F) Q i:ℝ))
      (Finset.univ.map selected) ζ (by simpa using hr)
      (fun i hi j hj => by exact_mod_cast htop i hi j hj) happrox
    exact h.trans (add_le_add (model_distance _ A X B₀ hB hmodel hdiag) le_rfl)
  refine ⟨fun k => (frame_direction_unit _ _ _ hQ k).le,?_,htrunc,?_⟩
  · intro k
    exact frame_coefficient_rayleigh (formulaMatrix F) Q selected k
  · have hrem := remainder_operator_bound _ A (representationMatrix d) X B₀ ζ hB hζ hmodel hdiag htrunc
    apply rank_correction_small A d ν χ hν hχ hA hr hsize
    have hs := Real.sqrt_nonneg ((n:ℝ)*χ*ν)
    linarith [hrem.2]

/-- The selected indices are computed by rational sorting, so no largest-
entry assumption is required from a caller of the numerical routine. -/
theorem sorted_frame_approximation_guarantees (F : Formula n)
    (Q : Matrix (Fin n) (Fin n) ℚ) (hrn : r≤n)
    (A X : Matrix (Fin n) (Fin n) ℝ) (B₀ ζ ν χ : ℝ)
    (hQ : Q.transpose*Q=1) (hA : A.IsHermitian) (hr : A.rank≤r)
    (hB : 0≤B₀) (hζ : 0≤ζ) (hν : 0≤ν) (hχ : 0≤χ)
    (hmodel : interactionMatrix (gainExpr F)=A+X-Matrix.diagonal (fun i => A i i))
    (hdiag : ∀ i, |A i i|≤B₀)
    (happrox : frobenius (interactionMatrix (gainExpr F)-
      Unitary.conjStarAlgAut ℝ _ (realOrthogonal Q hQ)
        (Matrix.diagonal (fun i => (frameDiagonal (formulaMatrix F) Q i:ℝ))))≤ζ)
    (hnoise : ‖X‖≤(58/10:ℝ)*Real.sqrt (n*χ*ν))
    (hBsmall : B₀≤Real.sqrt (n*χ*ν)) (hζsmall : ζ≤Real.sqrt (n*χ*ν))
    (hsize : 5120000*r*χ≤(n:ℝ)) :
    ApproximationGuarantees F (sortedFrameRepresentation F Q hrn) A X B₀ ζ ν :=
  frame_approximation_guarantees F Q _ A X B₀ ζ ν χ hQ hA hr hB hζ hν hχ
    hmodel hdiag (top_selection_largest _ hrn) happrox hnoise hBsmall hζsmall hsize

end
end Max2SAT.Community
