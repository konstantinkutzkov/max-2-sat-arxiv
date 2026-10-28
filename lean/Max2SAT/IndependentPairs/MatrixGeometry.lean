import Max2SAT.IndependentPairs.MatrixModel
import Mathlib.Analysis.Normed.Module.Convex

/-! Deterministic geometry for applying published random-matrix results.
The scoped norm is always the Euclidean operator norm. `upperMatrix` pads
unused rows with zeros, and uses each independent unordered pair at most once. -/
namespace Max2SAT.IndependentPairs
noncomputable section
set_option maxHeartbeats 800000
open RandomInput
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

def upperMatrix (T : ℕ) (z : Edge n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : i < j then if i.val < T then z ⟨(i,j),h⟩ else 0 else 0

theorem upper_matrix_sub (T : ℕ) (z w : Edge n → ℝ) :
    upperMatrix T (z-w)=upperMatrix T z-upperMatrix T w := by
  ext i j
  simp only [upperMatrix,Matrix.sub_apply,Pi.sub_apply]
  split_ifs <;> simp

theorem upper_matrix_smul (T : ℕ) (c : ℝ) (z : Edge n → ℝ) :
    upperMatrix T (c • z)=c • upperMatrix T z := by
  ext i j
  simp only [upperMatrix,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> simp

theorem upper_matrix_add (T : ℕ) (z w : Edge n → ℝ) :
    upperMatrix T (z+w)=upperMatrix T z+upperMatrix T w := by
  ext i j
  simp only [upperMatrix,Matrix.add_apply,Pi.add_apply]
  split_ifs <;> simp

/-- Cauchy--Schwarz bounds the operator norm by the Frobenius norm. -/
theorem matrix_norm_le_root_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (A : Matrix κ ι ℝ) :
    ‖A‖≤Real.sqrt (∑ i, ∑ j, (A i j)^2) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hc := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (fun j => x j))
  rw [←Finset.sum_mul] at hc
  have he : ‖((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A) x‖^2 ≤
      (∑ i, ∑ j, (A i j)^2)*‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    exact hc
  have hs := Real.sq_sqrt (x:=∑ i, ∑ j, (A i j)^2) (by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,hs]
  exact he

theorem upper_matrix_energy (T : ℕ) (z : Edge n → ℝ) :
    (∑ i, ∑ j, (upperMatrix T z i j)^2)≤∑ e, (z e)^2 := by
  have hp := sum_on_pairs (fun i j => (pairMatrix z i j)^2)
  simp_rw [pair_matrix_entry] at hp
  rw [hp]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases h : i < j
  · simp only [upperMatrix,h,↓reduceDIte,↓reduceIte,pairMatrix]
    split_ifs <;> simp [sq_nonneg]
  · simp [upperMatrix,h]

theorem upper_matrix_norm_le (T : ℕ) (z : Edge n → ℝ) :
    ‖upperMatrix T z‖≤Real.sqrt (∑ e, (z e)^2) :=
  (matrix_norm_le_root_energy _).trans (Real.sqrt_le_sqrt (upper_matrix_energy T z))

/-- The coordinate-to-matrix map is a contraction for Euclidean distance. -/
theorem upper_matrix_lipschitz (T : ℕ) :
    LipschitzWith 1 (fun z : EuclideanSpace ℝ (Edge n) => ‖upperMatrix T z‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  calc
    _ ≤ ‖upperMatrix T z-upperMatrix T w‖ := abs_norm_sub_norm_le _ _
    _ = ‖upperMatrix T (fun e => z e-w e)‖ := by rw [←upper_matrix_sub]; rfl
    _ ≤ Real.sqrt (∑ e, (z e-w e)^2) := upper_matrix_norm_le T _
    _ = ‖z-w‖ := by
      change Real.sqrt (∑ e, ((z-w).ofLp e)^2)=‖z-w‖
      rw [←EuclideanSpace.real_norm_sq_eq,Real.sqrt_sq (norm_nonneg _)]

theorem upper_matrix_convex (T : ℕ) :
    ConvexOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Edge n) => ‖upperMatrix T z‖) := by
  refine ⟨convex_univ,?_⟩
  intro z _ w _ a b ha hb _
  have he : upperMatrix T (fun e => (a • z+b • w) e)=
      a • upperMatrix T z+b • upperMatrix T w := by
    rw [show (fun e => (a • z+b • w) e)=
      a • (fun e => z e)+b • (fun e => w e) from rfl,
      upper_matrix_add,upper_matrix_smul,upper_matrix_smul]
  change ‖upperMatrix T (fun e => (a • z+b • w) e)‖≤a*‖upperMatrix T z‖+b*‖upperMatrix T w‖
  rw [he]
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,
    smul_eq_mul] using norm_add_le (a • upperMatrix T z) (b • upperMatrix T w)

theorem upper_matrix_shift_bound (T : ℕ) (z : Edge n → ℝ) (δ : ℝ) :
    ‖upperMatrix T (fun e => z e-δ)‖≤‖upperMatrix T z‖+(n:ℝ)*|δ| := by
  have hc : ‖upperMatrix (n:=n) T (fun _ => δ)‖≤(n:ℝ)*|δ| := by
    have hs : (∑ i : Fin n, ∑ j : Fin n,
        (upperMatrix (n:=n) T (fun _ => δ) i j)^2)≤((n:ℝ)*|δ|)^2 := by
      calc
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, δ^2 := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          dsimp [upperMatrix]
          split_ifs <;> simp [sq_nonneg]
        _ = _ := by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_pow,sq_abs]
          ring
    exact (matrix_norm_le_root_energy (upperMatrix (n:=n) T (fun _ => δ))).trans
      (Real.sqrt_le_iff.mpr ⟨by positivity,hs⟩)
  have he : upperMatrix T (fun e => z e-δ)=upperMatrix T z-upperMatrix T (fun _ => δ) :=
    upper_matrix_sub T z (fun _ => δ)
  rw [he]
  exact (norm_sub_le (upperMatrix T z) (upperMatrix T (fun _ => δ))).trans
    (add_le_add le_rfl hc)

end
end Max2SAT.IndependentPairs
