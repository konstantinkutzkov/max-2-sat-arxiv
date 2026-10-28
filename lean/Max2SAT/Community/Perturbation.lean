import Max2SAT.IndependentPairs.MatrixGeometry

/-! Geometry of the computed remainder. All matrix operator norms are
Euclidean. The Frobenius norm is explicitly a Euclidean vector norm, so
there is no ambiguity between two matrix norm instances. -/
namespace Max2SAT.Community
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 800000

def matrixVector (A : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

def frobenius (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ‖matrixVector A‖

def offDiagonal (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i=j then 0 else A i j

theorem frobenius_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0≤frobenius A := norm_nonneg _

theorem frobenius_square (A : Matrix (Fin n) (Fin n) ℝ) :
    (frobenius A)^2=∑ i, ∑ j, (A i j)^2 := by
  rw [frobenius,EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  rfl

theorem matrix_vector_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixVector (A+B)=matrixVector A+matrixVector B := rfl

theorem matrix_vector_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixVector (A-B)=matrixVector A-matrixVector B := rfl

theorem frobenius_add_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    frobenius (A+B)≤frobenius A+frobenius B := by
  unfold frobenius; rw [matrix_vector_add]; exact norm_add_le _ _

theorem frobenius_sub_norm (A B : Matrix (Fin n) (Fin n) ℝ) :
    |frobenius A-frobenius B|≤frobenius (A-B) := by
  unfold frobenius; rw [matrix_vector_sub]; exact abs_norm_sub_norm_le _ _

theorem off_diagonal_energy (A : Matrix (Fin n) (Fin n) ℝ) :
    (frobenius (offDiagonal A))^2≤(frobenius A)^2 := by
  simp only [frobenius_square]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  dsimp [offDiagonal]
  split_ifs <;> simp [sq_nonneg]

theorem off_diagonal_frobenius (A : Matrix (Fin n) (Fin n) ℝ) :
    frobenius (offDiagonal A)≤frobenius A :=
  (sq_le_sq₀ (frobenius_nonneg _) (frobenius_nonneg _)).mp (off_diagonal_energy A)

theorem entry_le_operator_norm (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |A i j|≤‖A‖ := by
  have h := Counts.matrix_squared_energy A (fun k => if k=j then 1 else 0) (‖A‖^2) le_rfl
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,
    ite_pow,one_pow,zero_pow (by norm_num : 2≠0)] at h
  have hs : (A i j)^2≤∑ k, (A k j)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A k j)) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs]
  simpa using hs.trans h

theorem diagonal_norm_le (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖Matrix.diagonal (fun i => A i i)‖≤‖A‖ := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr (fun i => by
    simpa only [Real.norm_eq_abs] using entry_le_operator_norm A i i)

theorem off_diagonal_decomposition (A : Matrix (Fin n) (Fin n) ℝ) :
    offDiagonal A=A-Matrix.diagonal (fun i => A i i) := by
  ext i j
  by_cases h:i=j <;> simp [offDiagonal,Matrix.diagonal,h]

theorem off_diagonal_norm (A : Matrix (Fin n) (Fin n) ℝ) : ‖offDiagonal A‖≤2*‖A‖ := by
  rw [off_diagonal_decomposition]
  have h := norm_sub_le A (Matrix.diagonal (fun i => A i i))
  linarith [diagonal_norm_le A]

/-- Subtracting a computed mean need not preserve independence. This is a
pointwise norm comparison and makes no probabilistic assumption. -/
theorem frobenius_perturbation (X H : Matrix (Fin n) (Fin n) ℝ) :
    |frobenius (X+offDiagonal H)-frobenius X|≤frobenius H := by
  have h := frobenius_sub_norm (X+offDiagonal H) X
  rw [add_sub_cancel_left] at h
  exact h.trans (off_diagonal_frobenius H)

def rowVector (A : Matrix (Fin n) (Fin n) ℝ) (C : Finset (Fin n)) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => if j∈C then A i j else 0)

def crossProfile (A : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n)) : ℝ :=
  ∑ i∈R, ‖rowVector A C i‖

theorem row_vector_square (A : Matrix (Fin n) (Fin n) ℝ) (C : Finset (Fin n)) (i : Fin n) :
    ‖rowVector A C i‖^2=∑ j∈C, (A i j)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [rowVector]

theorem cross_profile_roots (A : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n)) :
    crossProfile A R C=∑ i∈R, Real.sqrt (∑ j∈C, (A i j)^2) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [←row_vector_square,Real.sqrt_sq (norm_nonneg _)]

theorem cross_profile_bound (A : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n)) :
    crossProfile A R C≤Real.sqrt R.card*frobenius A := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1:ℝ)) (fun i => ‖rowVector A C i‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  have he : (∑ i∈R, ‖rowVector A C i‖^2)≤(frobenius A)^2 := by
    rw [frobenius_square]
    simp_rw [row_vector_square]
    apply le_trans (Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg (A i j))))
    exact Finset.sum_le_univ_sum_of_nonneg (fun i => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
  have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) R.card)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by unfold frobenius; positivity)).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) R.card)]
  exact hc.trans hm

theorem cross_profile_add_le (A B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n)) :
    crossProfile (A+B) R C≤crossProfile A R C+crossProfile B R C := by
  rw [crossProfile,crossProfile,crossProfile,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have he : rowVector (A+B) C i=rowVector A C i+rowVector B C i := by
    apply PiLp.ext
    intro j
    by_cases hj:j∈C <;> simp [rowVector,hj]
  rw [he]; exact norm_add_le _ _

/-- The sum of cross-round row norms changes by at most sqrt(|R|)||H||_F.
This is valid for arbitrary chosen row and column sets. -/
theorem cross_profile_perturbation (X H : Matrix (Fin n) (Fin n) ℝ)
    (R C : Finset (Fin n)) :
    crossProfile X R C-Real.sqrt R.card*frobenius H≤crossProfile (X+offDiagonal H) R C := by
  have he : X=(X+offDiagonal H)+offDiagonal (-H) := by
    ext i j; by_cases h:i=j <;> simp [offDiagonal,h]
  have hc := cross_profile_add_le (X+offDiagonal H) (offDiagonal (-H)) R C
  rw [←he] at hc
  have hh := (cross_profile_bound (offDiagonal (-H)) R C).trans
    (mul_le_mul_of_nonneg_left (off_diagonal_frobenius (-H)) (Real.sqrt_nonneg _))
  have hneg : frobenius (-H)=frobenius H := by
    unfold frobenius
    have he : matrixVector (-H)= -matrixVector H := rfl
    rw [he,norm_neg]
  rw [hneg] at hh
  linarith

end
end Max2SAT.Community
