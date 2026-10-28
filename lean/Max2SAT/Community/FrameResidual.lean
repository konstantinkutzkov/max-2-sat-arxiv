import Max2SAT.Community.JacobiParameters

/-! Translate the rational stopping criterion to the precise Frobenius
residual required by spectral truncation and the comparison search. -/
namespace Max2SAT.Community
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 1000000
noncomputable section

theorem frobenius_square_star_trace (A : Matrix (Fin n) (Fin n) ℝ) :
    (frobenius A)^2=(star A*A).trace := by
  rw [frobenius_square]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply,star_trivial]
  rw [Finset.sum_comm]
  simp only [pow_two]

theorem frobenius_unitary_conjugate (U : Matrix.unitaryGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    frobenius (Unitary.conjStarAlgAut ℝ _ U A)=frobenius A := by
  have he : (frobenius (Unitary.conjStarAlgAut ℝ _ U A))^2=(frobenius A)^2 := by
    rw [frobenius_square_star_trace,←map_star,←map_mul,trace_unitary_conjugate,
      ←frobenius_square_star_trace]
  nlinarith [frobenius_nonneg (Unitary.conjStarAlgAut ℝ _ U A),frobenius_nonneg A]

theorem off_energy_frobenius (A : Matrix (Fin n) (Fin n) ℚ) :
    ((offEnergy A:ℚ):ℝ)=(frobenius (offDiagonal (realMatrix A)))^2 := by
  rw [off_energy_sum,frobenius_square]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij:i=j <;> simp [offDiagonal,realMatrix,hij]

theorem frame_rotated_matrix (J Q : Matrix (Fin n) (Fin n) ℚ) (hQ : Q.transpose*Q=1) :
    realMatrix (Q.transpose*J*Q)=
      (Unitary.conjStarAlgAut ℝ _ (realOrthogonal Q hQ)).symm (realMatrix J) := by
  rw [Unitary.conjStarAlgAut_symm,Unitary.conjStarAlgAut_apply]
  simp only [Unitary.coe_star,realOrthogonal,real_matrix_mul,real_matrix_transpose,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose]

/-- The residual after restoring the original coordinates has exactly the
energy measured by the rational Jacobi stopping test. -/
theorem frame_residual_square (J Q : Matrix (Fin n) (Fin n) ℚ) (hQ : Q.transpose*Q=1) :
    (frobenius (realMatrix J-Unitary.conjStarAlgAut ℝ _ (realOrthogonal Q hQ)
      (Matrix.diagonal (fun i => (frameDiagonal J Q i:ℝ)))))^2=
      ((offEnergy (Q.transpose*J*Q):ℚ):ℝ) := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) (realOrthogonal Q hQ)
  have hd : Matrix.diagonal (fun i => (frameDiagonal J Q i:ℝ))=
      Matrix.diagonal (fun i => realMatrix (Q.transpose*J*Q) i i) := rfl
  have he : realMatrix J-φ (Matrix.diagonal (fun i => (frameDiagonal J Q i:ℝ)))=
      φ (offDiagonal (realMatrix (Q.transpose*J*Q))) := by
    rw [off_diagonal_decomposition,map_sub,←hd,frame_rotated_matrix J Q hQ]
    change realMatrix J-φ _=φ (φ.symm (realMatrix J))-φ _
    rw [StarAlgEquiv.apply_symm_apply]
  change (frobenius (realMatrix J-φ _))^2=_
  rw [he,frobenius_unitary_conjugate,←off_energy_frobenius]

/-- The constructed rational frame supplies the requested n^-4 residual. -/
theorem computed_frame_residual (J : Matrix (Fin n) (Fin n) ℚ) (hJ : J.IsSymm) :
    frobenius (realMatrix J-Unitary.conjStarAlgAut ℝ _
      (realOrthogonal (computedFrame J) (computed_frame_orthogonal J))
        (Matrix.diagonal (fun i => (frameDiagonal J (computedFrame J) i:ℝ))))≤1/(n:ℝ)^4 := by
  apply (sq_le_sq₀ (frobenius_nonneg _) (by positivity)).mp
  rw [frame_residual_square]
  have h := computed_frame_energy J hJ
  unfold diagonalizationAccuracy at h
  have hr : ((offEnergy ((computedFrame J).transpose*J*computedFrame J):ℚ):ℝ)≤1/(n:ℝ)^8 := by
    have hc : ((offEnergy ((computedFrame J).transpose*J*computedFrame J):ℚ):ℝ)≤
        ((1/(n:ℚ)^8:ℚ):ℝ) := (Rat.cast_le (K:=ℝ)).mpr h
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast] using hc
  convert hr using 1; ring

end
end Max2SAT.Community
