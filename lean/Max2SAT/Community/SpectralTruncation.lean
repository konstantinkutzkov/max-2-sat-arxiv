import Max2SAT.Community.DiagonalTruncation

/-! Deterministic truncation bounds for an approximate orthogonal
diagonalization. No individual eigenvector accuracy is required. -/
namespace Max2SAT.Community
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem unitary_conjugation_norm (U : Matrix.unitaryGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖Unitary.conjStarAlgAut ℝ _ U A‖=‖A‖ := by
  rw [Unitary.conjStarAlgAut_apply,←Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

theorem unitary_conjugation_rank_le (U : Matrix.unitaryGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Unitary.conjStarAlgAut ℝ _ U A).rank≤A.rank := by
  rw [Unitary.conjStarAlgAut_apply]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Retaining the largest |T| entries of an approximate diagonalization
costs at most twice its error relative to any rank-at-most-|T| matrix A. -/
theorem spectral_truncation_bound (J A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (d : Fin n → ℝ)
    (T : Finset (Fin n)) (ζ : ℝ)
    (hr : A.rank≤T.card) (htop : ∀ i∈T, ∀ j∉T, |d j|≤|d i|)
    (happrox : ‖J-Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal d)‖≤ζ) :
    ‖J-Unitary.conjStarAlgAut ℝ _ U
      (Matrix.diagonal (fun i => if i∈T then d i else 0))‖≤‖J-A‖+2*ζ := by
  classical
  let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U
  let D := Matrix.diagonal d
  let K := Matrix.diagonal (fun i => if i∈T then d i else 0)
  have hinv : (φ.symm A).rank≤A.rank := by
    exact unitary_conjugation_rank_le (star U) A
  have ht := diagonal_truncation_bound d (φ.symm A) T (hinv.trans hr) htop
  have hrot : ‖D-φ.symm A‖=‖φ D-A‖ := by
    rw [←unitary_conjugation_norm U (D-φ.symm A)]
    change ‖φ (D-φ.symm A)‖=_
    rw [map_sub,StarAlgEquiv.apply_symm_apply]
  have he : φ D-A=(φ D-J)+(J-A) := by abel
  have hDA : ‖D-φ.symm A‖≤ζ+‖J-A‖ := by
    rw [hrot,he]
    have h := norm_add_le (φ D-J) (J-A)
    rw [norm_sub_rev (φ D) J] at h
    linarith
  have htail : ‖φ D-φ K‖≤ζ+‖J-A‖ := by
    rw [←map_sub]
    exact (unitary_conjugation_norm U (D-K)).le.trans (ht.trans hDA)
  have hj : J-φ K=(J-φ D)+(φ D-φ K) := by abel
  change ‖J-φ K‖≤_
  rw [hj]
  have h := norm_add_le (J-φ D) (φ D-φ K)
  linarith

/-- The Euclidean operator norm is bounded by the explicitly defined
Frobenius norm used in the numerical stopping criterion. -/
theorem operator_le_frobenius (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖≤frobenius A := by
  apply (sq_le_sq₀ (norm_nonneg _) (frobenius_nonneg _)).mp
  apply Counts.matrix_norm_sq_of_energy A ((frobenius A)^2) (sq_nonneg _)
  intro x
  rw [frobenius_square,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) x)

theorem spectral_truncation_from_frobenius (J A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (d : Fin n → ℝ)
    (T : Finset (Fin n)) (ζ : ℝ)
    (hr : A.rank≤T.card) (htop : ∀ i∈T, ∀ j∉T, |d j|≤|d i|)
    (happrox : frobenius (J-Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal d))≤ζ) :
    ‖J-Unitary.conjStarAlgAut ℝ _ U
      (Matrix.diagonal (fun i => if i∈T then d i else 0))‖≤‖J-A‖+2*ζ :=
  spectral_truncation_bound J A U d T ζ hr htop ((operator_le_frobenius _).trans happrox)

end
end Max2SAT.Community
