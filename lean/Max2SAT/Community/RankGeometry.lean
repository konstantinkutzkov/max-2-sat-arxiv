import Max2SAT.Community.CoefficientBudget
import Mathlib.Analysis.Matrix.Spectrum
import Max2SAT.Community.RepresentationMatrix

/-! The rank-to-Frobenius inequality for symmetric matrices, derived from
mathlib's spectral theorem. All operator norms are Euclidean. -/
namespace Max2SAT.Community
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem trace_unitary_conjugate (U : Matrix.unitaryGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Unitary.conjStarAlgAut ℝ _ U A).trace=A.trace := by
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul]

theorem frobenius_square_trace (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (frobenius A)^2=(A*A).trace := by
  rw [frobenius_square]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : A j i=A i j := by simpa using hA.apply i j
  rw [hs,pow_two]

theorem frobenius_square_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (frobenius A)^2=∑ i, (hA.eigenvalues i)^2 := by
  rw [frobenius_square_trace A hA]
  have he : A*A=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal hA.eigenvalues*Matrix.diagonal hA.eigenvalues) := by
    rw [map_mul]
    have hh := hA.spectral_theorem
    simpa only [Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using congrArg (fun M => M*M) hh
  rw [he,trace_unitary_conjugate,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]
  congr 1
  funext i
  ring

theorem eigenvalue_abs_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i : Fin n) :
    |hA.eigenvalues i|≤‖A‖ := by
  let : Nonempty (Fin n) := ⟨i⟩
  have h := spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
  simpa only [Real.norm_eq_abs] using h

theorem frobenius_square_rank (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (frobenius A)^2≤A.rank*‖A‖^2 := by
  classical
  rw [frobenius_square_eigenvalues A hA]
  let S := Finset.univ.filter (fun i => hA.eigenvalues i≠0)
  have he : (∑ i, (hA.eigenvalues i)^2)=∑ i∈S, (hA.eigenvalues i)^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : hA.eigenvalues i=0 <;> simp [hi]
  have hc : S.card=A.rank := by
    rw [hA.rank_eq_card_non_zero_eigs]
    simp [S,Fintype.card_subtype]
  rw [he,←hc]
  calc
    _ ≤ ∑ _i∈S, ‖A‖^2 := Finset.sum_le_sum (fun i _ => by
      have h := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (eigenvalue_abs_bound A hA i)
      simpa only [sq_abs] using h)
    _ = _ := by simp

theorem frobenius_rank_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (r : ℕ) (hr : A.rank≤r) : frobenius A≤Real.sqrt r*‖A‖ := by
  apply (sq_le_sq₀ (frobenius_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) r)]
  exact (frobenius_square_rank A hA).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (sq_nonneg ‖A‖))

/-- The rank of a difference is at most the sum of the two ranks. -/
theorem rank_sub_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A-B).rank≤A.rank+B.rank := by
  have h : LinearMap.range (A-B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x,rfl⟩
    have he : (A-B).mulVecLin x=A.mulVecLin x-B.mulVecLin x := by
      ext i
      simp
    rw [he]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left ⟨x,rfl⟩) (Submodule.mem_sup_right ⟨x,rfl⟩)
  exact (Submodule.finrank_mono h).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- A sum of r symmetric rank-one terms has rank at most r. -/
theorem representation_rank {r : ℕ} (d : Representation n r) :
    (representationMatrix d).rank≤r := by
  let V : Matrix (Fin n) (Fin r) ℝ := fun i k => (d.direction k i:ℝ)
  let W : Matrix (Fin r) (Fin n) ℝ := fun k i => (d.coefficient k:ℝ)*(d.direction k i:ℝ)
  have he : representationMatrix d=V*W := by
    ext i j
    simp only [representationMatrix,V,W]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact (Matrix.rank_mul_le_left V W).trans (by simpa using Matrix.rank_le_card_width V)

theorem representation_hermitian {r : ℕ} (d : Representation n r) :
    (representationMatrix d).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,representationMatrix]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The discarded mean correction has rank at most twice the retained rank. -/
theorem correction_frobenius {r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : Representation n r) (hA : A.IsHermitian) (hr : A.rank≤r) :
    frobenius (A-representationMatrix d)≤Real.sqrt (2*r)*‖A-representationMatrix d‖ := by
  have h := frobenius_rank_bound (A-representationMatrix d)
    (hA.sub (representation_hermitian d)) (2*r)
    ((rank_sub_le _ _).trans (by have hp := representation_rank d; omega))
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end
end Max2SAT.Community
