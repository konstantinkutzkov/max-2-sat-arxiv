import Max2SAT.Community.RankGeometry

/-! Keeping the largest diagonal entries preserves a low-rank approximation.
The proof uses only dimension and Euclidean norm estimates, avoiding a
separate singular-value perturbation theorem. -/
namespace Max2SAT.Community
noncomputable section
open scoped Matrix.Norms.L2Operator
open Counts Matrix
set_option maxHeartbeats 1000000

/-- A matrix close to a diagonal matrix whose entries all exceed the error
in absolute value has no nonzero kernel vector. -/
theorem diagonal_near_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) (e : ℝ) (he : 0≤e)
    (hd : ∀ i, e< |d i|) (herr : ‖Matrix.diagonal d-A‖^2≤e^2) :
    Function.Injective A.mulVecLin := by
  apply (LinearMap.ker_eq_bot).mp
  apply (LinearMap.ker_eq_bot').mpr
  intro x hx
  by_contra hne
  obtain ⟨i,hi⟩ : ∃ i, x i≠0 := by
    contrapose! hne
    ext i
    exact hne i
  have heach : ∀ j, e^2*(x j)^2≤(d j*x j)^2 := by
    intro j
    have hs : e^2≤(d j)^2 := by
      have hh := (sq_le_sq₀ he (abs_nonneg (d j))).mpr (hd j).le
      simpa only [sq_abs] using hh
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hs (sq_nonneg (x j))
  have hstrict : e^2*(x i)^2<(d i*x i)^2 := by
    have hs : e^2<(d i)^2 := by
      have hh := (sq_lt_sq₀ he (abs_nonneg (d i))).mpr (hd i)
      simpa only [sq_abs] using hh
    simpa only [mul_pow] using mul_lt_mul_of_pos_right hs (sq_pos_of_ne_zero hi)
  have hsum : e^2*(∑ j, (x j)^2)<∑ j, (d j*x j)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum (fun j _ => heach j) ⟨i,Finset.mem_univ i,hstrict⟩
  have hv := matrix_squared_energy (Matrix.diagonal d-A) x (e^2) herr
  have hvec : (Matrix.diagonal d-A)*ᵥx=fun j => d j*x j := by
    rw [Matrix.sub_mulVec]
    rw [show A*ᵥx=0 from hx]
    ext j
    simp [Matrix.mulVec_diagonal]
  have hv' : (∑ j, (d j*x j)^2)≤e^2*(∑ j, (x j)^2) := by
    change (∑ j, ((Matrix.diagonal d-A)*ᵥx) j ^2)≤_ at hv
    rw [hvec] at hv
    exact hv
  exact (not_lt_of_ge hv') hsum

/-- At most rank(A) diagonal entries can exceed the approximation error. -/
theorem large_diagonal_card {n : ℕ} (d : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝ) (he : 0≤e)
    (herr : ‖Matrix.diagonal d-A‖≤e) :
    (Finset.univ.filter (fun i => e< |d i|)).card≤A.rank := by
  classical
  let S := Finset.univ.filter (fun i => e< |d i|)
  let B := restrictedMatrix A S
  have hb : restrictedMatrix (Matrix.diagonal d-A) S=
      Matrix.diagonal (fun i:S => d i)-B := by
    ext i j
    simp [restrictedMatrix,B,Matrix.diagonal_apply]
  have hnorm := block_norm_sq (Matrix.diagonal d-A) S (e^2) (sq_nonneg e)
    ((sq_le_sq₀ (norm_nonneg _) he).mpr herr)
  rw [hb] at hnorm
  have hinj := diagonal_near_injective (fun i:S => d i) B e he
    (fun i => (Finset.mem_filter.mp i.property).2) hnorm
  have hr : B.rank=S.card := by
    rw [Matrix.rank,LinearMap.finrank_range_of_inj hinj]
    simp
  rw [show (Finset.univ.filter (fun i => e< |d i|)).card=S.card from rfl,←hr]
  exact Matrix.rank_submatrix_le A (fun i:S => i.val) (fun i:S => i.val)

/-- T contains the largest absolute diagonal entries; the retained number
is at least the rank of A. The discarded entries are at most the error. -/
theorem discarded_diagonal_bound {n : ℕ} (d : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (T : Finset (Fin n)) (e : ℝ)
    (he : 0≤e) (herr : ‖Matrix.diagonal d-A‖≤e) (hr : A.rank≤T.card)
    (htop : ∀ i∈T, ∀ j∉T, |d j|≤|d i|) :
    ∀ j∉T, |d j|≤e := by
  classical
  intro j hj
  by_contra h
  have hjlarge : e< |d j| := lt_of_not_ge h
  let S := Finset.univ.filter (fun i => e< |d i|)
  have hsub : T⊆S := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hjlarge.trans_le (htop i hi j hj)⟩
  have hlt : T.card<S.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro heq
      have hjS : j∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ j,hjlarge⟩
      rw [←heq] at hjS
      exact hj hjS⟩)
  have hcard : S.card≤A.rank := large_diagonal_card d A e he herr
  omega

/-- Operator-norm form of the preceding coordinate bound. -/
theorem diagonal_truncation_bound {n : ℕ} (d : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (T : Finset (Fin n))
    (hr : A.rank≤T.card) (htop : ∀ i∈T, ∀ j∉T, |d j|≤|d i|) :
    ‖Matrix.diagonal d-Matrix.diagonal (fun i => if i∈T then d i else 0)‖≤
      ‖Matrix.diagonal d-A‖ := by
  classical
  have hb := discarded_diagonal_bound d A T ‖Matrix.diagonal d-A‖ (norm_nonneg _) le_rfl hr htop
  rw [Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  by_cases hi:i∈T
  · simp [hi]
  · simpa [hi,Real.norm_eq_abs] using hb i hi

end
end Max2SAT.Community
