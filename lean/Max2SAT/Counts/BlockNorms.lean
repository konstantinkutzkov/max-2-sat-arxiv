import Max2SAT.Counts.OperatorEnergy
import Max2SAT.Counts.RoundCompensation

/-! Euclidean norm control survives restriction to a round and the
preference-dependent sign change. These are deterministic statements. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_norm_sq_of_energy (N : Matrix ι ι ℝ) (V : ℝ) (hV : 0≤V)
    (he : ∀ z : ι → ℝ, (∑ t, (∑ w, N t w*z w)^2)≤V*(∑ w, (z w)^2)) :
    ‖N‖^2≤V := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) N
  have hb : ‖T‖≤Real.sqrt V := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg V)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hV,EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    exact he x
  have hs := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg V)).2 hb
  rwa [Real.sq_sqrt hV,Matrix.l2_opNorm_toEuclideanCLM] at hs

def extendBlock (S : Finset ι) (z : S → ℝ) (i : ι) : ℝ :=
  if hi : i∈S then z ⟨i,hi⟩ else 0

theorem extend_block_sum (S : Finset ι) (z : S → ℝ) :
    (∑ i, extendBlock S z i)=∑ i : S, z i := by
  unfold extendBlock
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero,add_zero]
  apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun i => by simp))
  intro i
  rfl

def restrictedMatrix (N : Matrix ι ι ℝ) (S : Finset ι) : Matrix S S ℝ := fun t w => N t w

theorem block_norm_sq (N : Matrix ι ι ℝ) (S : Finset ι)
    (V : ℝ) (hV : 0≤V) (hN : ‖N‖^2≤V) :
    ‖restrictedMatrix N S‖^2≤V := by
  apply matrix_norm_sq_of_energy _ V hV
  intro z
  let y := extendBlock S z
  have hy : (∑ w, (y w)^2)=∑ w : S, (z w)^2 := by
    have he : ∀ w, (y w)^2=extendBlock S (fun i => (z i)^2) w := by
      intro w
      dsimp [y,extendBlock]
      split_ifs <;> simp
    simp_rw [he]
    exact extend_block_sum S _
  have hm : ∀ t, (∑ w, N t w*y w)=∑ w : S, N t w*z w := by
    intro t
    have he : ∀ w, N t w*y w=extendBlock S (fun i => N t i*z i) w := by
      intro w
      dsimp [y,extendBlock]
      split_ifs <;> simp
    simp_rw [he]
    exact extend_block_sum S _
  have h := matrix_squared_energy N y V hN
  rw [hy] at h
  have hs : (∑ t : S, (∑ w, N t w*y w)^2)≤∑ t, (∑ w, N t w*y w)^2 := by
    rw [Finset.sum_coe_sort S (fun t : ι => (∑ w, N t w*y w)^2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _)
  simp_rw [hm] at hs h
  exact hs.trans h

def signedMatrix (N : Matrix ι ι ℝ) (p : ι → Bool) : Matrix ι ι ℝ := conjugated N p

theorem conjugated_norm_sq (N : Matrix ι ι ℝ) (p : ι → Bool)
    (V : ℝ) (hV : 0≤V) (hN : ‖N‖^2≤V) :
    ‖signedMatrix N p‖^2≤V := by
  apply matrix_norm_sq_of_energy _ V hV
  intro z
  have hs : ∀ i, (sign (p i))^2=(1:ℝ) := by
    intro i; cases p i <;> norm_num [sign]
  have he : ∀ t, (∑ w, conjugated N p t w*z w)^2 =
      (∑ w, N t w*(sign (p w)*z w))^2 := by
    intro t
    have hr : (∑ w, conjugated N p t w*z w) =
        sign (p t)*(∑ w, N t w*(sign (p w)*z w)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      unfold conjugated
      ring
    rw [hr,mul_pow,hs,one_mul]
  change (∑ t, (∑ w, conjugated N p t w*z w)^2)≤V*(∑ w, (z w)^2)
  simp_rw [he]
  have h := matrix_squared_energy N (fun i => sign (p i)*z i) V hN
  simpa only [mul_pow,hs,one_mul] using h

end
end Max2SAT.Counts
