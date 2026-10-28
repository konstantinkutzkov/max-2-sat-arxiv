import Max2SAT.Counts.ProfileParameters
import Max2SAT.Counts.LaterRounds

namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem rectangular_norm_sq_of_energy {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (N : Matrix κ ι ℝ) (V : ℝ) (hV : 0≤V)
    (he : ∀ z : ι → ℝ, (∑ t, (∑ w, N t w*z w)^2)≤V*(∑ w, (z w)^2)) :
    ‖N‖^2≤V := by
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)
  have hb : ‖T‖≤Real.sqrt V := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg V)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hV,EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    exact he x
  have hs := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg V)).2 hb
  rw [Real.sq_sqrt hV] at hs
  exact hs

theorem round_prefix_closed (round : Fin n → ℕ) (k : ℕ) :
    EarlierInPrefix (roundPrefix round k) round := by
  intro t ht w hw
  have ht' := (Finset.mem_filter.mp ht).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw.trans ht'⟩

theorem sequential_profile_norm (H : Fin n → Affine n) (P : Finset (Fin n))
    (hr : EarlierInPrefix P (fun i => i.val))
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t)
    (V : ℝ) (hV : 0≤V) (hN : ‖sequentialMatrix H P‖^2≤V) :
    ‖prefixRows H P (fun i => i.val)‖^2≤V := by
  apply rectangular_norm_sq_of_energy _ V hV
  intro z
  have hn : ‖(sequentialMatrix H P).transpose‖^2≤V := by
    simpa using (show ‖(sequentialMatrix H P).conjTranspose‖^2≤V by
      rw [Matrix.l2_opNorm_conjTranspose]; exact hN)
  have he : ∀ t : P, (∑ w, prefixRows H P (fun i => i.val) t w*z w)=
      ∑ w : P, (sequentialMatrix H P).transpose t w*z w := by
    intro t
    simp only [Matrix.transpose_apply,sequentialMatrix,ite_mul,zero_mul]
    rw [Finset.sum_coe_sort P (fun w =>
      if w.val<t.val.val then ((H w).coeff t : ℝ)*z w else 0),
      ←Fintype.sum_extend_by_zero P]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hp : w∈P
    · simp only [prefixRows,earlierRow,
        ite_mul,zero_mul,hp,↓reduceIte]
      rw [hsym t w]
    · have hh : ¬w.val<t.val.val := fun h => hp (hr t t.property w h)
      simp [prefixRows,earlierRow,hh,hp]
  simp_rw [he]
  have hb := matrix_squared_energy (sequentialMatrix H P).transpose (fun w : P => z w) V hn
  have hl : (∑ t : P, (∑ w : P, (sequentialMatrix H P).transpose t w*z w)^2)≤
      ∑ t, (∑ w : P, (sequentialMatrix H P).transpose t w*z w)^2 := by
    rw [Finset.sum_coe_sort P (fun t => (∑ w : P, (sequentialMatrix H P).transpose t w*z w)^2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hz : (∑ w : P, (z w)^2)≤∑ w, (z w)^2 := by
    rw [Finset.sum_coe_sort P (fun w => (z w)^2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  exact hl.trans (hb.trans (mul_le_mul_of_nonneg_left hz hV))


theorem round_profile_norm (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (hk : 0<k) (V : ℝ) (hV : 0≤V) (hN : ‖interactionMatrix H‖^2≤V) :
    ‖prefixRows H (roundPrefix round k) round‖^2≤(k-1:ℕ)*V := by
  apply rectangular_norm_sq_of_energy _ _ (by positivity)
  intro z
  let f : Fin n → ℝ := fun t => ∑ w, earlierRow H round t w*z w
  have hb : ∀ j, (∑ t∈roundBlock round j, (f t)^2)≤V*(∑ w, (z w)^2) := by
    intro j
    let y : Fin n → ℝ := fun w => if round w<j then z w else 0
    have hy : (∑ w, (y w)^2)≤∑ w, (z w)^2 := by
      apply Finset.sum_le_sum
      intro w _
      unfold y
      split_ifs <;> simp [sq_nonneg]
    have he : ∀ t∈roundBlock round j, f t=∑ w, interactionMatrix H t w*y w := by
      intro t ht
      have hh := (Finset.mem_filter.mp ht).2
      apply Finset.sum_congr rfl
      intro w _
      simp only [earlierRow,hh,interactionMatrix,y,ite_mul,mul_ite,mul_zero,zero_mul]
    calc
      _ = ∑ t∈roundBlock round j, (∑ w, interactionMatrix H t w*y w)^2 :=
        Finset.sum_congr rfl (fun t ht => congrArg (fun v : ℝ => v^2) (he t ht))
      _ ≤ ∑ t, (∑ w, interactionMatrix H t w*y w)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ V*(∑ w, (z w)^2) := (matrix_squared_energy (interactionMatrix H) y V hN).trans
        (mul_le_mul_of_nonneg_left hy hV)
  have h0 : (∑ t∈roundBlock round 0, (f t)^2)=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hh := (Finset.mem_filter.mp ht).2
    simp [f,earlierRow,hh]
  change (∑ t : roundPrefix round k, (f t)^2)≤_
  rw [Finset.sum_coe_sort (roundPrefix round k) (fun t => (f t)^2),←sum_round_blocks]
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Finset.sum_range_succ',h0,add_zero]
  calc
    _ ≤ ∑ _j∈Finset.range l, V*(∑ w, (z w)^2) := Finset.sum_le_sum (fun j _ => hb (j+1))
    _ = _ := by simp [mul_assoc]

end
end Max2SAT.Counts
