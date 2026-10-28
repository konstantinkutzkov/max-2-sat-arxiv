import Max2SAT.Counts.OperatorEnergy

/-! Exact deterministic centering identities used in the independent-pair
proof. Empirical centering is handled by algebra; it is not treated as a
new family of independent random entries. -/
namespace Max2SAT.IndependentPairs
noncomputable section
variable {ι : Type*} [Fintype ι]

def empiricalMean (x : ι → ℝ) : ℝ := (∑ i, x i)/Fintype.card ι

theorem shift_energy (x : ι → ℝ) (δ : ℝ) :
    (∑ i, (x i-δ)^2)=(∑ i, (x i)^2)-2*δ*(∑ i, x i)+(Fintype.card ι:ℝ)*δ^2 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,←Finset.sum_mul]
  ring

theorem centered_energy_identity (x : ι → ℝ) (δ : ℝ)
    (hmean : (∑ i, x i)=(Fintype.card ι:ℝ)*δ) :
    (∑ i, (x i-δ)^2)=(∑ i, (x i)^2)-(Fintype.card ι:ℝ)*δ^2 := by
  rw [shift_energy,hmean]; ring

theorem empirical_mean_sum [Nonempty ι] (x : ι → ℝ) :
    (∑ i, x i)=(Fintype.card ι:ℝ)*empiricalMean x := by
  have hc : (Fintype.card ι:ℝ)≠0 := by exact_mod_cast (ne_of_gt (Fintype.card_pos (α:=ι)))
  dsimp [empiricalMean]; field_simp

theorem empirical_energy [Nonempty ι] (x : ι → ℝ) :
    (∑ i, (x i-empiricalMean x)^2)=
      (∑ i, (x i)^2)-(Fintype.card ι:ℝ)*(empiricalMean x)^2 :=
  centered_energy_identity x _ (empirical_mean_sum x)

theorem empirical_mean_shift [Nonempty ι] (x : ι → ℝ) (μ : ℝ) :
    empiricalMean (fun i => x i-μ)=empiricalMean x-μ := by
  have hc : (Fintype.card ι:ℝ)≠0 := by exact_mod_cast (ne_of_gt (Fintype.card_pos (α:=ι)))
  simp only [empiricalMean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem shift_row_norm (x : ι → ℝ) (δ : ℝ) :
    Real.sqrt (∑ i, (x i)^2)-|δ| *Real.sqrt (Fintype.card ι)≤
      Real.sqrt (∑ i, (x i-δ)^2) := by
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 x
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => δ)
  have h := norm_le_norm_sub_add a b
  have ha : ‖a‖=Real.sqrt (∑ i, (x i)^2) := by simp [a,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs]
  have hab : ‖a-b‖=Real.sqrt (∑ i, (x i-δ)^2) := by
    simp [a,b,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs]
  have hb : ‖b‖=|δ| *Real.sqrt (Fintype.card ι) := by
    simp [b,EuclideanSpace.norm_eq,Real.norm_eq_abs,Real.sqrt_mul,Real.sqrt_sq_eq_abs,mul_comm]
  rw [ha,hab,hb] at h
  linarith

/-- The numerical row loss used in the paper, including an arbitrary
empirical shift satisfying the stated bound. -/
theorem centered_row_lower (x : ι → ℝ) (δ ν : ℝ) (hν : 0≤ν)
    (hmass : (99/100:ℝ)*(Fintype.card ι)*ν≤∑ i, (x i)^2)
    (hδ : |δ|≤(1/1000:ℝ)*Real.sqrt ν) :
    (993/1000:ℝ)*Real.sqrt ((Fintype.card ι)*ν)≤Real.sqrt (∑ i, (x i-δ)^2) := by
  have hraw : (994/1000:ℝ)*Real.sqrt ((Fintype.card ι)*ν)≤Real.sqrt (∑ i, (x i)^2) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)) hν]
  have hloss := mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg (Fintype.card ι:ℝ))
  have he : Real.sqrt ν*Real.sqrt (Fintype.card ι)=Real.sqrt ((Fintype.card ι)*ν) := by
    rw [←Real.sqrt_mul hν,mul_comm]
  have h := shift_row_norm x δ
  rw [mul_assoc,he] at hloss
  linarith

end
end Max2SAT.IndependentPairs
