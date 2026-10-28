import Max2SAT.Regular.Rows

namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ}

def projection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun t w => (if t=w then 1 else 0)-1/(n:ℝ)

def centered (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := fun t w => G.adjMatrix ℝ t w-(d:ℝ)/n

theorem projection_apply (x : Fin n → ℝ) (t : Fin n) :
    (∑ w, projection n t w*x w)=x t-(∑ w, x w)/(n:ℝ) := by
  simp only [projection,sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul]
  simp [Finset.sum_mul,div_eq_mul_inv,mul_comm]

theorem centered_energy (hn : 0<n) (x : Fin n → ℝ) :
    (∑ t, (x t-(∑ w, x w)/(n:ℝ))^2)≤∑ t, (x t)^2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have he : (∑ t, (x t-(∑ w, x w)/(n:ℝ))^2)=
      (∑ t, (x t)^2)-(∑ t, x t)^2/(n:ℝ) := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.sum_mul,←Finset.mul_sum]
    field_simp
    ring
  rw [he]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hn'.le)

theorem projection_norm (hn : 0<n) : ‖projection n‖≤1 := by
  have h : ‖projection n‖^2≤1 := Counts.rectangular_norm_sq_of_energy _ 1 (by norm_num)
    (fun x => by simpa only [projection_apply,one_mul] using centered_energy hn x)
  nlinarith [norm_nonneg (projection n)]

theorem corrected_decomposition (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 2≤n) : corrected G d=(-2:ℝ) • centered G d+(correction n d:ℝ) • projection n := by
  have h1 : (n:ℝ)-1≠0 := by
    have : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have h0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  ext t w
  by_cases h:t=w
  · subst w
    simp [corrected,centered,projection,correction_cast,Matrix.add_apply,Matrix.smul_apply]
    field_simp
    ring
  · simp only [corrected,centered,projection,h,↓reduceIte,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,correction_cast]
    field_simp
    ring

theorem corrected_norm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 2≤n) (hd : d≤n-1) (L : ℝ) (_hL : 0≤L)
    (hcenter : ‖centered G d‖≤L) : ‖corrected G d‖≤2*L+2 := by
  rw [corrected_decomposition G hn]
  have hp := projection_norm (n:=n) (by omega)
  have hb := correction_bound (n:=n) hn hd
  calc
    _≤‖(-2:ℝ) • centered G d‖+‖(correction n d:ℝ) • projection n‖ := norm_add_le _ _
    _=2*‖centered G d‖+|(correction n d:ℝ)| *‖projection n‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]; norm_num
    _≤2*L+2 := by
      have h := mul_le_mul_of_nonneg_left hp (abs_nonneg (correction n d:ℝ))
      nlinarith

end
end Max2SAT.Regular
