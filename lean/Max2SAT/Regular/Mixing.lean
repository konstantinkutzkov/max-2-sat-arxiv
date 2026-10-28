import Max2SAT.Regular.Centering

namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ}

def crossEdges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Finset (Fin n)) : ℝ := ∑ t∈X, ∑ w∈Y, G.adjMatrix ℝ t w

theorem matrix_set_sum (B : Matrix (Fin n) (Fin n) ℝ) (X Y : Finset (Fin n)) :
    |∑ t∈X, ∑ w∈Y, B t w|≤‖B‖*Real.sqrt ((X.card:ℝ)*Y.card) := by
  let z : Fin n → ℝ := fun w => if w∈Y then 1 else 0
  have hz : (∑ w, (z w)^2)=(Y.card:ℝ) := by simp [z]
  have hi : ∀ t, (∑ w, B t w*z w)=∑ w∈Y, B t w := by intro t; simp [z]
  have he := Counts.matrix_squared_energy B z (‖B‖^2) le_rfl
  rw [hz] at he
  simp_rw [hi] at he
  have hsub : (∑ t∈X, (∑ w∈Y, B t w)^2)≤∑ t, (∑ w∈Y, B t w)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq X (fun _ => (1:ℝ)) (fun t => ∑ w∈Y, B t w)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  have hs := hc.trans (mul_le_mul_of_nonneg_left (hsub.trans he) (Nat.cast_nonneg X.card))
  have hp : 0≤(X.card:ℝ)*Y.card := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt hp]
  nlinarith

theorem expander_mixing (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Finset (Fin n)) (L : ℝ) (hN : ‖centered G d‖≤L) :
    |crossEdges G X Y-(d:ℝ)*X.card*Y.card/n|≤L*Real.sqrt ((X.card:ℝ)*Y.card) := by
  have hid : (∑ t∈X, ∑ w∈Y, centered G d t w)=
      crossEdges G X Y-(d:ℝ)*X.card*Y.card/n := by
    simp only [centered,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,crossEdges]
    ring
  rw [←hid]
  exact (matrix_set_sum _ X Y).trans (mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg _))

/-- Rounding-aware form of the lower edge count between the two rounds. -/
theorem round_edge_lower (N a b D L e : ℝ) (hN : 80≤N) (ha : 0≤a) (hb : 0≤b)
    (ha' : N/4-1≤a) (hb' : N/4-1≤b) (hsum : a+b≤N/2)
    (hD : 0≤D) (hL : 0≤L) (hL' : L≤D/8)
    (hmix : |e-D*a*b/N|≤L*Real.sqrt (a*b)) : D*N/40≤e := by
  have hab : N^2/16-N/2≤a*b := by
    have h := mul_le_mul ha' hb' (by linarith) ha
    nlinarith
  have hsqrt : Real.sqrt (a*b)≤N/4 := by
    apply (Real.sqrt_le_left (by linarith)).2
    nlinarith [sq_nonneg (a-b),sq_nonneg (N/2-(a+b))]
  have hbase : D*N/16-D/2≤D*a*b/N := by
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [mul_le_mul_of_nonneg_left hab hD]
  have herr : L*Real.sqrt (a*b)≤D*N/32 := by
    have h := mul_le_mul hsqrt hL' hL (by linarith : 0≤N/4)
    nlinarith
  have hlow := (abs_le.mp hmix).1
  nlinarith [mul_nonneg hD (show 0≤N-80 by linarith)]

end
end Max2SAT.Regular
