import Max2SAT.Regular.Rows

namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def crossDegree (X : Finset (Fin n)) (t : Fin n) : ℝ := ∑ w∈X, G.adjMatrix ℝ t w
def roundRow (d : ℕ) (X : Finset (Fin n)) (t : Fin n) : ℝ :=
  ∑ w∈X, (corrected G d t w)^2

theorem adjacency_nonneg (t w : Fin n) : 0≤G.adjMatrix ℝ t w := by
  simp only [SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

theorem cross_degree_bounds (hd : G.IsRegularOfDegree d) (X : Finset (Fin n)) (t : Fin n) :
    0≤crossDegree G X t ∧ crossDegree G X t≤d := by
  refine ⟨Finset.sum_nonneg (fun w _ => adjacency_nonneg G t w),?_⟩
  rw [←adjacency_row_sum G hd t]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => adjacency_nonneg G t w)

theorem round_row_lower (hn : 2≤n) (ε : ℝ) (he : 0<ε) (he1 : ε≤1)
    (hsize : 2≤ε*n) (hd : (d:ℝ)≤(1-ε)*n)
    (X : Finset (Fin n)) (t : Fin n) (ht : t∉X) :
    ε^2*crossDegree G X t≤roundRow G d X t := by
  have hm := density_margin hn ε he he1 hsize hd
  unfold roundRow crossDegree
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have htw : t≠w := by intro h; subst w; exact ht hw
  by_cases hadj : G.Adj t w
  · have hc : corrected G d t w≤-ε := by
      simp only [corrected,htw,↓reduceIte,SimpleGraph.adjMatrix_apply,hadj,correction_cast,mul_div_assoc]
      nlinarith
    simp only [SimpleGraph.adjMatrix_apply,hadj,↓reduceIte,mul_one]
    nlinarith
  · simp only [SimpleGraph.adjMatrix_apply,hadj,↓reduceIte,mul_zero]
    exact sq_nonneg _

theorem sqrt_row_lower (ε a D W : ℝ) (he : 0≤ε) (ha : 0≤a) (hD : 0<D)
    (haD : a≤D) (hW : ε^2*a≤W) : ε*a/Real.sqrt D≤Real.sqrt W := by
  have hW0 : 0≤W := (mul_nonneg (sq_nonneg ε) ha).trans hW
  have hsD := Real.sq_sqrt hD.le
  have hsW := Real.sq_sqrt hW0
  have h1 := mul_le_mul_of_nonneg_left haD ha
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ε)
  have h3 := mul_le_mul_of_nonneg_right hW hD.le
  have hp : ε*a≤Real.sqrt W*Real.sqrt D := by
    apply (sq_le_sq₀ (mul_nonneg he ha) (by positivity)).mp
    simp only [mul_pow,hsW,hsD]
    nlinarith
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hD)).2 hp

theorem profile_from_edges (hn : 2≤n) (hreg : G.IsRegularOfDegree d)
    (hd0 : 0<d) (ε : ℝ) (he : 0<ε) (he1 : ε≤1)
    (hsize : 2≤ε*n) (hd : (d:ℝ)≤(1-ε)*n)
    (X Y : Finset (Fin n)) (hdis : Disjoint X Y)
    (hedges : (d:ℝ)*n/40≤∑ t∈Y, crossDegree G X t) :
    ε*n*Real.sqrt d/40≤∑ t∈Y, Real.sqrt (roundRow G d X t) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd0
  have hsum : (∑ t∈Y, ε*crossDegree G X t/Real.sqrt d)≤
      ∑ t∈Y, Real.sqrt (roundRow G d X t) := by
    apply Finset.sum_le_sum
    intro t ht
    have htX : t∉X := fun h => Finset.disjoint_left.mp hdis h ht
    exact sqrt_row_lower ε _ _ _ he.le (cross_degree_bounds G hreg X t).1 hd'
      (cross_degree_bounds G hreg X t).2 (round_row_lower G hn ε he he1 hsize hd X t htX)
  rw [←Finset.sum_div,←Finset.mul_sum] at hsum
  have hmul := mul_le_mul_of_nonneg_left hedges he.le
  have hdiv := div_le_div_of_nonneg_right hmul (Real.sqrt_nonneg (d:ℝ))
  have hid : ε*((d:ℝ)*n/40)/Real.sqrt d=ε*n*Real.sqrt d/40 := by
    have hs := Real.sq_sqrt hd'.le
    have hp := Real.sqrt_pos.mpr hd'
    apply (div_eq_iff (ne_of_gt hp)).2
    nlinarith
  rw [hid] at hdiv
  exact hdiv.trans hsum

end
end Max2SAT.Regular
