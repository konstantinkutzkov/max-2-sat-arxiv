import Max2SAT.Community.PlaneEnergy
import Max2SAT.Community.GridRotation

/-! The actual largest-pivot step and its quantitative energy decrease. -/
namespace Max2SAT.Community
variable {n : ℕ}
set_option maxHeartbeats 1000000

def pivotPairs (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).product (List.finRange n)).filter (fun p => p.1≠p.2)

def bestPivot (A : Matrix (Fin n) (Fin n) ℚ) : Option (Fin n × Fin n) :=
  (pivotPairs n).argmax (fun p => (A p.1 p.2)^2)

def stepRotation (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  match bestPivot A with
  | none => 1
  | some (i,j) => rationalPlane i j (gridParameter D (bestGridIndex (A i i) (A i j) (A j j) D))

def jacobiUpdate (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (stepRotation D A).transpose*A*stepRotation D A

theorem mem_pivot_pairs (i j : Fin n) : (i,j)∈pivotPairs n ↔ i≠j := by
  simp [pivotPairs]

theorem best_pivot_distinct (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    (h : bestPivot A=some (i,j)) : i≠j := by
  apply (mem_pivot_pairs i j).mp
  exact List.argmax_mem (by exact h)

theorem off_energy_sum {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K) :
    offEnergy A=∑ i, ∑ j, if i=j then 0 else (A i j)^2 := by
  unfold offEnergy squareSum diagonalSquareSum
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : (∑ j, if i=j then (A i j)^2 else 0)= (A i i)^2 := by simp
  rw [←h,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij:i=j <;> simp [hij]

theorem off_energy_nonneg (A : Matrix (Fin n) (Fin n) ℚ) : 0≤offEnergy A := by
  rw [off_energy_sum]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity))

theorem off_energy_le_square_sum (A : Matrix (Fin n) (Fin n) ℚ) : offEnergy A≤squareSum A := by
  unfold offEnergy diagonalSquareSum
  exact sub_le_self _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem no_pivot_energy (A : Matrix (Fin n) (Fin n) ℚ) (h : bestPivot A=none) : offEnergy A=0 := by
  have he : pivotPairs n=[] := List.argmax_eq_none.mp h
  rw [off_energy_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij:i=j
  · simp [hij]
  · have hm := (mem_pivot_pairs i j).mpr hij
    rw [he] at hm
    exact (List.not_mem_nil hm).elim

theorem largest_pivot_energy (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n)
    (h : bestPivot A=some (i,j)) : offEnergy A≤(n:ℚ)^2*(A i j)^2 := by
  rw [off_energy_sum]
  calc
    _ ≤ ∑ _p : Fin n, ∑ _q : Fin n, (A i j)^2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      by_cases hpq:p=q
      · simp [hpq,sq_nonneg]
      · rw [ite_eq_right hpq]
        exact List.le_of_mem_argmax (f:=fun p:Fin n × Fin n => (A p.1 p.2)^2)
          ((mem_pivot_pairs p q).mpr hpq) h
    _ = _ := by simp; ring

theorem entry_square_le_total (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (A i j)^2≤squareSum A := by
  exact (Finset.single_le_sum (fun q _ => sq_nonneg (A i q)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => sq_nonneg (A p q))) (Finset.mem_univ i))

theorem entry_bound_of_square_sum (A : Matrix (Fin n) (Fin n) ℚ) (M : ℚ)
    (hM : 0≤M) (hA : squareSum A≤M^2) (i j : Fin n) : |A i j|≤M := by
  apply (sq_le_sq₀ (abs_nonneg _) hM).mp
  rw [sq_abs]
  exact (entry_square_le_total A i j).trans hA

theorem step_rotation_orthogonal (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (stepRotation D A).transpose*stepRotation D A=1 := by
  unfold stepRotation
  split
  · simp
  · rename_i i j hp
    exact rational_plane_orthogonal i j (best_pivot_distinct A _ _ hp) _

theorem jacobi_square_sum (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    squareSum (jacobiUpdate D A)=squareSum A := by
  unfold jacobiUpdate stepRotation
  split
  · simp
  · rename_i i j hp
    exact square_sum_conjugate_plane A i j (best_pivot_distinct A _ _ hp) _ _ (rotation_circle _)

theorem jacobi_symmetric (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm) :
    (jacobiUpdate D A).IsSymm := by
  change (jacobiUpdate D A).transpose=jacobiUpdate D A
  simp only [jacobiUpdate,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq,Matrix.mul_assoc]

/-- A completed grid search controls the new pivot over the rationals. -/
theorem best_grid_pivot_bound_rat (a b d M : ℚ) (D : ℕ) (hD : 0<D)
    (ha : |a|≤M) (hb : |b|≤M) (hd : |d|≤M) :
    |rotatedPivot a b d (gridParameter D (bestGridIndex a b d D))|≤16*M/D := by
  have h := best_grid_pivot_bound a b d D hD (M:ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hd)
  exact_mod_cast h

/-- While the energy exceeds epsilon, a step decreases it by at least delta. -/
theorem jacobi_progress (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (M ε δ : ℚ)
    (hD : 0<D) (hn : 0<n) (hM : 0≤M) (hA : A.IsSymm) (hsize : squareSum A≤M^2)
    (hε : 0≤ε) (hδ : (n:ℚ)^2*δ≤ε)
    (hgrid : 2*(n:ℚ)^2*(16*M/D)^2≤ε) (hactive : ε<offEnergy A) :
    offEnergy (jacobiUpdate D A)≤offEnergy A-δ := by
  obtain ⟨p,hp⟩ : ∃ p, bestPivot A=some p := by
    cases h : bestPivot A with
    | none => have hz := no_pivot_energy A h; linarith
    | some p => exact ⟨p,rfl⟩
  let t := gridParameter D (bestGridIndex (A p.1 p.1) (A p.1 p.2) (A p.2 p.2) D)
  have hsmall := best_grid_pivot_bound_rat (A p.1 p.1) (A p.1 p.2) (A p.2 p.2) M D hD
    (entry_bound_of_square_sum A M hM hsize _ _) (entry_bound_of_square_sum A M hM hsize _ _)
    (entry_bound_of_square_sum A M hM hsize _ _)
  have hsq : (rotatedPivot (A p.1 p.1) (A p.1 p.2) (A p.2 p.2) t)^2≤(16*M/D)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hsmall
    simpa only [sq_abs] using h
  have hbound := largest_pivot_energy A p.1 p.2 hp
  have he : offEnergy (jacobiUpdate D A)=offEnergy A-2*(A p.1 p.2)^2+
      2*(rotatedPivot (A p.1 p.1) (A p.1 p.2) (A p.2 p.2) t)^2 := by
    unfold jacobiUpdate stepRotation
    rw [hp]
    exact plane_energy_identity A p.1 p.2 (best_pivot_distinct A _ _ hp) (hA.apply _ _) _ _ (rotation_circle t)
  have hnq : (0:ℚ)<n := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hsq (show 0≤2*(n:ℚ)^2 by positivity)
  rw [he]
  nlinarith [sq_pos_of_pos hnq]

end Max2SAT.Community
