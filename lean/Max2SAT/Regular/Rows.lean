import Max2SAT.Counts.TwoRounds
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! The corrected interactions of a regular Max-Cut instance. The graph
is the input graph, and all row identities refer to its actual adjacency. -/
namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def correction (n d : ℕ) : ℚ := -2*(d:ℚ)/((n:ℚ)-1)
def corrected (d : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun t w => if t=w then 0 else -2*G.adjMatrix ℝ t w-(correction n d:ℝ)
def rowEnergy (n d : ℕ) : ℝ := 4*d*(1-(d:ℝ)/((n:ℝ)-1))

theorem correction_cast : (correction n d:ℝ)=-2*(d:ℝ)/((n:ℝ)-1) := by
  simp [correction]

theorem adjacency_row_sum (hd : G.IsRegularOfDegree d) (t : Fin n) :
    (∑ w, G.adjMatrix ℝ t w)=(d:ℝ) := by
  have h := G.adjMatrix_mulVec_const_apply_of_regular (α:=ℝ) hd (a:=1) (v:=t)
  simpa [Matrix.mulVec,dotProduct] using h

theorem adjacency_square (t w : Fin n) : (G.adjMatrix ℝ t w)^2=G.adjMatrix ℝ t w := by
  simp only [SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

theorem corrected_square (t w : Fin n) :
    (corrected G d t w)^2=
      (4+4*(correction n d:ℝ))*G.adjMatrix ℝ t w+
        (correction n d:ℝ)^2*(if t=w then 0 else 1) := by
  by_cases h : t=w
  · subst w; simp [corrected]
  · simp only [corrected,h,↓reduceIte,mul_one]
    nlinarith [adjacency_square G t w]

theorem corrected_row_energy (hn : 2≤n) (hd : G.IsRegularOfDegree d) (t : Fin n) :
    (∑ w, (corrected G d t w)^2)=rowEnergy n d := by
  simp_rw [corrected_square]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,adjacency_row_sum G hd t]
  have hs : (∑ w : Fin n, if t=w then (0:ℝ) else 1)=(n:ℝ)-1 := by
    have he : ∀ w : Fin n, (if t=w then (0:ℝ) else 1)=1-(if t=w then 1 else 0) := by
      intro w; split_ifs <;> norm_num
    simp_rw [he]
    simp
  rw [hs,correction_cast,rowEnergy]
  have hn' : (n:ℝ)-1≠0 := by
    have : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  field_simp
  ring

theorem corrected_diagonal (t : Fin n) : corrected G d t t=0 := by simp [corrected]

theorem corrected_row_sum (hn : 2≤n) (hd : G.IsRegularOfDegree d) (t : Fin n) :
    (∑ w, corrected G d t w)=0 := by
  have he : ∀ w, corrected G d t w=
      -2*G.adjMatrix ℝ t w-(correction n d:ℝ)*(if t=w then 0 else 1) := by
    intro w; by_cases h:t=w <;> simp [corrected,h]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,adjacency_row_sum G hd t]
  have hs : (∑ w : Fin n, if t=w then (0:ℝ) else 1)=(n:ℝ)-1 := by
    have he : ∀ w : Fin n, (if t=w then (0:ℝ) else 1)=1-(if t=w then 1 else 0) := by
      intro w; split_ifs <;> norm_num
    simp_rw [he]; simp
  rw [hs,correction_cast]
  have hn' : (n:ℝ)-1≠0 := by
    have : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  field_simp
  ring

/-- The finite-size density calculation behind both the row scale and
an edge's contribution to the second-round requirements. -/
theorem density_margin (hn : 2≤n) (ε : ℝ) (he : 0<ε) (_he1 : ε≤1)
    (hsize : 2≤ε*n) (hd : (d:ℝ)≤(1-ε)*n) :
    ε/2≤1-(d:ℝ)/((n:ℝ)-1) := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hdiv : (d:ℝ)/((n:ℝ)-1)≤1-ε/2 := by
    apply (div_le_iff₀ (by linarith)).2
    nlinarith
  linarith

theorem row_energy_bounds (hn : 2≤n) (ε : ℝ) (he : 0<ε) (he1 : ε≤1)
    (hsize : 2≤ε*n) (hd : (d:ℝ)≤(1-ε)*n) :
    2*ε*d≤rowEnergy n d ∧ rowEnergy n d≤4*d := by
  have h := density_margin (n:=n) (d:=d) hn ε he he1 hsize hd
  have hn' : (0:ℝ)≤(n:ℝ)-1 := by
    have : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hf := div_nonneg (Nat.cast_nonneg d) hn'
  constructor <;> dsimp [rowEnergy] <;> nlinarith [Nat.cast_nonneg (α:=ℝ) d]

theorem correction_bound (hn : 2≤n) (hd : d≤n-1) : |(correction n d:ℝ)|≤2 := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hd' : (d:ℝ)≤(n:ℝ)-1 := by
    have h : d+1≤n := by omega
    have h' : (d:ℝ)+1≤n := by exact_mod_cast h
    linarith
  rw [correction_cast,abs_div,abs_mul]
  norm_num [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d),
    abs_of_pos (by linarith : (0:ℝ)<n-1)]
  exact (div_le_iff₀ (by linarith)).2 (by linarith)

end
end Max2SAT.Regular
