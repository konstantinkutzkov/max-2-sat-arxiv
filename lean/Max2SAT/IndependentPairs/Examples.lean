import Max2SAT.IndependentPairs.Bernoulli
import Max2SAT.IndependentPairs.MatrixNorm
import Max2SAT.IndependentPairs.InputMembership

namespace Max2SAT.IndependentPairs.Examples
open FiniteLaw RandomInput

-- Each unordered pair appears twice in the symmetric squared-energy sum.
example : Fintype.card (Edge 2)=1 := by have h:=pair_count (n:=2); omega
example : pairEnergy (fun _ : Edge 2 => (3:ℝ))=9 := by
  have hc : Fintype.card (Edge 2)=1 := by have h:=pair_count (n:=2); omega
  norm_num [pair_energy_formula,hc]

-- Empirical centering of a single pair removes all of its row energy.
example : pairEnergy (fun _ : Edge 2 => (3:ℝ)-empiricalMean (fun _ : Edge 2 => 3))=0 := by
  have hc : Fintype.card (Edge 2)=1 := by have h:=pair_count (n:=2); omega
  norm_num [empiricalMean,pair_energy_formula,hc]

-- The first variable has no earlier neighbor, even in a nonempty graph.
example (z : Edge 3 → ℝ) : earlierEnergy z (0 : Fin 3)=0 := by simp [earlierEnergy]
example : pairEnergy (fun _ : Edge 0 => (1:ℝ))=0 := by simp [pairEnergy]

-- Max-Cut coefficients have variance 4q(1-q), including deterministic edges.
example : expect (bernoulli (1/2) (by norm_num) (by norm_num))
    (fun b => (centeredCut (1/2) b)^2)=1 := by rw [centered_cut_variance]; norm_num
example : expect (bernoulli 0 (by norm_num) (by norm_num))
    (fun b => (centeredCut 0 b)^2)=0 := by rw [centered_cut_variance]; norm_num
example : expect (bernoulli 1 (by norm_num) (by norm_num))
    (fun b => (centeredCut 1 b)^2)=0 := by rw [centered_cut_variance]; norm_num

-- Bounds are needed only on positive-mass outcomes.
example : expect (point false) (fun b => Real.exp (if b then (1000000:ℝ) else 0))≤1 := by
  have h := centered_small_mgf (point false) (fun b => if b then (1000000:ℝ) else 0) 0 0 1
    (by simp) (by intro b hb; cases b <;> simp_all [point]) (by simp) (by norm_num)
  simpa only [one_mul,mul_zero,Real.exp_zero] using h

-- Norm-convention regression: these are Euclidean operator norms. An inline
-- matrix lambda can otherwise accidentally receive a function-space norm.
open scoped Matrix.Norms.L2Operator in
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    ‖External.signedMatrix A s‖=
      ‖Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (External.signedMatrix A s)‖ := rfl

open scoped Matrix.Norms.L2Operator in
example {n : ℕ} (z : Edge n → ℝ) (T : ℕ) :
    ‖upperMatrix T z‖=‖Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (upperMatrix T z)‖ := rfl

-- Unused rows and the lower orientation do not copy an independent entry.
example {n : ℕ} (z : Edge n → ℝ) : upperMatrix 0 z=0 := by
  ext i j; simp [upperMatrix]
example (z : Edge 2 → ℝ) : upperMatrix 2 z (1 : Fin 2) (0 : Fin 2)=0 := by
  simp [upperMatrix]
example (z : Edge 2 → ℝ) : upperMatrix 2 z (0 : Fin 2) (1 : Fin 2)=z ⟨(0,1),by decide⟩ := by
  simp [upperMatrix]

-- Prefix/rounding regression: paper rows 2 through T correspond to zero-based
-- indices starting at 1, and a prefix of length zero contains no row.
example {n : ℕ} (z : Edge n → ℝ) : rowProfile z 0=0 := by simp [rowProfile]
example : lateRows 4 (1/2)={1} := by
  ext t
  fin_cases t <;> norm_num [lateRows]
example : membershipGap (1/2) 1=Real.sqrt (1/2)/24 := by
  simp only [membershipGap,Real.sqrt_one]
  ring
example : (62/100:ℝ)*1000*Real.sqrt 1000≤
    ∑ j∈Finset.Ico (100:ℕ) 1000, Real.sqrt (j:ℝ) := by
  have h := root_interval_lower 1000 (by norm_num)
  norm_num at h ⊢
  exact h

end Max2SAT.IndependentPairs.Examples
