import Max2SAT.Community.ComputedDiscovery
import Max2SAT.IndependentPairs.Bernoulli
import Max2SAT.Regular.CutScore

/-! The original stochastic block model: a fixed arbitrary partition and
independent Boolean edges, with a symmetric matrix of block probabilities.
The partition and probabilities enter the law, not the search algorithm. -/
namespace Max2SAT.Community
noncomputable section
open Counts FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
variable {n k : ℕ}
set_option maxHeartbeats 1000000

def blockProbability (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ)
    (e : Edge n) : ℝ := π (group e.val.1) (group e.val.2)

def blockMean (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => -2*π (group i) (group j)

theorem block_mean_hermitian (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ)
    (hπ : π.IsSymm) : (blockMean group π).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,blockMean,hπ.apply (group i) (group j)]

theorem block_mean_rank (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ) :
    (blockMean group π).rank≤k := by
  classical
  let Z : Matrix (Fin n) (Fin k) ℝ := fun i a => if group i=a then 1 else 0
  let W : Matrix (Fin k) (Fin n) ℝ := fun a j => -2*π a (group j)
  have he : blockMean group π=Z*W := by
    ext i j
    change -2*π (group i) (group j)=∑ a, Z i a*W a j
    simp [Z,W]
  rw [he]
  exact (Matrix.rank_mul_le_left Z W).trans (by simpa using Matrix.rank_le_card_width Z)

theorem block_mean_entry_bound (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ)
    (h0 : ∀ a b, 0≤π a b) (h1 : ∀ a b, π a b≤1) (i j : Fin n) :
    |blockMean group π i j|≤2 := by
  simp only [blockMean]
  exact abs_le.mpr ⟨by linarith [h1 (group i) (group j)],by linarith [h0 (group i) (group j)]⟩

theorem block_mean_norm (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ)
    (h0 : ∀ a b, 0≤π a b) (h1 : ∀ a b, π a b≤1) :
    ‖blockMean group π‖≤2*n := by
  apply (operator_le_frobenius _).trans
  apply (sq_le_sq₀ (frobenius_nonneg _) (by positivity)).mp
  rw [frobenius_square]
  calc
    _ ≤ ∑ _i:Fin n, ∑ _j:Fin n, (2:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mpr
        (block_mean_entry_bound group π h0 h1 i j)
      simpa only [sq_abs] using h
    _ = _ := by simp; ring

/-- A Boolean sample includes precisely the unordered pairs with value true. -/
def sampledGraph (x : Edge n → Bool) : SimpleGraph (Fin n) where
  Adj i j := if h : i < j then x ⟨(i,j),h⟩=true else if h : j < i then x ⟨(j,i),h⟩=true else False
  symm := ⟨by
    intro i j
    rcases lt_trichotomy i j with h|rfl|h
    · simp [h,not_lt.mpr h.le]
    · simp
    · simp [h,not_lt.mpr h.le]⟩
  loopless := ⟨by intro i; simp⟩

noncomputable instance sampledGraphDecidable (x : Edge n → Bool) : DecidableRel (sampledGraph x).Adj :=
  Classical.decRel _

def sampledFormula (x : Edge n → Bool) (units : List (Literal n)) : Formula n :=
  Regular.formula (sampledGraph x) units

theorem sampled_formula_wellFormed (x : Edge n → Bool) (units : List (Literal n)) :
    wellFormed (sampledFormula x units) := Regular.formula_wellFormed _ _

theorem sampled_formula_matrix (x : Edge n → Bool) (units : List (Literal n)) :
    interactionMatrix (gainExpr (sampledFormula x units))=pairMatrix (fun e => cutInteraction (x e)) := by
  ext i j
  simp only [interactionMatrix,sampledFormula,Regular.formula_coeff]
  rcases lt_trichotomy i j with h|rfl|h
  · cases hx : x ⟨(i,j),h⟩ <;>
      simp [SimpleGraph.adjMatrix_apply,sampledGraph,pairMatrix,cutInteraction,h,hx]
  · simp [SimpleGraph.adjMatrix_apply,sampledGraph,pairMatrix]
  · cases hx : x ⟨(j,i),h⟩ <;>
      simp [SimpleGraph.adjMatrix_apply,sampledGraph,pairMatrix,cutInteraction,h,not_lt.mpr h.le,hx]

theorem sampled_formula_model (group : Fin n → Fin k) (π : Matrix (Fin k) (Fin k) ℝ)
    (hπ : π.IsSymm) (x : Edge n → Bool) (units : List (Literal n)) :
    interactionMatrix (gainExpr (sampledFormula x units))=blockMean group π+
      pairMatrix (fun e => centeredCut (blockProbability group π e) (x e))-
      Matrix.diagonal (fun i => blockMean group π i i) := by
  rw [sampled_formula_matrix]
  ext i j
  rcases lt_trichotomy i j with h|rfl|h
  · simp [pairMatrix,blockMean,blockProbability,centeredCut,h,ne_of_lt h]
  · simp [pairMatrix,blockMean]
  · simp [pairMatrix,blockMean,blockProbability,centeredCut,h,not_lt.mpr h.le,Ne.symm (ne_of_lt h),hπ.apply (group i) (group j)]

/-- Formula exactness specializes to the ordinary cut objective. -/
theorem sampled_maxcut_correct (x : Edge n → Bool) (r : ℕ) (g : ℚ) :
    ∃ q a, diagonalizedResult (sampledFormula x []) r g=some (q,a) ∧
      ∀ b, Regular.cutSize (sampledGraph x) b≤Regular.cutSize (sampledGraph x) a := by
  obtain ⟨q,a,he,hs,ho⟩ := diagonalized_result_correct (sampledFormula x []) r g
    (sampled_formula_wellFormed x [])
  refine ⟨q,a,he,Regular.optimal_cut_of_optimal_formula _ a ?_⟩
  intro b
  rw [hs] at ho
  exact ho b

end
end Max2SAT.Community
