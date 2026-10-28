import Max2SAT.Regular.IndependentSearch

namespace Max2SAT.Regular
noncomputable section
variable {n : ℕ}

def degreeBase (D : ℕ) : ℝ := Real.exp (Real.log 2*(1-1/((D:ℝ)+1)))

theorem degree_base_bounds (D : ℕ) : 1≤degreeBase D ∧ degreeBase D<2 := by
  have hp : (0:ℝ)<(D:ℝ)+1 := by positivity
  have hδ : (0:ℝ)<1/((D:ℝ)+1) := by positivity
  have hδ1 : 1/((D:ℝ)+1)≤1 := (div_le_iff₀ hp).2 (by norm_num)
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · exact Real.one_le_exp (mul_nonneg hl.le (sub_nonneg.mpr hδ1))
  · change Real.exp _<2
    rw [←Real.exp_log (by norm_num : (0:ℝ)<2)]
    apply Real.exp_lt_exp.mpr
    simp only [Real.log_exp]
    nlinarith [mul_pos hl hδ]

theorem independent_exponent (S : Finset (Fin n)) (D : ℕ)
    (hsize : n≤(D+1)*S.card) : ((n-S.card:ℕ):ℝ)≤(1-1/((D:ℝ)+1))*n := by
  have hcard : S.card≤n := by simpa using Finset.card_le_univ S
  rw [Nat.cast_sub hcard]
  have hs : (n:ℝ)≤((D:ℝ)+1)*S.card := by exact_mod_cast hsize
  have hp : (0:ℝ)<(D:ℝ)+1 := by positivity
  have hdiv : (n:ℝ)/((D:ℝ)+1)≤S.card := (div_le_iff₀ hp).2 (by nlinarith)
  have he : (1-1/((D:ℝ)+1))*(n:ℝ)=n-n/((D:ℝ)+1) := by ring
  rw [he]
  linarith

theorem independent_exponential_nodes (S : Finset (Fin n)) (D : ℕ)
    (hsize : n≤(D+1)*S.card) : (independentNodes S:ℝ)≤2*(degreeBase D)^n := by
  have hn : independentNodes S≤2^(n-S.card+1) := by
    rw [independent_nodes_exact]; exact Nat.sub_le _ _
  have hn' : (independentNodes S:ℝ)≤(2:ℝ)^(n-S.card+1) := by exact_mod_cast hn
  have hs := independent_exponent S D hsize
  have ht : (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have hp : (2:ℝ)^(n-S.card)≤(degreeBase D)^n := by
    rw [degreeBase,ht,←Real.exp_nat_mul,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    have h := mul_le_mul_of_nonneg_left hs (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    nlinarith
  rw [pow_succ] at hn'
  nlinarith

theorem bounded_degree_nodes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hd : ∀ v, G.degree v≤D) :
    (independentNodes (independentSet G):ℝ)≤2*(degreeBase D)^n ∧ degreeBase D<2 :=
  ⟨independent_exponential_nodes _ D (independent_set_size G D hd),(degree_base_bounds D).2⟩

end
end Max2SAT.Regular
