import Max2SAT.Bias.Complexity
import Max2SAT.Bias.PreprocessStats
import Max2SAT.Bias.Simple

/-! The dense effective-gap corollary, with hypotheses on the original simple
formula and the node bound for the actual preprocessed search. -/
namespace Max2SAT.Bias
open FairCoin
noncomputable section

structure DenseGap (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ) : Prop where
  epsilon_pos : 0 < ε
  epsilon_le : ε ≤ 1
  eta_pos : 0 < η
  eta_le : η ≤ 1
  size : η*n ≤ S.card
  bias : ∀ i ∈ S, ε*n ≤ |(gap F i : ℝ)|

theorem dense_total_gap (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ)
    (hF : wellFormed F) (h : DenseGap F S ε η) :
    ε*η*(n:ℝ)^2 ≤ (gapMass (preprocess F).1 Finset.univ : ℝ) := by
  have hsum := Finset.sum_le_sum h.bias
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hs : (∑ i ∈ S, |(gap F i : ℝ)|) ≤ ∑ i : Fin n, |(gap F i : ℝ)| :=
    Finset.sum_le_univ_sum_of_nonneg (fun i => abs_nonneg _)
  have hm := mul_le_mul_of_nonneg_left h.size
    (mul_nonneg h.epsilon_pos.le (Nat.cast_nonneg n))
  rw [gapMass_real]
  simp_rw [preprocess_gap F hF]
  nlinarith

theorem dense_occurrence_squares (F : Formula n) (hF : Simple F) :
    (∑ i : Fin n, (B (preprocess F).1 i : ℝ)^2) ≤ 16*(n:ℝ)^3 := by
  have hi : ∀ i : Fin n, (B (preprocess F).1 i : ℝ)^2 ≤ (4*(n:ℝ))^2 := by
    intro i
    have hb : (B (preprocess F).1 i : ℝ) ≤ 4*(n:ℝ) := by
      exact_mod_cast le_trans (preprocess_occurrences F i) (simple_occurrences_linear F hF i)
    have hz : (0:ℝ) ≤ B (preprocess F).1 i := by positivity
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  calc
    _ ≤ ∑ _i : Fin n, (4*(n:ℝ))^2 := hs
    _ = 16*(n:ℝ)^3 := by simp; ring

private theorem gap_zero_of_occurrences_zero (F : Formula n) (hF : wellFormed F)
    (i : Fin n) (hi : B F i = 0) : gap F i = 0 := by
  have hb : benefit F (initialPreference F) i = fun _ => 0 := by
    funext x
    have hs := score_change F x i ((initialPreference F) i)
    rw [hi, Nat.cast_zero, abs_le] at hs
    have he : (score F (Function.update x i (initialPreference F i)) : ℝ) - score F x = 0 := by
      linarith [hs.1,hs.2]
    simpa [benefit, preferred, Literal.force] using he
  have hm := mean_initial_benefit F i hF
  rw [hb, average_const] at hm
  have he : |(gap F i : ℝ)| = 0 := by linarith
  exact_mod_cast abs_eq_zero.mp he

theorem occurrence_squares_positive (F : Formula n) (hF : wellFormed F)
    (hG : 0 < (gapMass F Finset.univ : ℝ)) :
    0 < ∑ i : Fin n, (B F i : ℝ)^2 := by
  by_contra hh
  have hQ := le_of_not_gt hh
  have hz : ∀ i, gap F i = 0 := by
    intro i
    have hi : (B F i : ℝ)^2 ≤ ∑ j : Fin n, (B F j : ℝ)^2 :=
      Finset.single_le_sum (f := fun j => (B F j : ℝ)^2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have he : (B F i : ℝ) = 0 := by nlinarith
    have he' : B F i = 0 := by exact_mod_cast he
    exact gap_zero_of_occurrences_zero F hF i he'
  simp [gapMass,hz] at hG

theorem dense_gap_probability (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ)
    (hF : Simple F) (h : DenseGap F S ε η) (hn : 0 < n) :
    probability n (admissible (preprocess F).1 (initialPreference (preprocess F).1)
      (branchingSet (preprocess F).1)) ≤ Real.exp (-(ε*η)^2*n/8192) := by
  let F0 := (preprocess F).1
  let Q := ∑ i : Fin n, (B F0 i : ℝ)^2
  let G := (gapMass F0 Finset.univ : ℝ)
  have hw : wellFormed F0 := (preprocess_finished F hF.1).1
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hG : ε*η*(n:ℝ)^2 ≤ G := dense_total_gap F S ε η hF.1 h
  have hg0 : 0 < ε*η*(n:ℝ)^2 :=
    mul_pos (mul_pos h.epsilon_pos h.eta_pos) (sq_pos_of_pos hn')
  have hq : 0 < Q := occurrence_squares_positive F0 hw (lt_of_lt_of_le hg0 hG)
  have hQ : Q ≤ 16*(n:ℝ)^3 := dense_occurrence_squares F hF
  have hs : (ε*η*(n:ℝ)^2)^2 ≤ G^2 := by nlinarith
  have he : (ε*η*(n:ℝ)^2)^2 / (8192*(n:ℝ)^3) = (ε*η)^2*n/8192 := by
    field_simp
  have hr : (ε*η)^2*n/8192 ≤ G^2/(512*Q) := calc
    _ = (ε*η*(n:ℝ)^2)^2 / (8192*(n:ℝ)^3) := he.symm
    _ ≤ G^2 / (8192*(n:ℝ)^3) := div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ G^2 / (512*Q) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  apply le_trans (gap_mass_probability F0 hw hq)
  apply Real.exp_le_exp.mpr
  change -G^2/(512*Q) ≤ -(ε*η)^2*n/8192
  simpa only [neg_div,neg_mul] using neg_le_neg hr

theorem dense_gap_output_count (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ)
    (hF : Simple F) (h : DenseGap F S ε η) (hn : 0 < n) :
    ((Hybrid.outputs (preprocess F).1 (initialPreference (preprocess F).1)
      (branchingSet (preprocess F).1)).length : ℝ) ≤
      (2:ℝ)^n * Real.exp (-(ε*η)^2*n/8192) := by
  rw [Hybrid.output_count]
  have hp := dense_gap_probability F S ε η hF h hn
  rw [probability_eq_count] at hp
  have hc := (div_le_iff₀ (by positivity : (0:ℝ) < 2^n)).mp hp
  simpa only [mul_comm] using hc

/-- Converts the probability bound into the cost of the same executable
prefix/suffix search. This is the counting step used in both bias results. -/
private theorem nodes_of_probability (F : Formula n) (α : ℝ)
    (hα1 : α ≤ 1/512)
    (hp : probability n (admissible F (initialPreference F) (branchingSet F)) ≤
      Real.exp (-α*n)) :
    (Hybrid.nodeCount F (initialPreference F) (branchingSet F) : ℝ) ≤
      (4+2*n)*Real.exp ((Real.log 2-α)*n) := by
  have hl : (1:ℝ)/2≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have ht : ((branchingSet F).card : ℝ)≤(n:ℝ)/2+1 := by
    have hh := branchingSet_card F
    have hk : 2*(branchingSet F).card≤n+1 := by omega
    have hk' : 2*((branchingSet F).card : ℝ)≤(n:ℝ)+1 := by exact_mod_cast hk
    linarith
  have htwo : (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have hprefix : (2:ℝ)^((branchingSet F).card+1)≤
      4*Real.exp ((Real.log 2-α)*n) := by
    rw [htwo,←Real.exp_nat_mul]
    have h4 : (4:ℝ)=Real.exp (2*Real.log 2) := by
      rw [show 2*Real.log 2=Real.log 2+Real.log 2 by ring,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
      norm_num
    rw [h4,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    push_cast
    have hm := mul_le_mul_of_nonneg_right ht (by linarith : 0≤Real.log 2)
    have hs : α≤Real.log 2/2 := by linarith
    have hm' := mul_le_mul_of_nonneg_right hs (show (0:ℝ)≤n by positivity)
    nlinarith
  rw [probability_eq_count] at hp
  have hcount := (div_le_iff₀ (by positivity : (0:ℝ)<2^n)).mp hp
  have he : Real.exp (-α*n)*(2:ℝ)^n=
      Real.exp ((Real.log 2-α)*n) := by
    rw [htwo,←Real.exp_nat_mul,←Real.exp_add]
    simp only [Real.log_exp]
    congr 1; ring
  rw [he] at hcount
  have hnodes := Hybrid.nodeCount_bound F (initialPreference F) (branchingSet F)
  have hnodes' : (Hybrid.nodeCount F (initialPreference F) (branchingSet F) : ℝ)≤
      (2:ℝ)^((branchingSet F).card+1)+
        2*n*(eventCount n (admissible F (initialPreference F) (branchingSet F)) : ℝ) := by
    have hh : Hybrid.nodeCount F (initialPreference F) (branchingSet F)≤
        2^((branchingSet F).card+1)+2*n*eventCount n (admissible F (initialPreference F) (branchingSet F)) := le_trans hnodes (Nat.add_le_add_right (Nat.sub_le _ _) _)
    exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_left hcount (show (0:ℝ)≤2*n by positivity)
  change _≤(4+2*n)*Real.exp ((Real.log 2-α)*n)
  nlinarith

theorem dense_gap_nodes (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ)
    (hF : Simple F) (h : DenseGap F S ε η) (hn : 0 < n) :
    (Hybrid.nodeCount (preprocess F).1 (initialPreference (preprocess F).1)
      (branchingSet (preprocess F).1) : ℝ) ≤
      (4+2*n)*Real.exp ((Real.log 2-(ε*η)^2/8192)*n) := by
  have hθ0 : 0 < ε*η := mul_pos h.epsilon_pos h.eta_pos
  have hθ1 : ε*η ≤ 1 := by
    simpa using mul_le_mul h.epsilon_le h.eta_le h.eta_pos.le (by norm_num : (0:ℝ) ≤ 1)
  apply nodes_of_probability _ _ (by nlinarith)
  convert dense_gap_probability F S ε η hF h hn using 1
  congr 1
  ring

theorem dense_gap_paper_bound (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ)
    (hF : Simple F) (h : DenseGap F S ε η) (hn : 0 < n) :
    (Hybrid.nodeCount (preprocess F).1 (initialPreference (preprocess F).1)
      (branchingSet (preprocess F).1) : ℝ) ≤
      (4+2*n)*(2:ℝ)^((1-(ε*η)^2/48000)*n) := by
  apply le_trans (dense_gap_nodes F S ε η hF h hn)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hg0 : 0 ≤ (ε*η)^2/48000 := by positivity
  have hga : (ε*η)^2/48000 ≤ (ε*η)^2/8192 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hl hg0
  have he : Real.log 2-(ε*η)^2/8192 ≤ Real.log 2*(1-(ε*η)^2/48000) := by nlinarith
  have hn0 : (0:ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hn0]

theorem dense_gap_base_lt_two (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    (2:ℝ)^(1-(ε*η)^2/48000) < 2 := by
  have hh := exponential_base_lt_two ε η 16 hε hη (by norm_num)
  norm_num at hh
  exact hh

/-- Original simple-input hypotheses, optimality for that original formula,
and the paper's explicit recursion-node bound. No structural or probability
hypothesis on the reduced formula is left unproved. -/
theorem dense_gap_preprocessed (F : Formula n) (S : Finset (Fin n)) (ε η : ℝ)
    (hF : Simple F) (h : DenseGap F S ε η) (hn : 0 < n) :
    (∃ x, solveBiasPreprocessed F=some x ∧ ∀ y, score F y ≤ score F x) ∧
    (Hybrid.nodeCount (preprocess F).1 (initialPreference (preprocess F).1)
      (branchingSet (preprocess F).1) : ℝ) ≤
      (4+2*n)*(2:ℝ)^((1-(ε*η)^2/48000)*n) :=
  ⟨solveBiasPreprocessed_correct F hF.1, dense_gap_paper_bound F S ε η hF h hn⟩

end
end Max2SAT.Bias
