import Max2SAT.Bias.Counting
import Max2SAT.Preprocess
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exponential node bounds for a paper's fully specified deterministic
algorithm. The probability space is only a counting device. -/
namespace Max2SAT.Bias
open FairCoin
noncomputable section

theorem variance_positive (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (h : RelativeBias F S ε η R d) (hn : 0<n) :
    0<∑ i : Fin n, (2*(B F i : ℝ))^2 := by
  by_contra hv
  have hv' : (∑ i : Fin n, (2*(B F i : ℝ))^2)≤0 := le_of_not_gt hv
  have hz : ∀ i, (D F i : ℝ)=0 := by
    intro i
    have hi : (2*(B F i : ℝ))^2≤∑ j : Fin n, (2*(B F j : ℝ))^2 :=
      Finset.single_le_sum (f := fun j => (2*(B F j : ℝ))^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hB : (B F i : ℝ)=0 := by nlinarith
    simp only [B,Nat.cast_add] at hB
    have hU : (0:ℝ)≤U F i := by positivity
    have hD : (0:ℝ)≤D F i := by positivity
    linarith
  have hs : (∑ i∈S, (D F i : ℝ))=0 := by simp [hz]
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hsc : (0:ℝ)<S.card := lt_of_lt_of_le (mul_pos h.eta_pos hn') h.size
  have hp := mul_pos hsc (show 0<d by linarith [h.d_ge])
  rw [h.mean_degree] at hs
  linarith

/-- Exponentially few assignments satisfy the actual summed cuts. -/
theorem relative_bias_probability (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (hF : wellFormed F) (h : RelativeBias F S ε η R d) (hn : 0<n) :
    probability n (admissible F (initialPreference F) (branchingSet F))≤
      Real.exp (-(ε*η)^2*n/(512*R)) := by
  let V := ∑ i : Fin n, (2*(B F i : ℝ))^2
  let a := (∑ i∈branchingSet F, |(gap F i : ℝ)|)/4
  have hv : 0<V := variance_positive F S ε η R d h hn
  have hV : V≤4*R*n*d^2 := by
    have he : V=4*(∑ i : Fin n, (B F i : ℝ)^2) := by
      simp only [V,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    nlinarith [h.squares]
  have ha : ε*η*n*d/8≤a := by
    dsimp [a]
    linarith [selected_gap_lower F S ε η R d h]
  have hp := admissible_probability F (branchingSet F) hF hv
  apply le_trans hp
  apply Real.exp_le_exp.mpr
  have hR : 0<R := by linarith [h.R_ge]
  have hd : 0<d := by linarith [h.d_ge]
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h0 : 0≤ε*η*n*d/8 := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h.epsilon_pos.le h.eta_pos.le) hn'.le) hd.le) (by norm_num)
  have hs : (ε*η*n*d/8)^2≤a^2 := by nlinarith
  have he : (ε*η*n*d/8)^2/(8*R*n*d^2)=(ε*η)^2*n/(512*R) := by
    field_simp; ring
  have he' : (ε*η)^2*n/(512*R)≤a^2/(2*V) := calc
    _ = (ε*η*n*d/8)^2/(8*R*n*d^2) := he.symm
    _ ≤ a^2/(8*R*n*d^2) := div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ a^2/(2*V) := div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) (by linarith)
  change -a^2/(2*V)≤-(ε*η)^2*n/(512*R)
  simpa only [neg_div,neg_mul] using neg_le_neg he'

/-- A uniform exponential node bound. No probability or cost assumption is
left as a hypothesis: both are instantiated with the executable solver. -/
theorem relative_bias_nodes (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (hF : wellFormed F) (h : RelativeBias F S ε η R d) (hn : 0<n) :
    (Hybrid.nodeCount F (initialPreference F) (branchingSet F) : ℝ)≤
      (4+2*n)*Real.exp ((Real.log 2-(ε*η)^2/(512*R))*n) := by
  let α := (ε*η)^2/(512*R)
  have hR : 0<R := by linarith [h.R_ge]
  have hθ0 : 0<ε*η := mul_pos h.epsilon_pos h.eta_pos
  have hθ1 : ε*η≤1 := by simpa using mul_le_mul h.epsilon_le h.eta_le h.eta_pos.le (by norm_num : (0:ℝ)≤1)
  have hα0 : 0≤α := by positivity
  have hα1 : α≤1/512 := by
    dsimp [α]
    apply (div_le_iff₀ (by positivity : 0<512*R)).mpr
    nlinarith [h.R_ge]
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
  have hp := relative_bias_probability F S ε η R d hF h hn
  rw [probability_eq_count] at hp
  have hcount := (div_le_iff₀ (by positivity : (0:ℝ)<2^n)).mp hp
  have he : Real.exp (-(ε*η)^2*n/(512*R))*(2:ℝ)^n=
      Real.exp ((Real.log 2-α)*n) := by
    rw [htwo,←Real.exp_nat_mul,←Real.exp_add]
    simp only [Real.log_exp]
    congr 1; dsimp [α]; ring
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


/-- The more conservative exponent used in the manuscript follows from the
stronger finite bound above. -/
theorem relative_bias_paper_bound (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (hF : wellFormed F) (h : RelativeBias F S ε η R d) (hn : 0<n) :
    (Hybrid.nodeCount F (initialPreference F) (branchingSet F) : ℝ)≤
      (4+2*n)*(2:ℝ)^((1-(ε*η)^2/(3000*R))*n) := by
  apply le_trans (relative_bias_nodes F S ε η R d hF h hn)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  apply Real.exp_le_exp.mpr
  have hR : 0<R := by linarith [h.R_ge]
  have hg0 : 0≤(ε*η)^2/(3000*R) := by positivity
  have hga : (ε*η)^2/(3000*R)≤(ε*η)^2/(512*R) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have hl : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hl hg0
  have he : Real.log 2-(ε*η)^2/(512*R)≤Real.log 2*(1-(ε*η)^2/(3000*R)) := by nlinarith
  have hn0 : (0:ℝ)≤n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hn0]

theorem exponential_base_lt_two (ε η R : ℝ) (hε : 0<ε) (hη : 0<η) (hR : 0<R) :
    (2:ℝ)^(1-(ε*η)^2/(3000*R))<2 := by
  have hg : 0<(ε*η)^2/(3000*R) := by positivity
  have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    (show 1-(ε*η)^2/(3000*R)<1 by linarith)
  simpa using hh

end

/-- This deterministic solver requires only the formula. Its preferences and
branching set are computed from the original degrees and gaps. -/
def solveBias (F : Formula n) : Option (Assignment n) :=
  Hybrid.solve F (initialPreference F) (branchingSet F)

theorem solveBias_correct (F : Formula n) (hF : wellFormed F) :
    ∃ x, solveBias F=some x ∧ ∀ y, score F y≤score F x :=
  Hybrid.solve_correct F _ _ hF

/-- Preprocessing is the already verified score-preserving procedure. -/
def solveBiasPreprocessed (F : Formula n) : Option (Assignment n) :=
  solveBias (preprocess F).1

theorem solveBiasPreprocessed_correct (F : Formula n) (hF : wellFormed F) :
    ∃ x, solveBiasPreprocessed F=some x ∧ ∀ y, score F y≤score F x := by
  rcases solveBias_correct (preprocess F).1 (preprocess_finished F hF).1 with ⟨x,hx,ho⟩
  refine ⟨x,hx,?_⟩
  intro y
  rw [preprocess_correct F y,preprocess_correct F x]
  exact add_le_add (le_refl _) (ho y)

/-- End-to-end statement for the manuscript's postpreprocessing hypotheses.
The counted search is exactly the search called by solveBiasPreprocessed. -/
theorem relative_bias_preprocessed (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (hF : wellFormed F) (h : RelativeBias (preprocess F).1 S ε η R d) (hn : 0<n) :
    (∃ x, solveBiasPreprocessed F=some x ∧ ∀ y, score F y≤score F x) ∧
    (Hybrid.nodeCount (preprocess F).1 (initialPreference (preprocess F).1)
      (branchingSet (preprocess F).1) : ℝ)≤
        (4+2*n)*(2:ℝ)^((1-(ε*η)^2/(3000*R))*n) :=
  ⟨solveBiasPreprocessed_correct F hF,
    relative_bias_paper_bound (preprocess F).1 S ε η R d (preprocess_finished F hF).1 h hn⟩

end Max2SAT.Bias
