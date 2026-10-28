import Max2SAT.Bias.Accumulation

/-! A computable choice of at most half the variables (rounded up) carrying
at least half the total initial gap. It uses only two fixed halves. -/
namespace Max2SAT.Bias

def lowHalf (n : ℕ) : Finset (Fin n) := ((List.finRange n).take (n/2)).toFinset

theorem card_lowHalf (n : ℕ) : (lowHalf n).card=n/2 := by
  rw [lowHalf,List.toFinset_card_of_nodup ((List.nodup_finRange n).take)]
  simp [List.length_take,Nat.div_le_self]

def gapMass (F : Formula n) (P : Finset (Fin n)) : ℤ := ∑ i∈P, |gap F i|

def branchingSet (F : Formula n) : Finset (Fin n) :=
  if gapMass F (lowHalf n) ≤ gapMass F (lowHalf n)ᶜ then (lowHalf n)ᶜ else lowHalf n

theorem branchingSet_card (F : Formula n) : (branchingSet F).card≤(n+1)/2 := by
  have hh := card_lowHalf n
  have hc : (lowHalf n)ᶜ.card=n-(lowHalf n).card := by simpa using Finset.card_compl (lowHalf n)
  unfold branchingSet
  split <;> omega

theorem branchingSet_mass (F : Formula n) :
    gapMass F Finset.univ≤2*gapMass F (branchingSet F) := by
  have he : gapMass F (lowHalf n)+gapMass F (lowHalf n)ᶜ=gapMass F Finset.univ := by
    exact Finset.sum_add_sum_compl _ _
  unfold branchingSet
  split <;> omega

theorem gapMass_real (F : Formula n) (P : Finset (Fin n)) :
    (gapMass F P : ℝ)=∑ i∈P, |(gap F i : ℝ)| := by
  simp [gapMass,Int.cast_sum,Int.cast_abs]

/-- The paper's relative-bias and degree-square assumptions. The average degree
d is defined by the equality on S, rather than left implicit. -/
structure RelativeBias (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ) : Prop where
  epsilon_pos : 0<ε
  epsilon_le : ε≤1
  eta_pos : 0<η
  eta_le : η≤1
  R_ge : 1≤R
  d_ge : 1≤d
  size : η*n≤S.card
  mean_degree : (∑ i∈S, (D F i : ℝ))=S.card*d
  bias : ∀ i∈S, ε*(D F i : ℝ)≤|(gap F i : ℝ)|
  squares : (∑ i : Fin n, (B F i : ℝ)^2)≤R*n*d^2

theorem total_gap_lower (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (h : RelativeBias F S ε η R d) : ε*η*n*d≤(gapMass F Finset.univ : ℝ) := by
  have hsum := Finset.sum_le_sum h.bias
  rw [←Finset.mul_sum,h.mean_degree] at hsum
  have hs : (∑ i∈S, |(gap F i : ℝ)|)≤∑ i : Fin n, |(gap F i : ℝ)| :=
    Finset.sum_le_univ_sum_of_nonneg (fun i => abs_nonneg _)
  have hp := mul_le_mul_of_nonneg_left h.size (mul_nonneg h.epsilon_pos.le (show 0≤d by linarith [h.d_ge]))
  rw [gapMass_real]
  nlinarith

theorem selected_gap_lower (F : Formula n) (S : Finset (Fin n)) (ε η R d : ℝ)
    (h : RelativeBias F S ε η R d) :
    ε*η*n*d/2≤∑ i∈branchingSet F, |(gap F i : ℝ)| := by
  have hm : (gapMass F Finset.univ : ℝ)≤2*(gapMass F (branchingSet F) : ℝ) := by
    exact_mod_cast branchingSet_mass F
  simp only [gapMass_real] at hm
  have hg := total_gap_lower F S ε η R d h
  rw [gapMass_real] at hg
  linarith

end Max2SAT.Bias
