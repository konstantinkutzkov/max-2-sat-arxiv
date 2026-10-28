import Max2SAT.Regular.Algorithm

namespace Max2SAT.Regular
noncomputable section

def countBase (L ε : ℝ) : ℝ :=
  Counts.exponentialBase (1/2) (Counts.roundRate 2 (1/2) (gapConstant ε) (normConstant L ε))
def familyBase (L ε : ℝ) (D : ℕ) : ℝ := max (degreeBase D) (countBase L ε)

theorem family_base_bounds (L ε : ℝ) (D : ℕ) (hL : 1≤L) (he : 0<ε) :
    1≤familyBase L ε D ∧ familyBase L ε D<2 := by
  have hc : countBase L ε<2 := Counts.exponential_base_lt_two _ _ (by norm_num)
    (Counts.round_rate_pos 2 (by omega) (1/2) (gapConstant ε) (normConstant L ε)
      (by norm_num) (gap_constant_pos he) (norm_constant_pos hL he))
  exact ⟨(degree_base_bounds D).1.trans (le_max_left _ _),
    max_lt (degree_base_bounds D).2 hc⟩

theorem family_thresholds (L ε : ℝ) (he : 0<ε) :
    ∃ D N : ℕ, 64*L^2≤(D:ℝ) ∧ 80≤N ∧ 2≤ε*N ∧
      128≤(gapConstant ε)^2*ε*N := by
  obtain ⟨D,hD⟩ := exists_nat_gt (64*L^2)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 80 (max (2/ε) (128/((gapConstant ε)^2*ε))))
  have h80 : (80:ℝ)≤N := (le_max_left _ _).trans hN.le
  have heN : 2/ε≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN.le)
  have hgN : 128/((gapConstant ε)^2*ε)≤(N:ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN.le)
  refine ⟨D,N,hD.le,by exact_mod_cast h80,?_,?_⟩
  · nlinarith [(div_le_iff₀ he).mp heN]
  · have hp : 0<(gapConstant ε)^2*ε := mul_pos (sq_pos_of_pos (gap_constant_pos he)) he
    nlinarith [(div_le_iff₀ hp).mp hgN]

theorem regular_nodes_bound {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (units : List (Literal n)) (hreg : G.IsRegularOfDegree d)
    (L ε : ℝ) (hL : 1≤L) (he : 0<ε) (he1 : ε≤1/2)
    (D N : ℕ) (hD : 64*L^2≤(D:ℝ)) (hN : 80≤N) (hsize : 2≤ε*N)
    (hlarge : 128≤(gapConstant ε)^2*ε*N)
    (hdensity : (d:ℝ)≤(1-ε)*n) (hspec : n≤1 ∨ EigenBound G d (L*Real.sqrt d)) :
    (regularNodes G units D N:ℝ)≤(2:ℝ)^(N+1)*(n+1)*(2+14*n)*(familyBase L ε D)^n := by
  have hb := family_base_bounds L ε D hL he
  have hpow : 1≤(familyBase L ε D)^n := one_le_pow₀ hb.1
  have hC : 1≤(2:ℝ)^(N+1) := one_le_pow₀ (by norm_num)
  have hp : (2:ℝ)≤(n+1)*(2+14*n) := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  by_cases hn:n<N
  · simp only [regularNodes,hn,↓reduceIte,independent_nodes_exact,Finset.card_empty,Nat.sub_zero]
    have hnat : 2^(n+1)-1≤2^(N+1) := (Nat.sub_le _ _).trans
      (Nat.pow_le_pow_right (by omega : 0<2) (by omega))
    have hc : ((2^(n+1)-1:ℕ):ℝ)≤(2:ℝ)^(N+1) := by exact_mod_cast hnat
    have h1 := mul_le_mul_of_nonneg_left hp (pow_nonneg (by norm_num : (0:ℝ)≤2) (N+1))
    have h2 := mul_le_mul_of_nonneg_left hpow
      (show (0:ℝ)≤2^(N+1)*(n+1)*(2+14*n) by positivity)
    nlinarith
  · have hNn : N≤n := by omega
    have hNn' : (N:ℝ)≤n := by exact_mod_cast hNn
    have hn80 : 80≤n := hN.trans hNn
    have hi := input_degree_regular G d hreg (by omega)
    simp only [regularNodes,hn,↓reduceIte,hi]
    by_cases hd:d<D
    · simp only [hd,↓reduceIte]
      have hlow := (bounded_degree_nodes G D (fun v => (hreg v).le.trans (by omega))).1
      have hbase : (degreeBase D)^n≤(familyBase L ε D)^n :=
        pow_le_pow_left₀ (by linarith [(degree_base_bounds D).1]) (le_max_left _ _) n
      have h1 := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤2^(N+1) by positivity)
      have h2 : (2:ℝ)≤2^(N+1)*(n+1)*(2+14*n) := by nlinarith
      calc
        _≤2*(degreeBase D)^n := hlow
        _≤2*(familyBase L ε D)^n := by gcongr
        _≤_ := mul_le_mul_of_nonneg_right h2 (by positivity)
    · simp only [hd,↓reduceIte]
      have hdegree : 64*L^2≤(d:ℝ) := hD.trans (by exact_mod_cast (show D≤d by omega))
      have hsize' : 2≤ε*n := hsize.trans (mul_le_mul_of_nonneg_left hNn' he.le)
      have hlarge' : 128≤(gapConstant ε)^2*ε*n := hlarge.trans
        (mul_le_mul_of_nonneg_left hNn' (mul_nonneg (sq_nonneg _) he.le))
      have hs := hspec.resolve_left (by omega)
      have hhigh := (high_degree_nodes G units hreg L ε hL he he1 hn80 hsize' hdensity
        hdegree hlarge' hs).1
      have hbase : (countBase L ε)^n≤(familyBase L ε D)^n :=
        pow_le_pow_left₀ (Real.exp_pos _).le (le_max_right _ _) n
      calc
        _≤(n+1)*(2+14*n)*(countBase L ε)^n := hhigh
        _≤(n+1)*(2+14*n)*(familyBase L ε D)^n := by gcongr
        _≤_ := by
          have h := mul_le_mul_of_nonneg_right hC
            (show (0:ℝ)≤(n+1)*(2+14*n)*(familyBase L ε D)^n by positivity)
          simpa only [one_mul,mul_assoc] using h

/-- Corollary cor:maxcut at the explicit recursive-call level. The integer
cutoffs and the base are chosen once for the family, independently of n,
the graph, and the unit clauses. Small graphs are included. -/
theorem regular_family_nodes (L ε : ℝ) (hL : 1≤L) (he : 0<ε) (he1 : ε≤1/2) :
    ∃ D N : ℕ, ∃ c C : ℝ, 1≤c ∧ c<2 ∧ 0<C ∧
      ∀ (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (units : List (Literal n)), G.IsRegularOfDegree d →
        (d:ℝ)≤(1-ε)*n → (n≤1 ∨ EigenBound G d (L*Real.sqrt d)) →
        (regularNodes G units D N:ℝ)≤C*(n+1)*(2+14*n)*c^n := by
  obtain ⟨D,N,hD,hN,hsize,hlarge⟩ := family_thresholds L ε he
  have hb := family_base_bounds L ε D hL he
  refine ⟨D,N,familyBase L ε D,2^(N+1),hb.1,hb.2,by positivity,?_⟩
  intro n d G _ units hreg hdensity hspec
  exact regular_nodes_bound G units hreg L ε hL he he1 D N hD hN hsize hlarge hdensity hspec

end
end Max2SAT.Regular
