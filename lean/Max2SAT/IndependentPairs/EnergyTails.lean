import Max2SAT.IndependentPairs.RowTails

/-! Total squared interaction under the independent-pair law, and the
exact deterministic loss from empirical centering. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
variable {n : ℕ} {α : Type*} [Fintype α]

theorem pair_count_positive (hn : 2≤n) : 0<Fintype.card (Edge n) := by
  have h := pair_count (n:=n)
  have : 0<n*(n-1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem energy_scale (hn : 2≤n) :
    (2/(n:ℝ))*(Fintype.card (Edge n):ℝ)=(n:ℝ)-1 := by
  have h := pair_count_real (show 1≤n by omega)
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  field_simp
  nlinarith

theorem raw_energy_tails (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (hn : 2≤n) (B ν χ η : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hη : 0<η) (hη2 : η≤2)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (product p) (fun x =>
      pairEnergy (fun e => X e (x e))<(1-η)*((n:ℝ)-1)*ν ∨
      (1+η)*((n:ℝ)-1)*χ*ν<pairEnergy (fun e => X e (x e)))≤
      Real.exp (-η^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ))+
      Real.exp (-η^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2)) := by
  let m : ℝ := Fintype.card (Edge n)
  have hm : 0<m := by dsimp [m]; exact_mod_cast pair_count_positive hn
  have hmM : m*ν≤m*χ*ν := by nlinarith [mul_nonneg (mul_nonneg hm.le hν.le) (sub_nonneg.mpr hχ)]
  have hlo : m*ν≤∑ e, expect (p e) (fun x => (X e x)^2) := by
    simpa [m] using Finset.sum_le_sum (fun e (_ : e∈Finset.univ) => (hv e).1)
  have hhi : (∑ e, expect (p e) (fun x => (X e x)^2))≤m*χ*ν := by
    simpa [m,mul_assoc] using Finset.sum_le_sum (fun e (_ : e∈Finset.univ) => (hv e).2)
  have hlow := squares_lower_tail p X B (m*ν) (m*χ*ν) η hB (mul_pos hm hν) hmM hη hη2 hb hlo hhi
  have hupp := squares_upper_tail p X B (m*χ*ν) η hB (by positivity) hη hη2 hb hhi
  have hχ0 : χ≠0 := by linarith
  have hlrate : -(η*(m*ν))^2/(4*B^2*(m*χ*ν))= -η^2*m*ν/(4*B^2*χ) := by
    field_simp
  have hurate : -(η*(m*χ*ν))^2/(4*B^2*(m*χ*ν))= -η^2*m*χ*ν/(4*B^2) := by
    field_simp
  rw [hlrate] at hlow
  rw [hurate] at hupp
  apply (prob_mono_support (product p) _ _ ?_).trans
    ((prob_union_le (product p) _ _).trans (add_le_add hlow hupp))
  intro x _ hx
  have hk : 0<2/(n:ℝ) := by
    have : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    positivity
  have he : pairEnergy (fun e => X e (x e))=(2/(n:ℝ))*(∑ e, (X e (x e))^2) := by
    rw [pair_energy_formula]; ring
  have hs : (2/(n:ℝ))*m=(n:ℝ)-1 := energy_scale hn
  rcases hx with hx|hx
  · left
    rw [he,←hs] at hx
    nlinarith
  · right
    rw [he,←hs] at hx
    nlinarith

/-- On the two good scalar events, the paper's lower and upper bounds on
D_N hold for the actual empirically centered symmetric matrix. -/
theorem empirical_energy_bounds (z : Edge n → ℝ) (hn : 2≤n)
    (ν χ : ℝ) (hν : 0≤ν)
    (hraw : (99/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy z ∧
      pairEnergy z≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν)
    (hmean : |empiricalMean z|≤(1/1000:ℝ)*Real.sqrt ν) :
    (98/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy (fun e => z e-empiricalMean z) ∧
      pairEnergy (fun e => z e-empiricalMean z)≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν := by
  have : Nonempty (Edge n) := Fintype.card_pos_iff.mp (pair_count_positive hn)
  rw [empirical_pair_energy z (by omega)]
  have hn' : 0≤(n:ℝ)-1 := by exact_mod_cast (show 0≤(n:ℤ)-1 by omega)
  have hsq : (empiricalMean z)^2≤(1/1000000:ℝ)*ν := by
    have h := mul_self_le_mul_self (abs_nonneg _) hmean
    rw [←sq,←sq,sq_abs,mul_pow,Real.sq_sqrt hν] at h
    norm_num at h ⊢
    exact h
  constructor
  · have h := mul_le_mul_of_nonneg_left hsq hn'
    have hpos := mul_nonneg hn' hν
    nlinarith [hraw.1]
  · have h := mul_nonneg hn' (sq_nonneg (empiricalMean z))
    linarith [hraw.2]

end
end Max2SAT.IndependentPairs
