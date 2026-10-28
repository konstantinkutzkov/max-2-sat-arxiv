import Max2SAT.Counts.GridPrograms

/-! The lower cap on the projection spacing: coverage and polynomial grid
size on arbitrary inputs, and inactivity on the useful random-input event. -/
namespace Max2SAT.Community
open Counts
variable {n r : ℕ}

def cappedSpacing (n : ℕ) (δ : ℚ) : ℚ := max δ (1/(n:ℚ)^2)

theorem capped_spacing_pos (δ : ℚ) (hn : 0<n) : 0<cappedSpacing n δ := by
  have hn' : (0:ℚ)<n := by exact_mod_cast hn
  exact (by positivity : (0:ℚ)<1/(n:ℚ)^2).trans_le (le_max_right _ _)

theorem capped_spacing_cover (v : Fin r → Fin n → ℚ) (δ : ℚ) (hn : 0<n) :
    Covers (projectionGrids v (fun _ => cappedSpacing n δ)) v (fun _ => cappedSpacing n δ) :=
  projection_grids_cover v _ (fun _ => capped_spacing_pos δ hn)

theorem capped_grid_size (v : Fin r → Fin n → ℚ) (δ : ℚ) (hn : 1≤n)
    (hv : ∀ k, ∑ t, (v k t:ℝ)^2≤1) :
    ((projectionGrids v (fun _ => cappedSpacing n δ)).length:ℝ)≤(2*(n:ℝ)^3+3)^r := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hδ := capped_spacing_pos δ (by omega : 0<n)
  have hδ' : (0:ℝ)<cappedSpacing n δ := by exact_mod_cast hδ
  have hcap : 1/(n:ℝ)^2≤(cappedSpacing n δ:ℝ) := by
    have hh : (1:ℚ)/(n:ℚ)^2≤cappedSpacing n δ := le_max_right _ _
    have hc : ((1/(n:ℚ)^2:ℚ):ℝ)≤(cappedSpacing n δ:ℝ) := Rat.cast_le.mpr hh
    push_cast at hc
    exact hc
  have hroot : Real.sqrt n≤n := by
    apply (Real.sqrt_le_left hn0.le).mpr
    nlinarith
  have hc := projection_grid_card_bound v _ hδ hv
  apply hc.trans
  apply pow_le_pow_left₀ (by positivity)
  have hden := (div_le_iff₀ (sq_pos_of_pos hn0)).mp hcap
  have hh := mul_le_mul_of_nonneg_left hden hn0.le
  have hquot : 2*Real.sqrt n/(cappedSpacing n δ:ℝ)≤2*(n:ℝ)^3 := by
    apply (div_le_iff₀ hδ').mpr
    nlinarith
  linarith

/-- The statistical allowance bound makes the lower cap inactive. -/
theorem capped_spacing_inactive (δ : ℚ) (hn : 2≤n)
    (hδ : 1/(2*Real.sqrt n)≤(δ:ℝ)) : cappedSpacing n δ=δ := by
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hs : Real.sqrt n≤n := (Real.sqrt_le_left hn0.le).mpr (by nlinarith)
  have hlow : 1/(n:ℝ)^2≤1/(2*Real.sqrt n) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hh : (1/(n:ℚ)^2)≤δ := by
    apply (Rat.cast_le (K:=ℝ)).mp
    push_cast
    exact hlow.trans hδ
  exact max_eq_left hh

/-- Any factor-two approximation to the desired spacing suffices. -/
theorem spacing_from_allowance (n : ℕ) (g D Λ δ : ℝ)
    (hn : 0<n) (_hg : 0<g) (_hD : 0<D) (hΛ : 0<Λ)
    (hbudget : Λ≤g*n*Real.sqrt D/64)
    (hδ : g*Real.sqrt (n*D)/(128*Λ)≤δ) : 1/(2*Real.sqrt n)≤δ := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hsn := Real.sq_sqrt hn0.le
  have hmul := mul_le_mul_of_nonneg_left hbudget (show 0≤2*Real.sqrt n by positivity)
  apply le_trans _ hδ
  apply (div_le_div_iff₀ (by positivity : 0<2*Real.sqrt n) (by positivity : 0<128*Λ)).mpr
  rw [Real.sqrt_mul hn0.le]
  nlinarith

/-- The total comparison allowance after choosing the spacing. -/
theorem spacing_allowance (n : ℕ) (g D Λ δ : ℝ)
    (_hg : 0≤g) (_hD : 0≤D) (hΛ : 0<Λ)
    (hbudget : Λ≤g*n*Real.sqrt D/64)
    (hδ : δ≤g*Real.sqrt (n*D)/(64*Λ)) :
    Λ*(δ*Real.sqrt n+1)≤g*n*Real.sqrt D/32 := by
  have hn0 : 0≤(n:ℝ) := by positivity
  have hsn := Real.sq_sqrt hn0
  have hδ' := (le_div_iff₀ (show 0<64*Λ by positivity)).mp hδ
  rw [Real.sqrt_mul hn0] at hδ'
  have hm := mul_le_mul_of_nonneg_right hδ' (Real.sqrt_nonneg (n:ℝ))
  have hid : g*(Real.sqrt n*Real.sqrt D)*Real.sqrt n=g*n*Real.sqrt D := by
    calc
      _ = g*(Real.sqrt n)^2*Real.sqrt D := by ring
      _ = _ := by rw [hsn]
  rw [hid] at hm
  nlinarith

/-- On the useful event there are at most (4n+3)^r grid runs. -/
theorem useful_grid_size (v : Fin r → Fin n → ℚ) (δ : ℚ) (hn : 2≤n)
    (hv : ∀ k, ∑ t, (v k t:ℝ)^2≤1)
    (hδ : 1/(2*Real.sqrt n)≤(δ:ℝ)) :
    ((projectionGrids v (fun _ => cappedSpacing n δ)).length:ℝ)≤(4*(n:ℝ)+3)^r := by
  rw [capped_spacing_inactive δ hn hδ]
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hδ' : (0:ℝ)<δ := (by positivity : (0:ℝ)<1/(2*Real.sqrt n)).trans_le hδ
  have hc := projection_grid_card_bound v δ (by exact_mod_cast hδ') hv
  apply hc.trans
  apply pow_le_pow_left₀ (by positivity)
  have hm := (div_le_iff₀ (show 0<2*Real.sqrt n by positivity)).mp hδ
  have hh := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg (n:ℝ))
  have hs := Real.sq_sqrt hn0.le
  have hq : 2*Real.sqrt n/(δ:ℝ)≤4*n := by
    apply (div_le_iff₀ hδ').mpr
    nlinarith
  linarith

end Max2SAT.Community
