import Max2SAT.Community.Spacing
import Mathlib.Data.Nat.Sqrt

/-! A computable factor-two lower approximation to a positive rational
square root. Only an integer square root and rational division are needed. -/
namespace Max2SAT.Community

def rootBelow (q : ℚ) : ℚ := (Nat.sqrt (q.num.toNat*q.den):ℚ)/q.den

theorem root_below_positive (q : ℚ) (hq : 0<q) : 0<rootBelow q := by
  have hn : 0<q.num := Rat.num_pos.mpr hq
  have hnN : 0<q.num.toNat := by omega
  unfold rootBelow
  exact div_pos (by exact_mod_cast Nat.sqrt_pos.mpr (Nat.mul_pos hnN q.den_pos))
    (by exact_mod_cast q.den_pos)

theorem root_below_square_bounds (q : ℚ) (hq : 0<q) :
    (rootBelow q)^2≤q ∧ q≤4*(rootBelow q)^2 := by
  have hn : 0<q.num := Rat.num_pos.mpr hq
  have hnN : 0<q.num.toNat := by omega
  have hd : (0:ℚ)<q.den := by exact_mod_cast q.den_pos
  have hrepr : (q.num.toNat:ℚ)=q*q.den := by
    have he := q.num_div_den
    have hncast : (q.num.toNat:ℚ)=(q.num:ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn.le
    rw [hncast]
    exact (div_eq_iff (ne_of_gt hd)).mp he
  have hlo : ((Nat.sqrt (q.num.toNat*q.den):ℕ):ℚ)^2≤q.num.toNat*q.den := by
    exact_mod_cast Nat.sqrt_le' (q.num.toNat*q.den)
  have hhi : (q.num.toNat:ℚ)*q.den<((Nat.sqrt (q.num.toNat*q.den):ℕ)+1:ℚ)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (q.num.toNat*q.den)
  have hsp : (1:ℚ)≤Nat.sqrt (q.num.toNat*q.den) := by
    exact_mod_cast Nat.sqrt_pos.mpr (Nat.mul_pos hnN q.den_pos)
  rw [hrepr] at hlo hhi
  unfold rootBelow
  rw [div_pow]
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  · have hh : q*q.den^2≤4*((Nat.sqrt (q.num.toNat*q.den):ℕ):ℚ)^2 := by nlinarith
    rw [←mul_div_assoc]
    exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr hh

theorem root_below_real_bounds (q : ℚ) (hq : 0<q) :
    Real.sqrt (q:ℝ)/2≤(rootBelow q:ℝ) ∧ (rootBelow q:ℝ)≤Real.sqrt (q:ℝ) := by
  have h := root_below_square_bounds q hq
  have hlo : (rootBelow q:ℝ)^2≤(q:ℝ) := by exact_mod_cast h.1
  have hhi : (q:ℝ)≤4*(rootBelow q:ℝ)^2 := by exact_mod_cast h.2
  have hp : (0:ℝ)<rootBelow q := by exact_mod_cast root_below_positive q hq
  have hq0 : (0:ℝ)≤q := by exact_mod_cast hq.le
  constructor
  · have hh : Real.sqrt (q:ℝ)≤2*(rootBelow q:ℝ) := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
    linarith
  · exact Real.le_sqrt_of_sq_le hlo

def computedSpacing (n : ℕ) (g D Λ : ℚ) : ℚ := rootBelow (g^2*(n:ℚ)*D/(64*Λ)^2)

theorem computed_spacing_bounds (n : ℕ) (g D Λ : ℚ)
    (hn : 0<n) (hg : 0<g) (hD : 0<D) (hΛ : 0<Λ) :
    (g:ℝ)*Real.sqrt (n*(D:ℝ))/(128*(Λ:ℝ))≤(computedSpacing n g D Λ:ℝ) ∧
      (computedSpacing n g D Λ:ℝ)≤(g:ℝ)*Real.sqrt (n*(D:ℝ))/(64*(Λ:ℝ)) := by
  have hnQ : (0:ℚ)<n := by exact_mod_cast hn
  have hq : 0<g^2*(n:ℚ)*D/(64*Λ)^2 := by positivity
  have hgR : (0:ℝ)<g := by exact_mod_cast hg
  have hDR : (0:ℝ)<D := by exact_mod_cast hD
  have hΛR : (0:ℝ)<Λ := by exact_mod_cast hΛ
  have h := root_below_real_bounds _ hq
  have hid : Real.sqrt ((g^2*(n:ℚ)*D/(64*Λ)^2:ℚ):ℝ)=
      (g:ℝ)*Real.sqrt (n*(D:ℝ))/(64*(Λ:ℝ)) := by
    push_cast
    rw [Real.sqrt_div (by positivity),Real.sqrt_sq (by positivity : (0:ℝ)≤64*(Λ:ℝ))]
    rw [show (g:ℝ)^2*n*(D:ℝ)=(g:ℝ)^2*(n*(D:ℝ)) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hgR.le]
  rw [hid] at h
  unfold computedSpacing
  constructor
  · convert h.1 using 1
    ring
  · exact h.2

end Max2SAT.Community
