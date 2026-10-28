import Max2SAT.Regular.Centering
import Max2SAT.Regular.Profile

namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {n d : ℕ}

def gapConstant (ε : ℝ) : ℝ := ε/(320*Real.sqrt 3)
def normConstant (L ε : ℝ) : ℝ := 9*L^2/(2*ε)

theorem gap_constant_pos {ε : ℝ} (he : 0<ε) : 0<gapConstant ε := by
  unfold gapConstant; positivity

theorem norm_constant_pos {L ε : ℝ} (hL : 1≤L) (he : 0<ε) : 0<normConstant L ε := by
  unfold normConstant
  have : 0<L := by linarith
  positivity

theorem large_degree_scale (L : ℝ) (hL : 1≤L) (hd : 64*L^2≤(d:ℝ)) :
    2≤L*Real.sqrt d ∧ L*Real.sqrt d≤(d:ℝ)/8 := by
  have hD : (64:ℝ)≤d := by nlinarith
  have hs : (8:ℝ)≤Real.sqrt d := (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) d)
  constructor
  · nlinarith
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,hsq,div_pow]
    have h := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (α:=ℝ) d)
    nlinarith

theorem regular_norm_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 2≤n) (hdn : d≤n-1) (ε L : ℝ) (he : 0<ε) (he1 : ε≤1)
    (hL : 1≤L) (hsize : 2≤ε*n) (hdensity : (d:ℝ)≤(1-ε)*n)
    (hdegree : 64*L^2≤(d:ℝ)) (hcenter : ‖centered G d‖≤L*Real.sqrt d) :
    ‖corrected G d‖^2≤normConstant L ε*rowEnergy n d := by
  have hscale := (large_degree_scale L hL hdegree).1
  have hb := corrected_norm G hn hdn (L*Real.sqrt d) (by positivity) hcenter
  have hnorm : ‖corrected G d‖≤3*L*Real.sqrt d := by nlinarith
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) d)
  have hrow := (row_energy_bounds hn ε he he1 hsize hdensity).1
  have hp := norm_constant_pos hL he
  have hm := mul_le_mul_of_nonneg_left hrow hp.le
  have hid : normConstant L ε*(2*ε*d)=9*L^2*d := by
    unfold normConstant
    field_simp
  rw [hid] at hm
  nlinarith

theorem regular_profile_bound (ε : ℝ) (he : 0<ε) (D R : ℝ)
    (hD : D≤4*d) (hR : ε*n*Real.sqrt d/40≤R) :
    4*Real.sqrt 3*(gapConstant ε*n*Real.sqrt D)≤R := by
  have hs : Real.sqrt D≤2*Real.sqrt d := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) d)]
  have hid : 4*Real.sqrt 3*(gapConstant ε*n*Real.sqrt D)=ε*n*Real.sqrt D/80 := by
    unfold gapConstant
    field_simp
    ring
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hs (show 0≤ε*n by positivity)
  nlinarith

theorem count_allowance_le (hn : 2≤n) :
    (n/2:ℕ)*|(correction n d:ℝ)|≤2*d := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hhalf : (n/2:ℕ)≤n-1 := by omega
  have hhalf' : ((n/2:ℕ):ℝ)≤(n:ℝ)-1 := by
    have h : (n/2:ℕ)+1≤n := by omega
    have hh : ((n/2:ℕ):ℝ)+1≤n := by exact_mod_cast h
    linarith
  rw [correction_cast,abs_div,abs_mul]
  norm_num [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d),abs_of_pos (by linarith : (0:ℝ)<n-1)]
  apply (mul_le_mul_of_nonneg_right hhalf' (by positivity : (0:ℝ)≤2*d/(n-1))).trans_eq
  field_simp [ne_of_gt (show (0:ℝ)<n-1 by linarith)]

theorem regular_allowance_bound (hn : 2≤n) (hdn : d≤n) (ε g D : ℝ)
    (_he : 0<ε) (hg : 0<g) (hD : 0≤D) (hrow : 2*ε*d≤D)
    (hlarge : 128≤g^2*ε*n) : (n/2:ℕ)*|(correction n d:ℝ)|≤g*n*Real.sqrt D/8 := by
  have hdn' : (d:ℝ)≤n := by exact_mod_cast hdn
  have h1 := mul_le_mul_of_nonneg_right hdn' (Nat.cast_nonneg (α:=ℝ) d)
  have h2 := mul_le_mul_of_nonneg_right hlarge (show (0:ℝ)≤2*n*d by positivity)
  have h3 := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤g^2*n^2 by positivity)
  have hs : (16*(d:ℝ))^2≤(g*n*Real.sqrt D)^2 := by
    simp only [mul_pow,Real.sq_sqrt hD]
    nlinarith
  have hb := (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  have h := count_allowance_le (d:=d) hn
  nlinarith

end
end Max2SAT.Regular
