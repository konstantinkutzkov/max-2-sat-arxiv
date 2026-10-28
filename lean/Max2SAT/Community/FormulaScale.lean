import Max2SAT.Community.JacobiParameters

/-! Polynomial grid and iteration bounds in the explicitly listed formula
length. This does not assert a bit-cost theorem for succinct large weights. -/
namespace Max2SAT.Community
open Counts
variable {n : ℕ}
set_option maxHeartbeats 800000

theorem formula_score_range (F : Formula n) (x : Assignment n) :
    0≤score F x ∧ score F x≤F.length := by
  have hc : ∀ c : Clause n, 0≤c.score x ∧ c.score x≤1 := by
    intro c
    cases c with
    | unit a => exact ⟨Literal.value_nonneg a x,Literal.value_le_one a x⟩
    | pair a b => simp only [Clause.score]; split <;> norm_num
  induction F with
  | nil => simp
  | cons c F ih =>
    have hh := hc c
    simp only [score_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    constructor <;> omega

theorem score_gain_bound (F : Formula n) (i : Fin n) (x : Assignment n) :
    |scoreGain F i x|≤(F.length:ℚ) := by
  have h₁ := formula_score_range F (Function.update x i true)
  have h₀ := formula_score_range F (Function.update x i false)
  have ht : (0:ℚ)≤score F (Function.update x i true) ∧
      (score F (Function.update x i true):ℚ)≤F.length := by exact_mod_cast h₁
  have hf : (0:ℚ)≤score F (Function.update x i false) ∧
      (score F (Function.update x i false):ℚ)≤F.length := by exact_mod_cast h₀
  unfold scoreGain
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem formula_coefficient_bound (F : Formula n) (hF : wellFormed F) (i j : Fin n) :
    |formulaMatrix F i j|≤2*(F.length:ℚ) := by
  let x : Assignment n := fun _ => false
  have h := Affine.eval_update (gainExpr F i) x j true
  rw [gainExpr_eval F i _ hF,gainExpr_eval F i _ hF] at h
  simp only [x,bit_true,bit_false,sub_zero,mul_one] at h
  have h₁ := score_gain_bound F i (Function.update x j true)
  have h₀ := score_gain_bound F i x
  have he : formulaMatrix F i j=scoreGain F i (Function.update x j true)-scoreGain F i x := by
    change (gainExpr F i).coeff j=_
    linarith
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem formula_square_sum_bound (F : Formula n) (hF : wellFormed F) :
    squareSum (formulaMatrix F)≤4*(n:ℚ)^2*(F.length:ℚ)^2 := by
  calc
    _ ≤ ∑ _i:Fin n, ∑ _j:Fin n, (2*(F.length:ℚ))^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (formula_coefficient_bound F hF i j)
      simpa only [sq_abs] using h
    _ = _ := by simp; ring

theorem formula_scale_bound (F : Formula n) (hF : wellFormed F) :
    diagonalizationScale (formulaMatrix F)≤4*n^2*F.length^2+1 := by
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  exact_mod_cast formula_square_sum_bound F hF

theorem formula_grid_bound (F : Formula n) (hF : wellFormed F) :
    diagonalizationGrid n (diagonalizationScale (formulaMatrix F))≤
      32*n^5*(4*n^2*F.length^2+1) :=
  Nat.mul_le_mul_left _ (formula_scale_bound F hF)

theorem formula_fuel_bound (F : Formula n) (hF : wellFormed F) :
    diagonalizationFuel n (diagonalizationScale (formulaMatrix F))≤
      (4*n^2*F.length^2+1)*n^10 :=
  Nat.mul_le_mul_right _ (formula_scale_bound F hF)

end Max2SAT.Community
