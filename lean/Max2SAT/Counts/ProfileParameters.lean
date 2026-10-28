import Max2SAT.Counts.GapConcentration
import Max2SAT.Counts.GapBridge
import Max2SAT.Counts.RoundSplit
import Max2SAT.Counts.CreatorTail

namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def prefixRows (H : Fin n → Affine n) (P : Finset (Fin n)) (round : Fin n → ℕ) :
    Matrix P (Fin n) ℝ := fun t w => earlierRow H round t w

theorem prefix_row_energy (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hr : EarlierInPrefix P round)
    (V : ℝ) (hV : 0≤V) (hN : ‖prefixRows H P round‖^2≤V) (x : Assignment n) :
    (∑ t : P, (rawRows (prefixRows H P round) x t)^2)≤P.card*V := by
  let z : Fin n → ℝ := fun w => if w∈P then sign (x w) else 0
  have he : ∀ t : P, rawRows (prefixRows H P round) x t=
      ∑ w, prefixRows H P round t w*z w := by
    intro t
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w∈P
    · simp [z,hw]
    · have hh : ¬ round w<round t := fun hh => hw (hr t t.property w hh)
      simp [prefixRows,earlierRow,hh]
  simp_rw [he]
  have hz : (∑ w, (z w)^2)≤P.card := by
    have hs : ∀ w, (z w)^2=if w∈P then (1:ℝ) else 0 := by
      intro w; by_cases hw : w∈P <;> cases hx : x w <;> simp [z,hw,hx,sign]
    simp [hs]
  have h := (matrix_squared_energy (prefixRows H P round) z V hN).trans
    (mul_le_mul_of_nonneg_left hz hV)
  simpa [mul_comm] using h

theorem matrix_row_square_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Matrix κ (Fin n) ℝ) (V : ℝ) (hN : ‖L‖^2≤V) (t : κ) :
    (∑ i, (L t i)^2)≤V := by
  have hn : ‖L.transpose‖^2≤V := by
    simpa using (show ‖L.conjTranspose‖^2≤V by rw [Matrix.l2_opNorm_conjTranspose]; exact hN)
  have h := matrix_squared_energy L.transpose (fun w => if w=t then 1 else 0) V hn
  simpa using h

/-- Explicit tuning of smoothing and clipping, with no large-n premise. -/
theorem smoothing_parameters (T V α A : ℝ) (hT : 0≤T) (hV : 0<V) (hα : 2≤α)
    (hscale : 2*T*Real.sqrt V≤α*A) :
    T*V/(α*Real.sqrt V)≤A/2 ∧ T*(Real.sqrt V/α)/2≤A/4 ∧
    2*T*V+T*V^2/(2*(Real.sqrt V/α)^2)≤α^2*T*V := by
  have hv := Real.sqrt_pos.mpr hV
  have hv2 := Real.sq_sqrt hV.le
  have ha : 0<α := by linarith
  have hc : T*V/(α*Real.sqrt V)=T*Real.sqrt V/α := by
    field_simp
    nlinarith
  have hs : T*Real.sqrt V/α≤A/2 := by
    apply (div_le_iff₀ ha).2
    nlinarith
  refine ⟨by rw [hc]; exact hs,?_,?_⟩
  · nlinarith [show T*(Real.sqrt V/α)=T*Real.sqrt V/α by ring]
  · have he : T*V^2/(2*(Real.sqrt V/α)^2)=T*V*α^2/2 := by
      field_simp
      nlinarith
    rw [he]
    have h4 : 4≤α^2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hT hV.le) (sub_nonneg.mpr h4)]

/-- The paper's common-gap estimate, expressed directly for the rational
averages used by the comparison procedure. -/
theorem prefix_gap_tail (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hr : EarlierInPrefix P round) (hP : 0<P.card)
    (V α A : ℝ) (hV : 0<V) (hα : 2≤α) (hA : 0<A)
    (hN : ‖prefixRows H P round‖^2≤V)
    (hprofile : 2*A≤(∑ t : P, Real.sqrt ((∑ w, (earlierRow H round t w)^2)/3))/2)
    (hscale : 2*P.card*Real.sqrt V≤α*A) :
    prob (fairBits (Fin n)) (fun x =>
      (∑ t∈P, clippedGap H round (α*Real.sqrt V) t x)<3*A/4) ≤
      Real.exp (-A^2/(8*(α^2*P.card*V))) := by
  have ha : 0<α := by linarith
  have hp : (0:ℝ)<P.card := by exact_mod_cast hP
  have hv : 0<Real.sqrt V := Real.sqrt_pos.mpr hV
  have hs := smoothing_parameters (P.card:ℝ) V α A hp.le hV hα hscale
  have hrow : ∀ t : P, Real.sqrt ((∑ w, (prefixRows H P round t w)^2)/3)/2≤
      (α*Real.sqrt V)/4 := by
    intro t
    have hr := matrix_row_square_bound (prefixRows H P round) V hN t
    have hh : (∑ w, (prefixRows H P round t w)^2)/3≤V := by linarith
    have hh' := Real.sqrt_le_sqrt hh
    nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hα)]
  have ht := common_gap_tail (fun t : P => rowShift (H t)) (prefixRows H P round)
    (α*Real.sqrt V) (Real.sqrt V/α) V (P.card*V) (α^2*P.card*V) A
    (by positivity) (by positivity) hV.le (by positivity) hA hN
    (prefix_row_energy H P round hr V hV.le hN) hrow hprofile hs.1
    (by simpa using hs.2.1) (by simpa using hs.2.2)
  have he : ∀ x, (∑ t : P, min |rowValue (fun t : P => rowShift (H t))
      (prefixRows H P round) x t| (α*Real.sqrt V)) =
      ∑ t∈P, clippedGap H round (α*Real.sqrt V) t x := by
    intro x
    have hre : ∀ t : P, rowValue (fun t : P => rowShift (H t))
        (prefixRows H P round) x t = ((H t).average (earlier round t) x : ℝ) := by
      intro t
      rw [average_real_signed_form]
      unfold rowValue prefixRows
      congr 2
      apply Finset.sum_congr rfl
      intro w _
      ring
    simp_rw [hre]
    exact Finset.sum_coe_sort P (fun t => clippedGap H round (α*Real.sqrt V) t x)
  simpa only [he] using ht

end
end Max2SAT.Counts
