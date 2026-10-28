import Max2SAT.Counts.BitExposure

/-! Sequential compensation for the implemented comparisons. The squared
Euclidean operator bound is stated explicitly as a bound on all vectors;
no randomness or independence of the creator vector is assumed. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def incoming (H : Fin n → Affine n) (P : Finset (Fin n))
    (x : Assignment n) (w : Fin n) : ℝ :=
  ∑ t∈P, if t.val<w.val ∧ x t≠preference H (fun i => i.val) x t then
    sign (x t)*(H t).coeff w else 0

theorem incoming_known (H : Fin n → Affine n) (P : Finset (Fin n)) (w : Fin n) :
    Known (bitHistory n w.val) (fun x => incoming H P x w) := by
  intro x y h
  unfold incoming
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t.val<w.val
  · have hx := bit_history_agree w.val x y h t ht
    have hp := preference_known H (fun i => i.val) (fun _ _ h => h) t x y
      (bit_history_refines t.val w.val ht.le x y h)
    rw [hx,hp]
  · simp [ht]

theorem sequential_compensation_identity (H : Fin n → Affine n)
    (P : Finset (Fin n)) (hdiag : ∀ t, (H t).coeff t=0) (x : Assignment n) :
    (compensation H P (fun i => i.val) x : ℝ) =
      ∑ w, (-incoming H P x w/2)*sign (x w) := by
  unfold compensation incoming
  push_cast
  simp only [←Finset.sum_neg_distrib, Finset.sum_div,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : x t≠preference H (fun i => i.val) x t
  · simp only [ite_eq_left hc]
    push_cast
    simp only [direction_cast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w.val<t.val
    · have htw : ¬t.val<w.val := by omega
      simp [hw,htw]
    · by_cases ht : t.val<w.val
      · simp only [ite_eq_right hw]
        rw [ite_eq_left ⟨ht,hc⟩]
        push_cast
        rw [direction_cast]
        ring
      · have he : w=t := Fin.ext (by omega)
        subst w
        simp [hdiag]
  · simp [hc]

/-- Squared norm bound for the transpose of the rectangular strictly
upper-triangular matrix R in the sequential theorem. This is its
Euclidean operator inequality, expressed without matrix notation. -/
def SequentialEnergy (H : Fin n → Affine n) (P : Finset (Fin n)) (V : ℝ) : Prop :=
  ∀ z : Fin n → ℝ,
    (∑ w, (∑ t∈P, if t.val<w.val then z t*(H t).coeff w else 0)^2) ≤
      V*(∑ t∈P, (z t)^2)

theorem incoming_energy (H : Fin n → Affine n) (P : Finset (Fin n))
    (V : ℝ) (hV : 0≤V) (henergy : SequentialEnergy H P V) (x : Assignment n) :
    (∑ w, (incoming H P x w)^2) ≤ V*P.card := by
  let z : Fin n → ℝ := fun t =>
    if x t≠preference H (fun i => i.val) x t then sign (x t) else 0
  have he : ∀ w, incoming H P x w =
      ∑ t∈P, if t.val<w.val then z t*(H t).coeff w else 0 := by
    intro w
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val<w.val <;>
      by_cases hc : x t≠preference H (fun i => i.val) x t <;> simp [ht,hc,z]
  have hz : (∑ t∈P, (z t)^2) ≤ P.card := by
    calc
      _ ≤ ∑ _t∈P, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        dsimp only [z]
        split_ifs
        · cases x t <;> norm_num [sign]
        · norm_num
      _ = _ := by simp
  simp_rw [he]
  exact (henergy z).trans (mul_le_mul_of_nonneg_left hz hV)

/-- The sequential compensation tail, with every predictability
hypothesis and the random creator-vector energy discharged. -/
theorem sequential_compensation_tail (H : Fin n → Affine n)
    (P : Finset (Fin n)) (hdiag : ∀ t, (H t).coeff t=0)
    (V b : ℝ) (hV : 0<V) (hb : 0<b) (hP : 0<P.card)
    (henergy : SequentialEnergy H P V) :
    prob (fairBits (Fin n)) (fun x =>
      (compensation H P (fun i => i.val) x : ℝ) < -b) ≤
        Real.exp (-2*b^2/(V*P.card)) := by
  have h := assignment_sign_tail (fun w x => -incoming H P x w/2)
    (by intro w x y h; dsimp only; have he := incoming_known H P w x y h; dsimp only at he; rw [he])
    (V*P.card) b (mul_pos hV (by exact_mod_cast hP)) hb (by
      intro x
      have he : ∀ w, 4*(-incoming H P x w/2)^2=(incoming H P x w)^2 := by
        intro w; ring
      simp_rw [he]
      exact incoming_energy H P V hV.le henergy x)
  simpa only [sequential_compensation_identity H P hdiag] using h

end
end Max2SAT.Counts
