import Max2SAT.Random.CompensationRow
import Max2SAT.Random.BitHistory
import Max2SAT.Random.WeightBounds

/-! The fixed increasing-label exposure and the normalization budget on a
fixed observed graph. Isolated labels are harmless and may be skipped. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

def orderedFree (t : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => t ≤ i.val)

@[simp] theorem mem_orderedFree (t : ℕ) (i : Fin n) :
    i ∈ orderedFree t ↔ t ≤ i.val := by simp [orderedFree]

theorem orderedFree_antitone (s t : ℕ) (h : s ≤ t) :
    (orderedFree t : Finset (Fin n)) ⊆ orderedFree s := by
  intro i hi
  exact (mem_orderedFree s i).mpr (h.trans ((mem_orderedFree t i).mp hi))

def orderedHistory (E : Finset (Edge n)) (t : ℕ) :
    (ExposureBit E → Bool) → (ExposureBit E → Bool) :=
  observe (knownBefore E (orderedFree t))

theorem ordered_history_refines (s t : ℕ) (h : s ≤ t)
    (z w : ExposureBit E → Bool) (hh : orderedHistory E t z = orderedHistory E t w) :
    orderedHistory E s z = orderedHistory E s w :=
  observe_refines _ _ (known_before_antitone _ _ (orderedFree_antitone s t h)) z w hh

theorem ordered_history_eq (t : ℕ) (z w : ExposureBit E → Bool) :
    orderedHistory E t w = orderedHistory E t z ↔ history (knownBefore E (orderedFree t)) z w :=
  observe_eq_iff _ z w

theorem ordered_assignment_known (i : Fin n) (z w : ExposureBit E → Bool)
    (h : history (knownBefore E (orderedFree (i.val+1))) z w) : assignment w i = assignment z i := by
  have hh := h (.inl i)
  simpa [knownBefore, assignment] using hh

theorem ordered_endpoint_known (i : Fin n) (e : E) (left : Bool)
    (hi : vertex e.val left = i) (z w : ExposureBit E → Bool)
    (h : history (knownBefore E (orderedFree (i.val+1))) z w) :
    w (.inr (e,left)) = z (.inr (e,left)) := by
  have hh := h (.inr (e,left))
  simpa [knownBefore, hi] using hh

/-- The weights are computed from the observed support, before any
signs are drawn or preprocessing is performed. -/
def supportWeight (E : Finset (Edge n)) (i : Fin n) : ℝ :=
  1 / ((Nat.sqrt ((incident E i).card-1)+1 : ℕ) : ℝ)

theorem support_weight_eq (K : E → Pattern m) (hp : ∀ e, present (K e))
    (units : List (Literal n)) (i : Fin n) :
    supportWeight E i = (Random.weight (generate E K units) i : ℝ) := by
  simp only [supportWeight, Random.weight, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    observed_degree E K hp units i]

theorem support_weight_pos (i : Fin n) : 0 < supportWeight E i := by
  unfold supportWeight
  positivity

theorem support_weight_squared_degree (i : Fin n) :
    (supportWeight E i)^2 * (incident E i).card ≤ 1 := by
  by_cases hd : 0 < (incident E i).card
  · have h := (Random.sqrt_denominator_bounds (incident E i).card hd).1
    have hsq := sq_le_sq₀ (Real.sqrt_nonneg ((incident E i).card : ℝ)) (by positivity :
      (0:ℝ) ≤ ((Nat.sqrt ((incident E i).card-1)+1 : ℕ) : ℝ))
    have hb : ((incident E i).card : ℝ) ≤
        (((Nat.sqrt ((incident E i).card-1)+1 : ℕ) : ℝ))^2 := by
      simpa only [Real.sq_sqrt (Nat.cast_nonneg _)] using hsq.mpr h
    unfold supportWeight
    rw [div_pow, one_pow, div_mul_eq_mul_div]
    apply (div_le_one (by positivity)).2
    simpa using hb
  · have hz : (incident E i).card = 0 := by omega
    simp [hz]

/-- Charging each edge to its earlier endpoint uses no more than that
endpoint's full degree budget. The set of charged creators is arbitrary. -/
theorem forward_weight_budget (C : Finset (Fin n)) (w : Fin n → ℝ)
    (hdeg : ∀ i, (w i)^2 * (incident E i).card ≤ 1) :
    (∑ e : E, if e.val.val.1 ∈ C then (w e.val.val.1)^2 else 0) ≤ C.card := by
  have he : (∑ e : E, if e.val.val.1 ∈ C then (w e.val.val.1)^2 else 0) =
      ∑ i ∈ C, ∑ e : E, if i=e.val.val.1 then (w i)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp
  rw [he]
  calc
    _ ≤ ∑ i ∈ C, (w i)^2 * (incident E i).card := by
      apply Finset.sum_le_sum
      intro i _
      have heq : (w i)^2 * (incident E i).card = ∑ e : Incidence E i, (w i)^2 := by
        simp [mul_comm]
      rw [heq, sum_incident E i (fun _ => (w i)^2)]
      apply Finset.sum_le_sum
      intro e _
      by_cases h : i=e.val.val.1
      · simp [h]
      · simp only [h, ↓reduceIte, false_or]
        split_ifs <;> positivity
    _ ≤ ∑ _i ∈ C, (1:ℝ) := Finset.sum_le_sum (fun i _ => hdeg i)
    _ = _ := by simp

end
end Max2SAT.RandomInput
