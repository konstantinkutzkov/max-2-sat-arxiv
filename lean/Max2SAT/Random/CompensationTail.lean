import Max2SAT.Random.CompensationSum
import Max2SAT.Random.ConditionalMGF
import Max2SAT.Random.ConcentrationTools

/-! The complete compensation estimate, first for fixed base patterns
and then averaged over their prescribed distribution. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def incomingBudget (C : Finset (Fin n)) (w : Fin n → ℝ) (m : ℕ) (i : Fin n) : ℝ :=
  ∑ e : E, if e.val.val.2=i ∧ e.val.val.1∈C then (w e.val.val.1*(m:ℝ))^2 else 0

theorem incoming_compensation_known (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) :
    Known (orderedHistory E (i.val+1)) (incomingCompensation K units C w i) := by
  intro z y h
  have hh := (ordered_history_eq (i.val+1) y z).1 h
  have hbefore := history_restrict _ _
    (known_before_antitone (orderedFree i.val) (orderedFree (i.val+1))
      (orderedFree_antitone _ _ (by omega))) y z hh
  rw [incoming_row_eq, incoming_row_eq]
  apply Finset.sum_congr rfl
  intro e _
  have he := (Finset.mem_filter.1 e.property).2
  have hm := later_coefficient_known K units (fun j => orderedFree j.val) w i e.val
    (orderedFree i.val) (by simp) (by simp; exact he.1)
    (orderedFree_antitone _ _ (Nat.le_of_lt he.1)) y z hbefore
  have hr := ordered_endpoint_known i e.val.val (side i e.val.val.val)
    (incident_vertex e.val) y z hh
  have hx := ordered_assignment_known i y z hh
  simp only [hm, current, hr, hx]

theorem incoming_coefficients_budget (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (units : List (Literal n)) (C : Finset (Fin n)) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (i : Fin n) (z : ExposureBit E → Bool) :
    (∑ e : incomingIncidences (E:=E) C i,
      (laterCoefficient K units (fun j => orderedFree j.val) w i e.val z)^2) ≤
      incomingBudget (E:=E) C w m i / 4 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (e : incomingIncidences (E:=E) C i) _ =>
    show (laterCoefficient K units (fun j => orderedFree j.val) w i e.val z)^2 ≤
      (w e.val.val.val.val.1*(m:ℝ))^2/4 from by
      have he := incoming_incidence_right C i e.val e.property
      have hb := later_coefficient_bound K hK units (fun j => orderedFree j.val) w hw i e.val z
      rw [partner_right _ he.1] at hb
      have hs := (sq_le_sq₀ (abs_nonneg _) (by exact div_nonneg (mul_nonneg (hw _) (Nat.cast_nonneg _)) (by norm_num) :
        0 ≤ w e.val.val.val.val.1*(m:ℝ)/2)).2 hb
      norm_num only [sq_abs, div_pow, show (2:ℝ)^2=4 by norm_num] at hs
      exact hs)
  rw [← Finset.sum_div, incoming_sum C i (fun e => (w e.val.val.1*(m:ℝ))^2)] at h
  exact h

theorem incoming_compensation_mgf (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (units : List (Literal n)) (C : Finset (Fin n)) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (i : Fin n) (z : ExposureBit E → Bool) (t : ℝ) :
    expect (fiber (fairBits (ExposureBit E)) (orderedHistory E i.val) (orderedHistory E i.val z))
      (fun y => Real.exp (t*incomingCompensation K units C w i y)) ≤
    Real.exp (t^2*incomingBudget (E:=E) C w m i/8) := by
  have h := conditional_compensation_row_mgf K units (fun j => orderedFree j.val) w i
    (orderedFree i.val) (by simp) (incomingIncidences C i)
    (by intro e _; simp)
    (by
      intro e he
      have hh := (Finset.mem_filter.1 he).2.1
      simp only [mem_orderedFree, not_le]
      exact hh)
    (by
      intro e he
      exact orderedFree_antitone _ _ (Nat.le_of_lt (Finset.mem_filter.1 he).2.1)) z t
  change expect (fiber _ (observe _) (observe _ z)) _ ≤ _
  rw [fiber_fair_history]
  simp_rw [incoming_row_eq]
  apply h.trans
  apply Real.exp_le_exp.2
  have hb := incoming_coefficients_budget K hK units C w hw i z
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg t)]

theorem total_compensation_budget (C : Finset (Fin n)) (w : Fin n → ℝ)
    (hdeg : ∀ i, (w i)^2 * (incident E i).card ≤ 1) :
    (∑ i, incomingBudget (E:=E) C w m i) ≤ (m:ℝ)^2*C.card := by
  have he : (∑ i, incomingBudget (E:=E) C w m i) =
      (m:ℝ)^2 * ∑ e : E, if e.val.val.1∈C then (w e.val.val.1)^2 else 0 := by
    unfold incomingBudget
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : e.val.val.1∈C <;> simp [hc, mul_pow, mul_comm]
  rw [he]
  exact mul_le_mul_of_nonneg_left (forward_weight_budget C w hdeg) (sq_nonneg _)

/-- Fin-indexed form of sequential block composition. -/
theorem compensation_mgf (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (units : List (Literal n)) (C : Finset (Fin n)) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hdeg : ∀ i, (w i)^2 * (incident E i).card ≤ 1)
    (t : ℝ) :
    expect (fairBits (ExposureBit E)) (fun z => Real.exp (t*compensation K units C w z)) ≤
      Real.exp (t^2*((m:ℝ)^2*C.card)/8) := by
  let X : ℕ → (ExposureBit E → Bool) → ℝ :=
    fun j z => if h : j<n then incomingCompensation K units C w ⟨j,h⟩ z else 0
  let v : ℕ → ℝ := fun j => if h : j<n then incomingBudget (E:=E) C w m ⟨j,h⟩ else 0
  have h := conditional_mgf_sum (fairBits (ExposureBit E)) n (orderedHistory E) X v
    (ordered_history_refines)
    (by intro j hj; simpa only [X, dite_eq_left hj] using incoming_compensation_known K units C w ⟨j,hj⟩)
    (by intro j hj z _ t; simpa only [X, v, dite_eq_left hj] using incoming_compensation_mgf K hK units C w hw ⟨j,hj⟩ z t) t
  have hX : ∀ z, (∑ j ∈ Finset.range n, X j z) = compensation K units C w z := by
    intro z
    rw [← Fin.sum_univ_eq_sum_range (fun j => X j z), compensation_rows]
    apply Finset.sum_congr rfl
    intro i _
    simp [X, i.isLt]
  have hv : (∑ j ∈ Finset.range n, v j) = ∑ i, incomingBudget (E:=E) C w m i := by
    rw [← Fin.sum_univ_eq_sum_range v]
    apply Finset.sum_congr rfl
    intro i _
    simp [v, i.isLt]
  simp_rw [hX] at h
  rw [hv] at h
  apply h.trans
  apply Real.exp_le_exp.2
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (total_compensation_budget C w hdeg) (sq_nonneg t)) (by norm_num)

theorem compensation_tail_fixed (K : E → Pattern m) (hm : 0 < m)
    (hK : ∀ e, size (K e) ≤ m) (units : List (Literal n))
    (C : Finset (Fin n)) (hC : 0 < C.card) (c : ℝ) (hc : 0 < c) :
    prob (fairBits (ExposureBit E))
      (fun z => compensation K units C (supportWeight E) z < -c) ≤
      Real.exp (-2*c^2/((m:ℝ)^2*C.card)) := by
  apply lower_tail_of_mgf _ _ _ c (by positivity) hc
  intro t
  simpa only [neg_sq] using compensation_mgf K hK units C (supportWeight E)
    (fun i => (support_weight_pos i).le) support_weight_squared_degree (-t)

theorem compensation_tail (p : E → PairLaw m κ) (hm : 0 < m)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (c : ℝ) (hc : 0 < c) :
    prob (exposureLaw p)
      (fun z => compensation z.1 units C (supportWeight E) z.2 < -c) ≤
      Real.exp (-2*c^2/((m:ℝ)^2*C.card)) := by
  rw [exposureLaw, prob_tensor]
  change expect (product (fun e => (p e).law))
    (fun K => prob (fairBits (ExposureBit E))
      (fun z => compensation K units C (supportWeight E) z < -c)) ≤ _
  apply (expect_mono_support _ ?_).trans_eq (expect_const _ _)
  intro K hK
  exact compensation_tail_fixed K hm (base_pattern_bound p K hK) units C hC c hc

end
end Max2SAT.RandomInput
