import Max2SAT.Random.OrderedExposure

/-! Identify the paper's Q_T, defined by actual score gains, with its
edge contributions and then with incoming rows. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

def edgeCompensation (K : E → Pattern m) (units : List (Literal n))
    (w : Fin n → ℝ) (e : E) (z : ExposureBit E → Bool) : ℝ :=
  w e.val.val.1 * comparisonMultiplier K units (orderedFree e.val.val.1.val) e.val.val.1 z *
    sign (z (.inr (e,true))) * eta true (K e) *
      sign (theta (z (.inr (e,false))) (assignment z e.val.val.2))

def compensation (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (w : Fin n → ℝ) (z : ExposureBit E → Bool) : ℝ :=
  ∑ i ∈ C, w i * comparisonMultiplier K units (orderedFree i.val) i z *
    (gain (generate E (sampled K z) units) i (assignment z) -
      delta (generate E (sampled K z) units) (orderedFree i.val) (assignment z) i)

def incomingCompensation (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) (z : ExposureBit E → Bool) : ℝ :=
  ∑ e : E, if e.val.val.2=i ∧ e.val.val.1∈C then edgeCompensation K units w e z else 0

theorem ordered_gain_deviation (K : E → Pattern m) (units : List (Literal n))
    (i : Fin n) (z : ExposureBit E → Bool) :
    gain (generate E (sampled K z) units) i (assignment z) -
      delta (generate E (sampled K z) units) (orderedFree i.val) (assignment z) i =
    ∑ e : E, if i=e.val.val.1 then
      sign (z (.inr (e,true))) * eta true (K e) *
        sign (theta (z (.inr (e,false))) (assignment z e.val.val.2)) else 0 := by
  rw [generated_gain, generated_delta E _ units _ i _ (by simp), add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hlt := e.val.property
  by_cases hl : i=e.val.val.1
  · subst i
    have hf : e.val.val.2 ∈ orderedFree e.val.val.1.val := by simp; omega
    simp only [edgeDelta, decide_eq_true hf, ↓reduceIte]
    simpa [sampled, endpoint, rho] using endpoint_deviation true (K e) (rho z e)
      (assignment z e.val.val.2)
  · by_cases hr : i=e.val.val.2
    · subst i
      have hf : e.val.val.1 ∉ orderedFree e.val.val.2.val := by simp; omega
      simp [hl, edgeDelta, hf]
    · simp [hl, hr]

theorem compensation_edges (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (w : Fin n → ℝ) (z : ExposureBit E → Bool) :
    compensation K units C w z =
      ∑ e : E, if e.val.val.1∈C then edgeCompensation K units w e z else 0 := by
  unfold compensation
  simp_rw [ordered_gain_deviation, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [edgeCompensation, mul_assoc]

theorem compensation_rows (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (w : Fin n → ℝ) (z : ExposureBit E → Bool) :
    compensation K units C w z = ∑ i, incomingCompensation K units C w i z := by
  rw [compensation_edges]
  unfold incomingCompensation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hc : e.val.val.1∈C <;> simp [hc]

/-- The edge representation agrees with the previously checked
incidence-based conditional row estimate. -/
def incomingIncidences (C : Finset (Fin n)) (i : Fin n) : Finset (Incidence E i) :=
  Finset.univ.filter (fun e => partner i e.val.val < i ∧ partner i e.val.val ∈ C)

theorem incoming_incidence_right (C : Finset (Fin n)) (i : Fin n)
    (e : Incidence E i) (he : e ∈ incomingIncidences C i) :
    i=e.val.val.val.2 ∧ e.val.val.val.1∈C := by
  have h := (Finset.mem_filter.1 he).2
  rcases incident_cases e with hl | hr
  · rw [partner_left _ hl] at h
    have hlt := e.val.val.property
    omega
  · rw [partner_right _ hr] at h
    exact ⟨hr, h.2⟩

theorem incidence_edge_compensation (K : E → Pattern m) (units : List (Literal n))
    (w : Fin n → ℝ) (i : Fin n) (e : Incidence E i) (hi : i=e.val.val.val.2)
    (z : ExposureBit E → Bool) :
    laterCoefficient K units (fun j => orderedFree j.val) w i e z *
      sign (theta (z (current i e)) (assignment z i)) = edgeCompensation K units w e.val z := by
  have hl := ne_of_lt e.val.val.property
  simp [laterCoefficient, partner, side, vertex, current, hi, Ne.symm hl,
    edgeCompensation, opposite]

theorem incoming_sum (C : Finset (Fin n)) (i : Fin n) (f : E → ℝ) :
    (∑ e : incomingIncidences (E:=E) C i, f e.val.val) =
      ∑ e : E, if e.val.val.2=i ∧ e.val.val.1∈C then f e else 0 := by
  rw [← Finset.sum_subtype (incomingIncidences C i) (fun _ => Iff.rfl) (fun e : Incidence E i => f e.val), incomingIncidences, Finset.sum_filter,
    sum_incident E i (fun e => if partner i e.val < i ∧ partner i e.val ∈ C then f e else 0)]
  apply Finset.sum_congr rfl
  intro e _
  have hlt := e.val.property
  by_cases hl : i=e.val.val.1 <;> by_cases hr : i=e.val.val.2
  · omega
  · subst i
    simp [hr, partner, side, vertex, not_lt_of_ge (le_of_lt hlt), Ne.symm (ne_of_lt hlt)]
  · subst i
    simp [hl, partner, side, vertex, hlt]
  · simp [hl,hr,Ne.symm hr]

theorem incoming_row_eq (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) (z : ExposureBit E → Bool) :
    incomingCompensation K units C w i z =
      ∑ e : incomingIncidences (E:=E) C i,
        laterCoefficient K units (fun j => orderedFree j.val) w i e.val z *
          sign (theta (z (current i e.val)) (assignment z i)) := by
  have heq : (∑ e : incomingIncidences (E:=E) C i,
      laterCoefficient K units (fun j => orderedFree j.val) w i e.val z *
        sign (theta (z (current i e.val)) (assignment z i))) =
      ∑ e : incomingIncidences (E:=E) C i, edgeCompensation K units w e.val.val z := by
    apply Finset.sum_congr rfl
    intro e _
    exact incidence_edge_compensation K units w i e.val
      (incoming_incidence_right C i e.val e.property).1 z
  rw [heq, incoming_sum C i (fun e => edgeCompensation K units w e z)]
  rfl

end
end Max2SAT.RandomInput
