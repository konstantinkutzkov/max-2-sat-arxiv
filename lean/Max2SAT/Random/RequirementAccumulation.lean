import Max2SAT.Random.DriftMean
import Max2SAT.Random.RequirementMean
import Max2SAT.Random.RequirementTail
import Max2SAT.Random.ConcentrationTools

/-! Assemble the actual truncated requirements over the complete fixed
order. Selection of the prefix is represented by C; the more general
statement also permits any fixed set of charged variables. -/
namespace Max2SAT.FiniteLaw
noncomputable section
variable {Ω β : Type*} [Fintype Ω] [Fintype β] {n : ℕ}

theorem drift_lower_tail_indexed (p : Law Ω) (H : ℕ → Ω → β)
    (X μ : Fin n → Ω → ℝ) (u : Fin n → ℝ) (A : Ω → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, H j x = H j y → H i x = H i y)
    (hadapt : ∀ i, Known (H (i.val+1)) (X i))
    (hbound : ∀ i x, 0 < p.mass x → X i x ∈ Set.Icc 0 (u i))
    (hmean : ∀ i x, 0 < p.mass x → μ i x ≤ mean p (H i.val) (X i) x)
    (hA : ∀ x, 0 < p.mass x → (∑ i, X i x) ≤ A x)
    (B a : ℝ) (hB : 0 < B) (ha : 0 < a) (hbudget : (∑ i, (u i)^2) ≤ B) :
    prob p (fun x => A x < (∑ i, μ i x)-a) ≤ Real.exp (-2*a^2/B) := by
  let X' : ℕ → Ω → ℝ := fun j x => if h : j<n then X ⟨j,h⟩ x else 0
  let μ' : ℕ → Ω → ℝ := fun j x => if h : j<n then μ ⟨j,h⟩ x else 0
  let U : ℕ → β → ℝ := fun j _ => if h : j<n then u ⟨j,h⟩ else 0
  have hs : ∀ (f : Fin n → ℝ),
      (∑ j ∈ Finset.range n, if h : j<n then f ⟨j,h⟩ else 0) = ∑ i, f i := by
    intro f
    rw [← Fin.sum_univ_eq_sum_range]
    simp
  have hh := drift_lower_tail p n H X' μ' (fun _ _ => 0) U A href
    (by intro j hj; simpa only [X',dite_eq_left hj] using hadapt ⟨j,hj⟩)
    (by intro j hj x hx; simpa only [X',U,dite_eq_left hj] using hbound ⟨j,hj⟩ x hx)
    (by intro j hj x hx; simpa only [X',μ',dite_eq_left hj] using hmean ⟨j,hj⟩ x hx)
    (by intro x hx; dsimp only [X']; rw [hs (fun i => X i x)]; exact hA x hx)
    B a hB ha (by
      intro x _
      have he : (∑ j ∈ Finset.range n, (U j (H j x)-0)^2) = ∑ i, (u i)^2 := by
        rw [← Fin.sum_univ_eq_sum_range]
        simp [U]
      rw [he]
      exact hbudget)
  have he : ∀ x, (∑ j ∈ Finset.range n, μ' j x) = ∑ i, μ i x := by
    intro x
    exact hs (fun i => μ i x)
  simp_rw [he] at hh
  exact hh

end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def requirementAt (K : E → Pattern m) (units : List (Literal n))
    (i : Fin n) (z : ExposureBit E → Bool) : ℝ :=
  let D := delta (generate E (sampled K z) units) (orderedFree i.val) (assignment z) i
  if assignment z i ≠ decide (0 ≤ D) then supportWeight E i*(|D|+1) else 0

def requirements (K : E → Pattern m) (units : List (Literal n))
    (C : Finset (Fin n)) (z : ExposureBit E → Bool) : ℝ := ∑ i∈C, requirementAt K units i z

def truncatedAt (K : E → Pattern m) (units : List (Literal n))
    (i : Fin n) (z : ExposureBit E → Bool) : ℝ :=
  truncatedRequirement K units (orderedFree i.val) i
    ((m:ℝ)*Real.sqrt ((incident E i).card : ℝ)) z * supportWeight E i

theorem truncated_at_known (K : E → Pattern m) (units : List (Literal n)) (i : Fin n) :
    Known (orderedHistory E (i.val+1)) (truncatedAt K units i) := by
  intro z y h
  have hh := (ordered_history_eq (i.val+1) y z).1 h
  have hsigns := history_restrict _ _
    (known_after_subset (orderedFree i.val) (orderedFree (i.val+1)) i
      (orderedFree_antitone _ _ (by omega)) (by simp)) y z hh
  have hd := delta_known_after_signs K units (orderedFree i.val) i (by simp) y z hsigns
  have hx := ordered_assignment_known i y z hh
  simp only [truncatedAt,truncatedRequirement,hd,hx]

theorem truncated_at_bounds (K : E → Pattern m) (units : List (Literal n)) (i : Fin n)
    (hd : 0 < (incident E i).card) (z : ExposureBit E → Bool) :
    0 ≤ truncatedAt K units i z ∧ truncatedAt K units i z ≤ m := by
  have h := truncated_requirement_bounds K units (orderedFree i.val) i
    ((m:ℝ)*Real.sqrt ((incident E i).card : ℝ)) (supportWeight E i)
    (by positivity) (support_weight_pos (E:=E) i).le z
  refine ⟨h.1,h.2.trans ?_⟩
  have hs := mul_le_mul_of_nonneg_left (support_weight_sqrt_bounds i hd).2 (Nat.cast_nonneg m : (0:ℝ)≤m)
  nlinarith

theorem truncated_at_mean (K : E → Pattern m) (hm : 0 < m)
    (hK : ∀ e, size (K e) ≤ m) (units : List (Literal n)) (i : Fin n)
    (hd : 0 < (incident E i).card) (z : ExposureBit E → Bool) :
    supportWeight E i * Real.sqrt (∑ e : Incidence E i,
      (coefficient K (orderedFree i.val) z i e)^2)/13 ≤
      mean (fairBits (ExposureBit E)) (orderedHistory E i.val) (truncatedAt K units i) z := by
  unfold mean orderedHistory
  rw [fiber_fair_history]
  apply conditional_requirement_mean K units (orderedFree i.val) i (by simp) z
  · exact mul_pos (by exact_mod_cast hm) (Real.sqrt_pos.2 (by exact_mod_cast hd))
  · exact (support_weight_pos (E:=E) i).le
  · apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    exact variance_bound K hK (orderedFree i.val) z i

theorem requirement_drift_tail_fixed (K : E → Pattern m) (hm : 0 < m)
    (hK : ∀ e, size (K e) ≤ m) (units : List (Literal n))
    (C : Finset (Fin n)) (hC : 0 < C.card) (hd : ∀ i∈C, 0 < (incident E i).card)
    (a : ℝ) (ha : 0 < a) :
    prob (fairBits (ExposureBit E))
      (fun z => requirements K units C z < availableDrift K C z-a) ≤
      Real.exp (-2*a^2/((m:ℝ)^2*C.card)) := by
  let X : Fin n → (ExposureBit E → Bool) → ℝ :=
    fun i z => if i∈C then truncatedAt K units i z else 0
  let μ : Fin n → (ExposureBit E → Bool) → ℝ := fun i z => if i∈C then
    supportWeight E i * Real.sqrt (∑ e : Incidence E i,
      (coefficient K (orderedFree i.val) z i e)^2)/13 else 0
  let u : Fin n → ℝ := fun i => if i∈C then (m:ℝ) else 0
  have h := drift_lower_tail_indexed (fairBits (ExposureBit E)) (orderedHistory E) X μ u
    (requirements K units C) ordered_history_refines
    (by
      intro i z y h
      by_cases hi : i∈C
      · simp only [X,ite_eq_left hi]
        exact truncated_at_known K units i z y h
      · simp [X,hi])
    (by
      intro i z _
      by_cases hi : i∈C
      · simpa only [X,u,ite_eq_left hi,Set.mem_Icc] using truncated_at_bounds K units i (hd i hi) z
      · simp [X,u,hi])
    (by
      intro i z _
      by_cases hi : i∈C
      · simpa only [X,μ,ite_eq_left hi] using truncated_at_mean K hm hK units i (hd i hi) z
      · simp [X,μ,hi,mean])
    (by
      intro z _
      change (∑ i, if i∈C then truncatedAt K units i z else 0) ≤ _
      simp only [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
      apply Finset.sum_le_sum
      intro i _
      exact truncated_requirement_le_full K units (orderedFree i.val) i _ _
        (support_weight_pos (E:=E) i).le z)
    ((m:ℝ)^2*C.card) a (by positivity) ha (by
      simp only [u,ite_pow,zero_pow (by decide : (2:ℕ)≠0),← Finset.sum_filter]
      simp [mul_comm])
  have hμ : ∀ z, (∑ i, μ i z) = availableDrift K C z := by
    intro z
    simp only [μ,availableDrift,← Finset.sum_filter]
    simp
  simp_rw [hμ] at h
  exact h

theorem requirement_drift_tail (p : E → PairLaw m κ) (hm : 0 < m)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (a : ℝ) (ha : 0 < a) :
    prob (exposureLaw p)
      (fun z => requirements z.1 units C z.2 < availableDrift z.1 C z.2-a) ≤
      Real.exp (-2*a^2/((m:ℝ)^2*C.card)) := by
  rw [exposureLaw,prob_tensor]
  apply (expect_mono_support _ ?_).trans_eq (expect_const _ _)
  intro K hK
  exact requirement_drift_tail_fixed K hm (base_pattern_bound p K hK) units C hC hd a ha

end
end Max2SAT.RandomInput
