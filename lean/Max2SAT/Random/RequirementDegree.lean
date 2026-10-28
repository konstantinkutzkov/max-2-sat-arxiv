import Max2SAT.Random.RequirementMean
import Max2SAT.Random.WeightBounds

/-! Apply the local requirement estimate with the actual observed degree
and the implemented rational weight. These are the local bounds in Step 1
of the accumulated-requirement lemma, before summing along the order. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
variable {n m : ℕ} {E : Finset (Edge n)}

theorem degree_truncation_cap (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (hp : ∀ e, present (K e)) (units : List (Literal n)) (free : Finset (Fin n))
    (z : ExposureBit E → Bool) (i : Fin n) :
    Real.sqrt (∑ e : Incidence E i, (coefficient K free z i e)^2) ≤
      (m:ℝ)*Real.sqrt ((Random.neighbors (generate E (sampled K z) units) i).card : ℝ) := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact variance_observed_degree K hK hp units free z i

theorem normalized_requirement_mean (K : E → Pattern m) (hm : 0 < m)
    (hK : ∀ e, size (K e) ≤ m) (hp : ∀ e, present (K e))
    (units : List (Literal n)) (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z : ExposureBit E → Bool)
    (hd : 0 < (Random.neighbors (generate E (sampled K z) units) i).card) :
    let F := generate E (sampled K z) units
    let cap := (m:ℝ)*Real.sqrt ((Random.neighbors F i).card : ℝ)
    (Random.weight F i : ℝ) *
      Real.sqrt (∑ e : Incidence E i, (coefficient K free z i e)^2)/13 ≤
    expect (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z))
      (fun r => truncatedRequirement K units free i cap r * (Random.weight F i : ℝ)) := by
  dsimp only
  apply conditional_requirement_mean K units free i hi z
  · exact mul_pos (by exact_mod_cast hm) (Real.sqrt_pos.2 (by exact_mod_cast hd))
  · exact_mod_cast (Random.weight_positive (generate E (sampled K z) units) i).le
  · exact degree_truncation_cap K hK hp units free z i

theorem normalized_requirement_bounds (K : E → Pattern m)
    (units : List (Literal n)) (free : Finset (Fin n)) (i : Fin n)
    (z r : ExposureBit E → Bool)
    (hd : 0 < (Random.neighbors (generate E (sampled K z) units) i).card) :
    let F := generate E (sampled K z) units
    let cap := (m:ℝ)*Real.sqrt ((Random.neighbors F i).card : ℝ)
    0 ≤ truncatedRequirement K units free i cap r * (Random.weight F i : ℝ) ∧
    truncatedRequirement K units free i cap r * (Random.weight F i : ℝ) ≤ m := by
  dsimp only
  let F := generate E (sampled K z) units
  have hw : 0 ≤ (Random.weight F i : ℝ) := by exact_mod_cast (Random.weight_positive F i).le
  have h := truncated_requirement_bounds K units free i
    ((m:ℝ)*Real.sqrt ((Random.neighbors F i).card : ℝ)) (Random.weight F i : ℝ)
    (by positivity) hw r
  refine ⟨h.1, h.2.trans ?_⟩
  have hs : 0 < Real.sqrt ((Random.neighbors F i).card : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hb := (le_div_iff₀ hs).1 (Random.weight_sqrt_bounds F i hd).2
  have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  nlinarith

end
end Max2SAT.RandomInput
