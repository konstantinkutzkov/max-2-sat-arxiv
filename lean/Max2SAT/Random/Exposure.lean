import Max2SAT.Random.SequentialExposure
import Max2SAT.Random.ExposureSupport
import Max2SAT.Random.ExposureLaw
import Max2SAT.Random.Algorithm

/-! Assembled exposure results for Lemma lem:random_exposure. These include
the formula-only initialization and the full conditional sampling law;
they do not assert the later concentration or running-time theorems. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem conditional_exposure_moments (p : E → PairLaw m κ) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (p e).law)).mass K)
    (units : List (Literal n)) (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z : ExposureBit E → Bool) :
    let q := condition (exposureLaw p) (baseHistory K (knownBefore E free) z)
      (base_history_positive p K hK _ z)
    expect q (fun w => delta (generate E (sampled w.1 w.2) units) free (assignment w.2) i) =
      unitBias units i ∧
    expect q (fun w => (delta (generate E (sampled w.1 w.2) units) free (assignment w.2) i -
      unitBias units i)^2) = ∑ e : Incidence E i, (coefficient K free z i e)^2 := by
  dsimp only
  rw [condition_exposure_history p K hK (knownBefore E free) z,
    expect_tensor,expect_tensor,expect_point,expect_point]
  exact ⟨conditional_delta_mean K units free i hi z,conditional_delta_variance K units free i hi z⟩

theorem exposure_variance_bound (p : E → PairLaw m κ) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (p e).law)).mass K) (hp : ∀ e, present (K e))
    (units : List (Literal n)) (free : Finset (Fin n)) (z : ExposureBit E → Bool) (i : Fin n) :
    (∑ e : Incidence E i, (coefficient K free z i e)^2) ≤
      (m:ℝ)^2 * (Random.neighbors (generate E (sampled K z) units) i).card :=
  variance_observed_degree K (base_pattern_bound p K hK) hp units free z i

theorem retained_base_present (p : E → PairLaw m κ)
    (hp : ∀ e, 0 < prob (p e).law present) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (retained (p e) (hp e)).law)).mass K) :
    ∀ e, present (K e) := by
  intro e
  have hn : (∏ f, (retained (p f) (hp f)).law.mass (K f)) ≠ 0 := ne_of_gt hK
  have he := (Finset.prod_ne_zero_iff.mp hn) e (Finset.mem_univ e)
  have hm : 0 < (retained (p e) (hp e)).law.mass (K e) :=
    lt_of_le_of_ne ((retained (p e) (hp e)).law.nonneg _) (Ne.symm he)
  exact condition_support (p e).law present (hp e) (K e) hm

/-- This is exactly the transition made by the fixed-order recursive
algorithm, with the just-assigned head removed from the list of free labels. -/
theorem list_history_step (is : List (Fin n)) (i : Fin n) (hi : i ∉ is) :
    knownBefore E is.toFinset =
      insert (Sum.inl i) (knownAfterSigns E (i::is).toFinset i) := by
  have hh := history_step (E:=E) (i::is).toFinset i
  simpa [hi] using hh

private theorem delta_restrict_units (F : Formula n) (outer free : Finset (Fin n))
    (base x : Assignment n) (i : Fin n) (hi : i ∈ free) (ho : i ∈ outer)
    (hpair : ∀ a b, .pair a b ∈ F → a.var ∈ outer ∧ b.var ∈ outer) :
    delta (Residual.restrict outer base F).1 free x i = delta F free x i := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have ht := ih (fun a b h => hpair a b (by simp [h]))
    change delta ((Residual.clause outer base c).1 ++ (Residual.restrict outer base F).1) free x i = _
    rw [delta_append,ht]
    have hc : delta (Residual.clause outer base c).1 free x i = delta [c] free x i := by
      cases c with
      | unit a =>
        by_cases ha : a.var ∈ outer
        · simp [Residual.clause,ha]
        · have hn : a.var ≠ i := by intro he; exact ha (he ▸ ho)
          simp only [Residual.clause,ha,↓reduceIte,delta_unit a free x i hi,hn]
          simp [delta,Residual.restrict,Bias.gap,d1,d2]
      | pair a b =>
        have hh := hpair a b (by simp)
        simp [Residual.clause,hh.1,hh.2]
    rw [hc]
    exact (delta_append [c] F free x i).symm

theorem delta_core (F : Formula n) (free : Finset (Fin n)) (x : Assignment n)
    (i : Fin n) (hi : i ∈ free) (ha : i ∈ Random.active F) :
    delta (Random.core F) free x i = delta F free x i := by
  apply delta_restrict_units F _ free _ x i hi ha
  intro a b h
  constructor
  · exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨.pair a b,h,by simp [Random.clauseVars]⟩)
  · exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨.pair a b,h,by simp [Random.clauseVars]⟩)

/-- The preferred value of the actual initialized algorithm is the sign
of the exposed sum, including the arbitrary fixed unit-clause bias. -/
theorem algorithm_exposure (E : Finset (Edge n)) (K : E → Pattern m)
    (units : List (Literal n)) (free : List (Fin n)) (z : ExposureBit E → Bool)
    (i : Fin n) (hi : i ∈ free)
    (ha : i ∈ Random.active (generate E (sampled K z) units)) :
    (Random.branchLiteral (preprocess (Random.core (generate E (sampled K z) units))).1
      free (assignment z) i).positive =
    decide (0 ≤ unitBias units i +
      ∑ e : Incidence E i, sign (z (current i e))*coefficient K free.toFinset z i e) := by
  have hc : wellFormed (Random.core (generate E (sampled K z) units)) :=
    Residual.restrict_wellFormed _ _ _ (generate_wellFormed E _ units)
  rw [branch_preference,delta_preprocess _ hc,
    delta_core _ _ _ _ (by simpa using hi) ha,
    delta_exposure E K units _ z i (by simpa using hi)]

end
end Max2SAT.RandomInput
