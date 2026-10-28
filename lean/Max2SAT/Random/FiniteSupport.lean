import Max2SAT.Random.MeasureInput

/-! Encoding a bounded integer observation by a finite alphabet changes
neither its distribution nor its moments, even on an infinite sample space. -/
namespace Max2SAT.FiniteLaw
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

def boundedInteger (K : ℕ) (z : ℤ) : ↥(Finset.Icc (-(K:ℤ)) K) :=
  if h : z ∈ Finset.Icc (-(K:ℤ)) K then ⟨z,h⟩
  else ⟨0,by simp⟩

theorem bounded_integer_eq (K : ℕ) (z : ℤ) (hz : |z|≤K) :
    (boundedInteger K z : ℤ)=z := by
  have hh : z ∈ Finset.Icc (-(K:ℤ)) K := by simpa using abs_le.mp hz
  simp [boundedInteger,hh]

omit [DecidableEq ι] in
theorem integer_common_bound (μ : Measure Ω) (J : ι → Ω → ℤ)
    (a : ι → ℝ) (B : ℝ) (hb : ∀ i, ∀ᵐ ω ∂μ, |(J i ω:ℝ)-a i|≤B) :
    ∃ K : ℕ, ∀ i, ∀ᵐ ω ∂μ, |J i ω|≤(K:ℤ) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (B+∑ i, |a i|)
  refine ⟨K,fun i => ?_⟩
  filter_upwards [hb i] with ω hω
  have ha : |a i|≤∑ j, |a j| := Finset.single_le_sum
    (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hh : |(J i ω:ℝ)|≤(K:ℝ) := by
    have ht := abs_add_le ((J i ω:ℝ)-a i) (a i)
    have he : (J i ω:ℝ)-a i+a i=(J i ω:ℝ) := by ring
    rw [he] at ht
    linarith
  exact_mod_cast hh

omit [Fintype ι] [DecidableEq ι] in
theorem integer_encoding (μ : Measure Ω) (J : ι → Ω → ℤ)
    (hJ : ∀ i, Measurable (J i)) (hi : iIndepFun J μ)
    (K : ℕ) (hK : ∀ i, ∀ᵐ ω ∂μ, |J i ω|≤(K:ℤ)) :
    (∀ i, Measurable (fun ω => boundedInteger K (J i ω))) ∧
    iIndepFun (fun i ω => boundedInteger K (J i ω)) μ ∧
    ∀ i, ∀ᵐ ω ∂μ, (boundedInteger K (J i ω):ℤ)=J i ω := by
  have hm : Measurable (boundedInteger K) := measurable_of_countable _
  exact ⟨fun i => hm.comp (hJ i),hi.comp (fun _ => boundedInteger K) (fun _ => hm),
    fun i => (hK i).mono (fun ω hω => bounded_integer_eq K (J i ω) hω)⟩

def integerLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → ℤ) (hJ : Measurable J) (K : ℕ) : Law ↥(Finset.Icc (-(K:ℤ)) K) :=
  coordinateLaw μ (fun ω => boundedInteger K (J ω))
    ((measurable_of_countable (boundedInteger K)).comp hJ)

theorem integer_expect (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → ℤ) (hJ : Measurable J) (K : ℕ)
    (hK : ∀ᵐ ω ∂μ, |J ω|≤(K:ℤ)) (f : ℤ → ℝ) :
    expect (integerLaw μ J hJ K) (fun z => f z)=∫ ω, f (J ω) ∂μ := by
  rw [integerLaw,coordinate_expect]
  apply integral_congr_ae
  exact hK.mono (fun ω hω => congrArg f (bounded_integer_eq K (J ω) hω))

theorem integer_support (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → ℤ) (hJ : Measurable J) (K : ℕ)
    (hK : ∀ᵐ ω ∂μ, |J ω|≤(K:ℤ)) (P : ℤ → Prop)
    (hP : ∀ᵐ ω ∂μ, P (J ω)) (z : ↥(Finset.Icc (-(K:ℤ)) K))
    (hz : 0<(integerLaw μ J hJ K).mass z) : P z := by
  apply coordinate_support μ (fun ω => boundedInteger K (J ω))
    ((measurable_of_countable (boundedInteger K)).comp hJ)
    (fun z : ↥(Finset.Icc (-(K:ℤ)) K) => P (z:ℤ)) _ z hz
  filter_upwards [hK,hP] with ω hk hp
  simpa only [bounded_integer_eq K (J ω) hk] using hp

theorem independent_integer_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → ℤ) (hJ : ∀ i, Measurable (J i)) (hi : iIndepFun J μ)
    (K : ℕ) (hK : ∀ i, ∀ᵐ ω ∂μ, |J i ω|≤(K:ℤ)) (P : (ι → ℤ) → Prop) :
    prob (product (fun i => integerLaw μ (J i) (hJ i) K))
      (fun z => P (fun i => z i)) = μ.real {ω | P (fun i => J i ω)} := by
  obtain ⟨hm,he,ha⟩ := integer_encoding μ J hJ hi K hK
  rw [show product (fun i => integerLaw μ (J i) (hJ i) K)=
    product (fun i => coordinateLaw μ (fun ω => boundedInteger K (J i ω)) (hm i)) from rfl,
    independent_event μ _ hm he]
  apply measureReal_congr
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  have hh : (fun i => (boundedInteger K (J i ω):ℤ))=(fun i => J i ω) := funext hω
  simp only [hh]

omit [DecidableEq ι] in
/-- Any event determined by finitely many integer coordinates is measurable,
even when their common sample space is infinite. -/
theorem integer_event_measurable (J : ι → Ω → ℤ)
    (hJ : ∀ i, Measurable (J i)) (P : (ι → ℤ) → Prop) :
    MeasurableSet {ω | P (fun i => J i ω)} :=
  (Set.to_countable {z | P z}).measurableSet.preimage (.of_eval hJ)


end
end Max2SAT.FiniteLaw
