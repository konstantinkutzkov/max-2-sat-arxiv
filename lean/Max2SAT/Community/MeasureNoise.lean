import Max2SAT.Community.RandomEvent
import Max2SAT.Random.IntegerMoments

/-! The discovery noise event for independent bounded integer observations
on an arbitrary probability space, expressed using their original variance. -/
namespace Max2SAT.Community
noncomputable section
open FiniteLaw RandomInput IndependentPairs MeasureTheory ProbabilityTheory
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem integer_noise_probability
    (bvh : External.BandeiraVanHandel n)
    (ledoux : ∀ (α : Type) [Fintype α], External.LedouxUpperTail (Edge n) α)
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]
    (J : Edge n → Ω → ℤ) (hJ : ∀ e, Measurable (J e)) (hi : iIndepFun J μ₀)
    (a : Edge n → ℝ) (B ν χ : ℝ) (hn : 20≤n) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hm : ∀ e, (∫ ω, (J e ω:ℝ) ∂μ₀)=a e)
    (hb : ∀ e, ∀ᵐ ω ∂μ₀, |(J e ω:ℝ)-a e|≤B)
    (hv : ∀ e, ν≤variance (fun ω => (J e ω:ℝ)) μ₀ ∧
      variance (fun ω => (J e ω:ℝ)) μ₀≤χ*ν)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤n*ν) :
    1-1/(n:ℝ)≤μ₀.real {ω | rawGood (fun e => (J e ω:ℝ)-a e) ν χ} := by
  obtain ⟨K,hK⟩ := integer_common_bound μ₀ J a B hb
  let p := fun e => integerLaw μ₀ (J e) (hJ e) K
  have hmean (e : Edge n) : expect (p e) (fun z => ((z:ℤ):ℝ))=a e :=
    (integer_expect μ₀ (J e) (hJ e) K (hK e) (fun z => (z:ℝ))).trans (hm e)
  have hh := discovery_noise_probability bvh (ledoux _) p (fun e z => ((z:ℤ):ℝ)-a e)
    hn B ν χ hB hν hχ (by intro e; simp [expect_sub,hmean e])
    (fun e z hz => integer_support μ₀ (J e) (hJ e) K (hK e)
      (fun z => |(z:ℝ)-a e|≤B) (hb e) z hz)
    (by intro e; rw [integer_variance μ₀ (J e) (hJ e) K (hK e) (a e) (hm e)]; exact hv e) hd
  exact hh.trans_eq (independent_integer_event μ₀ J hJ hi K hK
    (fun z => rawGood (fun e => (z e:ℝ)-a e) ν χ))

end
end Max2SAT.Community
