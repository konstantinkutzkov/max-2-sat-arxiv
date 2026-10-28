import Max2SAT.IndependentPairs.InputMembership
import Max2SAT.Random.IntegerMoments

/-! The independent-pair criterion on an arbitrary probability space.
Bounded integer coefficients automatically have a finite alphabet; neither
the probability space nor its probabilities need to be finite or rational. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput MeasureTheory ProbabilityTheory
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem empirical_integer_membership
    (bvh : External.BandeiraVanHandel n)
    (ledoux : ∀ (α : Type) [Fintype α], External.LedouxUpperTail (Edge n) α)
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]
    (J : Edge n → Ω → ℤ) (hJ : ∀ e, Measurable (J e)) (hi : iIndepFun J μ₀)
    (B ν χ τ μ : ℝ) (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hm : ∀ e, (∫ ω, (J e ω:ℝ) ∂μ₀)=μ)
    (hb : ∀ e, ∀ᵐ ω ∂μ₀, |(J e ω:ℝ)-μ|≤B)
    (hv : ∀ e, ν≤variance (fun ω => (J e ω:ℝ)) μ₀ ∧
      variance (fun ω => (J e ω:ℝ)) μ₀≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*|μ|^2)≤n*ν) :
    1-1/(n:ℝ)≤μ₀.real {ω | membershipGood
      (fun e => (J e ω:ℝ)-empiricalMean (fun e => (J e ω:ℝ))) τ χ
      |empiricalMean (fun e => (J e ω:ℝ))|} := by
  obtain ⟨K,hK⟩ := integer_common_bound μ₀ J (fun _ => μ) B hb
  let p := fun e => integerLaw μ₀ (J e) (hJ e) K
  have hh := empirical_input_membership bvh (ledoux _) p (fun _ z => ((z:ℤ):ℝ))
    B ν χ τ μ hν hχ hτ hτ1 hn
    (fun e => (integer_expect μ₀ (J e) (hJ e) K (hK e) (fun z => (z:ℝ))).trans (hm e))
    (fun e z hz => integer_support μ₀ (J e) (hJ e) K (hK e)
      (fun z => |(z:ℝ)-μ|≤B) (hb e) z hz)
    (by intro e; rw [integer_variance μ₀ (J e) (hJ e) K (hK e) μ (hm e)]; exact hv e) hd
  exact hh.trans_eq (independent_integer_event μ₀ J hJ hi K hK
    (fun z => membershipGood (fun e => (z e:ℝ)-empiricalMean (fun e => (z e:ℝ)))
      τ χ |empiricalMean (fun e => (z e:ℝ))|))

theorem supplied_integer_membership
    (bvh : External.BandeiraVanHandel n)
    (ledoux : ∀ (α : Type) [Fintype α], External.LedouxUpperTail (Edge n) α)
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]
    (J : Edge n → Ω → ℤ) (hJ : ∀ e, Measurable (J e)) (hi : iIndepFun J μ₀)
    (P : Edge n → ℝ) (B ν χ τ σ : ℝ)
    (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1) (hσ : 0≤σ)
    (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hm : ∀ e, (∫ ω, (J e ω:ℝ) ∂μ₀)=P e)
    (hb : ∀ e, ∀ᵐ ω ∂μ₀, |(J e ω:ℝ)-P e|≤B)
    (hv : ∀ e, ν≤variance (fun ω => (J e ω:ℝ)) μ₀ ∧
      variance (fun ω => (J e ω:ℝ)) μ₀≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2)≤n*ν) :
    1-1/(n:ℝ)≤μ₀.real {ω | membershipGood (fun e => (J e ω:ℝ)-P e) τ χ σ} := by
  obtain ⟨K,hK⟩ := integer_common_bound μ₀ J P B hb
  let p := fun e => integerLaw μ₀ (J e) (hJ e) K
  have hh := supplied_input_membership bvh (ledoux _) p (fun _ z => ((z:ℤ):ℝ)) P
    B ν χ τ σ hν hχ hτ hτ1 hσ hn
    (fun e => (integer_expect μ₀ (J e) (hJ e) K (hK e) (fun z => (z:ℝ))).trans (hm e))
    (fun e z hz => integer_support μ₀ (J e) (hJ e) K (hK e)
      (fun z => |(z:ℝ)-P e|≤B) (hb e) z hz)
    (by intro e; rw [integer_variance μ₀ (J e) (hJ e) K (hK e) (P e) (hm e)]; exact hv e) hd
  exact hh.trans_eq (independent_integer_event μ₀ J hJ hi K hK
    (fun z => membershipGood (fun e => (z e:ℝ)-P e) τ χ σ))

end
end Max2SAT.IndependentPairs
