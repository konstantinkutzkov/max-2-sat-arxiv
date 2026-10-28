import Max2SAT.IndependentPairs.Membership
import Max2SAT.IndependentPairs.Bernoulli

/-! Translate from the original sampled coefficients, so the formal event
uses exactly J minus its empirical or supplied mean. Also instantiate
independent Bernoulli graph edges; community discovery is a separate task. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
variable {n : ℕ} {α : Type*} [Fintype α]

/-- The formal gap constant is the paper's tau^(3/2)/(12 sqrt chi). -/
theorem membership_gap_rpow (τ χ : ℝ) (hτ : 0<τ) :
    membershipGap τ χ=τ^(3/2:ℝ)/(12*Real.sqrt χ) := by
  have hpow : τ^(3/2:ℝ)=τ*Real.sqrt τ := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hτ,Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [hpow]; rfl

/-- Empirical case, stated for J and its common mean mu. The event contains
J-beta, and its allowance is |beta|, not an independent replacement for beta. -/
theorem empirical_input_membership
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (J : Edge n → α → ℝ) (B ν χ τ μ : ℝ)
    (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hm : ∀ e, expect (p e) (J e)=μ)
    (hb : ∀ e x, 0<(p e).mass x → |J e x-μ|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (J e x-μ)^2) ∧
      expect (p e) (fun x => (J e x-μ)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*|μ|^2)≤n*ν) :
    1-1/(n:ℝ)≤prob (product p) (fun x =>
      membershipGood (fun e => J e (x e)-empiricalMean (fun e => J e (x e))) τ χ
        |empiricalMean (fun e => J e (x e))|) := by
  have hsize := membership_size n χ τ hχ hτ hτ1 hn
  have : Nonempty (Edge n) := Fintype.card_pos_iff.mp (pair_count_positive (by omega : 2≤n))
  obtain ⟨e⟩ := ‹Nonempty (Edge n)›
  have hB := bound_positive (p e) (fun x => J e x-μ) ν B hν (hv e).1 (hb e)
  have h := empirical_membership bvh ledoux p (fun e x => J e x-μ) B ν χ τ μ
    hB hν hχ hτ hτ1 hn (by intro e; simp [expect_sub,hm e]) hb hv hd
  have hid : ∀ a : ℝ, μ+(a-μ)=a := by intro a; ring
  simpa only [empirical_mean_shift,sub_sub_sub_cancel_right,hid] using h

/-- Supplied case: P is fixed and equals the entrywise expectation. Its
representation coefficient sum is sigma; no random empirical mean is used. -/
theorem supplied_input_membership
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (J : Edge n → α → ℝ) (P : Edge n → ℝ) (B ν χ τ σ : ℝ)
    (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hσ : 0≤σ) (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hm : ∀ e, expect (p e) (J e)=P e)
    (hb : ∀ e x, 0<(p e).mass x → |J e x-P e|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (J e x-P e)^2) ∧
      expect (p e) (fun x => (J e x-P e)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2)≤n*ν) :
    1-1/(n:ℝ)≤prob (product p) (fun x => membershipGood (fun e => J e (x e)-P e) τ χ σ) := by
  have hsize := membership_size n χ τ hχ hτ hτ1 hn
  have : Nonempty (Edge n) := Fintype.card_pos_iff.mp (pair_count_positive (by omega : 2≤n))
  obtain ⟨e⟩ := ‹Nonempty (Edge n)›
  have hB := bound_positive (p e) (fun x => J e x-P e) ν B hν (hv e).1 (hb e)
  exact supplied_membership bvh ledoux p (fun e x => J e x-P e) B ν χ τ σ
    hB hν hχ hτ hτ1 hσ hn (by intro e; simp [expect_sub,hm e]) hb hv hd

/-- Inhomogeneous independent graph edges, including a supplied SBM mean.
This proves membership for the centered Max-Cut interaction, not recovery
of the unknown mean representation or the final hidden-community algorithm. -/
theorem bernoulli_supplied_membership
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) Bool)
    (q : Edge n → ℝ) (hq0 : ∀ e, 0≤q e) (hq1 : ∀ e, q e≤1)
    (ν χ τ σ : ℝ) (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hσ : 0≤σ) (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hv : ∀ e, ν≤4*q e*(1-q e) ∧ 4*q e*(1-q e)≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(4*Real.log n+χ*σ^2)≤n*ν) :
    1-1/(n:ℝ)≤prob (product (fun e => bernoulli (q e) (hq0 e) (hq1 e)))
      (fun x => membershipGood (fun e => cutInteraction (x e)+2*q e) τ χ σ) := by
  apply supplied_membership bvh ledoux _ (fun e => centeredCut (q e)) 2 ν χ τ σ
    (by norm_num) hν hχ hτ hτ1 hσ hn
  · intro e; exact centered_cut_mean _ _ _
  · intro e x _; exact centered_cut_bound _ (hq0 e) (hq1 e) x
  · intro e; simpa only [centered_cut_variance] using hv e
  · norm_num at hd ⊢; exact hd

/-- Homogeneous independent edges with their empirical interaction mean. -/
theorem bernoulli_empirical_membership
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) Bool)
    (q ν χ τ : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hv : ν≤4*q*(1-q) ∧ 4*q*(1-q)≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(4*Real.log n+χ*(2*q)^2)≤n*ν) :
    1-1/(n:ℝ)≤prob (product (fun _ : Edge n => bernoulli q hq0 hq1))
      (fun x => membershipGood
        (fun e => cutInteraction (x e)-empiricalMean (fun e => cutInteraction (x e))) τ χ
        |empiricalMean (fun e => cutInteraction (x e))|) := by
  apply empirical_input_membership bvh ledoux _ (fun _ => cutInteraction) 2 ν χ τ (-2*q)
    hν hχ hτ hτ1 hn
  · intro e; exact cut_interaction_mean q hq0 hq1
  · intro e x _
    simpa [centeredCut,sub_eq_add_neg] using centered_cut_bound q hq0 hq1 x
  · intro e
    have h : (fun x => (cutInteraction x-(-2*q))^2)=(fun x => (centeredCut q x)^2) := by
      funext x; simp [centeredCut,sub_eq_add_neg]
    rw [h,centered_cut_variance]
    exact hv
  · simpa only [sq_abs,neg_mul,neg_sq,show (2:ℝ)^2=4 by norm_num] using hd

end
end Max2SAT.IndependentPairs
