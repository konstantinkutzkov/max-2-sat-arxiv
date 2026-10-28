import Max2SAT.IndependentPairs.MembershipProbability
import Max2SAT.IndependentPairs.MatrixNorm

/-! The membership conditions and their joint high-probability conclusion.
The only external hypotheses are the two published matrix theorems.
Sampling is over arbitrary finite product laws. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {n : ℕ} {α : Type*} [Fintype α]

/-- Exactly the three inequalities in equation eq:remainder, with K=9*chi. -/
def membershipGood (z : Edge n → ℝ) (τ χ σ : ℝ) : Prop :=
  ‖upperMatrix ⌊τ*n⌋₊ z‖^2≤9*χ*pairEnergy z ∧
  4*Real.sqrt 3*(membershipGap τ χ)*n*Real.sqrt (pairEnergy z)≤rowProfile z ⌊τ*n⌋₊ ∧
  σ≤membershipGap τ χ*Real.sqrt (pairEnergy z)/(8*τ)

theorem membership_of_bounds (z : Edge n → ℝ) (τ ν χ σ : ℝ)
    (hn : 100≤n) (hτ : 0<τ) (hτ1 : τ<1) (hN : 1000≤τ*n)
    (hν : 0≤ν) (hχ : 1≤χ)
    (henergy : (98/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy z ∧
      pairEnergy z≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν)
    (hrows : ∀ t∈lateRows n τ, (993/1000:ℝ)*Real.sqrt (t.val*ν)≤Real.sqrt (earlierEnergy z t))
    (hnorm : ‖upperMatrix ⌊τ*n⌋₊ z‖^2≤9*χ*pairEnergy z)
    (hbudget : 100000*χ*σ^2≤τ*n*ν) : membershipGood z τ χ σ := by
  have hn1 : 0≤(n:ℝ)-1 := by exact_mod_cast (show 0≤(n:ℤ)-1 by omega)
  have hD : 0≤pairEnergy z := (show 0≤(98/100:ℝ)*((n:ℝ)-1)*ν by positivity).trans henergy.1
  have hcap : pairEnergy z≤(101/100:ℝ)*n*χ*ν := by
    have hh : 0≤χ*ν := by positivity
    nlinarith [henergy.2]
  have ht := profile_target n τ ν χ (pairEnergy z) hτ hν hχ hD hcap
  have hr := row_profile_lower z τ ν hτ hτ1 hN hν hrows
  have hnon : 0≤(τ*n)*Real.sqrt (τ*n)*Real.sqrt ν := by positivity
  exact ⟨hnorm,by nlinarith,comparison_allowance n τ ν χ _ σ hn hτ hν hχ henergy.1 hbudget⟩

theorem success_of_failure (p : Law α) (P : α → Prop) (q : ℝ)
    (h : prob p (fun x => ¬P x)≤q) : 1-q≤prob p P := by
  have hid : prob p P+prob p (fun x => ¬P x)=1 := by
    unfold prob
    rw [←Finset.sum_add_distrib]
    calc
      _ = ∑ x, p.mass x := Finset.sum_congr rfl (by intro x _; by_cases hx:P x <;> simp [hx])
      _ = 1 := p.total
  linarith

/-- Empirical centering: all three conditions, not just the matrix event,
hold jointly with probability at least 1-1/n under the paper assumptions. -/
theorem empirical_membership
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (B ν χ τ μ : ℝ)
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧ expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*|μ|^2)≤n*ν) :
    1-1/(n:ℝ)≤prob (product p) (fun x =>
      membershipGood (fun e => X e (x e)-empiricalMean (fun e => X e (x e))) τ χ
        |μ+empiricalMean (fun e => X e (x e))|) := by
  have hsize := membership_size n χ τ hχ hτ hτ1 hn
  have : Nonempty (Edge n) := Fintype.card_pos_iff.mp (pair_count_positive (by omega : 2≤n))
  obtain ⟨e⟩ := ‹Nonempty (Edge n)›
  have hνB := variance_le_bound (p e) (X e) ν B (hv e).1 (hb e)
  have hbud := membership_budgets n B ν χ τ |μ| (by omega) hν hχ hτ hνB hd
  have ha := mean_radius_bounds n B ν χ τ hsize.1 hB hν hχ hτ hτ1 hbud.1 hbud.2.2
  have hnormD := matrix_density_from_paper n B ν χ τ |μ| (by omega) hν.le hχ hτ hτ1 hd
  have hevent := scalar_operator_event bvh ledoux p X ⌊τ*n⌋₊ hsize.1 B ν χ
    (meanRadius n ν χ) (lateRows n τ) hB hν hχ ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    (late_rows_positive τ hsize.2.1) hm hb hv hnormD
  have htotal := membership_failure_bound n B ν χ τ hsize.1 hB hν hχ hτ hτ1 hbud.2.2
  apply success_of_failure
  apply le_trans (prob_mono_support (product p) _ _ ?_) (hevent.trans htotal)
  intro x _ hx hg
  apply hx
  apply membership_of_bounds _ τ ν χ _ hsize.1 hτ hτ1 hsize.2.1 hν.le hχ
    hg.1.2.1 hg.1.2.2 hg.2
  apply comparison_budget n ν χ τ |μ| _ hsize.1 hν.le hχ hτ hsize.2.2 (abs_nonneg μ)
    _ hbud.1 hbud.2.1
  rw [abs_abs]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hg.1.1)

/-- Scalar good event before any empirical shift. -/
def rawScalarGood (z : Edge n → ℝ) (ν χ : ℝ) (S : Finset (Fin n)) : Prop :=
  ((98/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy z ∧
    pairEnergy z≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν) ∧
  ∀ t∈S, (993/1000:ℝ)*Real.sqrt (t.val*ν)≤Real.sqrt (earlierEnergy z t)

theorem raw_scalar_event_probability (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (hn : 2≤n) (B ν χ a : ℝ) (S : Finset (Fin n))
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (hS : ∀ t∈S, 0<t.val)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧ expect (p e) (fun x => (X e x)^2)≤χ*ν) :
    prob (product p) (fun x => ¬rawScalarGood (fun e => X e (x e)) ν χ S)≤
      scalarFailureBound n B ν χ a S := by
  let z := fun (x : Edge n → α) e => X e (x e)
  let energyBad := fun x => pairEnergy (z x)<(99/100:ℝ)*((n:ℝ)-1)*ν ∨
    (101/100:ℝ)*((n:ℝ)-1)*χ*ν<pairEnergy (z x)
  let rowBad := fun t x => earlierEnergy (z x) t≤(99/100:ℝ)*t.val*ν
  have henergy := raw_energy_tails p X hn B ν χ (1/100) hB hν hχ
    (by norm_num) (by norm_num) hb hv
  have hrow : ∀ t∈S, prob (product p) (rowBad t)≤
      Real.exp (-(1/100:ℝ)^2*t.val*ν/(4*B^2*χ)) := by
    intro t ht
    simpa only [rowBad,z,show (1:ℝ)-1/100=99/100 by norm_num] using
      earlier_energy_tail p X t (hS t ht) B ν χ (1/100) hB hν hχ
        (by norm_num) (by norm_num) hb hv
  have hrows := (Counts.finite_union_bound (product p) S rowBad).trans (Finset.sum_le_sum hrow)
  have hsub := prob_mono_support (product p)
    (fun x => ¬rawScalarGood (z x) ν χ S)
    (fun x => energyBad x ∨ ∃ t∈S, rowBad t x) (by
      intro x _ hbad
      by_contra h
      have hlo : (99/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy (z x) := by
        by_contra hh; exact h (Or.inl (Or.inl (lt_of_not_ge hh)))
      have hhi : pairEnergy (z x)≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν := by
        by_contra hh; exact h (Or.inl (Or.inr (lt_of_not_ge hh)))
      have hr : ∀ t∈S, (99/100:ℝ)*t.val*ν≤earlierEnergy (z x) t := by
        intro t ht
        by_contra hh; exact h (Or.inr ⟨t,ht,le_of_lt (lt_of_not_ge hh)⟩)
      apply hbad
      refine ⟨⟨?_,hhi⟩,?_⟩
      · have hn1 : 0≤(n:ℝ)-1 := by exact_mod_cast (show 0≤(n:ℤ)-1 by omega)
        nlinarith [mul_nonneg hn1 hν.le]
      · intro t ht
        simpa using earlier_shift_lower (z x) t 0 ν hν.le (hr t ht) (by simp))
  have he : prob (product p) energyBad≤
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ))+
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2)) := by
    simpa only [energyBad,z,show (1:ℝ)-1/100=99/100 by norm_num,
      show (1:ℝ)+1/100=101/100 by norm_num] using henergy
  apply (hsub.trans ((prob_union_le _ _ _).trans (add_le_add he hrows))).trans
  unfold scalarFailureBound
  have hh := Real.exp_pos (-(Fintype.card (Edge n):ℝ)*a^2/(4*(χ*ν)))
  linarith

theorem raw_operator_event
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ)
    (hn : 100≤n) (B ν χ a : ℝ) (S : Finset (Fin n))
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (hS : ∀ t∈S, 0<t.val)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧ expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hdensity : (10^9:ℝ)*B^2*Real.log n≤n*χ*ν) :
    prob (product p) (fun x => ¬(rawScalarGood (fun e => X e (x e)) ν χ S ∧
      ‖upperMatrix T (fun e => X e (x e))‖^2≤9*χ*pairEnergy (fun e => X e (x e))))≤
      scalarFailureBound n B ν χ a S+1/(n:ℝ)^3 := by
  have hscalar := raw_scalar_event_probability p X (by omega) B ν χ a S hB hν hχ hS hb hv
  have hnorm := independent_pair_norm_tail bvh ledoux p X T (by omega) B ν χ
    hB hν (by linarith) hm hb (fun e => (hv e).2) hdensity
  have hsub := prob_mono_support (product p)
    (fun x => ¬(rawScalarGood (fun e => X e (x e)) ν χ S ∧
      ‖upperMatrix T (fun e => X e (x e))‖^2≤9*χ*pairEnergy (fun e => X e (x e))))
    (fun x => ¬rawScalarGood (fun e => X e (x e)) ν χ S ∨
      (290/100:ℝ)*Real.sqrt (n*χ*ν)<‖upperMatrix T (fun e => X e (x e))‖) (by
      intro x _ hx
      by_contra hh
      have hg : rawScalarGood (fun e => X e (x e)) ν χ S := by tauto
      have hr : ‖upperMatrix T (fun e => X e (x e))‖≤(290/100:ℝ)*Real.sqrt (n*χ*ν) := by
        by_contra h; exact hh (Or.inr (lt_of_not_ge h))
      apply hx
      refine ⟨hg,?_⟩
      apply operator_energy_bound T _ _ χ ν hn (by linarith) hν.le hg.1.1
      nlinarith [Real.sqrt_nonneg (n*χ*ν)])
  exact hsub.trans ((prob_union_le _ _ _).trans (add_le_add hscalar hnorm))

/-- Supplied mean: the same membership guarantee for centered entries X=J-P. -/
theorem supplied_membership
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (B ν χ τ σ : ℝ)
    (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ) (hτ : 0<τ) (hτ1 : τ<1)
    (hσ : 0≤σ) (hn : (10^9:ℝ)*χ^2/τ^2≤n)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧ expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ/τ*(B^2*Real.log n+χ*σ^2)≤n*ν) :
    1-1/(n:ℝ)≤prob (product p) (fun x => membershipGood (fun e => X e (x e)) τ χ σ) := by
  have hsize := membership_size n χ τ hχ hτ hτ1 hn
  have : Nonempty (Edge n) := Fintype.card_pos_iff.mp (pair_count_positive (by omega : 2≤n))
  obtain ⟨e⟩ := ‹Nonempty (Edge n)›
  have hνB := variance_le_bound (p e) (X e) ν B (hv e).1 (hb e)
  have hbud := membership_budgets n B ν χ τ σ (by omega) hν hχ hτ hνB hd
  have hnormD := matrix_density_from_paper n B ν χ τ σ (by omega) hν.le hχ hτ hτ1 hd
  have hevent := raw_operator_event bvh ledoux p X ⌊τ*n⌋₊ hsize.1 B ν χ
    (meanRadius n ν χ) (lateRows n τ) hB hν hχ (late_rows_positive τ hsize.2.1) hm hb hv hnormD
  have htotal := membership_failure_bound n B ν χ τ hsize.1 hB hν hχ hτ hτ1 hbud.2.2
  have hσbudget := comparison_budget n ν χ τ σ σ hsize.1 hν.le hχ hτ hsize.2.2 hσ
    (by
      rw [abs_of_nonneg hσ]
      have h : 0≤meanRadius n ν χ := by unfold meanRadius; positivity
      linarith)
    hbud.1 hbud.2.1
  apply success_of_failure
  apply le_trans (prob_mono_support (product p) _ _ ?_) (hevent.trans htotal)
  intro x _ hx hg
  exact hx (membership_of_bounds _ τ ν χ σ hsize.1 hτ hτ1 hsize.2.1 hν.le hχ
    hg.1.1 hg.1.2 hg.2 hσbudget)

end
end Max2SAT.IndependentPairs
