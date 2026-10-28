import Max2SAT.IndependentPairs.ScalarEvent

/-! Independent Bernoulli edges, including inhomogeneous edge probabilities.
This instantiates the scalar estimates for the Max-Cut interactions used
by the stochastic block model. It does not prove a matrix-norm or discovery
result. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput

def bernoulli (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) : Law Bool where
  mass b := if b then q else 1-q
  nonneg b := by cases b <;> simp [hq0,sub_nonneg.mpr hq1]
  total := by simp

def cutInteraction (b : Bool) : ℝ := if b then -2 else 0

def centeredCut (q : ℝ) (b : Bool) : ℝ := cutInteraction b+2*q

theorem cut_interaction_mean (q : ℝ) (h0 : 0≤q) (h1 : q≤1) :
    expect (bernoulli q h0 h1) cutInteraction= -2*q := by
  simp [expect,bernoulli,cutInteraction]; ring

theorem centered_cut_mean (q : ℝ) (h0 : 0≤q) (h1 : q≤1) :
    expect (bernoulli q h0 h1) (centeredCut q)=0 := by
  change expect _ (fun b => cutInteraction b+2*q)=0
  rw [expect_add,cut_interaction_mean,expect_const]
  ring

theorem centered_cut_bound (q : ℝ) (h0 : 0≤q) (h1 : q≤1) (b : Bool) :
    |centeredCut q b|≤2 := by
  cases b <;> simp only [centeredCut,cutInteraction,Bool.false_eq_true,↓reduceIte,zero_add]
  all_goals exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem centered_cut_variance (q : ℝ) (h0 : 0≤q) (h1 : q≤1) :
    expect (bernoulli q h0 h1) (fun b => (centeredCut q b)^2)=4*q*(1-q) := by
  simp [expect,bernoulli,centeredCut,cutInteraction]; ring

/-- The complete simultaneous scalar event for the actual independent
Bernoulli graph model. Blocks may determine q, but are not needed for
these scalar estimates. -/
theorem bernoulli_scalar_event {n : ℕ} (q : Edge n → ℝ)
    (hq0 : ∀ e, 0≤q e) (hq1 : ∀ e, q e≤1)
    (hn : 2≤n) (ν χ a : ℝ) (S : Finset (Fin n))
    (hν : 0<ν) (hχ : 1≤χ) (ha : 0<a)
    (haSmall : 2*a≤2*(χ*ν)) (haShift : a≤(1/1000:ℝ)*Real.sqrt ν)
    (hS : ∀ t∈S, 0<t.val)
    (hvar : ∀ e, ν≤4*q e*(1-q e) ∧ 4*q e*(1-q e)≤χ*ν) :
    prob (product (fun e => bernoulli (q e) (hq0 e) (hq1 e)))
      (fun x => ¬scalarGood (fun e => cutInteraction (x e)+2*q e) ν χ a S)≤
      scalarFailureBound n 2 ν χ a S := by
  apply scalar_event_probability _ (fun e => centeredCut (q e)) hn 2 ν χ a S
    (by norm_num) hν hχ ha (by linarith) haShift hS
  · intro e; exact centered_cut_mean _ _ _
  · intro e x _; exact centered_cut_bound _ (hq0 e) (hq1 e) x
  · intro e; simpa only [centered_cut_variance] using hvar e

end
end Max2SAT.IndependentPairs
