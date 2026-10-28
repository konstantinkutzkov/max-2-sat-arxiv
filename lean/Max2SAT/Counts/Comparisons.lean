import Max2SAT.Counts.FormulaGains
import Max2SAT.Counts.PrefixSearch

/-! The actual comparisons used after a guess. Preferences use only earlier
rounds; the completed sum is one rational budget on the suffix. -/
namespace Max2SAT.Counts

def earlier (round : Fin n → ℕ) (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => round w<round t)

def preference (H : Fin n → Affine n) (round : Fin n → ℕ)
    (x : Assignment n) (t : Fin n) : Bool :=
  decide (0≤(H t).average (earlier round t) x)

def comparisonExpr (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x : Assignment n) : Affine n :=
  Affine.sum P (fun t => if x t≠preference H round x t then
    ((H t).scale (direction (preference H round x t))).shift (-s t)
    else Affine.zero)

def comparisonBudget (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x : Assignment n) : Weighted.Budget n :=
  (comparisonExpr H s P round x).budget

def EarlierInPrefix (P : Finset (Fin n)) (round : Fin n → ℕ) : Prop :=
  ∀ t∈P, ∀ w, round w<round t → w∈P

theorem preference_agree (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hr : EarlierInPrefix P round)
    (x y : Assignment n) (hxy : ∀ i∈P, x i=y i) (t : Fin n) (ht : t∈P) :
    preference H round x t=preference H round y t := by
  unfold preference
  rw [Affine.average_agree (H t) (earlier round t) x y (by
    intro w hw
    exact hxy w (hr t ht w (Finset.mem_filter.mp hw).2))]

theorem comparison_stable (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (hr : EarlierInPrefix P round) :
    PrefixSearch.Stable (comparisonBudget H s P round) P := by
  intro x y hxy
  have he : comparisonExpr H s P round x=comparisonExpr H s P round y := by
    have hh : ∀ t∈P,
        (if x t≠preference H round x t then
          ((H t).scale (direction (preference H round x t))).shift (-s t) else Affine.zero) =
        (if y t≠preference H round y t then
          ((H t).scale (direction (preference H round y t))).shift (-s t) else Affine.zero) := by
      intro t ht
      rw [hxy t ht,preference_agree H P round hr x y hxy t ht]
    unfold comparisonExpr Affine.sum
    congr 1
    · exact Finset.sum_congr rfl (fun t ht => congrArg Affine.constant (hh t ht))
    · funext j
      exact Finset.sum_congr rfl (fun t ht => congrArg (fun A => A.coeff j) (hh t ht))
  simp only [comparisonBudget,he]

theorem comparison_budget_iff (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x y : Assignment n) :
    (comparisonBudget H s P round x).Holds y ↔
      (∑ t∈P, if x t≠preference H round x t then
        direction (preference H round x t)*(H t).eval y-s t else 0)≤0 := by
  simp only [comparisonBudget,Affine.budget_holds,comparisonExpr,Affine.eval_sum]
  have he : ∀ t,
      (if x t≠preference H round x t then
        ((H t).scale (direction (preference H round x t))).shift (-s t)
        else Affine.zero).eval y =
      if x t≠preference H round x t then
        direction (preference H round x t)*(H t).eval y-s t else 0 := by
    intro t
    split_ifs <;> simp [sub_eq_add_neg]
  simp only [he]

theorem oriented_approximation (p : Bool) (G H s : ℚ)
    (hG : direction p*G≤0) (herror : |G-H|≤s) : direction p*H≤s := by
  have hb := (abs_le.mp herror)
  cases p <;> norm_num [direction] at hG ⊢ <;> linarith

/-- Every optimum, not just a tie-broken representative, satisfies the sum
whenever this guess has valid error allowances at that optimum. -/
theorem optimum_satisfies (F : Formula n) (H : Fin n → Affine n) (s : Fin n → ℚ)
    (P : Finset (Fin n)) (round : Fin n → ℕ) (x : Assignment n)
    (hx : ∀ y, score F y≤score F x)
    (herr : ∀ t∈P, |scoreGain F t x-(H t).eval x|≤s t) :
    (comparisonBudget H s P round x).Holds x := by
  rw [comparison_budget_iff]
  apply Finset.sum_nonpos
  intro t ht
  split_ifs with h
  · exact sub_nonpos.mpr (oriented_approximation _ _ _ _
      (optimal_oriented_gain F x hx t _ h) (herr t ht))
  · exact le_refl _

end Max2SAT.Counts
