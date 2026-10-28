import Max2SAT.Counts.Adjustments
import Max2SAT.Counts.Comparisons
import Max2SAT.Counts.Runs

/-! Executable count and projection comparison procedures, with their
correctness tied to actual clause scores and the verified suffix enumeration. -/
namespace Max2SAT.Counts

def countBudget (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (h : ℕ) : Assignment n → Weighted.Budget n :=
  comparisonBudget (countGain F β h) (fun _ => |β|) P round

theorem count_optimum_survives (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) (hF : wellFormed F)
    (hx : ∀ y, score F y≤score F x) :
    ∃ h∈countGuesses n β, (countBudget F β P round h x).Holds x := by
  obtain ⟨h,hh,herr⟩ := exists_count_guess F β x hF
  exact ⟨h,hh,optimum_satisfies F _ _ P round x hx (fun t _ => herr t)⟩

def countSearch (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) : Option (Assignment n) :=
  Runs.solve F (countGuesses n β) (countBudget F β P round) P

theorem countSearch_correct (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hF : wellFormed F) (hr : EarlierInPrefix P round) :
    ∃ x, countSearch F β P round=some x ∧ ∀ y, score F y≤score F x := by
  apply Runs.solve_correct_of_survival
  · intro h _
    exact comparison_stable _ _ P round hr
  · intro x hx
    exact count_optimum_survives F β P round x hF hx

/-- The original variable labels and prefix rounds are retained by preprocessing. -/
def countComparisons (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) : Option (Assignment n) :=
  countSearch (preprocess F).1 β P round

/-- Manuscript Lemma lem:count_correctness, including preprocessing and ties. -/
theorem countComparisons_correct (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hF : wellFormed F) (hr : EarlierInPrefix P round) :
    ∃ x, countComparisons F β P round=some x ∧ ∀ y, score F y≤score F x := by
  obtain ⟨x,hx,ho⟩ := countSearch_correct (preprocess F).1 β P round
    (preprocess_finished F hF).1 hr
  refine ⟨x,hx,?_⟩
  intro y
  rw [preprocess_correct F y,preprocess_correct F x]
  exact add_le_add (le_refl _) (ho y)

def countResult (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) : Option (ℤ × Assignment n) :=
  let (G,s₀) := preprocess F
  (countSearch G β P round).map (fun x => (s₀+score G x,x))

theorem countResult_correct (F : Formula n) (β : ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (hF : wellFormed F) (hr : EarlierInPrefix P round) :
    ∃ q x, countResult F β P round=some (q,x) ∧ q=score F x ∧
      ∀ y, score F y≤q := by
  obtain ⟨x,hx,ho⟩ := countComparisons_correct F β P round hF hr
  refine ⟨score F x,x,?_,rfl,ho⟩
  change countSearch (preprocess F).1 β P round=some x at hx
  simp [countResult,hx,←preprocess_correct F x]

def projectionBudget (F : Formula n) (lam : Fin r → ℚ) (v : Fin r → Fin n → ℚ)
    (δ : Fin r → ℚ) (P : Finset (Fin n)) (round : Fin n → ℕ)
    (guess : Fin r → ℚ) : Assignment n → Weighted.Budget n :=
  comparisonBudget (projectionGain F lam v guess) (allowance lam v δ) P round

theorem projection_optimum_survives (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (guess δ : Fin r → ℚ) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) (hF : wellFormed F)
    (hx : ∀ y, score F y≤score F x)
    (hg : ∀ k, |projection (v k) x-guess k|≤δ k) :
    (projectionBudget F lam v δ P round guess x).Holds x :=
  optimum_satisfies F _ _ P round x hx
    (fun t _ => projection_gain_error_bound F lam v guess δ x t hF hg)

/-- The finite grid list covers every Boolean projection tuple within its errors. -/
def Covers (guesses : List (Fin r → ℚ)) (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ) : Prop :=
  ∀ x : Assignment n, ∃ guess∈guesses, ∀ k, |projection (v k) x-guess k|≤δ k

def projectionComparisons (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ) (guesses : List (Fin r → ℚ))
    (P : Finset (Fin n)) (round : Fin n → ℕ) : Option (Assignment n) :=
  Runs.solve F guesses (projectionBudget F lam v δ P round) P

theorem projection_optimum_enumerated (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ) (guesses : List (Fin r → ℚ))
    (P : Finset (Fin n)) (round : Fin n → ℕ) (hF : wellFormed F)
    (hr : EarlierInPrefix P round) (hcover : Covers guesses v δ)
    (x : Assignment n) (hx : ∀ y, score F y≤score F x) :
    x∈Runs.outputs guesses (projectionBudget F lam v δ P round) P := by
  apply (Runs.mem_outputs guesses (projectionBudget F lam v δ P round) P x
    (fun _ _ => comparison_stable _ _ P round hr)).mpr
  obtain ⟨guess,hg,herr⟩ := hcover x
  exact ⟨guess,hg,projection_optimum_survives F lam v guess δ P round x hF hx herr⟩

/-- Manuscript Lemma lem:counts-exact: rational representations need not be
eigenvectors, and candidates need not match the run's guessed projections. -/
theorem projectionComparisons_correct (F : Formula n) (lam : Fin r → ℚ)
    (v : Fin r → Fin n → ℚ) (δ : Fin r → ℚ) (guesses : List (Fin r → ℚ))
    (P : Finset (Fin n)) (round : Fin n → ℕ) (hF : wellFormed F)
    (hr : EarlierInPrefix P round) (hcover : Covers guesses v δ) :
    ∃ x, projectionComparisons F lam v δ guesses P round=some x ∧
      ∀ y, score F y≤score F x := by
  apply Runs.solve_correct_of_survival
  · intro _ _
    exact comparison_stable _ _ P round hr
  · intro x hx
    obtain ⟨guess,hg,herr⟩ := hcover x
    exact ⟨guess,hg,projection_optimum_survives F lam v guess δ P round x hF hx herr⟩

end Max2SAT.Counts
