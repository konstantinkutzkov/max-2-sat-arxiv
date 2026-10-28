import Max2SAT.Bias.ConstraintEnumeration

/-! Exact rational weighted sums. Each variable has a cost for each Boolean
value. Subtracting their smaller cost is precisely complementary cancellation;
the remaining coefficient is nonnegative. This representation never expands
rational coefficients into repeated occurrences. -/
namespace Max2SAT.Weighted

structure Budget (n : ℕ) where
  cost : Fin n → Bool → ℚ
  bound : ℚ

def Budget.lhs (C : Budget n) (x : Assignment n) : ℚ := ∑ i, C.cost i (x i)
def Budget.Holds (C : Budget n) (x : Assignment n) : Prop := C.lhs x ≤ C.bound
instance (C : Budget n) (x : Assignment n) : Decidable (C.Holds x) :=
  inferInstanceAs (Decidable (C.lhs x ≤ C.bound))

def termCost (a : Literal n) (i : Fin n) (b : Bool) : ℚ :=
  if a.var = i then if b = a.positive then 1 else 0 else 0

theorem termCost_sum (a : Literal n) (x : Assignment n) :
    (∑ i, termCost a i (x i)) = (a.value x : ℚ) := by
  simp [termCost, Literal.value, Literal.eval]

def ofConstraint (C : Constraint n) : Budget n :=
  ⟨fun i b => (C.terms.map (fun a => termCost a i b)).sum, C.bound⟩

theorem ofConstraint_lhs (C : Constraint n) (x : Assignment n) :
    (ofConstraint C).lhs x = (C.lhs x : ℚ) := by
  rcases C with ⟨terms,b⟩
  induction terms with
  | nil => simp [Budget.lhs, ofConstraint, Constraint.lhs]
  | cons a terms ih =>
    simpa [Budget.lhs, ofConstraint, Constraint.lhs, Finset.sum_add_distrib,
      termCost_sum] using congrArg ((a.value x : ℚ) + ·) ih

def sum : List (ℚ × Constraint n) → Budget n
  | [] => ⟨fun _ _ => 0, 0⟩
  | (w,C)::cs =>
    let R := sum cs
    ⟨fun i b => w * (ofConstraint C).cost i b + R.cost i b,
      w * C.bound + R.bound⟩

theorem sum_lhs (cs : List (ℚ × Constraint n)) (x : Assignment n) :
    (sum cs).lhs x = (cs.map (fun wc => wc.1 * (wc.2.lhs x : ℚ))).sum := by
  induction cs with
  | nil => simp [sum, Budget.lhs]
  | cons wc cs ih =>
    rcases wc with ⟨w,C⟩
    change (∑ i, (w * (ofConstraint C).cost i (x i) + (sum cs).cost i (x i))) = _
    rw [Finset.sum_add_distrib, ←Finset.mul_sum]
    change w * (ofConstraint C).lhs x + (sum cs).lhs x = _
    simp [ofConstraint_lhs, ih]

theorem sum_holds (cs : List (ℚ × Constraint n)) (x : Assignment n)
    (hw : ∀ wc ∈ cs, 0 ≤ wc.1) (hc : ∀ wc ∈ cs, wc.2.Holds x) :
    (sum cs).Holds x := by
  induction cs with
  | nil => simp [sum, Budget.Holds, Budget.lhs]
  | cons wc cs ih =>
    rcases wc with ⟨w,C⟩
    have hC : (C.lhs x : ℚ) ≤ C.bound := by exact_mod_cast hc (w,C) (by simp)
    have ht := ih (fun c h => hw c (by simp [h])) (fun c h => hc c (by simp [h]))
    have hm := mul_le_mul_of_nonneg_left hC (hw (w,C) (by simp))
    change (sum ((w,C)::cs)).lhs x ≤ _
    rw [sum_lhs]
    change w * (C.lhs x : ℚ) + (cs.map _).sum ≤ w * C.bound + (sum cs).bound
    rw [←sum_lhs]
    exact add_le_add hm ht

def minimum (C : Budget n) (free : List (Fin n)) (x : Assignment n) : ℚ :=
  ∑ i, if i ∈ free then min (C.cost i false) (C.cost i true) else C.cost i (x i)

def minimizer (C : Budget n) (free : List (Fin n)) (x : Assignment n) : Assignment n :=
  fun i => if i ∈ free then decide (C.cost i true < C.cost i false) else x i

theorem minimum_le (C : Budget n) (free : List (Fin n)) (x y : Assignment n)
    (hc : Compatible free.toFinset x y) : minimum C free x ≤ C.lhs y := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ free
  · simp only [hi, ite_true]
    cases y i
    · exact min_le_left _ _
    · exact min_le_right _ _
  · have he := hc i (by simpa using hi)
    simp [hi,he]

theorem minimizer_compatible (C : Budget n) (free : List (Fin n)) (x : Assignment n) :
    Compatible free.toFinset x (minimizer C free x) := by
  intro i hi
  have hh : i ∉ free := by simpa using hi
  simp [minimizer,hh]

theorem minimizer_lhs (C : Budget n) (free : List (Fin n)) (x : Assignment n) :
    C.lhs (minimizer C free x) = minimum C free x := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ free
  · by_cases hc : C.cost i true < C.cost i false
    · simp [minimizer,hi,hc,min_eq_right hc.le]
    · simp [minimizer,hi,hc,min_eq_left (le_of_not_gt hc)]
  · simp [minimizer,hi]

def reject (C : Budget n) (free : List (Fin n)) (x : Assignment n) : Bool :=
  decide (C.bound < minimum C free x)

theorem feasible_iff (C : Budget n) (free : List (Fin n)) (x : Assignment n) :
    reject C free x = false ↔ ∃ y, Compatible free.toFinset x y ∧ C.Holds y := by
  constructor
  · intro h
    have hb : minimum C free x ≤ C.bound := by simpa [reject] using h
    refine ⟨minimizer C free x, minimizer_compatible C free x, ?_⟩
    simpa [Budget.Holds,minimizer_lhs] using hb
  · rintro ⟨y,hc,hy⟩
    have hh := le_trans (minimum_le C free x y hc) hy
    simpa [reject] using hh

end Max2SAT.Weighted
