import Max2SAT.Random.FullTree
import Max2SAT.Random.WeightedEnumeration
import Max2SAT.Bias.Hybrid

/-! Deterministic weighted prefix/suffix search from Section sec:random.
The list version specifies outputs; the executable version streams them. -/
namespace Max2SAT.Random

def enumerate (F : Formula n) (w : Fin n → ℚ) (suffix : List (Fin n)) :
    List (Fin n) → Assignment n → List (ℚ × Constraint n) → List (Assignment n)
  | [], x, cs => Weighted.enumerate (Weighted.sum cs) suffix x
  | i::is, x, cs =>
    if Weighted.reject (Weighted.sum cs) (i::is++suffix) x then [] else
    let v := branchLiteral F (i::is++suffix) x i
    let C := branchCut F (i::is++suffix) x i
    enumerate F w suffix is (v.force true x) cs ++
      enumerate F w suffix is (v.force false x) ((w i,C)::cs)

def fold (F : Formula n) (w : Fin n → ℚ) (suffix : List (Fin n))
    (visit : σ → Assignment n → σ) :
    List (Fin n) → Assignment n → List (ℚ × Constraint n) → σ → σ
  | [], x, cs, acc => Weighted.fold (Weighted.sum cs) visit suffix x acc
  | i::is, x, cs, acc =>
    if Weighted.reject (Weighted.sum cs) (i::is++suffix) x then acc else
    let v := branchLiteral F (i::is++suffix) x i
    let C := branchCut F (i::is++suffix) x i
    let left := fold F w suffix visit is (v.force true x) cs acc
    fold F w suffix visit is (v.force false x) ((w i,C)::cs) left

theorem fold_eq_foldl (F : Formula n) (w : Fin n → ℚ) (suffix pre : List (Fin n))
    (x : Assignment n) (cs : List (ℚ × Constraint n))
    (visit : σ → Assignment n → σ) (acc : σ) :
    fold F w suffix visit pre x cs acc = (enumerate F w suffix pre x cs).foldl visit acc := by
  induction pre generalizing x cs acc with
  | nil => exact Weighted.fold_eq_foldl _ visit suffix x acc
  | cons i is ih =>
    simp only [fold,enumerate]
    split <;> simp [ih,List.foldl_append]

theorem output_compatible (F : Formula n) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (x y : Assignment n) (cs : List (ℚ × Constraint n))
    (hn : (pre++suffix).Nodup) (hy : y ∈ enumerate F w suffix pre x cs) :
    Compatible (pre++suffix).toFinset x y := by
  induction pre generalizing x cs with
  | nil => exact ((Weighted.mem_enumerate _ suffix x y (by simpa using hn)).mp hy).1
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    simp only [enumerate] at hy
    split at hy
    · simp at hy
    · rcases List.mem_append.mp hy with hy | hy
      all_goals
        have hc := ih _ _ ht hy
        exact ((Bias.Single.compatible_cons (is++suffix) i x y _ hi).mp hc).2

/-- The earliest optimum of the full tree survives every weighted sum on its
own path. Alternatives used for comparison need not satisfy older cuts. -/
theorem winner_survives (F : Formula n) (w : Fin n → ℚ)
    (suffix pre : List (Fin n)) (x : Assignment n) (cs : List (ℚ × Constraint n))
    (hF : wellFormed F) (hn : (pre++suffix).Nodup) (hw : ∀ i, 0 ≤ w i)
    (hcw : ∀ wc ∈ cs, 0 ≤ wc.1)
    (hc : ∀ wc ∈ cs, wc.2.Holds ((fullTree F (pre++suffix) x).winner (score F))) :
    (fullTree F (pre++suffix) x).winner (score F) ∈ enumerate F w suffix pre x cs := by
  induction pre generalizing x cs with
  | nil =>
    apply (Weighted.mem_enumerate _ suffix x _ (by simpa using hn)).mpr
    refine ⟨?_, Weighted.sum_holds cs _ hcw hc⟩
    exact (fullTree_covers F suffix x _ (by simpa using hn)).mp
      (ComparisonTree.winner_mem _ (score F))
  | cons i is ih =>
    have ht := (List.nodup_cons.mp hn).2
    let v := branchLiteral F (i::is++suffix) x i
    let C := branchCut F (i::is++suffix) x i
    let l := fullTree F (is++suffix) (v.force true x)
    let r := fullTree F (is++suffix) (v.force false x)
    have hvalid := fullTree_valid F (i::is++suffix) x hF hn
    have hcut := hvalid.2.2
    have hcomp := (fullTree_covers F (i::is++suffix) x _ hn).mp
      (ComparisonTree.winner_mem _ (score F))
    have hsum := Weighted.sum_holds cs _ hcw hc
    have hr : Weighted.reject (Weighted.sum cs) (i::is++suffix) x = false :=
      (Weighted.feasible_iff _ _ _).mpr ⟨_, hcomp, hsum⟩
    simp only [enumerate,hr,Bool.false_eq_true,↓reduceIte,List.mem_append]
    by_cases h : score F (r.winner (score F)) ≤ score F (l.winner (score F))
    · change (∀ wc ∈ cs, wc.2.Holds ((ComparisonTree.branch C l r).winner (score F))) at hc
      simp only [ComparisonTree.winner,ite_eq_left h] at hc
      change (ComparisonTree.branch C l r).winner (score F) ∈ _ ∨ _
      rw [ComparisonTree.winner,ite_eq_left h]
      exact Or.inl (ih _ cs ht hcw hc)
    · have hnew : C.Holds (r.winner (score F)) := by
        by_contra hbad
        rcases hcut _ (ComparisonTree.winner_mem r (score F)) hbad with ⟨y,hy,hle⟩
        exact h (le_trans hle (ComparisonTree.le_winner l (score F) y hy))
      change (∀ wc ∈ cs, wc.2.Holds ((ComparisonTree.branch C l r).winner (score F))) at hc
      simp only [ComparisonTree.winner,ite_eq_right h] at hc
      change (ComparisonTree.branch C l r).winner (score F) ∈ _ ∨ _
      rw [ComparisonTree.winner,ite_eq_right h]
      apply Or.inr
      change (ComparisonTree.branch C l r).winner (score F) ∈ _
      rw [ComparisonTree.winner,ite_eq_right h]
      apply ih _ ((w i,C)::cs) ht
      · simpa using And.intro (hw i) hcw
      · simpa [r,v] using And.intro hnew hc

private theorem fold_best_mem (F : Formula n) (xs : List (Assignment n))
    (acc : Option (Assignment n)) (z : Assignment n)
    (hz : xs.foldl (Bias.Hybrid.keepBest F) acc = some z) : z ∈ acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil =>
    cases acc with
    | none => simp at hz
    | some a =>
      have he : a=z := by simpa using hz
      simp [he]
  | cons y ys ih =>
    have hh := ih (Bias.Hybrid.keepBest F acc y) hz
    rcases List.mem_append.mp hh with hh | hh
    · have hmem : z ∈ acc.toList ∨ z=y := by
        cases acc with
        | none => simpa [Bias.Hybrid.keepBest] using hh
        | some a =>
          simp only [Bias.Hybrid.keepBest] at hh
          split at hh <;> simp_all
      simpa using hmem.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
    · simp [hh]

def solveOn (F : Formula n) (w : Fin n → ℚ) (U : List (Fin n))
    (T : ℕ) (x : Assignment n) : Option (Assignment n) :=
  fold F w (U.drop T) (Bias.Hybrid.keepBest F) (U.take T) x [] none

theorem solveOn_correct (F : Formula n) (w : Fin n → ℚ) (U : List (Fin n))
    (T : ℕ) (x : Assignment n) (hF : wellFormed F) (hU : U.Nodup)
    (hw : ∀ i, 0 ≤ w i) :
    ∃ y, solveOn F w U T x = some y ∧ Compatible U.toFinset x y ∧
      ∀ z, Compatible U.toFinset x z → score F z ≤ score F y := by
  have hn : (U.take T ++ U.drop T).Nodup := by simpa using hU
  let winner := (fullTree F (U.take T ++ U.drop T) x).winner (score F)
  have hwin : winner ∈ enumerate F w (U.drop T) (U.take T) x [] :=
    winner_survives F w _ _ x [] hF hn hw (by simp) (by simp)
  rcases Bias.Hybrid.fold_best_bound F (enumerate F w (U.drop T) (U.take T) x [])
    none winner (by simpa using hwin) with ⟨y,hy,hwy⟩
  have hymem := fold_best_mem F _ none y hy
  simp only [Option.toList_none,List.nil_append] at hymem
  refine ⟨y, ?_, ?_, ?_⟩
  · simpa [solveOn,fold_eq_foldl] using hy
  · simpa using output_compatible F w _ _ x y [] hn hymem
  · intro z hz
    apply le_trans (ComparisonTree.le_winner _ (score F) z ?_) hwy
    apply (fullTree_covers F _ x z hn).mpr
    simpa using hz

end Max2SAT.Random
