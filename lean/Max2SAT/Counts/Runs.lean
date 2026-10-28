import Max2SAT.Counts.PrefixSearch

/-! Stream each run's candidates through a common best-solution accumulator.
Different guesses may visit the same assignment; the cost bound counts each
visit, as required. The list of guesses is a finite enumeration specification. -/
namespace Max2SAT.Counts.Runs

def outputs (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) : List (Assignment n) :=
  guesses.flatMap (fun g => PrefixSearch.outputs (K g) P)

def fold (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) (visit : σ → Assignment n → σ) (initial : σ) : σ :=
  guesses.foldl (fun acc g => PrefixSearch.fold (K g) P (Bias.ordered Pᶜ) visit
    (Bias.ordered P) (fun _ => false) acc) initial

theorem fold_eq_foldl (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) (visit : σ → Assignment n → σ) (initial : σ) :
    fold guesses K P visit initial=(outputs guesses K P).foldl visit initial := by
  induction guesses generalizing initial with
  | nil => simp [fold,outputs]
  | cons g gs ih =>
    simp only [fold,List.foldl_cons]
    change fold gs K P visit _ = _
    rw [ih]
    simp [outputs,List.foldl_append,PrefixSearch.fold_eq_foldl,PrefixSearch.outputs]

theorem mem_outputs (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) (x : Assignment n)
    (hK : ∀ g∈guesses, PrefixSearch.Stable (K g) P) :
    x∈outputs guesses K P ↔ ∃ g∈guesses, (K g x).Holds x := by
  simp only [outputs,List.mem_flatMap]
  constructor
  · rintro ⟨g,hg,hx⟩
    exact ⟨g,hg,(PrefixSearch.mem_outputs (K g) P x (hK g hg)).mp hx⟩
  · rintro ⟨g,hg,hx⟩
    exact ⟨g,hg,(PrefixSearch.mem_outputs (K g) P x (hK g hg)).mpr hx⟩

def nodeCount (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) : ℕ :=
  (guesses.map (fun g => PrefixSearch.nodeCount (K g) P)).sum

theorem nodeCount_bound (guesses : List ι) (K : ι → Assignment n → Weighted.Budget n)
    (P : Finset (Fin n)) (hK : ∀ g∈guesses, PrefixSearch.Stable (K g) P) :
    nodeCount guesses K P ≤ guesses.length*(2^(P.card+1)-1)+
      2*n*(guesses.map (fun g => FairCoin.eventCount n (fun x => (K g x).Holds x))).sum := by
  induction guesses with
  | nil => simp [nodeCount]
  | cons g gs ih =>
    have hh := PrefixSearch.nodeCount_bound (K g) P (hK g (by simp))
    have ht := ih (fun z hz => hK z (by simp [hz]))
    simp only [nodeCount,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def solve (F : Formula n) (guesses : List ι)
    (K : ι → Assignment n → Weighted.Budget n) (P : Finset (Fin n)) :
    Option (Assignment n) := fold guesses K P (Bias.Hybrid.keepBest F) none

theorem solve_correct_of_survival (F : Formula n) (guesses : List ι)
    (K : ι → Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (hK : ∀ g∈guesses, PrefixSearch.Stable (K g) P)
    (hsurvive : ∀ x, (∀ y, score F y≤score F x) → ∃ g∈guesses, (K g x).Holds x) :
    ∃ z, solve F guesses K P=some z ∧ ∀ y, score F y≤score F z := by
  classical
  obtain ⟨x,_,hx⟩ := Finset.exists_max_image Finset.univ (score F)
    (Finset.univ_nonempty : (Finset.univ : Finset (Assignment n)).Nonempty)
  have hmax : ∀ y, score F y≤score F x := fun y => hx y (Finset.mem_univ y)
  have hmem := (mem_outputs guesses K P x hK).mpr (hsurvive x hmax)
  obtain ⟨z,hz,hxz⟩ := Bias.Hybrid.fold_best_bound F (outputs guesses K P) none x
    (by simpa using hmem)
  exact ⟨z,by simpa [solve,fold_eq_foldl] using hz,fun y => (hmax y).trans hxz⟩

end Max2SAT.Counts.Runs
