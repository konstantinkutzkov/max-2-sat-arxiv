import Max2SAT.Regular.Rows

namespace Max2SAT.Regular
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Pick the first available vertex and remove its neighbors. The initial
fuel is the list length; every nonempty step removes at least one vertex. -/
def greedy : ℕ → List (Fin n) → List (Fin n)
  | 0, _ => []
  | _+1, [] => []
  | k+1, v::vs => v::greedy k (vs.filter (fun w => !decide (G.Adj v w)))

theorem greedy_subset (k : ℕ) (vs : List (Fin n)) : ∀ v∈greedy G k vs, v∈vs := by
  induction k generalizing vs with
  | zero => simp [greedy]
  | succ k ih =>
    cases vs with
    | nil => simp [greedy]
    | cons v vs =>
      intro w hw
      rw [greedy] at hw
      rcases List.mem_cons.mp hw with rfl|hw
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_of_mem_filter (ih _ w hw))

theorem greedy_independent (k : ℕ) (vs : List (Fin n)) :
    (greedy G k vs).Pairwise (fun v w => ¬G.Adj v w) := by
  induction k generalizing vs with
  | zero => simp [greedy]
  | succ k ih =>
    cases vs with
    | nil => simp [greedy]
    | cons v vs =>
      rw [greedy,List.pairwise_cons]
      refine ⟨?_,ih _⟩
      intro w hw
      have hh := greedy_subset G k _ w hw
      simpa using (List.mem_filter.mp hh).2

theorem greedy_covers (k : ℕ) (vs : List (Fin n)) (hk : vs.length≤k)
    (w : Fin n) (hw : w∈vs) : ∃ v∈greedy G k vs, w=v ∨ G.Adj v w := by
  induction k generalizing vs with
  | zero => have : vs=[] := List.length_eq_zero_iff.mp (by omega); simp_all
  | succ k ih =>
    cases vs with
    | nil => simp at hw
    | cons v vs =>
      rw [greedy]
      by_cases h : w=v
      · exact ⟨v,by simp,Or.inl h⟩
      · have hvs : w∈vs := (List.mem_cons.mp hw).resolve_left h
        by_cases ha : G.Adj v w
        · exact ⟨v,by simp,Or.inr ha⟩
        · have hlen : (vs.filter (fun w => !decide (G.Adj v w))).length≤k :=
            (List.length_filter_le _ _).trans (by simpa using hk)
          obtain ⟨u,hu,hh⟩ := ih _ hlen (by simp [hvs,ha])
          exact ⟨u,by simp [hu],hh⟩

def independentSet : Finset (Fin n) := (greedy G n (Bias.ordered Finset.univ)).toFinset

theorem independent_set_independent (v w : Fin n) (hv : v∈independentSet G)
    (hw : w∈independentSet G) : ¬G.Adj v w := by
  have hp := greedy_independent G n (Bias.ordered Finset.univ)
  let : Std.Symm (fun v w => ¬G.Adj v w) := ⟨fun _ _ h ha => h ((G.adj_comm _ _).mp ha)⟩
  exact List.Pairwise.forall_of_forall (fun v _ => G.irrefl) hp
    (List.mem_toFinset.mp hv) (List.mem_toFinset.mp hw)

theorem independent_set_covers (w : Fin n) :
    ∃ v∈independentSet G, w=v ∨ G.Adj v w := by
  obtain ⟨v,hv,hh⟩ := greedy_covers G n (Bias.ordered Finset.univ) (by simp) w (by simp [Bias.ordered])
  exact ⟨v,List.mem_toFinset.mpr hv,hh⟩

theorem independent_set_size (d : ℕ) (hd : ∀ v, G.degree v≤d) :
    n≤(d+1)*(independentSet G).card := by
  have hcover : Finset.univ⊆(independentSet G).biUnion (fun v => insert v (G.neighborFinset v)) := by
    intro w _
    obtain ⟨v,hv,hh⟩ := independent_set_covers G w
    refine Finset.mem_biUnion.mpr ⟨v,hv,?_⟩
    simpa only [Finset.mem_insert,SimpleGraph.mem_neighborFinset] using hh
  have hcard : ∀ v∈independentSet G, (insert v (G.neighborFinset v)).card≤d+1 := by
    intro v _
    rw [Finset.card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree]
    exact Nat.add_le_add_right (hd v) 1
  have h := (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le_card_mul _ _ (d+1) hcard)
  simpa [mul_comm] using h

end Max2SAT.Regular
