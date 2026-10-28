import Max2SAT.Random.ActiveCandidates

/-! Deleting empty pair draws preserves all scores and observed neighbors.
Selecting the retained coordinates has the exact conditional product law. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E H : Finset (Edge n)}

def includeEdge (hHE : H⊆E) (e : H) : E := ⟨e.val,hHE e.property⟩

theorem include_edge_injective (hHE : H⊆E) : Function.Injective (includeEdge hHE) := by
  intro e f h
  exact Subtype.ext (congrArg (fun e : E => e.val) h)

def selectPatterns (hHE : H⊆E) (K : E → Pattern m) : H → Pattern m :=
  fun e => K (includeEdge hHE e)

theorem sum_restricted_edges {A : Type*} [AddCommMonoid A] (hHE : H⊆E) (f : E → A)
    (hz : ∀ e, e.val∉H → f e=0) :
    (∑ e : E, f e)=∑ e : H, f (includeEdge hHE e) := by
  have he : (∑ e∈Finset.univ.filter (fun e : E => e.val∈H), f e)=∑ e : E, f e := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e _ he
    apply hz e
    simpa using he
  rw [←he]
  apply Finset.sum_bij (fun e he => (⟨e.val,(Finset.mem_filter.mp he).2⟩ : H))
  · intros; exact Finset.mem_univ _
  · intro e _ f _ he
    exact Subtype.ext (congrArg (fun e : H => e.val) he)
  · intro e _
    refine ⟨includeEdge hHE e,?_,?_⟩
    · simp [includeEdge,e.property]
    · rfl
  · intro e _
    rfl

theorem edge_clauses_absent (e : Edge n) (K : Pattern m) (h : ¬present K) :
    edgeClauses e K=[] := by simp [edgeClauses,absent_count K h]

theorem generated_score (K : E → Pattern m) (units : List (Literal n)) (x : Assignment n) :
    score (generate E K units) x=score (units.map Clause.unit) x+
      ∑ e : E, score (edgeClauses e.val (K e)) x := by
  have hs : ∀ L : List E,
      score (L.flatMap (fun e => edgeClauses e.val (K e))) x=
        (L.map (fun e => score (edgeClauses e.val (K e)) x)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons e L ih => simp [ih]
  rw [generate,score_append,hs]
  simp only [Finset.attach_eq_univ]
  simp [-Finset.univ_eq_attach]

theorem selected_present (hHE : H⊆E) (K : E → Pattern m)
    (hobs : ∀ e, present (K e) ↔ e.val∈H) : ∀ e, present (selectPatterns hHE K e) := by
  intro e
  exact (hobs (includeEdge hHE e)).mpr e.property

theorem generated_restrict_score (hHE : H⊆E) (K : E → Pattern m)
    (hobs : ∀ e, present (K e) ↔ e.val∈H) (units : List (Literal n)) :
    EquivalentWithOffset (generate E K units) (generate H (selectPatterns hHE K) units) 0 := by
  intro x
  rw [generated_score,generated_score,zero_add]
  congr 1
  apply sum_restricted_edges hHE
  intro e he
  rw [edge_clauses_absent _ _ (fun h => he ((hobs e).mp h)),score_nil]

theorem generated_restrict_support (hHE : H⊆E) (K : E → Pattern m)
    (hobs : ∀ e, present (K e) ↔ e.val∈H) (units : List (Literal n)) :
    pairSupport (generate E K units)=pairSupport (generate H (selectPatterns hHE K) units) := by
  ext uv
  rw [generated_support,generated_support]
  constructor
  · rintro ⟨e,he,hp⟩
    exact ⟨⟨e.val,(hobs e).mp hp⟩,he,hp⟩
  · rintro ⟨e,he,hp⟩
    exact ⟨includeEdge hHE e,he,hp⟩

theorem generated_restrict_neighbors (hHE : H⊆E) (K : E → Pattern m)
    (hobs : ∀ e, present (K e) ↔ e.val∈H) (units : List (Literal n)) (i : Fin n) :
    Random.neighbors (generate E K units) i=
      Random.neighbors (generate H (selectPatterns hHE K) units) i := by
  ext j
  rw [neighbors_iff_pairSupport,neighbors_iff_pairSupport,generated_restrict_support hHE K hobs units]

theorem active_eq_of_neighbors (F G : Formula n)
    (he : ∀ i, Random.neighbors F i=Random.neighbors G i) : Random.active F=Random.active G := by
  have hi (F : Formula n) (i : Fin n) : i∈Random.active F ↔ 0<(Random.neighbors F i).card := by
    constructor
    · exact Random.active_degree_positive F i
    · intro h
      obtain ⟨j,hj⟩ := Finset.card_pos.mp h
      exact neighbors_imply_active F i j hj
  ext i
  rw [hi,hi,he]

theorem generated_restrict_active (hHE : H⊆E) (K : E → Pattern m)
    (hobs : ∀ e, present (K e) ↔ e.val∈H) (units : List (Literal n)) :
    Random.active (generate E K units)=activeVertices H := by
  rw [active_eq_of_neighbors _ _ (generated_restrict_neighbors hHE K hobs units),
    generated_active _ (selected_present hHE K hobs) units]

theorem generated_restrict_candidates (hHE : H⊆E) (K : E → Pattern m)
    (hobs : ∀ e, present (K e) ↔ e.val∈H) (units : List (Literal n)) :
    Random.candidateCount (generate E K units)=
      Random.candidateCount (generate H (selectPatterns hHE K) units) := by
  have h1 := initialized_candidate_probability (generate E K units) (generate_wellFormed E K units)
    (selectPatterns hHE K) units 0 (generated_restrict_score hHE K hobs units)
    (generated_restrict_active hHE K hobs units) (fun i => by
      rw [Random.weight,generated_restrict_neighbors hHE K hobs units i]
      exact (support_weight_eq _ (selected_present hHE K hobs) units i).symm)
  have h2 := generated_candidate_probability (selectPatterns hHE K) (selected_present hHE K hobs) units
  exact_mod_cast h1.trans h2.symm

theorem selected_conditional_law (p : E → PairLaw m κ) (hk : 0<κ) (hHE : H⊆E)
    (h : 0<prob (product (fun e => (p e).law)) (observedEvent (fun e => e.val∈H))) :
    push (condition (product (fun e => (p e).law)) (observedEvent (fun e => e.val∈H)) h)
      (selectPatterns hHE) =
      product (fun e : H => (retained (p (includeEdge hHE e))
        (present_positive (p (includeEdge hHE e)) hk)).law) := by
  rw [observed_factorization]
  rw [show selectPatterns hHE=(fun K e => K (includeEdge hHE e)) from rfl,
    product_select _ _ (include_edge_injective hHE)]
  congr 1
  funext e
  simp only [includeEdge,e.property,↓reduceIte,retained]

end
end Max2SAT.RandomInput
