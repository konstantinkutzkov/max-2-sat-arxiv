import Max2SAT.Random.ObservedRestriction
import Max2SAT.Random.ActiveNodes

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E H : Finset (Edge n)}

def observedEdges (E : Finset (Edge n)) (K : E → Pattern m) : Finset (Edge n) :=
  (Finset.univ.filter (fun e : E => present (K e))).image Subtype.val

theorem observed_edges_subset (K : E → Pattern m) : observedEdges E K⊆E := by
  intro e he
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
  exact f.property

theorem mem_observed_edge (K : E → Pattern m) (e : E) :
    e.val∈observedEdges E K ↔ present (K e) := by
  constructor
  · intro h
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp h
    have hfe : f=e := Subtype.ext he
    subst f
    exact (Finset.mem_filter.mp hf).2
  · intro h
    exact Finset.mem_image.mpr ⟨e,by simp [h],rfl⟩

theorem observed_event_iff (K : E → Pattern m) :
    observedEvent (fun e : E => e.val∈H) K ↔ ∀ e, present (K e) ↔ e.val∈H := by
  unfold observedEvent
  constructor
  · intro h e
    have hh := h e
    by_cases he : e.val∈H <;> simp_all
  · intro h e
    have hh := h e
    by_cases he : e.val∈H <;> simp_all

theorem observed_edges_event (hHE : H⊆E) (K : E → Pattern m) :
    observedEdges E K=H ↔ observedEvent (fun e : E => e.val∈H) K := by
  rw [observed_event_iff]
  constructor
  · intro h e
    rw [←h,mem_observed_edge]
  · intro h
    ext e
    by_cases he : e∈E
    · exact (mem_observed_edge K ⟨e,he⟩).trans (h ⟨e,he⟩)
    · have h1 : e∉observedEdges E K := fun hh => he (observed_edges_subset K hh)
      have h2 : e∉H := fun hh => he (hHE hh)
      simp [h1,h2]

theorem active_vertices_empty : activeVertices (∅ : Finset (Edge n))=∅ := by
  ext i
  simp [activeVertices,incident]

theorem conditional_candidate_expectation (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (units : List (Literal n)) (hHE : H⊆E)
    (h : 0<prob (product (fun e => (p e).law)) (observedEvent (fun e => e.val∈H))) :
    expect (condition (product (fun e => (p e).law)) (observedEvent (fun e => e.val∈H)) h)
      (fun K => (Random.candidateCount (generate E K units):ℝ))≤
      3*(2:ℝ)^(activeVertices H).card*Real.exp (-runtimeConstant m κ*(activeVertices H).card) := by
  let q := condition (product (fun e => (p e).law)) (observedEvent (fun e => e.val∈H)) h
  have hobs (K : E → Pattern m) (hK : 0<q.mass K) : ∀ e, present (K e) ↔ e.val∈H :=
    observed_event_iff K |>.mp (condition_support _ _ h K hK)
  by_cases hH : H.Nonempty
  · have he : expect q (fun K => (Random.candidateCount (generate E K units):ℝ))=
        expect (product (fun e : H => (retained (p (includeEdge hHE e))
          (present_positive (p (includeEdge hHE e)) hk)).law))
          (fun L => (Random.candidateCount (generate H L units):ℝ)) := by
      calc
        _=expect q (fun K => (Random.candidateCount (generate H (selectPatterns hHE K) units):ℝ)) :=
          expect_congr_support _ _ _ (fun K hK => by rw [generated_restrict_candidates hHE K (hobs K hK) units])
        _=_ := by
          rw [←expect_push q (selectPatterns hHE)
            (fun L => (Random.candidateCount (generate H L units):ℝ)),
            selected_conditional_law p hk hHE h]
    change expect q _≤_
    rw [he]
    exact active_candidate_expectation _ hm hk hH units
      (fun L hL => retained_base_present (fun e : H => p (includeEdge hHE e))
        (fun e => present_positive _ hk) L hL)
  · have hz : H=∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    have he : expect q (fun K => (Random.candidateCount (generate E K units):ℝ))=1 := by
      calc
        _=expect q (fun _ => 1) := expect_congr_support _ _ _ (fun K hK => by
          have ha := generated_restrict_active hHE K (hobs K hK) units
          rw [hz,active_vertices_empty] at ha
          rw [Random.candidateCount_of_active_empty _ ha]
          norm_num)
        _=1 := expect_const _ _
    change expect q _≤_
    rw [he,hz,active_vertices_empty]
    norm_num

end
end Max2SAT.RandomInput
