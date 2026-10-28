import Max2SAT.Random.ConcreteRuntime

/-! Boundary cases for the original-label count and empty observed support.
These are kernel proofs, not samples from the random input distribution. -/
namespace Max2SAT.RandomInput.SupportExamples
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

-- Only two nonconsecutive labels are free: the count is four, even though
-- the ambient input has five variables and any initialized values outside S.
example (base : Assignment 5) :
    ((Finset.univ.filter (fun x => Compatible ({1,3} : Finset (Fin 5)) base x)).card:ℝ)=4 := by
  have h := fixed_coordinate_count ({1,3} : Finset (Fin 5)) base
    (fun _ => True) (by intros; trivial)
  norm_num at h
  exact h

-- A nonempty potential support can produce no binary clauses at all.
-- The initial assignment still handles its unit clauses, and just one call
-- is charged; unused original labels do not multiply the candidate count.
example (E : Finset (Edge n)) (units : List (Literal n)) :
    Random.nodeCount (generate E (fun _ => (0 : Pattern m)) units)=1 ∧
      Random.candidateCount (generate E (fun _ => (0 : Pattern m)) units)=1 := by
  have ha : Random.active (generate E (fun _ => (0 : Pattern m)) units)=∅ := by
    have h := generated_restrict_active
      (show (∅ : Finset (Edge n))⊆E from Finset.empty_subset E)
      (fun _ : E => (0 : Pattern m))
      (by intro e; simp [present,size]) units
    simpa only [active_vertices_empty] using h
  exact ⟨(Random.nodeCount_of_active_empty _ ha).1,
    Random.candidateCount_of_active_empty _ ha⟩

-- The completed theorem includes no variables and no potential pairs.
example : ∃ q x, Random.randomFormula (generate (∅ : Finset (Edge 0))
    (fun _ => (0 : Pattern 4)) [])=some (q,x) ∧
    q=score (generate ∅ (fun _ => (0 : Pattern 4)) []) x ∧
    ∀ y : Assignment 0, score (generate ∅ (fun _ => (0 : Pattern 4)) []) y≤q :=
  generated_input_exact _ _ _

end
end Max2SAT.RandomInput.SupportExamples
