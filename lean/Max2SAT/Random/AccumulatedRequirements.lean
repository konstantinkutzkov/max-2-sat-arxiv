import Max2SAT.Random.RequirementAccumulation
import Max2SAT.Random.DriftTail

/-! The complete accumulated-requirement inequality, with both sources
of deviation under the actual auxiliary input/assignment experiment. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem requirements_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    prob (exposureLaw p)
      (fun z => requirements z.1 units C z.2 < requirementConstant m κ*C.card/26-a-b) ≤
    Real.exp (-2*a^2/((m:ℝ)^2*C.card)) + Real.exp (-169*b^2/((m:ℝ)^2*n)) := by
  have hE : E.Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.1 hC
    obtain ⟨e,_⟩ := Finset.card_pos.1 (hd i hi)
    exact ⟨e.val,e.property⟩
  exact two_deviation_bound (exposureLaw p)
    (fun z => requirements z.1 units C z.2) (fun z => availableDrift z.1 C z.2)
    (requirementConstant m κ*C.card/26) a b _ _
    (requirement_drift_tail p hm units C hC hd a ha)
    (available_drift_tail p hm hk hE C hd b hb)

end
end Max2SAT.RandomInput
