import Max2SAT.Random.HistoryAverage
import Max2SAT.Random.ExposureLaw

/-! Identify the finite history classes used by concentration with the
positive-history conditional laws in the endpoint exposure proofs. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def observe (known : Finset ι) (z : ι → Bool) : ι → Bool :=
  fun i => if i ∈ known then z i else false

omit [Fintype ι] in
theorem observe_eq_iff (known : Finset ι) (z w : ι → Bool) :
    observe known w = observe known z ↔ history known z w := by
  constructor
  · intro h i
    by_cases hi : i ∈ known
    · simpa [observe, hi] using congrFun h i
    · simp [hi]
  · intro h
    funext i
    have hh := h i
    by_cases hi : i ∈ known <;> simp_all [observe]

omit [Fintype ι] in
theorem observe_refines (A B : Finset ι) (hAB : A ⊆ B) (x y : ι → Bool)
    (h : observe B x = observe B y) : observe A x = observe A y := by
  funext i
  by_cases hi : i ∈ A
  · have hh := congrFun h i
    simpa [observe, hi, hAB hi] using hh
  · simp [observe, hi]

theorem fiber_fair_history (known : Finset ι) (z : ι → Bool) :
    fiber (fairBits ι) (observe known) (observe known z) =
      condition (fairBits ι) (history known z) (fair_history_positive known z) := by
  have he : (fun w => observe known w = observe known z) = history known z := by
    funext w
    exact propext (observe_eq_iff known z w)
  have hp : 0 < prob (fairBits ι) (fun w => observe known w = observe known z) := by
    rw [he]
    exact fair_history_positive known z
  rw [fiber_eq _ _ _ hp]
  simp only [he]

end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def observedState (known : Finset (ExposureBit E))
    (w : (E → Pattern m) × (ExposureBit E → Bool)) := (w.1, observe known w.2)

theorem observed_state_eq_iff (known : Finset (ExposureBit E))
    (K : E → Pattern m) (z : ExposureBit E → Bool)
    (w : (E → Pattern m) × (ExposureBit E → Bool)) :
    observedState known w = observedState known (K,z) ↔ baseHistory K known z w := by
  simp only [observedState, Prod.mk.injEq, observe_eq_iff, baseHistory]

theorem fiber_exposure_history (p : E → PairLaw m κ) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (p e).law)).mass K)
    (known : Finset (ExposureBit E)) (z : ExposureBit E → Bool) :
    fiber (exposureLaw p) (observedState known) (observedState known (K,z)) =
      condition (exposureLaw p) (baseHistory K known z) (base_history_positive p K hK known z) := by
  have he : (fun w => observedState known w = observedState known (K,z)) = baseHistory K known z := by
    funext w
    exact propext (observed_state_eq_iff known K z w)
  have hp : 0 < prob (exposureLaw p) (fun w => observedState known w = observedState known (K,z)) := by
    rw [he]
    exact base_history_positive p K hK known z
  rw [fiber_eq _ _ _ hp]
  simp only [he]

end
end Max2SAT.RandomInput
