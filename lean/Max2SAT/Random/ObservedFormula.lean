import Max2SAT.Random.Encoding
import Max2SAT.Random.Sampling

/-! Condition the pair sampling law on the graph extracted from the actual
generated Formula. The random variable is represented as the map generate
on its finite sample space; the unrestricted Formula type need not be finite. -/
namespace Max2SAT.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

theorem prob_indicator (p : Law α) (P : α → Prop) :
    prob p P = expect p (fun a => if P a then 1 else 0) := by
  simp [prob,expect,mul_ite]

theorem prob_push (p : Law α) (f : α → β) (P : β → Prop) :
    prob (push p f) P = prob p (fun a => P (f a)) := by
  rw [prob_indicator,expect_push,prob_indicator]


end
end Max2SAT.FiniteLaw

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

/-- Equality of events, including the Formula-to-neighbor connection. -/
theorem observed_event_eq (E : Finset (Edge n)) (units : List (Literal n)) (H : E → Prop) :
    (fun K : E → Pattern m => ∀ e : E,
      e.val.val.2 ∈ Random.neighbors (generate E K units) e.val.val.1 ↔ H e) =
      observedEvent (m := m) H := by
  funext K
  apply propext
  simp only [generated_edge_neighbors,observedEvent]
  constructor
  · intro h e
    by_cases hh : H e <;> simp [hh,h e]
  · intro h e
    have hh := h e
    by_cases he : H e <;> simpa [he] using hh

/-- Observing a graph in the generated Formula is precisely the
coordinatewise event in Lemma lem:observed_pairs. -/
theorem observed_event_probability (E : Finset (Edge n)) (p : E → PairLaw m κ)
    (units : List (Literal n)) (H : E → Prop) :
    prob (product (fun e => (p e).law))
      (fun K => ∀ e : E, e.val.val.2 ∈ Random.neighbors (generate E K units) e.val.val.1 ↔ H e) =
      ∏ e : E, prob (p e).law (fun K => if H e then present K else ¬ present K) := by
  rw [observed_event_eq]
  exact product_prob (fun e => (p e).law)
    (fun e K => if H e then present K else ¬ present K)

/-- The conditional law of sampled pair multisets, when conditioning on
 the neighbor relation extracted by the algorithm from the generated input. -/
theorem condition_observed_input (E : Finset (Edge n)) (p : E → PairLaw m κ)
    (units : List (Literal n)) (H : E → Prop)
    (h : 0 < prob (product (fun e => (p e).law)) (observedEvent H)) :
    condition (product (fun e => (p e).law))
      (fun K => ∀ e : E, e.val.val.2 ∈ Random.neighbors (generate E K units) e.val.val.1 ↔ H e)
      (by simpa only [observed_event_eq] using h) =
      product (fun e => condition (p e).law
        (fun K => if H e then present K else ¬ present K)
        (product_event_positive (fun e => (p e).law)
          (fun e K => if H e then present K else ¬ present K) h e)) := by
  simpa only [observed_event_eq] using observed_factorization p H h

end
end Max2SAT.RandomInput
