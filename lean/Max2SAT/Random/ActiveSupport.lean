import Max2SAT.Random.FixedSupportNodes
import Max2SAT.Random.DriftSensitivity

/-! Keep the input labels while charging concentration only to vertices
incident to the observed support. Isolated coordinates spend no influence. -/
namespace Max2SAT.RandomInput
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

def activeVertices (E : Finset (Edge n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0<(incident E i).card)

@[simp] theorem mem_activeVertices (i : Fin n) :
    i∈activeVertices E ↔ 0<(incident E i).card := by simp [activeVertices]

theorem endpoints_active (e : E) :
    e.val.val.1∈activeVertices E ∧ e.val.val.2∈activeVertices E := by
  constructor
  all_goals
    apply mem_activeVertices _ |>.mpr
    apply Finset.card_pos.mpr
    exact ⟨e,by simp [incident]⟩

theorem active_card_pos (hE : E.Nonempty) : 0<(activeVertices E).card := by
  obtain ⟨e,he⟩ := hE
  exact Finset.card_pos.mpr ⟨e.val.1,(endpoints_active ⟨e,he⟩).1⟩

theorem generated_active (K : E → Pattern m) (hp : ∀ e, present (K e))
    (units : List (Literal n)) : Random.active (generate E K units)=activeVertices E := by
  ext i
  rw [mem_activeVertices,←observed_degree E K hp units i]
  constructor
  · exact Random.active_degree_positive _ i
  · intro h
    obtain ⟨j,hj⟩ := Finset.card_pos.mp h
    exact neighbors_imply_active _ i j hj

theorem edge_influence_active_budget :
    (∑ e : E, (edgeInfluence E m e)^2)≤2*(m:ℝ)^2*(activeVertices E).card/169 := by
  have hz : ∀ i∉activeVertices E, (supportWeight E i)^2*(incident E i).card=0 := by
    intro i hi
    have hd : (incident E i).card=0 := by simpa using hi
    simp [hd]
  have hs : (∑ i, (supportWeight E i)^2*(incident E i).card)≤(activeVertices E).card := by
    rw [←Finset.sum_subset (Finset.subset_univ (activeVertices E)) (by
      intro i _ hi; exact hz i hi)]
    calc
      _≤∑ _i∈activeVertices E, (1:ℝ) :=
        Finset.sum_le_sum (fun i _ => support_weight_squared_degree i)
      _=_ := by simp
  have h : (∑ e : E, (supportWeight E e.val.val.1+supportWeight E e.val.val.2)^2)≤
      2*(activeVertices E).card := by
    calc
      _≤∑ e : E, 2*((supportWeight E e.val.val.1)^2+(supportWeight E e.val.val.2)^2) := by
        apply Finset.sum_le_sum
        intro e _
        nlinarith [sq_nonneg (supportWeight E e.val.val.1-supportWeight E e.val.val.2)]
      _=2*∑ i, (supportWeight E i)^2*(incident E i).card := by
        rw [←Finset.mul_sum,degree_square_sum]
      _≤_ := by linarith
  have he : (∑ e : E, (edgeInfluence E m e)^2)=
      (m:ℝ)^2*(∑ e : E, (supportWeight E e.val.val.1+supportWeight E e.val.val.2)^2)/169 := by
    simp only [edgeInfluence,div_pow,mul_pow]
    norm_num
    rw [←Finset.sum_div,←Finset.mul_sum]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (m:ℝ))
  nlinarith

end
end Max2SAT.RandomInput
