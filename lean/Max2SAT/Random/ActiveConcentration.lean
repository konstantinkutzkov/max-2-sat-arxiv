import Max2SAT.Random.ActiveSupport

/-! The same three deviations, charged to the active vertices rather than
all input labels. The constants and exposure order are unchanged. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem active_drift_data_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (hE : E.Nonempty) (C : Finset (Fin n)) (hC : ∀ i∈C, 0 < (incident E i).card)
    (b : ℝ) (hb : 0 < b) :
    prob (product (fun e => edgeDataLaw (p e)))
      (fun D => driftData E C D < requirementConstant m κ*C.card/26-b) ≤
      Real.exp (-169*b^2/((m:ℝ)^2*(activeVertices E).card)) := by
  obtain ⟨e,he⟩ := hE
  let e₀ : E := ⟨e,he⟩
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn : 0 < (activeVertices E).card := active_card_pos ⟨e,he⟩
  have hn' : (0:ℝ) < (activeVertices E).card := by exact_mod_cast hn
  have hinf : 0 < edgeInfluence E m e₀ := by
    unfold edgeInfluence
    exact div_pos (mul_pos hm' (add_pos (support_weight_pos (E:=E) _) (support_weight_pos (E:=E) _))) (by norm_num)
  have hs : 0 < ∑ f : E, (edgeInfluence E m f)^2 := by
    apply (sq_pos_of_pos hinf).trans_le
    exact Finset.single_le_sum (fun f _ => sq_nonneg _) (Finset.mem_univ e₀)
  have h := bounded_differences_finite (fun e => edgeDataLaw (p e)) (driftData E C)
    (edgeInfluence E m) (fun e D a => drift_data_update C D e a) b hb hs
  have hmean := drift_data_mean p hm hk C hC
  apply (prob_mono_support _ _ _ (fun D _ hD => lt_of_lt_of_le hD (sub_le_sub_right hmean b))).trans
  apply h.trans
  apply Real.exp_le_exp.2
  apply (div_le_div_iff₀ hs (mul_pos (sq_pos_of_pos hm') hn')).2
  have hbudget := edge_influence_active_budget (E:=E) (m:=m)
  have hh := mul_le_mul_of_nonneg_left hbudget (sq_nonneg b)
  nlinarith

theorem active_available_drift_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (hE : E.Nonempty) (C : Finset (Fin n)) (hC : ∀ i∈C, 0 < (incident E i).card)
    (b : ℝ) (hb : 0 < b) :
    prob (exposureLaw p)
      (fun z => availableDrift z.1 C z.2 < requirementConstant m κ*C.card/26-b) ≤
      Real.exp (-169*b^2/((m:ℝ)^2*(activeVertices E).card)) := by
  have h := prob_mono_support (exposureLaw p)
    (fun z => availableDrift z.1 C z.2 < requirementConstant m κ*C.card/26-b)
    (fun z => driftData E C (edgeInputs z.1 z.2) < requirementConstant m κ*C.card/26-b) (by
      intro z hz h
      have hK : 0 < (product (fun e => (p e).law)).mass z.1 :=
        pos_of_mul_pos_left hz ((fairBits (ExposureBit E)).nonneg z.2)
      rw [drift_data_exposure z.1 (base_pattern_bound p z.1 hK)]
      exact h)
  rw [← prob_push (exposureLaw p) (fun z => edgeInputs z.1 z.2)
    (fun D => driftData E C D < requirementConstant m κ*C.card/26-b), edge_inputs_law] at h
  exact h.trans (active_drift_data_tail p hm hk hE C hC b hb)

theorem active_requirements_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    prob (exposureLaw p)
      (fun z => requirements z.1 units C z.2 < requirementConstant m κ*C.card/26-a-b) ≤
    Real.exp (-2*a^2/((m:ℝ)^2*C.card)) + Real.exp (-169*b^2/((m:ℝ)^2*(activeVertices E).card)) := by
  have hE : E.Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.1 hC
    obtain ⟨e,_⟩ := Finset.card_pos.1 (hd i hi)
    exact ⟨e.val,e.property⟩
  exact two_deviation_bound (exposureLaw p)
    (fun z => requirements z.1 units C z.2) (fun z => availableDrift z.1 C z.2)
    (requirementConstant m κ*C.card/26) a b _ _
    (requirement_drift_tail p hm units C hC hd a ha)
    (active_available_drift_tail p hm hk hE C hd b hb)

theorem active_sum_feasibility_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (hhalf : (activeVertices E).card ≤ 2*C.card) :
    prob (exposureLaw p)
      (fun z => comparisonSum E (generate E (sampled z.1 z.2) units) C (assignment z.2) ≤ 0) ≤
      3*Real.exp (-runtimeConstant m κ*(activeVertices E).card) := by
  have hn : 0 < (activeVertices E).card := by
    obtain ⟨i,hi⟩ := Finset.card_pos.1 hC
    exact Finset.card_pos.mpr ⟨i,(mem_activeVertices i).mpr (hd i hi)⟩
  have hc := requirement_constant_pos hm hk
  let a : ℝ := requirementConstant m κ*C.card/104
  have ha : 0 < a := by dsimp [a]; positivity
  have hA := active_requirements_tail p hm hk units C hC hd a a ha ha
  have hQ := compensation_tail p hm units C hC a ha
  have h := summed_constraint_failure (exposureLaw p)
    (fun z => requirements z.1 units C z.2)
    (fun z => compensation z.1 units C (supportWeight E) z.2)
    (requirementConstant m κ*C.card/26) a a a _ _ (by convert ha using 1; dsimp [a]; ring) hA hQ
  have he := deviation_exponents (m:ℝ) (requirementConstant m κ) (C.card:ℝ) ((activeVertices E).card:ℝ)
    (by exact_mod_cast hm) hc (by exact_mod_cast hC) (by exact_mod_cast hn) (by exact_mod_cast hhalf)
  have he₁ := Real.exp_le_exp.2 he.1
  have he₂ := Real.exp_le_exp.2 he.2
  simp only [← comparison_sum_identity] at h
  apply h.trans
  dsimp only [a, runtimeConstant] at *
  nlinarith

/-- The event is about the original sampled formula and an independent
uniform assignment, not an auxiliary distribution with extra assumptions. -/
theorem active_sum_feasibility_input_law (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (units : List (Literal n)) (C : Finset (Fin n)) (hC : 0 < C.card)
    (hd : ∀ i∈C, 0 < (incident E i).card) (hhalf : (activeVertices E).card ≤ 2*C.card) :
    prob (tensor (product (fun e => (p e).law)) (fairBits (Fin n)))
      (fun z => comparisonSum E (generate E z.1 units) C z.2 ≤ 0) ≤
      3*Real.exp (-runtimeConstant m κ*(activeVertices E).card) := by
  have h := active_sum_feasibility_tail p hm hk units C hC hd hhalf
  rw [← prob_push (exposureLaw p) (fun z => (sampled z.1 z.2,assignment z.2))
    (fun z => comparisonSum E (generate E z.1 units) C z.2 ≤ 0), exposure_joint_law] at h
  exact h

end
end Max2SAT.RandomInput
