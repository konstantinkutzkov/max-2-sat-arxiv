import Max2SAT.Random.DriftSensitivity
import Max2SAT.Random.DriftMean
import Max2SAT.Random.RequirementTail

/-! Concentration of the available drift under the actual joint
formula/assignment law, with the paper's constants. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem drift_data_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (hE : E.Nonempty) (C : Finset (Fin n)) (hC : ∀ i∈C, 0 < (incident E i).card)
    (b : ℝ) (hb : 0 < b) :
    prob (product (fun e => edgeDataLaw (p e)))
      (fun D => driftData E C D < requirementConstant m κ*C.card/26-b) ≤
      Real.exp (-169*b^2/((m:ℝ)^2*n)) := by
  obtain ⟨e,he⟩ := hE
  let e₀ : E := ⟨e,he⟩
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn : 0 < n := Nat.zero_lt_of_lt e.val.1.isLt
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
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
  have hbudget := edge_influence_budget (E:=E) (m:=m)
  have hh := mul_le_mul_of_nonneg_left hbudget (sq_nonneg b)
  nlinarith

theorem available_drift_tail (p : E → PairLaw m κ) (hm : 0 < m) (hk : 0 < κ)
    (hE : E.Nonempty) (C : Finset (Fin n)) (hC : ∀ i∈C, 0 < (incident E i).card)
    (b : ℝ) (hb : 0 < b) :
    prob (exposureLaw p)
      (fun z => availableDrift z.1 C z.2 < requirementConstant m κ*C.card/26-b) ≤
      Real.exp (-169*b^2/((m:ℝ)^2*n)) := by
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
  exact h.trans (drift_data_tail p hm hk hE C hC b hb)

end
end Max2SAT.RandomInput
