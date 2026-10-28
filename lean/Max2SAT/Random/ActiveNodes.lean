import Max2SAT.Random.ActiveCandidates
import Max2SAT.Random.RuntimeRates

namespace Max2SAT.Random
noncomputable section
open FiniteLaw

theorem candidateCount_of_active_empty (F : Formula n) (h : active F=∅) :
    candidateCount F=1 := by
  classical
  have he : (Finset.univ.filter (fun x : Assignment n => x=initial F))={initial F} := by
    ext x
    simp
  simpa [candidateCount,h,Bias.ordered,pathCandidates,pathExcess,compatible_empty]
    using congrArg Finset.card he

/-- The active-size premise is needed only on outcomes of positive mass. -/
theorem expected_nodes_on_support {Ω : Type*} [Fintype Ω]
    (p : Law Ω) (F : Ω → Formula n) (r : ℕ)
    (ha : ∀ z, 0<p.mass z → (active (F z)).card=r)
    (B : ℝ) (hB : expect p (fun z => (candidateCount (F z):ℝ))≤B) :
    expect p (fun z => (nodeCount (F z):ℝ))≤(2:ℝ)^((r+1)/2+1)+2*r*B := by
  have hb : ∀ z, 0<p.mass z → (nodeCount (F z):ℝ)≤
      (2:ℝ)^((r+1)/2+1)+2*r*(candidateCount (F z):ℝ) := by
    intro z hz
    have h := nodes_le_candidates (F z)
    rw [ha z hz] at h
    exact_mod_cast h.trans (Nat.add_le_add_right (Nat.sub_le _ _) _)
  apply (expect_mono_support p hb).trans
  rw [expect_add,expect_const]
  have he : expect p (fun z => 2*(r:ℝ)*(candidateCount (F z):ℝ))=
      2*r*expect p (fun z => (candidateCount (F z):ℝ)) := by
    simp only [expect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  gcongr

end
end Max2SAT.Random

namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem active_candidate_expectation (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hE : E.Nonempty) (units : List (Literal n))
    (hp : ∀ K, 0<(product (fun e => (p e).law)).mass K → ∀ e, present (K e)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.candidateCount (generate E K units):ℝ))≤
      3*(2:ℝ)^(activeVertices E).card*Real.exp (-runtimeConstant m κ*(activeVertices E).card) := by
  have hr := active_card_pos hE
  have hc : 0<(supportPrefix E).card := by rw [support_prefix_card]; omega
  have hd : ∀ i∈supportPrefix E, 0<(incident E i).card :=
    fun i hi => (mem_activeVertices i).mp (support_prefix_subset hi)
  have hh : (activeVertices E).card≤2*(supportPrefix E).card := by rw [support_prefix_card]; omega
  have h := active_sum_feasibility_input_law p hm hk units (supportPrefix E) hc hd hh
  rw [prob_tensor] at h
  have he : expect (product (fun e => (p e).law))
      (fun K => (Random.candidateCount (generate E K units):ℝ))=
      (2:ℝ)^(activeVertices E).card * expect (product (fun e => (p e).law))
        (fun K => prob (fairBits (Fin n)) (fun x => comparisonSum E (generate E K units) (supportPrefix E) x≤0)) := by
    calc
      _=expect (product (fun e => (p e).law)) (fun K =>
          (2:ℝ)^(activeVertices E).card * prob (fairBits (Fin n))
            (fun x => comparisonSum E (generate E K units) (supportPrefix E) x≤0)) :=
        expect_congr_support _ _ _ (fun K hK => generated_candidate_probability K (hp K hK) units)
      _=_ := by
        simp only [expect,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro K _
        ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h
    (pow_nonneg (by norm_num : (0:ℝ)≤2) (activeVertices E).card)
  nlinarith

theorem active_search_expectation (p : E → PairLaw m κ)
    (hm : 0<m) (hk : 0<κ) (hE : E.Nonempty) (units : List (Literal n))
    (hp : ∀ K, 0<(product (fun e => (p e).law)).mass K → ∀ e, present (K e)) :
    expect (product (fun e => (p e).law)) (fun K => (Random.nodeCount (generate E K units):ℝ))≤
      (2:ℝ)^(((activeVertices E).card+1)/2+1)+
        6*(activeVertices E).card*(2:ℝ)^(activeVertices E).card*
          Real.exp (-runtimeConstant m κ*(activeVertices E).card) := by
  have h := Random.expected_nodes_on_support (product (fun e => (p e).law))
    (fun K => generate E K units) (activeVertices E).card
    (fun K hK => congrArg Finset.card (generated_active K (hp K hK) units)) _
    (active_candidate_expectation p hm hk hE units hp)
  convert h using 1
  ring

end
end Max2SAT.RandomInput
