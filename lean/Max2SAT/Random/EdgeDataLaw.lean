import Max2SAT.Random.EdgeVariance

/-! The edge-data representation used for bounded differences has exactly
the law induced by the original endpoint-sign exposure experiment. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

theorem theta_involution (r x : Bool) : theta (theta r x) x = r := by
  cases r <;> cases x <;> rfl

def thetaTransform (E : Finset (Edge n)) : (ExposureBit E → Bool) ≃ (ExposureBit E → Bool) where
  toFun z b := match b with
    | .inl i => z (.inl i)
    | .inr (e,left) => theta (z (.inr (e,left))) (assignment z (vertex e.val left))
  invFun z b := match b with
    | .inl i => z (.inl i)
    | .inr (e,left) => theta (z (.inr (e,left))) (assignment z (vertex e.val left))
  left_inv z := by
    funext b
    cases b with
    | inl i => rfl
    | inr e => exact theta_involution _ _
  right_inv z := by
    funext b
    cases b with
    | inl i => rfl
    | inr e => exact theta_involution _ _

theorem theta_transform_law : push (fairBits (ExposureBit E)) (thetaTransform E) = fairBits (ExposureBit E) := by
  apply Law.ext
  funext z
  rw [push_equiv_mass, fairBits_mass, fairBits_mass]

def thetaSigns (z : ExposureBit E → Bool) (e : E) : Signs :=
  (theta (z (.inr (e,true))) (assignment z e.val.val.1),
   theta (z (.inr (e,false))) (assignment z e.val.val.2))

theorem theta_signs_law :
    push (fairBits (ExposureBit E)) thetaSigns = product (fun _ : E => uniformSigns) := by
  have hr := congrArg (fun p => push p Prod.snd) (fair_repack (E:=E))
  rw [push_comp, push_tensor_snd] at hr
  have ht := congrArg (fun p => push p (rho (E:=E))) (theta_transform_law (E:=E))
  rw [push_comp] at ht
  exact ht.trans hr

def edgeInputs (K : E → Pattern m) (z : ExposureBit E → Bool) : E → EdgeData m :=
  fun e => (K e,thetaSigns z e)

theorem edge_inputs_law (p : E → PairLaw m κ) :
    push (exposureLaw p) (fun z => edgeInputs z.1 z.2) =
      product (fun e => edgeDataLaw (p e)) := by
  have h := push_tensor_right (product (fun e => (p e).law)) (fairBits (ExposureBit E))
    (thetaSigns (E:=E))
  rw [theta_signs_law] at h
  have hh := congrArg (fun q => push q (fun z e => (z.1 e,z.2 e))) h
  rw [push_comp,tensor_product_law] at hh
  exact hh

theorem data_coefficient_exposure (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (i : Fin n) (e : Incidence E i) (z : ExposureBit E → Bool) :
    dataCoefficient (decide (partner i e.val.val < i)) (side i e.val.val)
      (edgeInputs K z e.val) = coefficient K (orderedFree i.val) z i e := by
  have hclip := clipped_eq (K e.val) (hK e.val)
  have hp : (partner i e.val.val ∈ orderedFree i.val) ↔ ¬partner i e.val.val < i := by
    simp only [mem_orderedFree, not_lt]
    rfl
  have ht : endpoint (!(side i e.val.val)) (thetaSigns z e.val) =
      theta (z (.inr (e.val,!(side i e.val.val)))) (assignment z (partner i e.val.val)) := by
    unfold partner
    cases hs : side i e.val.val <;> rfl
  unfold dataCoefficient coefficient
  change (if decide (partner i e.val.val < i) then
    pairGain (side i e.val.val) (clippedPattern (K e.val))
      (endpoint (!(side i e.val.val)) (thetaSigns z e.val))
    else signedCount (side i e.val.val) (clippedPattern (K e.val))/2) = _
  rw [hclip,ht]
  by_cases he : partner i e.val.val < i <;> simp [hp, he]

def availableDrift (K : E → Pattern m) (C : Finset (Fin n)) (z : ExposureBit E → Bool) : ℝ :=
  ∑ i ∈ C, supportWeight E i *
    Real.sqrt (∑ e : Incidence E i, (coefficient K (orderedFree i.val) z i e)^2)/13

def driftData (E : Finset (Edge n)) (C : Finset (Fin n)) (D : E → EdgeData m) : ℝ :=
  ∑ i ∈ C, supportWeight E i * Real.sqrt (varianceData E i D)/13

theorem drift_data_exposure (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (C : Finset (Fin n)) (z : ExposureBit E → Bool) :
    driftData E C (edgeInputs K z) = availableDrift K C z := by
  unfold driftData availableDrift varianceData
  simp_rw [data_coefficient_exposure K hK]

end
end Max2SAT.RandomInput
