import Max2SAT.Random.ExposureGraph
import Max2SAT.Random.BlockLaws

/-! Lemma lem:random_exposure, conditional on the base multisets and the
exact preceding history. Histories with positive probability are expressed
as finite events, rather than measure-theoretic sigma-algebras. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {E : Finset (Edge n)}

theorem current_signs_law (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z : ExposureBit E → Bool) :
    push (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z)) (fun w e => w (current i e)) = fairBits (Incidence E i) :=
  fresh_selection _ _ _ _ (current_injective i) (current_fresh free i hi)

theorem assignment_after_signs_law (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z : ExposureBit E → Bool) :
    push (condition (fairBits (ExposureBit E)) (history (knownAfterSigns E free i) z)
      (fair_history_positive _ z)) (fun w => assignment w i) = fair :=
  fresh_coordinate _ _ _ _ (assignment_fresh free i hi)

theorem delta_known_after_signs (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z w : ExposureBit E → Bool) (h : history (knownAfterSigns E free i) z w) :
    delta (generate E (sampled K w) units) free (assignment w) i =
      delta (generate E (sampled K z) units) free (assignment z) i := by
  have hb : history (knownBefore E free) z w := by
    intro b
    by_cases hmem : b ∈ knownBefore E free
    · have hh := h b
      have hmem' : b ∈ knownAfterSigns E free i := Finset.mem_union_left _ hmem
      simpa [hmem,hmem'] using hh
    · simp [hmem]
  rw [delta_exposure E K units free w i hi,delta_exposure E K units free z i hi]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [coefficient_known K free z w i hb e]
  have hh := h (current i e)
  have hm : current i e ∈ knownAfterSigns E free i :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,Finset.mem_univ e,rfl⟩)
  have he : w (current i e)=z (current i e) := by simpa [hm] using hh
  rw [he]

theorem conditional_delta_mean (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free) (z : ExposureBit E → Bool) :
    expect (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z))
      (fun w => delta (generate E (sampled K w) units) free (assignment w) i) = unitBias units i := by
  let q := condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
    (fair_history_positive _ z)
  have he := expect_congr_support q
    (fun w => delta (generate E (sampled K w) units) free (assignment w) i)
    (fun w => unitBias units i + ∑ e : Incidence E i, sign (w (current i e))*coefficient K free z i e)
    (by
      intro w hw
      have hh := condition_support _ _ _ w hw
      rw [delta_exposure E K units free w i hi]
      simp only [coefficient_known K free z w i hh])
  change expect q _ = _
  rw [he,expect_add,expect_const]
  have hm := congrArg (fun p => expect p
    (fun r => ∑ e : Incidence E i, sign (r e)*coefficient K free z i e))
    (current_signs_law (E:=E) free i hi z)
  rw [expect_push,signed_sum_mean] at hm
  change expect q _ = 0 at hm
  rw [hm,add_zero]

theorem conditional_delta_variance (K : E → Pattern m) (units : List (Literal n))
    (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free) (z : ExposureBit E → Bool) :
    expect (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z))
      (fun w => (delta (generate E (sampled K w) units) free (assignment w) i - unitBias units i)^2) =
      ∑ e : Incidence E i, (coefficient K free z i e)^2 := by
  let q := condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
    (fair_history_positive _ z)
  have he := expect_congr_support q
    (fun w => (delta (generate E (sampled K w) units) free (assignment w) i-unitBias units i)^2)
    (fun w => (∑ e : Incidence E i, sign (w (current i e))*coefficient K free z i e)^2)
    (by
      intro w hw
      have hh := condition_support _ _ _ w hw
      rw [delta_exposure E K units free w i hi]
      simp only [coefficient_known K free z w i hh,add_sub_cancel_left])
  change expect q _ = _
  rw [he]
  have hm := congrArg (fun p => expect p
    (fun r => (∑ e : Incidence E i, sign (r e)*coefficient K free z i e)^2))
    (current_signs_law (E:=E) free i hi z)
  rw [expect_push,signed_sum_second] at hm
  exact hm

/-- Multiplication by the same assignment bit preserves the entire joint
law of the row, conditional on everything exposed before this variable. -/
theorem current_theta_law (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z : ExposureBit E → Bool) :
    push (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z))
      (fun w e => theta (w (current i e)) (assignment w i)) = fairBits (Incidence E i) := by
  have hxi : (Sum.inl i : ExposureBit E) ∉ knownBefore E free := by simp [knownBefore,hi]
  have hj := fresh_bit_and_vector (knownBefore E free) z (fair_history_positive _ z)
    (Sum.inl i) hxi (current i) (current_injective i) (current_fresh free i hi)
    (fun e => by simp [current])
  have hm := congrArg (fun p => push p (fun z : Bool × (Incidence E i → Bool) => z.2))
    (joint_multiply fair (fun b (_ : Incidence E i) => b))
  rw [push_comp,push_tensor_snd] at hm
  have hh := congrArg (fun p => push p (fun z : Bool × (Incidence E i → Bool) =>
    multiplyBits (fun _ => z.1) z.2)) hj
  rw [push_comp] at hh
  have hh' : push (tensor fair (fairBits (Incidence E i)))
      (fun z => multiplyBits (fun _ => z.1) z.2) = fairBits (Incidence E i) := hm
  rw [hh'] at hh
  have he : (fun (w : ExposureBit E → Bool) (e : Incidence E i) => theta (w (current i e)) (assignment w i)) =
      (fun w => multiplyBits (fun _ => w (.inl i)) (fun e => w (current i e))) := by
    funext w e
    dsimp [theta,multiplyBits,assignment]
    cases w (current i e) <;> cases w (.inl i) <;> rfl
  rw [he]
  exact hh

theorem edge_deviation_exposure (K : E → Pattern m) (z : ExposureBit E → Bool)
    (i : Fin n) (e : Incidence E i) :
    pairGain (side i e.val.val) (sampled K z e.val) (assignment z (partner i e.val.val)) -
      signedCount (side i e.val.val) (sampled K z e.val)/2 =
      sign (z (current i e)) * eta (side i e.val.val) (K e.val) *
        sign (theta (z (.inr (e.val,!(side i e.val.val)))) (assignment z (partner i e.val.val))) := by
  rw [sampled,endpoint_deviation]
  have h1 : endpoint (side i e.val.val) (rho z e.val) = z (current i e) := by
    unfold endpoint rho current
    cases side i e.val.val <;> rfl
  have h2 : endpoint (!(side i e.val.val)) (rho z e.val) = z (.inr (e.val,!(side i e.val.val))) := by
    unfold endpoint rho
    cases side i e.val.val <;> rfl
  rw [h1,h2]

/-- In particular, select the incidences whose other endpoint occurred
earlier. Their theta signs retain the full independent fair product law. -/
theorem theta_subrow_law (free : Finset (Fin n)) (i : Fin n) (hi : i ∈ free)
    (z : ExposureBit E → Bool) (S : Finset (Incidence E i)) :
    push (condition (fairBits (ExposureBit E)) (history (knownBefore E free) z)
      (fair_history_positive _ z))
      (fun w (e : S) => theta (w (current i e.val)) (assignment w i)) = fairBits S := by
  have hh := congrArg (fun p => push p (fun r (e : S) => r e.val))
    (current_theta_law (E:=E) free i hi z)
  rw [push_comp] at hh
  have hp := product_select (fun _ : Incidence E i => fair)
    (fun e : S => e.val) Subtype.val_injective
  exact hh.trans hp

theorem deviation_coefficient_bound (K : E → Pattern m) (hK : ∀ e, size (K e) ≤ m)
    (i : Fin n) (e : Incidence E i) : |eta (side i e.val.val) (K e.val)| ≤ (m:ℝ)/2 := by
  apply le_trans (eta_bound _ _)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hK e.val) (by norm_num)

end
end Max2SAT.RandomInput
