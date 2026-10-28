import Max2SAT.Counts.RoundSplit
import Max2SAT.Counts.OperatorEnergy

/-! Later-round compensation. We expose individual bits in the fixed
order and bound the total predictable energy by grouping destination
variables into rounds. No independence of creator decisions is assumed. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def interactionMatrix (H : Fin n → Affine n) : Matrix (Fin n) (Fin n) ℝ :=
  fun t w => (H t).coeff w

theorem later_incoming_known (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (horder : OrderedRounds round) (w : Fin n) :
    Known (bitHistory n w.val) (fun x => laterIncoming H P round x w) := by
  intro x y h
  unfold laterIncoming
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : round t<round w
  · have hi := horder w t ht
    have hx := bit_history_agree w.val x y h t hi
    have hp := preference_known H round horder t x y
      (bit_history_refines t.val w.val hi.le x y h)
    rw [hx,hp]
  · simp [ht]

theorem later_block_energy (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (j : ℕ) (x : Assignment n)
    (V : ℝ) (hV : 0≤V) (hN : ‖interactionMatrix H‖^2≤V) :
    (∑ w∈roundBlock round j, (laterIncoming H P round x w)^2) ≤ V*P.card := by
  let z : Fin n → ℝ := fun t => if t∈P ∧ round t<j ∧ x t≠preference H round x t
    then sign (x t) else 0
  have hz : (∑ t, (z t)^2) ≤ P.card := by
    have hp : ∀ t, (z t)^2 ≤ if t∈P then (1:ℝ) else 0 := by
      intro t
      by_cases ht : t∈P
      · simp only [z,ht,true_and]
        split_ifs
        · cases x t <;> norm_num [sign]
        · norm_num
      · simp [z,ht]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun t _ => hp t)
  have hrow : ∀ w∈roundBlock round j, laterIncoming H P round x w =
      ∑ t, (interactionMatrix H).transpose w t*z t := by
    intro w hw
    have hr : round w=j := (Finset.mem_filter.mp hw).2
    unfold laterIncoming
    rw [←Fintype.sum_extend_by_zero P (fun t =>
      if round t<round w ∧ x t≠preference H round x t then
        sign (x t)*(H t).coeff w else 0)]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Matrix.transpose_apply,interactionMatrix,z,hr]
    by_cases hp : t∈P <;> by_cases hlt : round t<j <;>
      by_cases hc : x t≠preference H round x t <;> simp [hp,hlt,hc,mul_comm]
  have hn : ‖(interactionMatrix H).transpose‖=‖interactionMatrix H‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose (interactionMatrix H)
  have he := matrix_squared_energy (interactionMatrix H).transpose z V (by rw [hn]; exact hN)
  calc
    _ = ∑ w∈roundBlock round j, (∑ t, (interactionMatrix H).transpose w t*z t)^2 :=
      Finset.sum_congr rfl (fun w hw => congrArg (fun v : ℝ => v^2) (hrow w hw))
    _ ≤ ∑ w, (∑ t, (interactionMatrix H).transpose w t*z t)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ V*P.card := he.trans (mul_le_mul_of_nonneg_left hz hV)

theorem later_first_round_zero (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (x : Assignment n) (w : Fin n) (hw : round w=0) :
    laterIncoming H P round x w=0 := by
  simp [laterIncoming,hw]

theorem later_total_energy (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (k : ℕ) (hround : ∀ t, round t≤k) (x : Assignment n)
    (V : ℝ) (hV : 0≤V) (hN : ‖interactionMatrix H‖^2≤V) :
    (∑ w, (laterIncoming H P round x w)^2) ≤ k*V*P.card := by
  have hp : roundPrefix round (k+1)=Finset.univ := by
    ext t
    simp only [roundPrefix,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact Nat.lt_succ_of_le (hround t)
  have h0 : (∑ w∈roundBlock round 0, (laterIncoming H P round x w)^2)=0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [later_first_round_zero H P round x w (Finset.mem_filter.mp hw).2]
    norm_num
  rw [←hp,←sum_round_blocks,Finset.sum_range_succ',h0,add_zero]
  calc
    _ ≤ ∑ _j∈Finset.range k, V*P.card :=
      Finset.sum_le_sum (fun j _ => later_block_energy H P round (j+1) x V hV hN)
    _ = _ := by simp [mul_assoc]

/-- This is the paper's bound with V=K*D_N, k prefix rounds, and
|P|=T. The suffix is the final round k; the first round contributes zero. -/
theorem later_compensation_tail (H : Fin n → Affine n) (P : Finset (Fin n))
    (round : Fin n → ℕ) (horder : OrderedRounds round)
    (k : ℕ) (hk : 0<k) (hround : ∀ t, round t≤k) (hP : 0<P.card)
    (V b : ℝ) (hV : 0<V) (hb : 0<b) (hN : ‖interactionMatrix H‖^2≤V) :
    prob (fairBits (Fin n)) (fun x => laterCompensation H P round x < -b) ≤
      Real.exp (-2*b^2/(k*V*P.card)) := by
  apply assignment_sign_tail (fun w x => -laterIncoming H P round x w/2)
    (by
      intro w x y h
      have he := later_incoming_known H P round horder w x y h
      dsimp only at he ⊢
      rw [he]) (k*V*P.card) b (by positivity) hb
  intro x
  have he : ∀ w, 4*(-laterIncoming H P round x w/2)^2=(laterIncoming H P round x w)^2 := by
    intro w; ring
  simp_rw [he]
  exact later_total_energy H P round k hround x V hV.le hN

end
end Max2SAT.Counts
