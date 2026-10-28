import Max2SAT.Random.ExposureGraph
import Max2SAT.Random.BlockLaws

/-! The complete auxiliary experiment, including the independent uniform
assignment, has exactly the prescribed joint law. Conditioning on all base
patterns and the exposed bits gives the histories used in the proof. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} {κ : ℝ} {E : Finset (Edge n)}

def repackBits : (ExposureBit E → Bool) ≃ Assignment n × (E → Signs) where
  toFun z := (assignment z,rho z)
  invFun z := Sum.elim z.1 (fun a => endpoint a.2 (z.2 a.1))
  left_inv z := by
    funext b
    cases b with
    | inl i => rfl
    | inr a => rcases a with ⟨e,left⟩; cases left <;> rfl
  right_inv z := rfl

theorem fair_repack :
    push (fairBits (ExposureBit E)) (repackBits (E:=E)) =
      tensor (fairBits (Fin n)) (product (fun _ : E => uniformSigns)) := by
  apply Law.ext
  funext z
  rw [push_equiv_mass,fairBits_mass]
  simp only [tensor,fairBits_mass,product,uniformSigns,Finset.prod_const,Finset.card_univ]
  simp only [ExposureBit,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,pow_add]
  rw [Nat.mul_comm (Fintype.card E) 2,pow_mul]
  norm_num

def flipAll (r : E → Signs) : (E → Pattern m) ≃ (E → Pattern m) where
  toFun K e := signedFlip (r e) (K e)
  invFun K e := (signedFlip (r e)).symm (K e)
  left_inv K := by funext e; exact (signedFlip (r e)).left_inv (K e)
  right_inv K := by funext e; exact (signedFlip (r e)).right_inv (K e)

def exposureLaw (p : E → PairLaw m κ) : Law ((E → Pattern m) × (ExposureBit E → Bool)) :=
  tensor (product (fun e => (p e).law)) (fairBits (ExposureBit E))

theorem exposure_joint_law (p : E → PairLaw m κ) :
    push (exposureLaw p) (fun z => (sampled z.1 z.2,assignment z.2)) =
      tensor (product (fun e => (p e).law)) (fairBits (Fin n)) := by
  have hinv : ∀ r K,
      (product (fun e => (p e).law)).mass (flipAll r K) =
        (product (fun e => (p e).law)).mass K := by
    intro r K
    simp only [product,flipAll,signedFlip]
    apply Finset.prod_congr rfl
    intro e _
    exact (p e).invariant _ _
  have hh := congrArg (fun q => push q (fun z : (E → Pattern m) × (Assignment n × (E → Signs)) =>
      (flipAll z.2.2 z.1,z.2.1)))
    (push_tensor_right (product (fun e => (p e).law)) (fairBits (ExposureBit E)) repackBits)
  rw [push_comp,fair_repack,random_symmetries_with_data _ _ _ flipAll hinv] at hh
  exact hh

theorem base_pattern_bound (p : E → PairLaw m κ) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (p e).law)).mass K) (e : E) : size (K e) ≤ m := by
  apply (p e).bounded
  have hn : (∏ f, (p f).law.mass (K f)) ≠ 0 := ne_of_gt hK
  have he := (Finset.prod_ne_zero_iff.mp hn) e (Finset.mem_univ e)
  exact lt_of_le_of_ne ((p e).law.nonneg _) (Ne.symm he)

def baseHistory (K : E → Pattern m) (known : Finset (ExposureBit E))
    (z : ExposureBit E → Bool) (w : (E → Pattern m) × (ExposureBit E → Bool)) : Prop :=
  w.1=K ∧ history known z w.2

theorem base_history_positive (p : E → PairLaw m κ) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (p e).law)).mass K)
    (known : Finset (ExposureBit E)) (z : ExposureBit E → Bool) :
    0 < prob (exposureLaw p) (baseHistory K known z) := by
  change 0 < prob (tensor _ _) (fun w => w.1=K ∧ history known z w.2)
  rw [tensor_prob_both _ _ (fun L => L=K) (history known z),prob_eq]
  exact mul_pos hK (fair_history_positive known z)

theorem condition_exposure_history (p : E → PairLaw m κ) (K : E → Pattern m)
    (hK : 0 < (product (fun e => (p e).law)).mass K)
    (known : Finset (ExposureBit E)) (z : ExposureBit E → Bool) :
    condition (exposureLaw p) (baseHistory K known z) (base_history_positive p K hK known z) =
      tensor (point K)
        (condition (fairBits (ExposureBit E)) (history known z) (fair_history_positive known z)) := by
  have hp : 0 < prob (product (fun e => (p e).law)) (fun L => L=K) := by simpa using hK
  have hh := condition_tensor_both (product (fun e => (p e).law)) (fairBits (ExposureBit E))
    (fun L => L=K) (history known z) hp (fair_history_positive known z)
  rw [condition_eq] at hh
  exact hh

end
end Max2SAT.RandomInput
