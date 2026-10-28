import Max2SAT.Counts.RoundHistory
import Max2SAT.Counts.LaterRounds
import Max2SAT.Counts.BlockNorms

/-! Conditional analysis of the actual within-round terms. The linear
tail is proved. The generic quadratic tail is an explicit remaining
hypothesis, not an axiom or a verified Hanson--Wright theorem. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def quadraticTerm {ι : Type*} [Fintype ι] (N : Matrix ι ι ℝ) (z : ι → Bool) : ℝ :=
  -(1/4 : ℝ)*(∑ t, ∑ w, sign (z t)*N t w*sign (z w))

def maskedQuadratic {ι : Type*} [Fintype ι] (N : Matrix ι ι ℝ) (p z : ι → Bool) : ℝ :=
  -(1/4 : ℝ)*(∑ t, ∑ w, changedSign (p t) (z t)*
    conjugated N p t w*changedSign (p w) (z w))

def maskedLinear {ι : Type*} [Fintype ι] (N : Matrix ι ι ℝ) (p z : ι → Bool) : ℝ :=
  -(1/4 : ℝ)*(∑ t, (∑ w, conjugated N p t w)*changedSign (p t) (z t))

def withinQuadratic (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ)
    (x : Assignment n) : ℝ :=
  maskedQuadratic (blockInteractions H round j) (roundMask H round j x) (fun t => x t)

def withinLinear (H : Fin n → Affine n) (round : Fin n → ℕ) (j : ℕ)
    (x : Assignment n) : ℝ :=
  maskedLinear (blockInteractions H round j) (roundMask H round j x) (fun t => x t)

theorem within_round_decomposition (H : Fin n → Affine n) (round : Fin n → ℕ)
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t) (j : ℕ) (x : Assignment n) :
    withinRound H round j x=withinQuadratic H round j x+withinLinear H round j x := by
  have h := round_compensation_expansion (blockInteractions H round j)
    (roundMask H round j x) (fun t => x t) (by
      intro t w
      dsimp [blockInteractions]
      exact_mod_cast hsym t w)
  unfold roundMask at h
  unfold withinRound withinQuadratic withinLinear maskedQuadratic maskedLinear roundMask
  simpa only [sub_eq_add_neg,neg_mul] using h

theorem block_interactions_norm (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (V : ℝ) (hV : 0≤V) (hN : ‖interactionMatrix H‖^2≤V) :
    ‖blockInteractions H round j‖^2≤V :=
  block_norm_sq (interactionMatrix H) (roundBlock round j) V hV hN

theorem within_linear_tail (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (V B e : ℝ) (hV : 0≤V) (hB : 0<B) (he : 0<e)
    (hN : ‖interactionMatrix H‖^2≤V) (hsize : (roundBlock round j).card*V≤B) :
    prob (fairBits (Fin n)) (fun x => withinLinear H round j x < -e) ≤
      Real.exp (-8*e^2/B) := by
  apply round_probability_of_fixed_masks H round j
    (fun p z => maskedLinear (blockInteractions H round j) p z < -e)
  intro p
  apply round_linear_tail _ p B e hB he
  have hn := conjugated_norm_sq (blockInteractions H round j) p V hV
    (block_interactions_norm H round j V hV hN)
  have h := matrix_row_sum_energy (signedMatrix (blockInteractions H round j) p) V hn
  have hc : Fintype.card (roundBlock round j)=(roundBlock round j).card := Fintype.card_coe _
  rw [hc] at h
  exact h.trans hsize

/-- Transfer a generic symmetric zero-diagonal quadratic-tail estimate to
the actual adaptive round. Every structural premise of that estimate is
discharged; proving the quadratic-tail estimate itself remains separate. -/
theorem within_quadratic_tail (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (hsym : ∀ t w, (H t).coeff w=(H w).coeff t)
    (hdiag : ∀ t, (H t).coeff t=0)
    (V e q : ℝ) (hV : 0≤V) (hN : ‖interactionMatrix H‖^2≤V)
    (hquad : ∀ N : Matrix (roundBlock round j) (roundBlock round j) ℝ,
      (∀ t w, N t w=N w t) → (∀ t, N t t=0) → ‖N‖^2≤V →
      prob (fairBits (roundBlock round j)) (fun z => quadraticTerm N z < -e)≤q) :
    prob (fairBits (Fin n)) (fun x => withinQuadratic H round j x < -e)≤q := by
  apply round_probability_of_fixed_masks H round j
    (fun p z => maskedQuadratic (blockInteractions H round j) p z < -e)
  intro p
  let N := blockInteractions H round j
  let M := signedMatrix N p
  have hs : ∀ t w, N t w=N w t := by intro t w; dsimp [N,blockInteractions]; exact_mod_cast hsym t w
  have hd : ∀ t, N t t=0 := by intro t; dsimp [N,blockInteractions]; exact_mod_cast hdiag t
  have h := hquad M (conjugated_symmetric N p hs) (conjugated_diagonal N p hd)
    (conjugated_norm_sq N p V hV (block_interactions_norm H round j V hV hN))
  have hlaw := changed_sign_law p
  have hp := congrArg (fun μ => prob μ (fun z => quadraticTerm M z < -e)) hlaw
  rw [prob_push] at hp
  simp only [quadraticTerm,changed_sign_value] at hp
  change prob _ (fun z => maskedQuadratic N p z < -e)=_ at hp
  rw [hp]
  exact h

theorem within_round_tail (H : Fin n → Affine n) (round : Fin n → ℕ)
    (j : ℕ) (hsym : ∀ t w, (H t).coeff w=(H w).coeff t)
    (e qL qQ : ℝ)
    (hL : prob (fairBits (Fin n)) (fun x => withinLinear H round j x < -e)≤qL)
    (hQ : prob (fairBits (Fin n)) (fun x => withinQuadratic H round j x < -e)≤qQ) :
    prob (fairBits (Fin n)) (fun x => withinRound H round j x < -2*e)≤qL+qQ := by
  have hsub := prob_mono_support (fairBits (Fin n))
    (fun x => withinRound H round j x < -2*e)
    (fun x => withinLinear H round j x < -e ∨ withinQuadratic H round j x < -e) (by
      intro x _ hx
      rw [within_round_decomposition H round hsym] at hx
      by_cases h : withinLinear H round j x < -e
      · exact Or.inl h
      · exact Or.inr (by linarith [le_of_not_gt h]))
  exact hsub.trans ((prob_union_le _ _ _).trans (add_le_add hL hQ))

end
end Max2SAT.Counts
