import Max2SAT.Counts.CompletePassing
import Max2SAT.Counts.Resources

namespace Max2SAT.Counts
noncomputable section
open FiniteLaw
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def sequentialRate (τ g K : ℝ) : ℝ := g^2/(64*τ*(clipParameter τ g K)^2*K)
def roundScale (k : ℕ) (K : ℝ) : ℝ := (k-1:ℕ)*K
def roundRate (k : ℕ) (τ g K : ℝ) : ℝ :=
  min (g^2/(32*τ*(clipParameter τ g (roundScale k K))^2*roundScale k K))
      (g^2/(8192*(k:ℝ)^2*τ*K))

theorem sequential_rate_pos (τ g K : ℝ) (hτ : 0<τ) (hg : 0<g) (hK : 0<K) :
    0<sequentialRate τ g K := by
  have ha := clip_parameter_ge_two τ g K
  unfold sequentialRate
  positivity

theorem round_rate_pos (k : ℕ) (hk : 2≤k) (τ g K : ℝ)
    (hτ : 0<τ) (hg : 0<g) (hK : 0<K) : 0<roundRate k τ g K := by
  have hk' : (0:ℝ)<(k-1:ℕ) := by exact_mod_cast (show 0<k-1 by omega)
  have hs : 0<roundScale k K := mul_pos hk' hK
  have ha := clip_parameter_ge_two τ g (roundScale k K)
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  unfold roundRate
  positivity

theorem sequential_passing_paper (H : Fin n → Affine n) (P : Finset (Fin n))
    (hr : EarlierInPrefix P (fun i => i.val)) (hP : 0<P.card)
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t) (hdiag : ∀ t, (H t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈P, 0≤s t)
    (τ g K D : ℝ) (hτ : 0<τ) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : (P.card:ℝ)≤τ*n)
    (hN : ‖sequentialMatrix H P‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : P, Real.sqrt (∑ w, (earlierRow H (fun i => i.val) t w)^2))
    (hslack : (∑ t∈P, (s t : ℝ))≤g*n*Real.sqrt D/8) :
    prob (fairBits (Fin n)) (fun x => (comparisonBudget H s P (fun i => i.val) x).Holds x)≤
      3*Real.exp (-sequentialRate τ g K*n) := by
  have hn : 0<n := by have h := Finset.card_le_univ P; simp only [Fintype.card_fin] at h; omega
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hp : (0:ℝ)<P.card := by exact_mod_cast hP
  let α := clipParameter τ g K
  have ha : 2≤α := clip_parameter_ge_two τ g K
  have hrates := normalized_rate (P.card:ℝ) n τ g K D (64*α^2)
    hp hn' hτ hK hD (by positivity) hsize
  have hc : sequentialRate τ g K*n≤(g*n*Real.sqrt D)^2/(64*α^2*P.card*(K*D)) := by
    convert hrates using 1
    · unfold sequentialRate
      ring
    · ring
  have h := sequential_passing_closed H P hr hP hsym hdiag s hs (K*D) α
    (g*n*Real.sqrt D) (sequentialRate τ g K*n) (by positivity) ha (by positivity) hN
    (row_profile_rescale _ _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hprofile)
    (clip_parameter_scale _ _ _ _ _ _ hn'.le hτ.le hg hK.le hD.le hsize) hslack hc
  simpa only [neg_mul] using h

theorem round_passing_paper (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (hk : 2≤k) (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t) (hdiag : ∀ t, (H t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈roundPrefix round k, 0≤s t)
    (τ g K D : ℝ) (hτ : 0<τ) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : ((roundPrefix round k).card:ℝ)≤τ*n)
    (hN : ‖interactionMatrix H‖^2≤K*D)
    (hprofile : 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : roundPrefix round k, Real.sqrt (∑ w, (earlierRow H round t w)^2))
    (hslack : (∑ t∈roundPrefix round k, (s t : ℝ))≤g*n*Real.sqrt D/8) :
    prob (fairBits (Fin n)) (fun x =>
      (comparisonBudget H s (roundPrefix round k) round x).Holds x)≤
      (3+2*k)*Real.exp (-roundRate k τ g K*n) := by
  let T := (roundPrefix round k).card
  let KL := roundScale k K
  let α := clipParameter τ g KL
  have hp : (0:ℝ)<T := by exact_mod_cast hP
  have hn : 0<n := by
    have h := Finset.card_le_univ (roundPrefix round k)
    simp only [Fintype.card_fin] at h
    omega
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkminus : (0:ℝ)<(k-1:ℕ) := by exact_mod_cast (show 0<k-1 by omega)
  have hKL : 0<KL := by dsimp [KL,roundScale]; positivity
  have ha : 2≤α := clip_parameter_ge_two τ g KL
  have hL : ‖prefixRows H (roundPrefix round k) round‖^2≤KL*D := by
    have h := round_profile_norm H round k (by omega) (K*D) (by positivity) hN
    simpa only [KL,roundScale,mul_assoc] using h
  have r1 := normalized_rate (T:ℝ) n τ g KL D (32*α^2) hp hn' hτ hKL hD (by positivity) hsize
  have r2 := normalized_rate (T:ℝ) n τ g K D (8192*(k:ℝ)^2) hp hn' hτ hK hD (by positivity) hsize
  have hc1 : roundRate k τ g K*n≤(g*n*Real.sqrt D)^2/(32*α^2*T*(KL*D)) := by
    have h := mul_le_mul_of_nonneg_right (min_le_left
      (g^2/(32*τ*α^2*KL)) (g^2/(8192*(k:ℝ)^2*τ*K))) hn'.le
    apply h.trans
    convert r1 using 1 <;> ring
  have hc2 : roundRate k τ g K*n≤(g*n*Real.sqrt D)^2/(8192*(k:ℝ)^2*T*(K*D)) := by
    have h := mul_le_mul_of_nonneg_right (min_le_right
      (g^2/(32*τ*α^2*KL)) (g^2/(8192*(k:ℝ)^2*τ*K))) hn'.le
    apply h.trans
    convert r2 using 1 <;> ring
  have h := round_passing_closed H round k (by omega) horder hround hP hsym hdiag s hs
    (K*D) (KL*D) α (g*n*Real.sqrt D) (roundRate k τ g K*n)
    (by positivity) (by positivity) ha (by positivity) hN hL
    (row_profile_rescale _ _ (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hprofile)
    (clip_parameter_scale _ _ _ _ _ _ hn'.le hτ.le hg hKL.le hD.le hsize) hslack hc1 hc2
  simpa only [neg_mul] using h

end
end Max2SAT.Counts
