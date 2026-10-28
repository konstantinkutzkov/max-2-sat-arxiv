import Max2SAT.Counts.ProfileNorms
import Max2SAT.Counts.ScalarRates
import Max2SAT.Counts.QuadraticTail
import Max2SAT.Counts.RoundPassing
import Max2SAT.Counts.SequentialPassing

namespace Max2SAT.Counts
noncomputable section
open FiniteLaw
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem exponential_fraction_bound (N d D c : ℝ) (hN : 0≤N)
    (hd : 0<d) (hdD : d≤D) (hc : c≤N/D) :
    Real.exp (-N/d)≤Real.exp (-c) := by
  apply Real.exp_le_exp.mpr
  have h := hc.trans (div_le_div_of_nonneg_left hN hd hdD)
  simpa only [neg_div] using neg_le_neg h

theorem sequential_passing_closed (H : Fin n → Affine n) (P : Finset (Fin n))
    (hr : EarlierInPrefix P (fun i => i.val)) (hP : 0<P.card)
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t) (hdiag : ∀ t, (H t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈P, 0≤s t)
    (V α A c : ℝ) (hV : 0<V) (hα : 2≤α) (hA : 0<A)
    (hN : ‖sequentialMatrix H P‖^2≤V)
    (hprofile : 2*A≤(∑ t : P, Real.sqrt ((∑ w, (earlierRow H (fun i => i.val) t w)^2)/3))/2)
    (hscale : 2*P.card*Real.sqrt V≤α*A)
    (hslack : (∑ t∈P, (s t : ℝ))≤A/8)
    (hc : c≤A^2/(64*α^2*P.card*V)) :
    prob (fairBits (Fin n)) (fun x => (comparisonBudget H s P (fun i => i.val) x).Holds x)≤
      3*Real.exp (-c) := by
  have hp : (0:ℝ)<P.card := by exact_mod_cast hP
  have ha : 0<α := by linarith
  have ha2 : 4≤α^2 := by nlinarith
  have hg := prefix_gap_tail H P (fun i => i.val) hr hP V α A hV hα hA
    (sequential_profile_norm H P hr hsym V hV.le hN) hprofile hscale
  have he : 6*(A/8)=3*A/4 := by ring
  have h := sequential_passing_probability H P hP hdiag s hs (α*Real.sqrt V) V (A/8)
    (Real.exp (-A^2/(8*(α^2*P.card*V)))) (by positivity) hV (by positivity) hN hslack
    (by simpa only [he] using hg)
  have h1 := exponential_fraction_bound (A^2) (8*(α^2*P.card*V)) (64*α^2*P.card*V) c
    (sq_nonneg _) (by positivity) (by nlinarith [mul_pos (sq_pos_of_pos ha) (mul_pos hp hV)]) hc
  have h2 : Real.exp (-2*(A/8)^2/(P.card*(α*Real.sqrt V)^2))≤Real.exp (-c) := by
    have hh := exponential_fraction_bound (A^2) (32*α^2*P.card*V) (64*α^2*P.card*V) c
      (sq_nonneg _) (by positivity) (by nlinarith [mul_pos (sq_pos_of_pos ha) (mul_pos hp hV)]) hc
    rw [mul_pow,Real.sq_sqrt hV.le]
    convert hh using 1
    congr 1
    ring
  have h3 : Real.exp (-(A/8)^2/(2*V*P.card))≤Real.exp (-c) := by
    have hd : 128*V*P.card≤64*α^2*P.card*V := by
      nlinarith [mul_nonneg (mul_nonneg hp.le hV.le) (sub_nonneg.mpr ha2)]
    have hh := exponential_fraction_bound (A^2) (128*V*P.card) (64*α^2*P.card*V) c
      (sq_nonneg _) (by positivity) hd hc
    convert hh using 1
    congr 1
    ring
  linarith

/-- The complete fixed-round passing estimate: there is no assumed
probability estimate in this statement. -/
theorem round_passing_closed (H : Fin n → Affine n) (round : Fin n → ℕ)
    (k : ℕ) (hk : 0<k) (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (hsym : ∀ t w, (H t).coeff w=(H w).coeff t) (hdiag : ∀ t, (H t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈roundPrefix round k, 0≤s t)
    (V W α A c : ℝ) (hV : 0<V) (hW : 0<W) (hα : 2≤α) (hA : 0<A)
    (hN : ‖interactionMatrix H‖^2≤V)
    (hL : ‖prefixRows H (roundPrefix round k) round‖^2≤W)
    (hprofile : 2*A≤(∑ t : roundPrefix round k,
      Real.sqrt ((∑ w, (earlierRow H round t w)^2)/3))/2)
    (hscale : 2*(roundPrefix round k).card*Real.sqrt W≤α*A)
    (hslack : (∑ t∈roundPrefix round k, (s t : ℝ))≤A/8)
    (hc1 : c≤A^2/(32*α^2*(roundPrefix round k).card*W))
    (hc2 : c≤A^2/(8192*(k:ℝ)^2*(roundPrefix round k).card*V)) :
    prob (fairBits (Fin n)) (fun x =>
      (comparisonBudget H s (roundPrefix round k) round x).Holds x)≤
      (3+2*k)*Real.exp (-c) := by
  let T := (roundPrefix round k).card
  have hp : (0:ℝ)<T := by exact_mod_cast hP
  have ha : 0<α := by linarith
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hg := prefix_gap_tail H (roundPrefix round k) round (round_prefix_closed round k)
    hP W α A hW hα hA hL hprofile hscale
  let q := Real.exp (-(A/8/(8*k))^2/(2*(V*T)))
  have hq : ∀ j<k, ∀ N : Matrix (roundBlock round j) (roundBlock round j) ℝ,
      (∀ t w, N t w=N w t) → (∀ t, N t t=0) → ‖N‖^2≤V →
      prob (fairBits (roundBlock round j)) (fun z => quadraticTerm N z< -(A/8/(8*k)))≤q := by
    intro j hj N _ hd hn
    apply quadratic_norm_tail N hd V (V*T) (A/8/(8*k)) hV.le (by positivity) (by positivity) hn
    have hcard : (Fintype.card (roundBlock round j) : ℝ)≤T := by
      simp only [Fintype.card_coe]
      exact_mod_cast block_card_le_prefix round j k hj
    nlinarith
  have h := round_passing_probability H round k hk horder hround hP hsym hdiag s hs
    (α*Real.sqrt W) V (A/8) (Real.exp (-A^2/(8*(α^2*T*W)))) q
    (by positivity) hV (by positivity) hN hslack
    (by simpa only [show 6*(A/8)=3*A/4 by ring] using hg) hq
  have h1 := exponential_fraction_bound (A^2) (8*(α^2*T*W)) (32*α^2*T*W) c
    (sq_nonneg _) (by positivity) (by nlinarith [mul_pos (sq_pos_of_pos ha) (mul_pos hp hW)]) hc1
  have h2 : Real.exp (-2*(A/8)^2/(T*(α*Real.sqrt W)^2))≤Real.exp (-c) := by
    rw [mul_pow,Real.sq_sqrt hW.le]
    convert Real.exp_le_exp.mpr (neg_le_neg hc1) using 1
    congr 1
    ring
  have h3 : Real.exp (-2*(A/8/4)^2/(k*V*T))≤Real.exp (-c) := by
    have hd : 512*k*V*T≤8192*(k:ℝ)^2*T*V := by
      have hkk : 0≤(k:ℝ)^2-k := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hp.le hV.le) hkk,
        show 0≤(k:ℝ)*V*T by positivity]
    have hh := exponential_fraction_bound (A^2) (512*k*V*T) (8192*(k:ℝ)^2*T*V) c
      (sq_nonneg _) (by positivity) hd hc2
    convert hh using 1
    congr 1
    ring
  have h4 : Real.exp (-8*(A/8/(8*k))^2/(V*T))≤Real.exp (-c) := by
    have hh := exponential_fraction_bound (A^2) (512*(k:ℝ)^2*V*T) (8192*(k:ℝ)^2*T*V) c
      (sq_nonneg _) (by positivity) (by nlinarith [mul_pos (sq_pos_of_pos (show (0:ℝ)<k by positivity)) (mul_pos hp hV)]) hc2
    convert hh using 1
    congr 1
    ring
  have h5 : q≤Real.exp (-c) := by
    dsimp [q]
    convert Real.exp_le_exp.mpr (neg_le_neg hc2) using 1
    congr 1
    ring
  change prob _ _≤_ at h
  dsimp only [T] at h1 h2 h3 h4 h5
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h4 h5) (show (0:ℝ)≤k by positivity)]

end
end Max2SAT.Counts
