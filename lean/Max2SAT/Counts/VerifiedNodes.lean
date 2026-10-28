import Max2SAT.Counts.VerifiedAccumulation

/-! Close the probability-to-execution link, including the two equivalent
finite fair-bit probability representations and every supplied guess. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {ι : Type*}

theorem cube_mean_eq_average (n : ℕ) (f : Assignment n → ℝ) :
    cubeMean n f=FairCoin.average n f := by
  induction n with
  | zero =>
    simp only [cubeMean,expect,fairBits_mass,FairCoin.average]
    simp
    congr 1
  | succ n ih =>
    rw [cube_mean_succ,FairCoin.average]
    have he : cubeMean n (fun x => (f (Fin.cons false x)+f (Fin.cons true x))/2)=
        (cubeMean n (fun x => f (Fin.cons false x))+cubeMean n (fun x => f (Fin.cons true x)))/2 := by
      change (∑ x, (fairBits (Fin n)).mass x *
        ((f (Fin.cons false x)+f (Fin.cons true x))/2)) = _
      simp_rw [←mul_div_assoc,mul_add]
      rw [←Finset.sum_div,Finset.sum_add_distrib]
      rfl
    rw [he,ih,ih]

theorem fair_probability_bridge (n : ℕ) (E : Assignment n → Prop) :
    prob (fairBits (Fin n)) E=FairCoin.probability n E := by
  rw [FairCoin.probability,←cube_mean_eq_average]
  simp only [cubeMean,expect,prob,mul_ite,mul_one,mul_zero]

theorem sequential_runs_nodes (guesses : List ι) (H : ι → Fin n → Affine n)
    (P : Finset (Fin n)) (hr : EarlierInPrefix P (fun i => i.val)) (hP : 0<P.card)
    (hsym : ∀ b∈guesses, ∀ t w, (H b t).coeff w=(H b w).coeff t)
    (hdiag : ∀ b∈guesses, ∀ t, (H b t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈P, 0≤s t)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : (P.card:ℝ)≤τ*n)
    (hN : ∀ b∈guesses, ‖sequentialMatrix (H b) P‖^2≤K*D)
    (hprofile : ∀ b∈guesses, 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : P, Real.sqrt (∑ w, (earlierRow (H b) (fun i => i.val) t w)^2))
    (hslack : (∑ t∈P, (s t : ℝ))≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount guesses (fun b => comparisonBudget (H b) s P (fun i => i.val)) P : ℝ)≤
      guesses.length*(2+6*n)*(exponentialBase τ (sequentialRate τ g K))^n ∧
      exponentialBase τ (sequentialRate τ g K)<2 := by
  constructor
  · have h := all_runs_exponential guesses (fun b => comparisonBudget (H b) s P (fun i => i.val))
      P (fun _ _ => comparison_stable _ _ _ _ hr) τ (sequentialRate τ g K) 3
      (by norm_num) hsize (by
        intro b hb
        rw [←fair_probability_bridge]
        exact sequential_passing_paper (H b) P hr hP (hsym b hb) (hdiag b hb) s hs
          τ g K D hτ hg hK hD hsize (hN b hb) (hprofile b hb) hslack)
    convert h using 1
    ring
  · exact exponential_base_lt_two τ _ hτ1 (sequential_rate_pos τ g K hτ hg hK)

theorem round_runs_nodes (guesses : List ι) (H : ι → Fin n → Affine n)
    (round : Fin n → ℕ) (k : ℕ) (hk : 2≤k)
    (horder : OrderedRounds round) (hround : ∀ t, round t≤k)
    (hP : 0<(roundPrefix round k).card)
    (hsym : ∀ b∈guesses, ∀ t w, (H b t).coeff w=(H b w).coeff t)
    (hdiag : ∀ b∈guesses, ∀ t, (H b t).coeff t=0)
    (s : Fin n → ℚ) (hs : ∀ t∈roundPrefix round k, 0≤s t)
    (τ g K D : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hg : 0<g) (hK : 0<K) (hD : 0<D)
    (hsize : ((roundPrefix round k).card:ℝ)≤τ*n)
    (hN : ∀ b∈guesses, ‖interactionMatrix (H b)‖^2≤K*D)
    (hprofile : ∀ b∈guesses, 4*Real.sqrt 3*(g*n*Real.sqrt D)≤
      ∑ t : roundPrefix round k, Real.sqrt (∑ w, (earlierRow (H b) round t w)^2))
    (hslack : (∑ t∈roundPrefix round k, (s t : ℝ))≤g*n*Real.sqrt D/8) :
    (Runs.nodeCount guesses (fun b => comparisonBudget (H b) s (roundPrefix round k) round)
      (roundPrefix round k) : ℝ)≤
      guesses.length*(2+2*n*(3+2*k))*(exponentialBase τ (roundRate k τ g K))^n ∧
      exponentialBase τ (roundRate k τ g K)<2 := by
  constructor
  · apply all_runs_exponential guesses (fun b => comparisonBudget (H b) s (roundPrefix round k) round)
      (roundPrefix round k) (fun _ _ => comparison_stable _ _ _ _ (round_prefix_closed round k))
      τ (roundRate k τ g K) (3+2*k) (by positivity) hsize
    intro b hb
    rw [←fair_probability_bridge]
    exact round_passing_paper (H b) round k hk horder hround hP (hsym b hb) (hdiag b hb)
      s hs τ g K D hτ hg hK hD hsize (hN b hb) (hprofile b hb) hslack
  · exact exponential_base_lt_two τ _ hτ1 (round_rate_pos k hk τ g K hτ hg hK)

end
end Max2SAT.Counts
