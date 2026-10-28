import Max2SAT.Counts.CubeMGF
import Max2SAT.Random.RequirementTail

/-! The finite-sum Herbst argument, including the limit at zero. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- Integrate t*f'(t)-f(t)<=C*t^2 without dividing by zero. -/
theorem herbst_scalar (f d : ℝ → ℝ) (C t : ℝ)
    (hf : ∀ s, HasDerivAt f (d s) s) (h0 : f 0=0) (ht : 0<t)
    (h : ∀ s, 0<s → s*d s-f s≤C*s^2) : f t≤t*d 0+C*t^2 := by
  let k : ℝ → ℝ := fun s => f s/s-C*s
  have hd : ∀ s, 0<s → HasDerivAt k ((d s*s-f s)/s^2-C) s := by
    intro s hs
    convert ((hf s).div (hasDerivAt_id s) hs.ne').sub
      ((hasDerivAt_id s).const_mul C) using 1
    all_goals first | rfl | simp only [mul_one,id_eq]
  have hm : AntitoneOn k (Set.Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (by simpa only [interior_Ioi,Set.mem_Ioi] using hs)).hasDerivWithinAt
    · intro s hs
      have hpos : 0<s := by simpa only [interior_Ioi,Set.mem_Ioi] using hs
      apply sub_nonpos.mpr
      apply (div_le_iff₀ (sq_pos_of_pos hpos)).2
      nlinarith [h s hpos]
  have hl : Tendsto k (𝓝[>] (0:ℝ)) (𝓝 (d 0)) := by
    have hh := (hf 0).tendsto_slope_zero_right
    have hc : Tendsto (fun s : ℝ => C*s) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
      simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun s : ℝ => C*s) (𝓝[>] 0) (𝓝 (C*0)))
    simpa [k,h0,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh.sub hc
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), k t≤k s := by
    have hst : ∀ᶠ s in 𝓝[>] (0:ℝ), s<t :=
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hst] with s hs hst
    exact hm hs ht hst.le
  have hk : k t≤d 0 := ge_of_tendsto hl he
  dsimp [k] at hk
  have hh : f t/t≤d 0+C*t := by linarith
  have hh' := (div_le_iff₀ ht).mp hh
  nlinarith

def cubeMGF {n : ℕ} (f : Assignment n → ℝ) (t : ℝ) : ℝ :=
  cubeMean n (fun x => Real.exp (t*f x))

def cubeMGFDeriv {n : ℕ} (f : Assignment n → ℝ) (t : ℝ) : ℝ :=
  cubeMean n (fun x => f x*Real.exp (t*f x))

theorem cube_mgf_pos {n : ℕ} (f : Assignment n → ℝ) (t : ℝ) : 0<cubeMGF f t := by
  unfold cubeMGF cubeMean expect
  apply Finset.sum_pos
  · intro x _; exact mul_pos (by rw [fairBits_mass]; positivity) (Real.exp_pos _)
  · exact Finset.univ_nonempty

theorem cube_mgf_deriv {n : ℕ} (f : Assignment n → ℝ) (t : ℝ) :
    HasDerivAt (cubeMGF f) (cubeMGFDeriv f t) t := by
  unfold cubeMGF cubeMGFDeriv cubeMean expect
  apply HasDerivAt.fun_sum
  intro x _
  convert (((hasDerivAt_id t).mul_const (f x)).exp).const_mul
    ((fairBits (Fin n)).mass x) using 1 <;> simp [mul_comm]

theorem cube_mgf_bound_positive {n : ℕ} (f : Assignment n → ℝ) (B t : ℝ) (ht : 0<t)
    (hB : ∀ x, (∑ i, (f x-f (cubeFlip i x))^2)≤B) :
    cubeMGF f t≤Real.exp (t*cubeMean n f+t^2*B/2) := by
  have hd : ∀ s, HasDerivAt (fun s => Real.log (cubeMGF f s))
      (cubeMGFDeriv f s/cubeMGF f s) s := by
    intro s; exact (cube_mgf_deriv f s).log (cube_mgf_pos f s).ne'
  have hz : cubeMGF f 0=1 := by simp [cubeMGF,cubeMean]
  have hd0 : cubeMGFDeriv f 0=cubeMean n f := by simp [cubeMGFDeriv]
  have hh := herbst_scalar (fun s => Real.log (cubeMGF f s))
    (fun s => cubeMGFDeriv f s/cubeMGF f s) (B/2) t hd
    (by rw [hz,Real.log_one]) ht (by
      intro s _
      have h := cube_entropy_exponential f B s hB
      have he : cubeEntropy n (fun x => Real.exp (s*f x)) =
          s*cubeMGFDeriv f s-cubeMGF f s*Real.log (cubeMGF f s) := by
        unfold cubeEntropy cubeMGF cubeMGFDeriv
        simp only [Real.log_exp,cubeMean,expect,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [he] at h
      apply (mul_le_mul_iff_right₀ (cube_mgf_pos f s)).mp
      convert h using 1
      · field_simp [(cube_mgf_pos f s).ne']
      · dsimp [cubeMGF]; ring)
  rw [hz,hd0,div_one] at hh
  have h := Real.exp_le_exp.mpr hh
  rw [Real.exp_log (cube_mgf_pos f t)] at h
  convert h using 1
  congr 1
  ring


/-- Both signs are covered, although only the lower tail is needed here. -/
theorem cube_lower_tail {n : ℕ} (f : Assignment n → ℝ) (B a : ℝ)
    (hB : 0<B) (ha : 0<a)
    (henergy : ∀ x, (∑ i, (f x-f (cubeFlip i x))^2)≤B) :
    prob (fairBits (Fin n)) (fun x => f x<cubeMean n f-a)≤Real.exp (-a^2/(2*B)) := by
  let t := a/B
  have ht : 0<t := div_pos ha hB
  have hn : cubeMean n (fun x => -f x)= -cubeMean n f := by
    simp [cubeMean,expect,Finset.sum_neg_distrib]
  have hm := cube_mgf_bound_positive (fun x => -f x) B t ht (by
    intro x
    convert henergy x using 1
    apply Finset.sum_congr rfl
    intro i _
    ring)
  rw [hn] at hm
  have hs := prob_mono_support (fairBits (Fin n))
    (fun x => f x<cubeMean n f-a) (fun x => a-cubeMean n f≤ -f x)
    (by intro x _ hx; linarith)
  have h := exponential_markov (fairBits (Fin n)) (fun x => -f x) t (a-cubeMean n f) ht
  have he : expect (fairBits (Fin n)) (fun x => Real.exp (t*(-f x)))=cubeMGF (fun x => -f x) t := rfl
  rw [he] at h
  have hh := hs.trans (h.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le))
  rw [←Real.exp_add] at hh
  have ee : -t*(a-cubeMean n f)+(t*(-cubeMean n f)+t^2*B/2)= -a^2/(2*B) := by
    dsimp [t]
    field_simp
    ring
  rwa [ee] at hh

end
end Max2SAT.Counts
