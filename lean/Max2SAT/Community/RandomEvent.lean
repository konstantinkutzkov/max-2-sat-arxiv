import Max2SAT.Community.CrossRows
import Max2SAT.Community.Noise
import Max2SAT.IndependentPairs.Membership

/-! The joint noise event used by hidden-mean discovery, proved from the
original independent entries. Only the two named matrix results remain
external hypotheses; the rectangular row estimates are proved here. -/
namespace Max2SAT.Community
noncomputable section
open FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {α : Type*} [Fintype α]
set_option maxHeartbeats 1000000

def rawScalarGood (z : Edge n → ℝ) (ν χ : ℝ) : Prop :=
  ((99/100:ℝ)*((n:ℝ)-1)*ν≤pairEnergy z ∧
    pairEnergy z≤(101/100:ℝ)*((n:ℝ)-1)*χ*ν) ∧
  ∀ t∈secondRound n, (99/100:ℝ)*(firstRound n).card*ν≤
    ∑ j∈firstRound n, (pairMatrix z t j)^2

def rawGood (z : Edge n → ℝ) (ν χ : ℝ) : Prop :=
  rawScalarGood z ν χ ∧ ‖pairMatrix z‖≤(58/10:ℝ)*Real.sqrt (n*χ*ν)

theorem discovery_scalar_probability (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (hn : 20≤n) (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤n*ν) :
    prob (product p) (fun x => ¬rawScalarGood (fun e => X e (x e)) ν χ)≤
      ((secondRound n).card+2:ℝ)/(n:ℝ)^3 := by
  let z := fun (x : Edge n → α) e => X e (x e)
  let energyBad := fun x => pairEnergy (z x)<(99/100:ℝ)*((n:ℝ)-1)*ν ∨
    (101/100:ℝ)*((n:ℝ)-1)*χ*ν<pairEnergy (z x)
  let rowBad := fun t x => (∑ j∈firstRound n, (pairMatrix (z x) t j)^2)≤
    (99/100:ℝ)*(firstRound n).card*ν
  have hpair := pair_count_real (n:=n) (by omega)
  have hn20 : (20:ℝ)≤n := by exact_mod_cast hn
  have hpc : (n:ℝ)/10≤Fintype.card (Edge n) := by nlinarith
  have htlo := row_failure_bound n B ν χ 1 _ (by omega) hB hν.le hχ (by norm_num)
    (by simpa using hpc) (by simpa using hd)
  have hthi : Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2))≤
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ)) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ (by positivity : 0<4*B^2) (by positivity : 0<4*B^2*χ)).mpr
    have hm := mul_le_mul_of_nonneg_left (show 1≤χ^2 by nlinarith)
      (show 0≤(Fintype.card (Edge n):ℝ)*ν*B^2 by positivity)
    nlinarith
  have he : prob (product p) energyBad≤2/(n:ℝ)^3 := by
    have hh := raw_energy_tails p X (by omega) B ν χ (1/100) hB hν hχ
      (by norm_num) (by norm_num) hb hv
    have he' : prob (product p) energyBad≤
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*ν/(4*B^2*χ))+
      Real.exp (-(1/100:ℝ)^2*(Fintype.card (Edge n):ℝ)*χ*ν/(4*B^2)) := by
      simpa only [energyBad,z,show (1:ℝ)-1/100=99/100 by norm_num,
        show (1:ℝ)+1/100=101/100 by norm_num] using hh
    exact he'.trans ((add_le_add htlo (hthi.trans htlo)).trans_eq (by ring))
  have hr : ∀ t∈secondRound n, prob (product p) (rowBad t)≤1/(n:ℝ)^3 := by
    intro t ht
    have hc := (round_sizes hn).1
    have ht := two_round_row_tail p X t ht (by omega) B ν χ hB hν hχ hb hv
    apply ht.trans
    exact row_failure_bound n B ν χ 1 _ (by omega) hB hν.le hχ (by norm_num)
      (by simp only [one_mul]; linarith) (by simpa using hd)
  have hrs := (Counts.finite_union_bound (product p) (secondRound n) rowBad).trans
    (Finset.sum_le_sum hr)
  simp only [Finset.sum_const,nsmul_eq_mul] at hrs
  have hsub := prob_mono_support (product p)
    (fun x => ¬rawScalarGood (z x) ν χ)
    (fun x => energyBad x ∨ ∃ t∈secondRound n, rowBad t x) (by
      intro x _ hbad
      by_contra h
      apply hbad
      refine ⟨⟨?_,?_⟩,?_⟩
      · exact le_of_not_gt (fun hh => h (Or.inl (Or.inl hh)))
      · exact le_of_not_gt (fun hh => h (Or.inl (Or.inr hh)))
      · intro t ht
        exact le_of_not_gt (fun hh => h (Or.inr ⟨t,ht,hh.le⟩)))
  apply hsub.trans
  have hu := prob_union_le (product p) energyBad (fun x => ∃ t∈secondRound n, rowBad t x)
  calc
    _ ≤ _ := hu
    _ ≤ 2/(n:ℝ)^3+(secondRound n).card*(1/(n:ℝ)^3) := add_le_add he hrs
    _ = _ := by ring

/-- All scalar rows, total energy and the symmetric matrix norm hold jointly
with probability at least 1-1/n. Rows may share unordered-pair coordinates. -/
theorem discovery_noise_probability
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (hn : 20≤n) (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤n*ν) :
    1-1/(n:ℝ)≤prob (product p) (fun x => rawGood (fun e => X e (x e)) ν χ) := by
  have hs := discovery_scalar_probability p X hn B ν χ hB hν hχ hb hv hd
  have hlog : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hd' : (10^9:ℝ)*B^2*Real.log n≤n*χ*ν := by
    have h1 := mul_le_mul_of_nonneg_right hχ (show 0≤(10^9:ℝ)*B^2*Real.log n by positivity)
    have h2 := mul_le_mul_of_nonneg_right hχ (show 0≤(n:ℝ)*ν by positivity)
    nlinarith
  have hmN := symmetric_noise_tail bvh ledoux p X (by omega) B ν χ hB hν
    (by linarith) hm hb (fun e => (hv e).2) hd'
  apply success_of_failure
  have hu := prob_union_le (product p)
    (fun x => ¬rawScalarGood (fun e => X e (x e)) ν χ)
    (fun x => (58/10:ℝ)*Real.sqrt (n*χ*ν)<‖pairMatrix (fun e => X e (x e))‖)
  have hsub := prob_mono_support (product p)
    (fun x => ¬rawGood (fun e => X e (x e)) ν χ) _ (by
      intro x _ hx
      by_contra hh
      apply hx
      exact ⟨not_not.mp (fun h => hh (Or.inl h)),le_of_not_gt (fun h => hh (Or.inr h))⟩)
  apply (hsub.trans hu).trans
  apply (add_le_add hs hmN).trans
  have hc : ((secondRound n).card:ℝ)≤n := by
    exact_mod_cast (show (secondRound n).card≤n by simpa using Finset.card_le_univ (secondRound n))
  have hn20 : (20:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  field_simp
  nlinarith [sq_nonneg ((n:ℝ)-1)]

/-- Convert the normalization in the probability model to the explicit
Frobenius inequalities used in deterministic perturbation. -/
theorem raw_good_energy (z : Edge n → ℝ) (ν χ : ℝ) (hn : 0<n)
    (h : rawGood z ν χ) :
    (99/100:ℝ)*n*((n:ℝ)-1)*ν≤(frobenius (pairMatrix z))^2 ∧
    (frobenius (pairMatrix z))^2≤(101/100:ℝ)*χ*n*((n:ℝ)-1)*ν := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have he : pairEnergy z=(frobenius (pairMatrix z))^2/n := by rw [pairEnergy,frobenius_square]
  have hh := h.1.1
  rw [he] at hh
  have hlo := (le_div_iff₀ hn0).mp hh.1
  have hhi := (div_le_iff₀ hn0).mp hh.2
  constructor <;> nlinarith

end
end Max2SAT.Community
