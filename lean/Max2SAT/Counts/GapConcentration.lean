import Max2SAT.Counts.SmoothEnergy
import Max2SAT.Counts.Herbst

/-! Common-gap concentration from the proved finite-cube estimate.
All hypotheses below are deterministic row, norm, and allowance bounds. -/
namespace Max2SAT.Counts
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

def rawRows (L : Matrix κ (Fin n) ℝ) (x : Assignment n) (t : κ) : ℝ :=
  ∑ i, L t i*sign (x i)

omit [DecidableEq κ] in
theorem smooth_proxy_sandwich (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ)
    (M δ : ℝ) (hδ : 0<δ) (x : Assignment n) :
    gapProxy H (rawRows L x) M≤smoothProxy H L M δ x ∧
    smoothProxy H L M δ x≤gapProxy H (rawRows L x) M+Fintype.card κ*δ/2 := by
  have hlo : ∀ t, (if |H t|≤M/2 then |rowValue H L x t| else M/4)≤
      (if |H t|≤M/2 then smoothAbs δ (rowValue H L x t) else M/4) := by
    intro t; split_ifs; exact (smooth_approximation δ _ hδ).1; rfl
  have hhi : ∀ t, (if |H t|≤M/2 then smoothAbs δ (rowValue H L x t) else M/4)≤
      (if |H t|≤M/2 then |rowValue H L x t| else M/4)+δ/2 := by
    intro t; split_ifs; exact (smooth_approximation δ _ hδ).2; linarith
  constructor
  · exact Finset.sum_le_sum (fun t _ => hlo t)
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hhi t)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      mul_div_assoc,smoothProxy,gapProxy,rowValue,rawRows] using h

/-- No concentration estimate is a hypothesis of this theorem. The
first-moment, smoothing, energy, and exponential estimates are proved. -/
theorem common_gap_tail (H : κ → ℝ) (L : Matrix κ (Fin n) ℝ)
    (M δ V E B A : ℝ) (hM : 0<M) (hδ : 0<δ) (hV : 0≤V) (hB : 0<B) (hA : 0<A)
    (hN : ‖L‖^2≤V)
    (henergy : ∀ x, (∑ t, (rawRows L x t)^2)≤E)
    (hrow : ∀ t, Real.sqrt ((∑ i, (L t i)^2)/3)/2≤M/4)
    (hprofile : 2*A≤(∑ t, Real.sqrt ((∑ i, (L t i)^2)/3))/2)
    (hclip : E/M≤A/2) (hsmooth : Fintype.card κ*δ/2≤A/4)
    (hbudget : 2*Fintype.card κ*V+Fintype.card κ*V^2/(2*δ^2)≤B) :
    prob (fairBits (Fin n)) (fun x => (∑ t, min |rowValue H L x t| M)<3*A/4) ≤
      Real.exp (-A^2/(8*B)) := by
  have hm0 := gap_proxy_mean H (fun t i => L t i) M hrow
  have he : ∀ x t, (∑ i, sign (x i)*L t i)=rawRows L x t := by
    intro x t
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he] at hm0
  have hmean : 2*A≤cubeMean n (smoothProxy H L M δ) :=
    hprofile.trans (hm0.trans (expect_mono _ (fun x => (smooth_proxy_sandwich H L M δ hδ x).1)))
  have hs := cube_lower_tail (smoothProxy H L M δ) B (A/2) hB (by positivity)
    (fun x => (smooth_proxy_energy H L M δ V hδ hV hN x).trans hbudget)
  have hi := prob_mono_support (fairBits (Fin n))
    (fun x => (∑ t, min |rowValue H L x t| M)<3*A/4)
    (fun x => smoothProxy H L M δ x<cubeMean n (smoothProxy H L M δ)-A/2) (by
      intro x _ hx
      have hc := clipped_sum_lower H (rawRows L x) M E hM (henergy x)
      have hh := (smooth_proxy_sandwich H L M δ hδ x).2
      change gapProxy H (rawRows L x) M-E/M≤∑ t, min |rowValue H L x t| M at hc
      linarith)
  apply hi.trans
  convert hs using 1
  congr 1
  ring

end
end Max2SAT.Counts
