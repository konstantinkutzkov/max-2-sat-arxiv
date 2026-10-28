import Max2SAT.Counts.CubeEntropy
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace Max2SAT.Counts
noncomputable section
open FiniteLaw Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- An elementary bound sufficient for the exponential substitution. -/
theorem exponential_difference_sq (a b : ℝ) :
    (Real.exp a-Real.exp b)^2≤(a-b)^2*(Real.exp (2*a)+Real.exp (2*b)) := by
  have hordered : ∀ a b : ℝ, b≤a →
      (Real.exp a-Real.exp b)^2≤(a-b)^2*(Real.exp (2*a)+Real.exp (2*b)) := by
    intro a b hba
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_pos a).le
    rw [←Real.exp_add,show a+(b-a)=b by ring] at hh
    have hd : 0≤Real.exp a-Real.exp b := sub_nonneg.mpr (Real.exp_le_exp.mpr hba)
    have hu : Real.exp a-Real.exp b≤(a-b)*Real.exp a := by nlinarith
    have hs := mul_self_le_mul_self hd hu
    have he : (Real.exp a)^2=Real.exp (2*a) := by rw [pow_two,←Real.exp_add]; congr 1; ring
    have hz : 0≤(a-b)^2*Real.exp (2*b) := by positivity
    nlinarith [he]
  by_cases h : b≤a
  · exact hordered a b h
  · have hh := hordered b a (le_of_not_ge h)
    nlinarith

theorem cube_flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (cubeFlip i) := by
  intro x
  funext j
  by_cases h : j=i <;> simp [cubeFlip,Function.update,h]

theorem cube_mean_flip {n : ℕ} (i : Fin n) (f : Assignment n → ℝ) :
    cubeMean n (fun x => f (cubeFlip i x))=cubeMean n f := by
  let e : Assignment n ≃ Assignment n :=
    ⟨cubeFlip i,cubeFlip i,cube_flip_involutive i,cube_flip_involutive i⟩
  simpa only [cubeMean,expect,fairBits_mass,Fintype.card_fin] using
    (show (∑ x, (1/2:ℝ)^n*f (cubeFlip i x)) = ∑ x, (1/2:ℝ)^n*f x from
      e.sum_comp (fun x => (1/2:ℝ)^n*f x))

theorem cube_edge_energy {n : ℕ} (a f : Assignment n → ℝ) :
    cubeMean n (fun x => ∑ i,
      (a x+a (cubeFlip i x))*(f x-f (cubeFlip i x))^2) =
      2*cubeMean n (fun x => a x*∑ i, (f x-f (cubeFlip i x))^2) := by
  have hh : ∀ i : Fin n,
      cubeMean n (fun x => a (cubeFlip i x)*(f x-f (cubeFlip i x))^2) =
      cubeMean n (fun x => a x*(f x-f (cubeFlip i x))^2) := by
    intro i
    have he := cube_mean_flip i (fun x => a x*(f x-f (cubeFlip i x))^2)
    change cubeMean n (fun x => a (cubeFlip i x)*
      (f (cubeFlip i x)-f (cubeFlip i (cubeFlip i x)))^2)=_ at he
    convert he using 1
    congr 1
    funext x
    rw [cube_flip_involutive i x]
    ring
  simp only [cubeMean,add_mul,Finset.mul_sum,expect_sum,expect_add]
  simp only [hh]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cube_entropy_exponential {n : ℕ} (f : Assignment n → ℝ)
    (B t : ℝ) (hB : ∀ x, (∑ i, (f x-f (cubeFlip i x))^2)≤B) :
    cubeEntropy n (fun x => Real.exp (t*f x)) ≤
      t^2*B/2*cubeMean n (fun x => Real.exp (t*f x)) := by
  let g : Assignment n → ℝ := fun x => Real.exp (t*f x/2)
  have he : ∀ x, (g x)^2=Real.exp (t*f x) := by
    intro x
    dsimp [g]
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have h := cube_log_sobolev n g (fun _ => Real.exp_pos _)
  simp_rw [he] at h
  apply h.trans
  have hp : ∀ x, (∑ i, (g x-g (cubeFlip i x))^2) ≤
      t^2/4*(∑ i, (Real.exp (t*f x)+Real.exp (t*f (cubeFlip i x)))*
        (f x-f (cubeFlip i x))^2) := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := exponential_difference_sq (t*f x/2) (t*f (cubeFlip i x)/2)
    convert hh using 1
    ring_nf
  have hh := expect_mono (fairBits (Fin n)) hp
  have hm : cubeMean n (fun x =>
      Real.exp (t*f x)*(∑ i, (f x-f (cubeFlip i x))^2)) ≤
        cubeMean n (fun x => Real.exp (t*f x))*B := by
    rw [←expect_mul_const]
    apply expect_mono
    intro x
    exact mul_le_mul_of_nonneg_left (hB x) (Real.exp_pos _).le
  have eh : cubeMean n (fun x => t^2/4*(∑ i,
      (Real.exp (t*f x)+Real.exp (t*f (cubeFlip i x)))*(f x-f (cubeFlip i x))^2)) =
      t^2/4*(2*cubeMean n (fun x => Real.exp (t*f x)*∑ i,
        (f x-f (cubeFlip i x))^2)) := by
    calc
      _ = t^2/4*cubeMean n (fun x => ∑ i,
          (Real.exp (t*f x)+Real.exp (t*f (cubeFlip i x)))*(f x-f (cubeFlip i x))^2) := by
        simp only [cubeMean,expect,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [cube_edge_energy]
  change cubeMean n (fun x => ∑ i, (g x-g (cubeFlip i x))^2) ≤
    cubeMean n (fun x => t^2/4*(∑ i,
      (Real.exp (t*f x)+Real.exp (t*f (cubeFlip i x)))*(f x-f (cubeFlip i x))^2)) at hh
  rw [eh] at hh
  have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
  nlinarith

end
end Max2SAT.Counts
