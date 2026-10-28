import Max2SAT.IndependentPairs.MatrixNorm
import Max2SAT.Community.Perturbation

/-! A symmetric noise bound from the already verified upper-triangle
estimate. This avoids an additional external symmetric-matrix theorem.
The larger numerical constant does not alter the input family. -/
namespace Max2SAT.Community
noncomputable section
open FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} [Fintype α]

theorem symmetric_from_upper (z : Edge n → ℝ) :
    pairMatrix z=upperMatrix n z+(upperMatrix n z).transpose := by
  ext i j
  rcases lt_trichotomy i j with h|rfl|h
  · simp [pairMatrix,upperMatrix,Matrix.transpose_apply,h,not_lt.mpr h.le,i.isLt]
  · simp [pairMatrix,upperMatrix]
  · simp [pairMatrix,upperMatrix,Matrix.transpose_apply,h,not_lt.mpr h.le,j.isLt]

theorem symmetric_norm_from_upper (z : Edge n → ℝ) : ‖pairMatrix z‖≤2*‖upperMatrix n z‖ := by
  rw [symmetric_from_upper]
  have he : ‖(upperMatrix n z).transpose‖=‖upperMatrix n z‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose (upperMatrix n z)
  have h := norm_add_le (upperMatrix n z) (upperMatrix n z).transpose
  rw [he] at h
  linarith

/-- The full symmetric centered matrix has norm <=5.8 sqrt(n chi nu),
except with probability at most n^-3, under the same density budget. -/
theorem symmetric_noise_tail
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (hn : 2≤n) (B ν χ : ℝ) (hB : 0<B) (hν : 0<ν) (hχ : 0<χ)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hdensity : (10^9:ℝ)*B^2*Real.log n≤n*χ*ν) :
    prob (product p) (fun x => (58/10:ℝ)*Real.sqrt (n*χ*ν)<
      ‖pairMatrix (fun e => X e (x e))‖)≤1/(n:ℝ)^3 := by
  apply le_trans (prob_mono_support (product p) _ _ ?_)
    (independent_pair_norm_tail bvh ledoux p X n hn B ν χ hB hν hχ hm hb hv hdensity)
  intro x _ hx
  have h := symmetric_norm_from_upper (fun e => X e (x e))
  linarith

/-- Deterministic consequences of a truncated approximation. Its construction
and low-rank quality will be checked separately; they are explicit here. -/
theorem remainder_operator_bound (J A P X : Matrix (Fin n) (Fin n) ℝ)
    (B₀ ζ : ℝ) (hB : 0≤B₀) (_hζ : 0≤ζ)
    (hmodel : J=A+X-Matrix.diagonal (fun i => A i i))
    (hdiag : ∀ i, |A i i|≤B₀)
    (happrox : ‖J-P‖≤‖X‖+B₀+2*ζ) :
    ‖offDiagonal (J-P)‖≤2*(‖X‖+B₀)+4*ζ ∧
    ‖A-P‖≤2*(‖X‖+B₀)+2*ζ := by
  have hdiagN : ‖Matrix.diagonal (fun i => A i i)‖≤B₀ := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hB).mpr (fun i => by simpa only [Real.norm_eq_abs] using hdiag i)
  have hJA : ‖A-J‖≤‖X‖+B₀ := by
    rw [hmodel]
    have he : A-(A+X-Matrix.diagonal (fun i => A i i))=
        Matrix.diagonal (fun i => A i i)-X := by abel
    rw [he]
    have h := norm_sub_le (Matrix.diagonal (fun i => A i i)) X
    linarith
  constructor
  · have h := off_diagonal_norm (J-P)
    linarith
  · have he : A-P=(A-J)+(J-P) := by abel
    rw [he]
    have h := norm_add_le (A-J) (J-P)
    linarith

/-- A convenient bound for the revised discovery proof. -/
theorem discovery_operator_constant (N : Matrix (Fin n) (Fin n) ℝ)
    (ν χ D : ℝ) (hν : 0≤ν) (hχ : 0≤χ)
    (hD : (9/10:ℝ)*n*ν≤D)
    (hN : ‖N‖≤18*Real.sqrt (n*χ*ν)) : ‖N‖^2≤400*χ*D := by
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hN
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)*χ*ν)] at hs
  have hd := mul_le_mul_of_nonneg_left hD hχ
  nlinarith [show 0≤(n:ℝ)*χ*ν by positivity]

end
end Max2SAT.Community
