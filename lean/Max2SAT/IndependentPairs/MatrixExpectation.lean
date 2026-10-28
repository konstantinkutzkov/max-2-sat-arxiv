import Max2SAT.IndependentPairs.ExternalResults
import Max2SAT.IndependentPairs.Symmetrization

/-! Application of the published Rademacher expectation estimate.
Symmetrization, the change of product law, and sign insertion are proved here;
only the named Rademacher theorem is an external hypothesis. -/
namespace Max2SAT.IndependentPairs
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
variable {n : ℕ} {α : Type*} [Fintype α]

/-- Largest Euclidean row norm; the empty-array value is zero. -/
def rowSize (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)))‖

theorem row_root_le (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Real.sqrt (∑ j, (A i j)^2)≤rowSize A := by
  simpa [rowSize,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs] using
    norm_le_pi_norm (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))) i

def copyLaw (p : Edge n → Law α) := product (fun e => tensor (p e) (p e))
def copyDifference (X : Edge n → α → ℝ) (x : Edge n → α × α) (e : Edge n) : ℝ :=
  X e (x e).1-X e (x e).2

theorem expect_coordinate (p : Edge n → Law α) (X : Edge n → α → ℝ) (e : Edge n) :
    expect (product p) (fun x => X e (x e))=expect (p e) (X e) := by
  rw [←expect_push (product p) (fun x => x e) (X e),push_product_apply]

/-- Jensen's inequality for an independent centered copy, with the actual
pair-to-upper-matrix map rather than an assumed matrix expectation identity. -/
theorem upper_expect_symmetrized (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (T : ℕ) (hm : ∀ e, expect (p e) (X e)=0) :
    expect (product p) (fun x => ‖upperMatrix T (fun e => X e (x e))‖)≤
      expect (copyLaw p) (fun x => ‖upperMatrix T (copyDifference X x)‖) := by
  have hx : ∀ x : Edge n → α,
      ‖upperMatrix T (fun e => X e (x e))‖≤expect (product p)
        (fun y => ‖upperMatrix T (fun e => X e (x e)-X e (y e))‖) := by
    intro x
    have hj := (convexOn_norm (E:=Matrix (Fin n) (Fin n) ℝ) convex_univ).map_sum_le
      (t:=Finset.univ) (w:=(product p).mass)
      (p:=fun y => upperMatrix T (fun e => X e (x e)-X e (y e)))
      (fun y _ => (product p).nonneg y) (product p).total (fun _ _ => Set.mem_univ _)
    have he : (∑ y, (product p).mass y • upperMatrix T (fun e => X e (x e)-X e (y e)))=
        upperMatrix T (fun e => X e (x e)) := by
      ext i j
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,upperMatrix]
      split_ifs with h hT
      · change expect (product p) (fun y => X ⟨(i,j),h⟩ (x ⟨(i,j),h⟩)-
            X ⟨(i,j),h⟩ (y ⟨(i,j),h⟩))=X ⟨(i,j),h⟩ (x ⟨(i,j),h⟩)
        rw [expect_sub,expect_const,expect_coordinate,hm,sub_zero]
      · simp
      · simp
    rw [he] at hj
    exact hj
  have h := expect_mono (product p) hx
  have hlaw := tensor_product_law p p
  have he := congrArg (fun q => expect q
    (fun x => ‖upperMatrix T (copyDifference X x)‖)) hlaw
  rw [expect_push,expect_tensor] at he
  exact h.trans_eq he

def copySwap (s : Edge n → Bool) : (Edge n → α × α) ≃ (Edge n → α × α) :=
  Equiv.piCongrRight (fun e => if s e then Equiv.refl _ else Equiv.prodComm α α)

theorem copy_swap_mass (p : Edge n → Law α) (s : Edge n → Bool)
    (x : Edge n → α × α) : (copyLaw p).mass (copySwap s x)=(copyLaw p).mass x := by
  apply Finset.prod_congr rfl
  intro e _
  cases hs : s e <;> simp [copySwap,hs,tensor,mul_comm]

omit [Fintype α] in
theorem copy_swap_difference (X : Edge n → α → ℝ) (s : Edge n → Bool)
    (x : Edge n → α × α) :
    copyDifference X (copySwap s x)=fun e => sign (s e)*copyDifference X x e := by
  funext e
  cases hs : s e <;> simp [copyDifference,copySwap,hs,sign]

theorem copy_sign_invariance (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (s : Edge n → Bool) (f : (Edge n → ℝ) → ℝ) :
    expect (copyLaw p) (fun x => f (fun e => sign (s e)*copyDifference X x e))=
      expect (copyLaw p) (fun x => f (copyDifference X x)) := by
  simp_rw [←copy_swap_difference]
  unfold expect
  simpa only [copy_swap_mass] using (copySwap (α:=α) s).sum_comp
    (fun x => (copyLaw p).mass x*f (copyDifference X x))

theorem copy_insert_signs (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (f : (Edge n → ℝ) → ℝ) :
    expect (copyLaw p) (fun x => f (copyDifference X x))=
      expect (copyLaw p) (fun x => expect (fairBits (Edge n))
        (fun s => f (fun e => sign (s e)*copyDifference X x e))) := by
  have hs : expect (fairBits (Edge n)) (fun s => expect (copyLaw p)
      (fun x => f (fun e => sign (s e)*copyDifference X x e)))=
      expect (copyLaw p) (fun x => f (copyDifference X x)) := by
    simp_rw [copy_sign_invariance,expect_const]
  rw [←hs]
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Restricting independent signs to distinct upper-pair coordinates gives
exactly the independent sign law used by the matrix estimate. -/
theorem upper_sign_expectation (T : ℕ) (z : Edge n → ℝ) :
    expect (fairBits (Edge n)) (fun s => ‖upperMatrix T (fun e => sign (s e)*z e)‖)=
      expect (fairBits (Fin n × Fin n))
        (fun s => ‖External.signedMatrix (upperMatrix T z) s‖) := by
  have hlaw := product_select (fun _ : Fin n × Fin n => fair)
    (fun e : Edge n => e.val) Subtype.val_injective
  have he := congrArg (fun q => expect q
    (fun s => ‖upperMatrix T (fun e => sign (s e)*z e)‖)) hlaw
  rw [expect_push] at he
  change expect (product (fun _ : Edge n => fair)) _=expect (product (fun _ : Fin n × Fin n => fair)) _
  rw [←he]
  apply congrArg (expect (product (fun _ : Fin n × Fin n => fair)))
  funext s
  apply congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => ‖A‖)
  ext i j
  simp only [upperMatrix,External.signedMatrix]
  split_ifs <;> simp

/-- A direct, parameter-preserving application of the external theorem. -/
theorem upper_rademacher_bound (ext : External.BandeiraVanHandel n) (hn : 0<n)
    (T : ℕ) (z : Edge n → ℝ) (θ b : ℝ) (hθ : 0<θ) (hθ' : θ≤1/2)
    (hb : 0≤b) (hz : ∀ e, |z e|≤b) :
    expect (fairBits (Edge n)) (fun s => ‖upperMatrix T (fun e => sign (s e)*z e)‖)≤
      (1+θ)*(rowSize (upperMatrix T z)+rowSize (upperMatrix T z).transpose+
        5*b*Real.sqrt (Real.log n)/Real.sqrt (Real.log (1+θ))) := by
  rw [upper_sign_expectation]
  apply ext _ θ _ _ b hn hθ hθ' (norm_nonneg _) (norm_nonneg _) hb
  · exact row_root_le _
  · exact row_root_le (upperMatrix T z).transpose
  · intro i j
    dsimp [upperMatrix]
    split_ifs
    · exact hz _
    · simpa using hb
    · simpa using hb

/-- Positive product mass forces every sampled coordinate into its support. -/
theorem product_coordinate_positive {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] (p : ι → Law β) (x : ι → β) (hx : 0<(product p).mass x) (i : ι) :
    0<(p i).mass (x i) := by
  have hne : (∏ j, (p j).mass (x j))≠0 := ne_of_gt hx
  exact lt_of_le_of_ne ((p i).nonneg (x i)) (Ne.symm
    ((Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)))

/-- The elementary second-moment bound on an expectation. -/
theorem expect_le_root_second {β : Type*} [Fintype β] (p : Law β) (f : β → ℝ)
    (V : ℝ) (hV : expect p (fun x => (f x)^2)≤V) : expect p f≤Real.sqrt V := by
  have he : expect p (fun x => (f x-expect p f)^2)=
      expect p (fun x => (f x)^2)-(expect p f)^2 := by
    simp_rw [sub_sq]
    rw [expect_add,expect_sub,expect_const]
    have hh : expect p (fun x => 2*f x*expect p f)=2*(expect p f)^2 := by
      rw [expect_mul_const,expect_const_mul]; ring
    rw [hh]; ring
  have hnon := expect_nonneg p (fun x => sq_nonneg (f x-expect p f))
  rw [he] at hnon
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- Average the external bound after the proved independent-copy and sign
transformations. The two row-size moments remain explicit inputs. -/
theorem upper_expect_from_row_moments (ext : External.BandeiraVanHandel n)
    (hn : 0<n) (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ)
    (B V A C : ℝ) (hB : 0≤B)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hrow : expect (copyLaw p) (fun x => (rowSize (upperMatrix T (copyDifference X x)))^2)≤A)
    (hcol : expect (copyLaw p) (fun x => (rowSize (upperMatrix T (copyDifference X x)).transpose)^2)≤C)
    (hnoise : (1+(1/100:ℝ))*(5*(2*B)*Real.sqrt (Real.log n)/
      Real.sqrt (Real.log (1+(1/100:ℝ))))≤V) :
    expect (product p) (fun x => ‖upperMatrix T (fun e => X e (x e))‖)≤
      (101/100:ℝ)*(Real.sqrt A+Real.sqrt C)+V := by
  have hfirst := upper_expect_symmetrized p X T hm
  rw [copy_insert_signs p X (fun z => ‖upperMatrix T z‖)] at hfirst
  have hbvh := expect_mono_support (copyLaw p) (fun x hx =>
    upper_rademacher_bound ext hn T (copyDifference X x) (1/100) (2*B)
      (by norm_num) (by norm_num) (by positivity) (fun e =>
        difference_bound (p e) (X e) B (hb e) (x e)
          (product_coordinate_positive (fun e => tensor (p e) (p e)) x hx e)))
  have hr := expect_le_root_second (copyLaw p)
    (fun x => rowSize (upperMatrix T (copyDifference X x))) A hrow
  have hc := expect_le_root_second (copyLaw p)
    (fun x => rowSize (upperMatrix T (copyDifference X x)).transpose) C hcol
  rw [expect_const_mul,expect_add,expect_add,expect_const] at hbvh
  linarith [hfirst]

/-- The numerical expectation constant in the manuscript; no randomness or
norm estimate is hidden in this arithmetic step. -/
theorem upper_expect_289 (ext : External.BandeiraVanHandel n) (hn : 0<n)
    (p : Edge n → Law α) (X : Edge n → α → ℝ) (T : ℕ) (B v : ℝ)
    (hB : 0≤B) (hv : 0≤v)
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hrow : expect (copyLaw p) (fun x => (rowSize (upperMatrix T (copyDifference X x)))^2)≤(204/100:ℝ)*v)
    (hcol : expect (copyLaw p) (fun x => (rowSize (upperMatrix T (copyDifference X x)).transpose)^2)≤(204/100:ℝ)*v)
    (hnoise : (1+(1/100:ℝ))*(5*(2*B)*Real.sqrt (Real.log n)/
      Real.sqrt (Real.log (1+(1/100:ℝ))))≤(4/1000:ℝ)*Real.sqrt v) :
    expect (product p) (fun x => ‖upperMatrix T (fun e => X e (x e))‖)≤
      (289/100:ℝ)*Real.sqrt v := by
  have h := upper_expect_from_row_moments ext hn p X T B _ _ _ hB hm hb hrow hcol hnoise
  have hs : Real.sqrt ((204/100:ℝ)*v)≤(14283/10000:ℝ)*Real.sqrt v := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow,Real.sq_sqrt hv]; nlinarith
  nlinarith [Real.sqrt_nonneg v]

end
end Max2SAT.IndependentPairs
