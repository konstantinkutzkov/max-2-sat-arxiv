import Max2SAT.Community.FrameResidual
import Max2SAT.Community.FormulaScale

/-! Concrete discovery from the input formula, with no numerical callback.
Small dimensions below the fixed rank parameter use the zero representation;
the previously checked search is exact for that representation as well. -/
namespace Max2SAT.Community
open Counts FiniteLaw RandomInput IndependentPairs
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} [Fintype α]
set_option maxHeartbeats 1000000

def discoverFormula (r : ℕ) (F : Formula n) : Representation n r :=
  if hrn : r≤n then
    sortedFrameRepresentation F (computedFrame (formulaMatrix F)) hrn
  else ⟨fun _ => 0,fun _ _ => 0,1⟩

def diagonalizedResult (F : Formula n) (r : ℕ) (g : ℚ) : Option (ℤ × Assignment n) :=
  computedResult F g (discoverFormula r)

def diagonalizedNodes (F : Formula n) (r : ℕ) (g : ℚ) : ℕ :=
  computedNodes F g (discoverFormula r)

theorem formula_matrix_symmetric (F : Formula n) (hF : wellFormed F) : (formulaMatrix F).IsSymm := by
  ext i j
  exact gainExpr_symmetric F hF j i

/-- The entire algorithm, including numerical discovery, is total and exact
for every well-formed explicitly listed input formula. -/
theorem diagonalized_result_correct (F : Formula n) (r : ℕ) (g : ℚ) (hF : wellFormed F) :
    ∃ q x, diagonalizedResult F r g=some (q,x) ∧ q=score F x ∧ ∀ y, score F y≤q :=
  computed_result_correct F g (discoverFormula r) hF

noncomputable section

theorem computed_discovery_guarantees (F : Formula n) (r : ℕ) (hrn : r≤n)
    (A X : Matrix (Fin n) (Fin n) ℝ) (B₀ ν χ : ℝ)
    (hF : wellFormed F) (hA : A.IsHermitian) (hr : A.rank≤r)
    (hB : 0≤B₀) (hν : 0≤ν) (hχ : 0≤χ)
    (hmodel : interactionMatrix (gainExpr F)=A+X-Matrix.diagonal (fun i => A i i))
    (hdiag : ∀ i, |A i i|≤B₀)
    (hnoise : ‖X‖≤(58/10:ℝ)*Real.sqrt (n*χ*ν))
    (hBsmall : B₀≤Real.sqrt (n*χ*ν)) (hζsmall : 1/(n:ℝ)^4≤Real.sqrt (n*χ*ν))
    (hsize : 5120000*r*χ≤(n:ℝ)) :
    ApproximationGuarantees F (discoverFormula r F) A X B₀ (1/(n:ℝ)^4) ν := by
  unfold discoverFormula
  rw [dite_eq_left hrn]
  exact sorted_frame_approximation_guarantees F (computedFrame (formulaMatrix F)) hrn A X B₀
    (1/(n:ℝ)^4) ν χ (computed_frame_orthogonal _) hA hr hB (by positivity) hν hχ
    hmodel hdiag (computed_frame_residual _ (formula_matrix_symmetric F hF)) hnoise hBsmall hζsmall hsize

/-- The high-probability node bound now applies to the concrete algorithm.
No diagonalization, truncation, rank-error, or discovery callback hypothesis
is left. FamilyRuntime discharges these explicit density/size conditions
from the paper hypothesis; SBMRuntime specializes the original graph law. -/
theorem diagonalized_search_probability
    (bvh : External.BandeiraVanHandel n) (ledoux : External.LedouxUpperTail (Edge n) α)
    (p : Edge n → Law α) (X : Edge n → α → ℝ)
    (input : (Edge n → α) → Formula n) (r : ℕ) (hrn : r≤n)
    (A : Matrix (Fin n) (Fin n) ℝ) (g : ℚ) (B ν χ μ B₀ : ℝ)
    (hn : 100≤n) (hg : 0<g) (hB : 0<B) (hν : 0<ν) (hχ : 1≤χ)
    (hμ : 0≤μ) (hB₀ : 0≤B₀) (hAsym : A.IsHermitian) (hr : A.rank≤r)
    (hgu : (g:ℝ)≤1/(256*Real.sqrt χ))
    (hm : ∀ e, expect (p e) (X e)=0)
    (hb : ∀ e x, 0<(p e).mass x → |X e x|≤B)
    (hv : ∀ e, ν≤expect (p e) (fun x => (X e x)^2) ∧
      expect (p e) (fun x => (X e x)^2)≤χ*ν)
    (hd : (10^9:ℝ)*χ*B^2*Real.log n≤n*ν)
    (hF : ∀ x, wellFormed (input x))
    (hmodel : ∀ x, interactionMatrix (gainExpr (input x))=
      A+pairMatrix (fun e => X e (x e))-Matrix.diagonal (fun i => A i i))
    (hA : ‖A‖≤μ*n) (hdiag : ∀ i, |A i i|≤B₀)
    (hBsmall : B₀≤Real.sqrt (n*χ*ν)) (hζsmall : 1/(n:ℝ)^4≤Real.sqrt (n*χ*ν))
    (hmean : (256*r*μ)^2≤(g:ℝ)^2*n*ν)
    (hsize : 1792*r*Real.sqrt χ≤(g:ℝ)*n)
    (hcorrection : 5120000*r*χ≤(n:ℝ)) :
    1-1/(n:ℝ)≤prob (product p) (fun x =>
      (diagonalizedNodes (input x) r g:ℝ)≤(4*(n:ℝ)+3)^r*(2+14*n)*
        (exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ)))^n) ∧
      exponentialBase (1/2) (roundRate 2 (1/2) (g:ℝ) (400*χ))<2 := by
  apply discovered_search_probability bvh ledoux p X input (discoverFormula r) A g B ν χ μ B₀
    (1/(n:ℝ)^4) hn hg hB hν hχ hμ hB₀ (by positivity) hgu hm hb hv hd hF hmodel hA
    hdiag hBsmall hζsmall hmean hsize
  intro x _ hraw
  exact computed_discovery_guarantees (input x) r hrn A _ B₀ ν χ (hF x) hAsym hr hB₀ hν.le
    (by linarith) (hmodel x) hdiag hraw.2 hBsmall hζsmall hcorrection

end
end Max2SAT.Community
