import Max2SAT.IndependentPairs.MatrixGeometry
import Max2SAT.Random.ConcentrationTools

/-! Explicit external-theorem statements, not postulates or proved theorems.

`BandeiraVanHandel` is the square case of Theorem 3.1 and its Rademacher
extension in Corollary 3.2 of Bandeira--van Handel, Ann. Probab. 44 (2016),
2479--2506, DOI 10.1214/15-AOP1025. Row, column and entry maxima are expressed
by arbitrary upper bounds, an equivalent formulation of the published bound.

`LedouxUpperTail` is the convex special case of Corollary 3.3 and its interval
rescaling on pp. 165--166 of Ledoux, Seminaire de Probabilites XXXIII (1999),
120--216. It bounds the upper tail around the expectation directly. The
source permits separately convex functions; we only need globally convex ones.

Both statements are arguments to the application theorems. They are not
asserted as Lean theorems. See verification/EXTERNAL_RESULTS.txt for the source
mapping, conventions, and exact limits of the conditional verification. -/
namespace Max2SAT.IndependentPairs.External
noncomputable section
open FiniteLaw RandomInput
open scoped Matrix.Norms.L2Operator

/-- A named matrix avoids inferring the default function-space norm on an
inline two-argument lambda. All norms below use the matrix operator instance. -/
def signedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin n × Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => sign (s (i,j))*A i j

/-- Rademacher operator-norm estimate, on square arrays (including zeros). -/
def BandeiraVanHandel (n : ℕ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℝ) (θ r c b : ℝ),
    0<n → 0<θ → θ≤1/2 → 0≤r → 0≤c → 0≤b →
    (∀ i, Real.sqrt (∑ j, (A i j)^2)≤r) →
    (∀ j, Real.sqrt (∑ i, (A i j)^2)≤c) →
    (∀ i j, |A i j|≤b) →
    expect (fairBits (Fin n × Fin n))
      (fun s => ‖signedMatrix A s‖)≤
      (1+θ)*(r+c+5*b*Real.sqrt (Real.log n)/Real.sqrt (Real.log (1+θ)))

/-- Finite-law form of the published upper-tail inequality on [-B,B]. -/
def LedouxUpperTail (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α] : Prop :=
  ∀ (p : ι → Law α) (X : ι → α → ℝ) (f : EuclideanSpace ℝ ι → ℝ) (B r : ℝ),
    0<B → 0<r →
    (∀ i x, 0<(p i).mass x → |X i x|≤B) →
    ConvexOn ℝ Set.univ f → LipschitzWith 1 f →
    prob (product p) (fun x =>
      expect (product p) (fun y => f (WithLp.toLp 2 (fun i => X i (y i))))+r <
        f (WithLp.toLp 2 (fun i => X i (x i))))≤Real.exp (-r^2/(8*B^2))

end
end Max2SAT.IndependentPairs.External
