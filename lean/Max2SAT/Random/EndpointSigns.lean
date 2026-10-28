import Max2SAT.Random.Sampling
import Max2SAT.Random.FreshBits

/-! The symmetry construction and per-edge identities used in
Lemma lem:random_exposure. Exposure.lean assembles the full sequential
connection; these lemmas do not assume cut independence. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

/-- The four-mask formulation in PairLaw is exactly the manuscript's
invariance under complementing either endpoint separately. -/
theorem invariant_iff_endpoints (p : Law (Pattern m)) :
    (∀ mask K, p.mass (flip mask K) = p.mass K) ↔
      (∀ K, p.mass (flip (true,false) K) = p.mass K) ∧
      (∀ K, p.mass (flip (false,true) K) = p.mass K) := by
  constructor
  · intro h
    exact ⟨h (true,false),h (false,true)⟩
  · rintro ⟨hl,hr⟩ ⟨a,b⟩ K
    cases a <;> cases b
    · have he : flip (false,false) K = K := by
        funext s
        rcases s with ⟨c,d⟩
        cases c <;> cases d <;> rfl
      rw [he]
    · exact hr K
    · exact hl K
    · have he : flip (true,true) K = flip (true,false) (flip (false,true) K) := by
        funext s
        rcases s with ⟨c,d⟩
        cases c <;> cases d <;> rfl
      rw [he,hl,hr]

/-- A true auxiliary bit is the sign +1 and leaves the endpoint unchanged. -/
def signedFlip (rho : Signs) : Pattern m ≃ Pattern m := flip (!rho.1,!rho.2)

theorem randomized_pair_law (p : PairLaw m κ) :
    push (tensor p.law uniformSigns) (fun z => signedFlip z.2 z.1) = p.law := by
  apply random_symmetries
  intro rho K
  exact p.invariant (!rho.1,!rho.2) K

/-- Independent base pair draws and independent endpoint masks produce
exactly the original joint pair law. Patterns with stabilizing symmetries
are allowed; no free-action assumption is needed. -/
theorem randomized_pairs_law {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → PairLaw m κ) :
    push (product (fun e => tensor (p e).law uniformSigns))
      (fun z e => signedFlip (z e).2 (z e).1) = product (fun e => (p e).law) := by
  have hh := product_push (fun e => tensor (p e).law uniformSigns)
    (fun _ z => signedFlip z.2 z.1)
  apply hh.trans
  congr 1
  funext e
  exact randomized_pair_law (p e)

/-- Contribution of a sampled pair to the score gain when the selected
endpoint changes from false to true. -/
def pairGain (left : Bool) (K : Pattern m) (x : Bool) : ℝ :=
  ∑ s, if endpoint (!left) s ≠ x then (K s).val * sign (endpoint left s) else 0

def eta (left : Bool) (K : Pattern m) : ℝ :=
  pairGain left K true - signedCount left K / 2

def theta (rho x : Bool) : Bool := !(xor rho x)

theorem sign_theta (rho x : Bool) : sign (theta rho x) = sign rho * sign x := by
  cases rho <;> cases x <;> norm_num [theta,sign]

theorem pairGain_centered (left : Bool) (K : Pattern m) (x : Bool) :
    pairGain left K x - signedCount left K / 2 = eta left K * sign x := by
  cases left <;> cases x <;>
    simp [pairGain,signedCount,eta,endpoint,sign,Fintype.sum_prod_type] <;> ring

theorem signedCount_flip (left : Bool) (K : Pattern m) (rho : Signs) :
    signedCount left (signedFlip rho K) = sign (endpoint left rho) * signedCount left K := by
  rcases rho with ⟨a,b⟩
  cases left <;> cases a <;> cases b <;>
    simp [signedCount,signedFlip,flip,flipSigns,endpoint,sign,Fintype.sum_prod_type] <;> ring

theorem pairGain_flip (left : Bool) (K : Pattern m) (rho : Signs) (x : Bool) :
    pairGain left (signedFlip rho K) x =
      sign (endpoint left rho) * pairGain left K (theta (endpoint (!left) rho) x) := by
  rcases rho with ⟨a,b⟩
  cases left <;> cases a <;> cases b <;> cases x <;>
    simp [pairGain,signedFlip,flip,flipSigns,endpoint,sign,theta,Fintype.sum_prod_type]

theorem endpoint_deviation (left : Bool) (K : Pattern m) (rho : Signs) (x : Bool) :
    pairGain left (signedFlip rho K) x - signedCount left (signedFlip rho K) / 2 =
      sign (endpoint left rho) * eta left K * sign (theta (endpoint (!left) rho) x) := by
  rw [pairGain_flip,signedCount_flip]
  calc
    _ = sign (endpoint left rho) *
        (pairGain left K (theta (endpoint (!left) rho) x) - signedCount left K / 2) := by ring
    _ = _ := by rw [pairGain_centered]; ring

theorem eta_bound (left : Bool) (K : Pattern m) : |eta left K| ≤ (size K : ℝ) / 2 := by
  have h1 : (0 : ℝ) ≤ (K (true,true)).val := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (K (true,false)).val := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (K (false,true)).val := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (K (false,false)).val := Nat.cast_nonneg _
  cases left <;>
    simp [eta,pairGain,signedCount,size,endpoint,sign,Fintype.sum_prod_type] <;>
    rw [abs_le] <;> constructor <;> linarith

theorem pairGain_bound (left : Bool) (K : Pattern m) (x : Bool) :
    |pairGain left K x| ≤ size K := by
  have h1 : (0 : ℝ) ≤ (K (true,true)).val := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (K (true,false)).val := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (K (false,true)).val := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (K (false,false)).val := Nat.cast_nonneg _
  cases left <;> cases x <;>
    simp [pairGain,size,endpoint,sign,Fintype.sum_prod_type] <;>
    rw [abs_le] <;> constructor <;> linarith

end
end Max2SAT.RandomInput
