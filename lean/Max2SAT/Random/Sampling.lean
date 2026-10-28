import Max2SAT.Random.PairModel

/-! The two concrete models of Theorem thm:random_main. The independent-
inclusion model is proved for every q in [0,1]; its second moment is
4q(1-q). In the paper q=1/4, giving the common lower bound 3/4. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

def onePattern (s : Signs) : Pattern 4 := fun t => if t = s then 1 else 0

def uniformSigns : Law Signs where
  mass _ := 1/4
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

def oneClause : Law (Pattern 4) := push uniformSigns onePattern

@[simp] theorem onePattern_size (s : Signs) : size (onePattern s) = 1 := by
  simp [size, onePattern, apply_ite]

theorem onePattern_flip (mask s : Signs) :
    onePattern (flipSigns mask s) = flip mask (onePattern s) := by
  funext t
  change (if t = flipSigns mask s then (1 : Fin 5) else 0) =
    (if flipSigns mask t = s then 1 else 0)
  have he : t = flipSigns mask s ↔ flipSigns mask t = s := by
    exact (flipSigns mask).eq_symm_apply
  simp only [he]

theorem oneClause_invariant (mask : Signs) (K : Pattern 4) :
    oneClause.mass (flip mask K) = oneClause.mass K :=
  push_invariant uniformSigns onePattern (flipSigns mask) (flip mask)
    (fun _ => rfl) (onePattern_flip mask) K

theorem oneClause_moment (left : Bool) :
    expect oneClause (fun K => (signedCount left K)^2) = 1 := by
  rw [oneClause, expect_push]
  cases left <;>
    norm_num [expect, uniformSigns, signedCount, onePattern, endpoint, sign,
      Fintype.sum_prod_type, Fintype.sum_bool]

theorem oneClause_bounded (K : Pattern 4) (h : 0 < oneClause.mass K) : size K ≤ 4 := by
  by_contra hn
  have he : ∀ s, onePattern s ≠ K := by
    intro s hs
    have hh := onePattern_size s
    rw [hs] at hh
    omega
  have hz : oneClause.mass K = 0 := by simp [oneClause, push, he]
  linarith

def oneClauseModel : PairLaw 4 1 where
  law := oneClause
  bounded := oneClause_bounded
  invariant := oneClause_invariant
  moment left := (oneClause_moment left).ge

def bernoulli (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Law Bool where
  mass b := if b then q else 1-q
  nonneg b := by cases b <;> simp_all
  total := by simp

def inclusionBits (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Law (Signs → Bool) :=
  product (ι := Signs) (fun _ => bernoulli q h0 h1)

def included (bits : Signs → Bool) : Pattern 4 := fun s => if bits s then 1 else 0

def independentClauses (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Law (Pattern 4) :=
  push (inclusionBits q h0 h1) included

def flipBits (mask : Signs) : (Signs → Bool) ≃ (Signs → Bool) where
  toFun x := x ∘ flipSigns mask
  invFun x := x ∘ flipSigns mask
  left_inv x := by funext s; exact congrArg x ((flipSigns mask).left_inv s)
  right_inv x := by funext s; exact congrArg x ((flipSigns mask).right_inv s)

theorem inclusionBits_invariant (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (mask : Signs) (x : Signs → Bool) :
    (inclusionBits q h0 h1).mass (flipBits mask x) = (inclusionBits q h0 h1).mass x := by
  exact (flipSigns mask).prod_comp (fun s => (bernoulli q h0 h1).mass (x s))

theorem independentClauses_invariant (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (mask : Signs) (K : Pattern 4) :
    (independentClauses q h0 h1).mass (flip mask K) =
      (independentClauses q h0 h1).mass K := by
  apply push_invariant (inclusionBits q h0 h1) included (flipBits mask) (flip mask)
    (inclusionBits_invariant q h0 h1 mask)
  intro x
  rfl

/-- A constant-size reindexing for the four independent clause indicators.
It expands only one pair, not the exponentially many input formulas. -/
def fourBits : (Signs → Bool) ≃ (Bool × Bool) × (Bool × Bool) where
  toFun x := ((x (true,true),x (true,false)),(x (false,true),x (false,false)))
  invFun x s := if s.1 then (if s.2 then x.1.1 else x.1.2)
    else (if s.2 then x.2.1 else x.2.2)
  left_inv x := by funext s; rcases s with ⟨a,b⟩; cases a <;> cases b <;> rfl
  right_inv x := by rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl

theorem independentClauses_moment (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (left : Bool) :
    expect (independentClauses q h0 h1) (fun K => (signedCount left K)^2) =
      4*q*(1-q) := by
  rw [independentClauses, expect_push]
  unfold expect
  rw [← fourBits.symm.sum_comp]
  cases left <;>
    simp [fourBits, inclusionBits, product, bernoulli, signedCount, included,
      endpoint, sign, Fintype.sum_prod_type, Fintype.prod_prod_type,
      ] <;> ring

theorem included_size (x : Signs → Bool) : size (included x) ≤ 4 := by
  calc
    _ ≤ ∑ _ : Signs, 1 := Finset.sum_le_sum (fun s _ => by
      simp only [included]; split <;> decide)
    _ = 4 := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem independentClauses_bounded (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (K : Pattern 4) (h : 0 < (independentClauses q h0 h1).mass K) : size K ≤ 4 := by
  by_contra hn
  have he : ∀ x, included x ≠ K := by
    intro x hx
    have hh := included_size x
    rw [hx] at hh
    contradiction
  have hz : (independentClauses q h0 h1).mass K = 0 := by
    simp [independentClauses, push, he]
  linarith

def independentClauseModel (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : PairLaw 4 (4*q*(1-q)) where
  law := independentClauses q h0 h1
  bounded := independentClauses_bounded q h0 h1
  invariant := independentClauses_invariant q h0 h1
  moment left := (independentClauses_moment q h0 h1 left).ge

theorem quarter_moment (left : Bool) :
    expect (independentClauses (1/4) (by norm_num) (by norm_num))
      (fun K => (signedCount left K)^2) = 3/4 := by
  rw [independentClauses_moment]
  norm_num

end
end Max2SAT.RandomInput
