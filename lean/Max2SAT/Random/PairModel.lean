import Max2SAT.Random.FiniteLaw

/-! Definition def:invariant and Lemma lem:observed_pairs. A bounded multiset
of clauses on one ordered variable pair is represented canonically by its
four multiplicities. Clause order has no mathematical role. -/
namespace Max2SAT.RandomInput
noncomputable section
open FiniteLaw
attribute [local instance] Classical.propDecidable

abbrev Signs := Bool × Bool
abbrev Pattern (m : ℕ) := Signs → Fin (m+1)

def size (K : Pattern m) : ℕ := ∑ s, (K s).val
def present (K : Pattern m) : Prop := 0 < size K
def sign (b : Bool) : ℝ := if b then 1 else -1
def endpoint (left : Bool) (s : Signs) : Bool := if left then s.1 else s.2
def signedCount (left : Bool) (K : Pattern m) : ℝ :=
  ∑ s, (K s).val * sign (endpoint left s)

def flipSigns (mask : Signs) : Signs ≃ Signs where
  toFun s := (xor mask.1 s.1, xor mask.2 s.2)
  invFun s := (xor mask.1 s.1, xor mask.2 s.2)
  left_inv s := by rcases mask with ⟨a,b⟩; rcases s with ⟨c,d⟩; cases a <;> cases b <;> cases c <;> cases d <;> rfl
  right_inv s := by rcases mask with ⟨a,b⟩; rcases s with ⟨c,d⟩; cases a <;> cases b <;> cases c <;> cases d <;> rfl

def flip (mask : Signs) : Pattern m ≃ Pattern m where
  toFun K := K ∘ flipSigns mask
  invFun K := K ∘ flipSigns mask
  left_inv K := by funext s; exact congrArg K ((flipSigns mask).left_inv s)
  right_inv K := by funext s; exact congrArg K ((flipSigns mask).right_inv s)

@[simp] theorem flip_size (mask : Signs) (K : Pattern m) : size (flip mask K) = size K := by
  exact Equiv.sum_comp (flipSigns mask) (fun s => (K s).val)

@[simp] theorem flip_present (mask : Signs) (K : Pattern m) :
    present (flip mask K) ↔ present K := by simp [present]

theorem absent_count (K : Pattern m) (h : ¬ present K) (s : Signs) : (K s).val = 0 := by
  have hz : size K = 0 := by unfold present at h; omega
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => Nat.zero_le (K t).val)).mp hz s
    (Finset.mem_univ s)

theorem absent_signedCount (left : Bool) (K : Pattern m) (h : ¬ present K) :
    signedCount left K = 0 := by
  simp [signedCount, absent_count K h]

/-- The three assumptions of Definition def:invariant. Only patterns of
positive mass must satisfy the clause-count bound. The four-coordinate
ambient type is finite even when multiplicities are allowed. -/
structure PairLaw (m : ℕ) (κ : ℝ) where
  law : Law (Pattern m)
  bounded : ∀ K, 0 < law.mass K → size K ≤ m
  invariant : ∀ mask K, law.mass (flip mask K) = law.mass K
  moment : ∀ left, κ ≤ expect law (fun K => (signedCount left K)^2)

theorem present_positive (p : PairLaw m κ) (hk : 0 < κ) :
    0 < prob p.law present := by
  by_contra hn
  have hz : prob p.law present = 0 := le_antisymm (le_of_not_gt hn) (prob_nonneg _ _)
  have hzero : ∀ K, present K → p.law.mass K = 0 := by
    intro K hK
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun L _ =>
      show 0 ≤ (if present L then p.law.mass L else 0) by
        split_ifs <;> simp_all [p.law.nonneg])).mp hz K (Finset.mem_univ K)
    simpa [hK] using hs
  have he : expect p.law (fun K => (signedCount true K)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro K _
    by_cases hK : present K
    · simp [hzero K hK]
    · simp [absent_signedCount true K hK]
  have hm := p.moment true
  rw [he] at hm
  linarith

theorem conditional_moment (p : PairLaw m κ) (h : 0 < prob p.law present) (left : Bool) :
    expect (condition p.law present h) (fun K => (signedCount left K)^2) =
      expect p.law (fun K => (signedCount left K)^2) / prob p.law present := by
  apply condition_expect
  intro K hK
  simp [absent_signedCount left K hK]

/-- Retaining a nonempty pair preserves symmetry and the size bound and
cannot decrease either second moment. No conditional moment assumption is
introduced. -/
def retained (p : PairLaw m κ) (h : 0 < prob p.law present) : PairLaw m κ where
  law := condition p.law present h
  bounded K hK := by
    have hm : 0 < p.law.mass K := by
      rw [condition_mass] at hK
      by_cases hp : present K
      · simpa [hp] using (div_pos_iff_of_pos_right h).mp hK
      · simp [hp] at hK
    exact p.bounded K hm
  invariant mask K := condition_invariant p.law present h (flip mask)
    (p.invariant mask) (flip_present mask) K
  moment left := by
    rw [conditional_moment]
    apply le_trans (p.moment left)
    exact le_div_self (expect_nonneg _ (fun K => sq_nonneg _)) h (prob_le_one _ _)

/-- An observed support H is precisely the coordinate event saying that
each sampled pair is nonempty iff it belongs to H. -/
def observedEvent {ι : Type*} [Fintype ι] (H : ι → Prop) (K : ι → Pattern m) : Prop :=
  ∀ e, if H e then present (K e) else ¬ present (K e)

/-- Full conditional joint law on every potential edge. On retained edges
this is the original law conditioned only on nonemptiness. Factorization
expresses joint independence, including when the observed graph is empty. -/
theorem observed_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → PairLaw m κ) (H : ι → Prop)
    (h : 0 < prob (product (fun e => (p e).law)) (observedEvent H)) :
    condition (product (fun e => (p e).law)) (observedEvent H) h =
      product (fun e => condition (p e).law
        (fun K => if H e then present K else ¬ present K)
        (product_event_positive (fun e => (p e).law)
          (fun e K => if H e then present K else ¬ present K) h e)) := by
  exact condition_product (fun e => (p e).law)
    (fun e K => if H e then present K else ¬ present K) h

end
end Max2SAT.RandomInput
