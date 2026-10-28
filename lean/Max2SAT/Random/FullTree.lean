import Max2SAT.Random.ComparisonTree
import Max2SAT.Random.Residual
import Max2SAT.Bias.ConstraintEnumeration

/-! The restored decision tree in Lemma lem:exactA. Preferences are recomputed
from the current residual formula, including units created by substitution. -/
namespace Max2SAT.Random

def branchLiteral (F : Formula n) (free : List (Fin n)) (x : Assignment n)
    (i : Fin n) : Literal n :=
  ⟨i, Bias.initialPreference (Residual.restrict free.toFinset x F).1 i⟩

def branchCut (F : Formula n) (free : List (Fin n)) (x : Assignment n)
    (i : Fin n) : Constraint n :=
  pruningConstraint (Residual.restrict free.toFinset x F).1 (branchLiteral F free x i)

def fullTree (F : Formula n) : List (Fin n) → Assignment n →
    ComparisonTree (Assignment n) (Constraint n)
  | [], x => .leaf x
  | i::is, x =>
    let v := branchLiteral F (i::is) x i
    .branch (branchCut F (i::is) x i)
      (fullTree F is (v.force true x)) (fullTree F is (v.force false x))

theorem fullTree_covers (F : Formula n) (free : List (Fin n)) (x y : Assignment n)
    (hn : free.Nodup) :
    y ∈ (fullTree F free x).leaves ↔ Compatible free.toFinset x y := by
  induction free generalizing x with
  | nil => simp [fullTree,ComparisonTree.leaves,compatible_empty]
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    simp only [fullTree,ComparisonTree.leaves,List.mem_append,ih _ ht]
    simp only [Literal.force,branchLiteral,Bias.Single.compatible_cons is i _ _ _ hi]
    cases Bias.initialPreference (Residual.restrict (i::is).toFinset x F).1 i <;>
      cases y i <;> simp

private theorem force_compatible (free : Finset (Fin n)) (x y : Assignment n)
    (v : Literal n) (b : Bool) (hi : v.var ∈ free) (hc : Compatible free x y) :
    Compatible free x (v.force b y) := by
  intro j hj
  have hji : j ≠ v.var := by intro h; subst j; exact hj hi
  simpa [Literal.force,hji] using hc j hj

private theorem right_flip (is : List (Fin n)) (i : Fin n) (x y : Assignment n)
    (p : Bool) (hi : i ∉ is)
    (hc : Compatible is.toFinset ((Literal.mk i p).force false x) y) :
    (Literal.mk i p).eval y = false ∧
      Compatible is.toFinset ((Literal.mk i p).force true x) ((Literal.mk i p).force true y) := by
  have he := hc i (by simpa using hi)
  constructor
  · cases p <;> simp_all [Literal.eval,Literal.force]
  · intro j hj
    by_cases hji : j=i
    · subst j; simp [Literal.force]
    · simpa [Literal.force,hji] using hc j hj

theorem fullTree_valid (F : Formula n) (free : List (Fin n)) (x : Assignment n)
    (hF : wellFormed F) (hn : free.Nodup) :
    (fullTree F free x).Valid (score F) Constraint.Holds := by
  induction free generalizing x with
  | nil => trivial
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    let v := branchLiteral F (i::is) x i
    change (fullTree F is (v.force true x)).Valid _ _ ∧
      (fullTree F is (v.force false x)).Valid _ _ ∧ _
    refine ⟨ih _ ht, ih _ ht, ?_⟩
    intro y hy hbad
    have hc := (fullTree_covers F is (v.force false x) y ht).mp hy
    have hr := right_flip is i x y v.positive hi hc
    have hiv : v.var = i := rfl
    have hyv : v.eval y = false := hr.1
    have hl : Compatible is.toFinset (v.force true x) (v.force true y) := hr.2
    refine ⟨v.force true y, (fullTree_covers F is _ _ ht).mpr hl, ?_⟩
    have hparent : Compatible (i::is).toFinset x y := by
      have hh := (Bias.Single.compatible_cons is i x y (false == v.positive) hi).mp hc
      exact hh.2
    have hp := force_compatible (i::is).toFinset x y v true (by simp [hiv]) hparent
    have h0 := Residual.restrict_score F (i::is).toFinset x y hparent
    have h1 := Residual.restrict_score F (i::is).toFinset x (v.force true y) hp
    have hw := Residual.restrict_wellFormed F (i::is).toFinset x hF
    have hcut : ¬ score (Residual.restrict (i::is).toFinset x F).1 (v.force true y) <
        score (Residual.restrict (i::is).toFinset x F).1 (v.force false y) := by
      intro hh
      exact hbad ((pruning_iff_strict_improvement _ v y hw).mpr hh)
    rw [Literal.force_eq_self v y false hyv] at hcut
    omega

end Max2SAT.Random
