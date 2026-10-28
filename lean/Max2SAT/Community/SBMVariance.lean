import Max2SAT.Community.SBMModel

/-! The minimum and maximum are over every block pair, including pairs
whose communities happen to be empty. No balance or separation is assumed. -/
namespace Max2SAT.Community
noncomputable section
variable {k : ℕ}

def minBlockVariance (hk : 0<k) (π : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (Finset.univ : Finset (Fin k × Fin k)).inf'
    ⟨(⟨0,hk⟩,⟨0,hk⟩),Finset.mem_univ _⟩ (fun ab => π ab.1 ab.2*(1-π ab.1 ab.2))

def maxBlockVariance (hk : 0<k) (π : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (Finset.univ : Finset (Fin k × Fin k)).sup'
    ⟨(⟨0,hk⟩,⟨0,hk⟩),Finset.mem_univ _⟩ (fun ab => π ab.1 ab.2*(1-π ab.1 ab.2))

theorem block_variance_bounds (hk : 0<k) (π : Matrix (Fin k) (Fin k) ℝ) (a b : Fin k) :
    minBlockVariance hk π≤π a b*(1-π a b) ∧ π a b*(1-π a b)≤maxBlockVariance hk π :=
  ⟨Finset.inf'_le _ (Finset.mem_univ (a,b)),Finset.le_sup' (fun ab : Fin k × Fin k => π ab.1 ab.2*(1-π ab.1 ab.2)) (Finset.mem_univ (a,b))⟩

end
end Max2SAT.Community
