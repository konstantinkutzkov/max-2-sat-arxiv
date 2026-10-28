import Max2SAT.Random.Algorithm

/-! Exact recursion-node accounting for the paper's random-sign search.
All failed tests are charged. The search itself remains deterministic. -/
namespace Max2SAT.Random

/-- Mirrors enumerate/fold, charging one for each call, including rejection. -/
def nodes (F : Formula n) (w : Fin n → ℚ) (suffix : List (Fin n)) :
    List (Fin n) → Assignment n → List (ℚ × Constraint n) → ℕ
  | [], x, cs => Weighted.nodes (Weighted.sum cs) suffix x
  | i::is, x, cs =>
    if Weighted.reject (Weighted.sum cs) (i::is++suffix) x then 1 else
    let v := branchLiteral F (i::is++suffix) x i
    let C := branchCut F (i::is++suffix) x i
    1+nodes F w suffix is (v.force true x) cs+
      nodes F w suffix is (v.force false x) ((w i,C)::cs)

theorem nodes_bound (F : Formula n) (w : Fin n → ℚ) (suffix pre : List (Fin n))
    (x : Assignment n) (cs : List (ℚ × Constraint n)) (hs : suffix.Nodup) :
    nodes F w suffix pre x cs≤2^(pre.length+1)-1+
      2*suffix.length*(enumerate F w suffix pre x cs).length := by
  induction pre generalizing x cs with
  | nil => simpa [nodes,enumerate] using Weighted.nodes_bound (Weighted.sum cs) suffix x hs
  | cons i is ih =>
    have hp : 0<2^(is.length+1) := pow_pos (by omega) _
    simp only [nodes,enumerate]
    split
    · simp only [List.length_nil,mul_zero,add_zero,List.length_cons]
      have hpow : 2≤2^(is.length+1+1) := by rw [pow_succ]; omega
      omega
    · have h0 := ih ((branchLiteral F (i::is++suffix) x i).force true x) cs
      have h1 := ih ((branchLiteral F (i::is++suffix) x i).force false x)
        ((w i,branchCut F (i::is++suffix) x i)::cs)
      simp only [List.length_append,List.length_cons]
      rw [pow_succ]
      simp only [Nat.mul_add]
      omega

theorem enumerate_nodup (F : Formula n) (w : Fin n → ℚ) (suffix pre : List (Fin n))
    (x : Assignment n) (cs : List (ℚ × Constraint n)) (hn : (pre++suffix).Nodup) :
    (enumerate F w suffix pre x cs).Nodup := by
  induction pre generalizing x cs with
  | nil => exact Weighted.enumerate_nodup _ suffix x (by simpa using hn)
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    simp only [enumerate]
    split
    · exact List.nodup_nil
    · rw [List.nodup_append]
      refine ⟨ih _ _ ht,ih _ _ ht,?_⟩
      intro a ha b hb hab
      subst b
      have h0 := output_compatible F w suffix is _ a cs ht ha
      have h1 := output_compatible F w suffix is _ a _ ht hb
      have h0' := h0 i (by simpa using hi)
      have h1' := h1 i (by simpa using hi)
      simp only [Literal.force,show (branchLiteral F (i::is++suffix) x i).var=i from rfl,
        Function.update_self] at h0' h1'
      cases hp : (branchLiteral F (i::is++suffix) x i).positive <;> simp_all

def nodeCount (F : Formula n) : ℕ :=
  let U := Bias.ordered (active F)
  nodes (preprocess (core F)).1 (weight F) (U.drop ((U.length+1)/2))
    (U.take ((U.length+1)/2)) (initial F) []

def outputs (F : Formula n) : List (Assignment n) :=
  let U := Bias.ordered (active F)
  enumerate (preprocess (core F)).1 (weight F) (U.drop ((U.length+1)/2))
    (U.take ((U.length+1)/2)) (initial F) []

theorem nodeCount_of_active_empty (F : Formula n) (h : active F=∅) :
    nodeCount F=1 ∧ (outputs F).length=1 := by
  simp [nodeCount,outputs,h,Bias.ordered,nodes,enumerate,Weighted.nodes,
    Weighted.enumerate,Weighted.reject,Weighted.minimum,Weighted.sum]

theorem nodeCount_bound (F : Formula n) :
    nodeCount F≤2^(((active F).card+1)/2+1)-1+2*(active F).card*(outputs F).length := by
  let U := Bias.ordered (active F)
  let T := (U.length+1)/2
  have h := nodes_bound (preprocess (core F)).1 (weight F) (U.drop T) (U.take T)
    (initial F) [] ((Bias.ordered_nodup _).drop)
  have hp : (U.take T).length≤T := List.length_take_le T U
  have hs : (U.drop T).length≤U.length := by simp only [List.length_drop]; omega
  have hpow := Nat.pow_le_pow_right (by omega : 0<2) (Nat.add_le_add_right hp 1)
  have hm := Nat.mul_le_mul_right (outputs F).length (Nat.mul_le_mul_left 2 hs)
  change nodeCount F≤_ at h
  change _≤2*U.length*(outputs F).length at hm
  have hh := h.trans (Nat.add_le_add (Nat.sub_le_sub_right hpow 1) hm)
  simpa only [T,U,Bias.length_ordered] using hh

theorem outputs_nodup (F : Formula n) : (outputs F).Nodup := by
  apply enumerate_nodup
  simpa using Bias.ordered_nodup (active F)

end Max2SAT.Random
