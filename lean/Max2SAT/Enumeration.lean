import Mathlib.Tactic

/-! Output-sensitive enumeration of a nonnegative rational inequality.
`enumerate` is the mathematical output specification. `foldEnumerate`
visits the same solutions without storing the output list. -/
namespace Max2SAT.Enumeration

def weightedSum : List ℚ → List Bool → ℚ
  | w :: ws, b :: bs => (if b then w else 0) + weightedSum ws bs
  | _, _ => 0

def enumerate : List ℚ → ℚ → List (List Bool)
  | [], B => if B < 0 then [] else [[]]
  | w :: ws, B => if B < 0 then [] else
      (enumerate ws B).map (false :: ·) ++ (enumerate ws (B-w)).map (true :: ·)

/-- Number of visited recursion nodes, including rejected nodes. -/
def nodes : List ℚ → ℚ → ℕ
  | [], _ => 1
  | w :: ws, B => if B < 0 then 1 else 1 + nodes ws B + nodes ws (B-w)

def stackDepth : List ℚ → ℚ → ℕ
  | [], _ => 1
  | w :: ws, B => if B < 0 then 1 else
      1 + max (stackDepth ws B) (stackDepth ws (B-w))

/-- A streaming visitor. Its accumulator may, for example, hold a best solution. -/
def foldEnumerate (visit : List Bool → α → α) : List ℚ → ℚ → α → α
  | [], B, acc => if B < 0 then acc else visit [] acc
  | w :: ws, B, acc => if B < 0 then acc else
      let left := foldEnumerate (fun bs a => visit (false :: bs) a) ws B acc
      foldEnumerate (fun bs a => visit (true :: bs) a) ws (B-w) left

theorem weightedSum_nonneg (ws : List ℚ) (bs : List Bool)
    (h : ∀ w ∈ ws, 0 ≤ w) : 0 ≤ weightedSum ws bs := by
  induction ws generalizing bs with
  | nil => simp [weightedSum]
  | cons w ws ih =>
    cases bs with
    | nil => simp [weightedSum]
    | cons b bs =>
      have hw := h w (by simp)
      have ht := ih bs (fun z hz => h z (by simp [hz]))
      cases b <;> simp only [weightedSum, Bool.false_eq_true, ↓reduceIte, zero_add] <;> linarith

theorem mem_enumerate (ws : List ℚ) (B : ℚ) (bs : List Bool)
    (h : ∀ w ∈ ws, 0 ≤ w) :
    bs ∈ enumerate ws B ↔ bs.length = ws.length ∧ weightedSum ws bs ≤ B := by
  induction ws generalizing B bs with
  | nil =>
    cases bs with
    | nil => simp [enumerate, weightedSum]
    | cons b bs => simp [enumerate, weightedSum]
  | cons w ws ih =>
    have ht : ∀ z ∈ ws, 0 ≤ z := fun z hz => h z (by simp [hz])
    by_cases hB : B < 0
    · have hn := weightedSum_nonneg (w::ws) bs h
      simp only [enumerate, ite_eq_left hB, List.not_mem_nil, false_iff]
      intro hc; linarith [hc.2]
    · cases bs with
      | nil => simp [enumerate, hB, weightedSum]
      | cons b bs =>
        cases b with
        | false => simpa [enumerate, hB, weightedSum] using ih B bs ht
        | true =>
          simpa [enumerate, hB, weightedSum, le_sub_iff_add_le, add_comm]
            using ih (B-w) bs ht

theorem enumerate_nodup (ws : List ℚ) (B : ℚ) : (enumerate ws B).Nodup := by
  induction ws generalizing B with
  | nil => by_cases h : B < 0 <;> simp [enumerate, h]
  | cons w ws ih =>
    by_cases h : B < 0
    · simp [enumerate, h]
    · rw [enumerate, ite_eq_right h, List.nodup_append]
      refine ⟨List.Nodup.map (by intro a b h; exact List.cons.inj h |>.2) (ih B),
        List.Nodup.map (by intro a b h; exact List.cons.inj h |>.2) (ih (B-w)), ?_⟩
      intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨a',ha',rfl⟩
      rcases List.mem_map.mp hb with ⟨b',hb',rfl⟩
      cases hab

theorem length_pos (ws : List ℚ) (B : ℚ) (hB : 0 ≤ B) :
    0 < (enumerate ws B).length := by
  induction ws generalizing B with
  | nil => simp [enumerate, not_lt.mpr hB]
  | cons w ws ih =>
    simp only [enumerate, ite_eq_right (not_lt.mpr hB), List.length_append, List.length_map]
    have := ih B hB
    omega

/-- Explicit bound: one root plus at most two children per live node per level. -/
theorem nodes_bound (ws : List ℚ) (B : ℚ) :
    nodes ws B ≤ 1 + 2 * ws.length * (enumerate ws B).length := by
  induction ws generalizing B with
  | nil => simp [nodes]
  | cons w ws ih =>
    by_cases hB : B < 0
    · simp [nodes, enumerate, hB]
    · have h0 := ih B
      have h1 := ih (B-w)
      have hp := length_pos ws B (le_of_not_gt hB)
      simp only [nodes, enumerate, ite_eq_right hB, List.length_cons,
        List.length_append, List.length_map]
      nlinarith

theorem stackDepth_bound (ws : List ℚ) (B : ℚ) :
    stackDepth ws B ≤ ws.length + 1 := by
  induction ws generalizing B with
  | nil => simp [stackDepth]
  | cons w ws ih =>
    by_cases hB : B < 0
    · simp [stackDepth, hB]
    · simp only [stackDepth, ite_eq_right hB, List.length_cons]
      have h0 := ih B
      have h1 := ih (B-w)
      omega

theorem foldEnumerate_eq_foldl (ws : List ℚ) (B : ℚ)
    (visit : List Bool → α → α) (acc : α) :
    foldEnumerate visit ws B acc =
      (enumerate ws B).foldl (fun a bs => visit bs a) acc := by
  induction ws generalizing B visit acc with
  | nil => by_cases hB : B < 0 <;> simp [foldEnumerate, enumerate, hB]
  | cons w ws ih =>
    by_cases hB : B < 0 <;>
      simp [foldEnumerate, enumerate, hB, ih, List.foldl_append, List.foldl_map]

theorem total_nodes_bound (ws : List ℚ) (bounds : List ℚ) :
    (bounds.map (nodes ws)).sum ≤ bounds.length +
      2 * ws.length * (bounds.map (fun B => (enumerate ws B).length)).sum := by
  induction bounds with
  | nil => simp
  | cons B bounds ih =>
    have h := nodes_bound ws B
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith
/-- Prefixes may induce different coefficients and bounds. Only the common
upper bound k on the number of remaining variables is used. -/
theorem varying_nodes_bound (instances : List (List ℚ × ℚ)) (k : ℕ)
    (hk : ∀ p ∈ instances, p.1.length ≤ k) :
    (instances.map (fun p => nodes p.1 p.2)).sum ≤ instances.length +
      2*k*(instances.map (fun p => (enumerate p.1 p.2).length)).sum := by
  induction instances with
  | nil => simp
  | cons p ps ih =>
    have hp := nodes_bound p.1 p.2
    have hl := hk p (by simp)
    have ht := ih (fun q hq => hk q (by simp [hq]))
    have hm := Nat.mul_le_mul_right ((enumerate p.1 p.2).length) hl
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Cost of a full depth-T prefix tree followed by suffix enumeration;
prefix leaves are counted as the suffix roots, so they are not counted twice. -/
def prefixSuffixNodes (T : ℕ) (instances : List (List ℚ × ℚ)) : ℕ :=
  (2^T-1) + (instances.map (fun p => nodes p.1 p.2)).sum

theorem prefix_suffix_bound (T k : ℕ) (instances : List (List ℚ × ℚ))
    (hc : instances.length ≤ 2^T)
    (hk : ∀ p ∈ instances, p.1.length ≤ k) :
    prefixSuffixNodes T instances ≤ 2^(T+1)-1 +
      2*k*(instances.map (fun p => (enumerate p.1 p.2).length)).sum := by
  have ht := varying_nodes_bound instances k hk
  have hp : 0 < 2^T := pow_pos (by omega) T
  simp only [prefixSuffixNodes,pow_succ]
  omega
end Max2SAT.Enumeration
