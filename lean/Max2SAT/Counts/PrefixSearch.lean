import Max2SAT.Random.WeightedEnumeration
import Max2SAT.Bias.Hybrid

/-! Prefix enumeration followed by exact rational-budget enumeration.
The parameter K computes a budget from a completed prefix. Its stability
condition means it uses only prefix values, and is proved at each application. -/
namespace Max2SAT.Counts.PrefixSearch

 def Stable (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n)) : Prop :=
  ∀ x y, (∀ i∈P, x i=y i) → K x=K y

/-- List specification; the executable solver below uses the streaming fold. -/
def enumerate (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (suffix : List (Fin n)) : List (Fin n) → Assignment n → List (Assignment n)
  | [], x => Weighted.enumerate (K x) suffix x
  | i::is, x => enumerate K P suffix is (Function.update x i false) ++
      enumerate K P suffix is (Function.update x i true)

def nodes (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (suffix : List (Fin n)) : List (Fin n) → Assignment n → ℕ
  | [], x => Weighted.nodes (K x) suffix x
  | i::is, x => 1+nodes K P suffix is (Function.update x i false)+
      nodes K P suffix is (Function.update x i true)

def fold (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (suffix : List (Fin n)) (visit : σ → Assignment n → σ) :
    List (Fin n) → Assignment n → σ → σ
  | [], x, acc => Weighted.fold (K x) visit suffix x acc
  | i::is, x, acc =>
      let left := fold K P suffix visit is (Function.update x i false) acc
      fold K P suffix visit is (Function.update x i true) left

theorem mem_enumerate (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x y : Assignment n)
    (hK : Stable K P) (hn : (pre++suffix).Nodup) (hd : ∀ i∈suffix, i∉P) :
    y∈enumerate K P suffix pre x ↔
      Compatible (pre++suffix).toFinset x y ∧ (K y).Holds y := by
  induction pre generalizing x with
  | nil =>
    simp only [enumerate,List.nil_append] at *
    rw [Weighted.mem_enumerate _ suffix x y hn]
    constructor
    · rintro ⟨hc,hy⟩
      refine ⟨hc,?_⟩
      have he := hK x y (fun i hi => (hc i (by simpa using fun his => hd i his hi)).symm)
      simpa only [he] using hy
    · rintro ⟨hc,hy⟩
      refine ⟨hc,?_⟩
      have he := hK x y (fun i hi => (hc i (by simpa using fun his => hd i his hi)).symm)
      simpa only [he] using hy
  | cons i is ih =>
    have hi : i∉is++suffix := (List.nodup_cons.mp hn).1
    have ht : (is++suffix).Nodup := (List.nodup_cons.mp hn).2
    simp only [enumerate,List.mem_append,ih _ ht,
      Bias.Single.compatible_cons (is++suffix) i _ _ _ hi,List.cons_append]
    cases y i <;> simp

theorem enumerate_nodup (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n)
    (hK : Stable K P) (hn : (pre++suffix).Nodup) (hd : ∀ i∈suffix, i∉P) :
    (enumerate K P suffix pre x).Nodup := by
  induction pre generalizing x with
  | nil => exact Weighted.enumerate_nodup _ suffix x (by simpa using hn)
  | cons i is ih =>
    have hi : i∉is++suffix := (List.nodup_cons.mp hn).1
    have ht : (is++suffix).Nodup := (List.nodup_cons.mp hn).2
    rw [enumerate,List.nodup_append]
    refine ⟨ih _ ht,ih _ ht,?_⟩
    intro a ha b hb hab
    subst b
    have h0 := (mem_enumerate K P is suffix _ a hK ht hd).mp ha
    have h1 := (mem_enumerate K P is suffix _ a hK ht hd).mp hb
    have h0' := (Bias.Single.compatible_cons (is++suffix) i _ a false hi).mp h0.1
    have h1' := (Bias.Single.compatible_cons (is++suffix) i _ a true hi).mp h1.1
    simp [h0'.1] at h1'

/-- Exact recursion-node accounting, including failed suffix tests. -/
theorem nodes_bound (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n) (hs : suffix.Nodup) :
    nodes K P suffix pre x≤2^(pre.length+1)-1+
      2*suffix.length*(enumerate K P suffix pre x).length := by
  induction pre generalizing x with
  | nil => simpa [nodes,enumerate] using Weighted.nodes_bound _ suffix x hs
  | cons i is ih =>
    have h0 := ih (Function.update x i false)
    have h1 := ih (Function.update x i true)
    have hp : 0<2^(is.length+1) := pow_pos (by omega) _
    simp only [nodes,enumerate,List.length_append,List.length_cons]
    rw [pow_succ]
    simp only [Nat.mul_add]
    omega

theorem fold_eq_foldl (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (pre suffix : List (Fin n)) (x : Assignment n) (visit : σ → Assignment n → σ)
    (acc : σ) : fold K P suffix visit pre x acc=
      (enumerate K P suffix pre x).foldl visit acc := by
  induction pre generalizing x acc with
  | nil => exact Weighted.fold_eq_foldl _ visit suffix x acc
  | cons i is ih => simp [fold,enumerate,ih,List.foldl_append]

private theorem partition_nodup (P : Finset (Fin n)) : ((Bias.ordered P)++(Bias.ordered Pᶜ)).Nodup := by
  rw [List.nodup_append]
  refine ⟨(Bias.ordered_nodup P),(Bias.ordered_nodup Pᶜ),?_⟩
  intro a ha b hb hab
  subst b
  simpa using And.intro ha hb

def outputs (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n)) : List (Assignment n) :=
  enumerate K P (Bias.ordered Pᶜ) (Bias.ordered P) (fun _ => false)

def nodeCount (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n)) : ℕ :=
  nodes K P (Bias.ordered Pᶜ) (Bias.ordered P) (fun _ => false)

theorem mem_outputs (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n))
    (x : Assignment n) (hK : Stable K P) : x∈outputs K P ↔ (K x).Holds x := by
  rw [outputs,mem_enumerate K P _ _ _ x hK (partition_nodup P) (by simp)]
  simp [Compatible]

theorem outputs_nodup (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n)) (hK : Stable K P) :
    (outputs K P).Nodup :=
  enumerate_nodup K P _ _ _ hK (partition_nodup P) (by simp)

theorem output_count (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n)) (hK : Stable K P) :
    (outputs K P).length=FairCoin.eventCount n (fun x => (K x).Holds x) := by
  classical
  let ys := (FairCoin.assignments n).filter (fun x => @decide ((K x).Holds x) (Classical.propDecidable _))
  have hn : ys.Nodup := (FairCoin.assignments_nodup n).filter _
  have he : (outputs K P).toFinset=ys.toFinset := by
    ext x
    simp [ys,mem_outputs K P _ hK,FairCoin.mem_assignments]
  have hc := congrArg Finset.card he
  rw [List.toFinset_card_of_nodup (outputs_nodup K P hK),List.toFinset_card_of_nodup hn] at hc
  simpa [ys,FairCoin.eventCount,List.countP_eq_length_filter] using hc

theorem nodeCount_bound (K : Assignment n → Weighted.Budget n) (P : Finset (Fin n)) (hK : Stable K P) :
    nodeCount K P≤2^(P.card+1)-1+2*n*FairCoin.eventCount n (fun x => (K x).Holds x) := by
  have hh := nodes_bound K P (Bias.ordered P) (Bias.ordered Pᶜ) (fun _ => false) (Bias.ordered_nodup Pᶜ)
  have hk : Pᶜ.card≤n := by simpa using Finset.card_le_univ Pᶜ
  change nodeCount K P≤_ at hh
  simp only [Bias.length_ordered] at hh
  rw [←output_count K P hK]
  change nodeCount K P≤2^(P.card+1)-1+2*n*(outputs K P).length
  change nodeCount K P≤2^(P.card+1)-1+2*Pᶜ.card*(outputs K P).length at hh
  nlinarith


end Max2SAT.Counts.PrefixSearch
