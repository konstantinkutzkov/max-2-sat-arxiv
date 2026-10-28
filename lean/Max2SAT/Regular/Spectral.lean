import Max2SAT.Regular.Centering
import Mathlib.Analysis.Matrix.Spectrum

/-! The adjacency eigenvalue assumption is converted to the centered
operator bound used by the combinatorial estimates. -/
namespace Max2SAT.Regular
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix
variable {n : ℕ}

theorem basis_map_coordinate (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (eig : Fin n → ℝ)
    (he : ∀ i, T (b i)=eig i • b i) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    b.repr (T x) i=eig i*b.repr x i := by
  conv_lhs => rw [←b.sum_repr x,map_sum]
  simp_rw [map_smul,he]
  simp [map_sum,map_smul,Finset.sum_apply,Pi.single_apply,mul_ite,ite_mul,mul_comm]

theorem basis_trivial_coordinates
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (eig : Fin n → ℝ)
    (he : ∀ i, T (b i)=eig i • b i) (j : Fin n) (D L : ℝ) (hLD : L<D)
    (heig : ∀ i, i≠j → |eig i|≤L)
    (hones : T (WithLp.toLp 2 (fun _ => (1:ℝ)))=D • WithLp.toLp 2 (fun _ => (1:ℝ))) :
    (∀ i, i≠j → b.repr (WithLp.toLp 2 (fun _ => (1:ℝ))) i=0) ∧
      b.repr (WithLp.toLp 2 (fun _ => (1:ℝ))) j≠0 := by
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have hz (i : Fin n) (hi : i≠j) : b.repr u i=0 := by
    have hc := basis_map_coordinate T b eig he u i
    rw [hones] at hc
    simp only [map_smul,PiLp.smul_apply,smul_eq_mul] at hc
    have hb := (abs_le.mp (heig i hi)).2
    dsimp [u] at hc ⊢
    nlinarith
  refine ⟨hz,?_⟩
  intro hj
  have hu : b.repr u=0 := by
    ext i
    by_cases hi:i=j
    · subst i; exact hj
    · exact hz i hi
  have hu0 : u=0 := b.repr.injective (by simpa using hu)
  have hv := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x j) hu0
  norm_num [u] at hv

theorem zero_sum_basis_coordinate
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (j : Fin n)
    (hz : ∀ i, i≠j → b.repr (WithLp.toLp 2 (fun _ => (1:ℝ))) i=0)
    (hj : b.repr (WithLp.toLp 2 (fun _ => (1:ℝ))) j≠0)
    (x : EuclideanSpace ℝ (Fin n)) (hx : (∑ i, x i)=0) : b.repr x j=0 := by
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have h := b.repr.inner_map_map u x
  have hi : inner ℝ u x=0 := by
    simpa [u,EuclideanSpace.inner_eq_star_dotProduct,dotProduct] using hx
  have hs : inner ℝ (b.repr u) (b.repr x)=b.repr u j*b.repr x j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,star_trivial]
    calc
      (∑ i, b.repr x i*b.repr u i)=b.repr x j*b.repr u j := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          rw [show b.repr u i=0 from hz i hij,mul_zero]
        · simp
      _=b.repr u j*b.repr x j := mul_comm _ _
  rw [hi,hs] at h
  exact (mul_eq_zero.mp h).resolve_left hj

theorem zero_sum_spectral_energy
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (eig : Fin n → ℝ)
    (he : ∀ i, T (b i)=eig i • b i) (j : Fin n) (D L : ℝ) (_hL : 0≤L) (hLD : L<D)
    (heig : ∀ i, i≠j → |eig i|≤L)
    (hones : T (WithLp.toLp 2 (fun _ => (1:ℝ)))=D • WithLp.toLp 2 (fun _ => (1:ℝ)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : (∑ i, x i)=0) :
    ‖T x‖^2≤L^2*‖x‖^2 := by
  have hc := basis_trivial_coordinates T b eig he j D L hLD heig hones
  have hj := zero_sum_basis_coordinate b j hc.1 hc.2 x hx
  rw [←b.repr.norm_map (T x),←b.repr.norm_map x,
    EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [basis_map_coordinate T b eig he x i]
  by_cases hi:i=j
  · subst i; simp [hj]
  · have hsq : (eig i)^2≤L^2 := by nlinarith [(abs_le.mp (heig i hi)).1,(abs_le.mp (heig i hi)).2]
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (b.repr x i))

/-- The usual eigenvalue hypothesis: retain all multiplicities and exclude
one occurrence of the regular eigenvalue d. The algorithm never uses it. -/
def EigenBound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : ℕ) (L : ℝ) : Prop :=
  let hA : (G.adjMatrix ℝ).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  ∃ j, hA.eigenvalues j=d ∧ ∀ i, i≠j → |hA.eigenvalues i|≤L

theorem centered_norm_of_eigenvalues (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : ℕ) (hd : G.IsRegularOfDegree d) (L : ℝ) (hL : 0≤L) (hLd : L<d)
    (hspec : EigenBound G d L) : ‖centered G d‖≤L := by
  let A := G.adjMatrix ℝ
  let hA : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  let T := Matrix.toEuclideanLin A
  let b := hA.eigenvectorBasis
  obtain ⟨j,_hjd,hrest⟩ := hspec
  have hn : 0<n := (Nat.zero_le j.val).trans_lt j.isLt
  have hn' : (n:ℝ)≠0 := by exact_mod_cast (ne_of_gt hn)
  have he : ∀ i, T (b i)=hA.eigenvalues i • b i := by
    intro i
    apply PiLp.ext
    intro t
    exact congrFun (hA.mulVec_eigenvectorBasis i) t
  have ho : T (WithLp.toLp 2 (fun _ => (1:ℝ)))=(d:ℝ) • WithLp.toLp 2 (fun _ => (1:ℝ)) := by
    apply PiLp.ext
    intro t
    change (G.adjMatrix ℝ *ᵥ (fun _ => (1:ℝ))) t=(d:ℝ)*1
    exact G.adjMatrix_mulVec_const_apply_of_regular hd
  have hnorm : ‖centered G d‖^2≤L^2 := by
    apply Counts.rectangular_norm_sq_of_energy _ _ (sq_nonneg L)
    intro x
    let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x i-(∑ w, x w)/(n:ℝ))
    have hy : (∑ i, y i)=0 := by
      dsimp only [y,WithLp.ofLp_toLp]
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
      ring
    have hact : ∀ t, (∑ w, centered G d t w*x w)=(T y) t := by
      intro t
      change (∑ w, (G.adjMatrix ℝ t w-(d:ℝ)/n)*x w)=
        ∑ w, G.adjMatrix ℝ t w*(x w-(∑ w, x w)/(n:ℝ))
      simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul,
        adjacency_row_sum G hd t]
      ring
    simp_rw [hact]
    have hb := zero_sum_spectral_energy T b hA.eigenvalues he j d L hL hLd hrest ho y hy
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (centered_energy hn x) (sq_nonneg L))
  exact (sq_le_sq₀ (norm_nonneg _) hL).mp hnorm

end
end Max2SAT.Regular
