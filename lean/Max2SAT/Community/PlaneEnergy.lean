import Max2SAT.Community.PlaneRotation

/-! Exact energy accounting for one Jacobi rotation. -/
namespace Max2SAT.Community
variable {K : Type*} [Field K] {n : ℕ}
set_option maxHeartbeats 800000

def squareSum (A : Matrix (Fin n) (Fin n) K) : K := ∑ p, ∑ q, (A p q)^2
def diagonalSquareSum (A : Matrix (Fin n) (Fin n) K) : K := ∑ p, (A p p)^2
def offEnergy (A : Matrix (Fin n) (Fin n) K) : K := squareSum A-diagonalSquareSum A

theorem sum_remove_two (f : Fin n → K) (i j : Fin n) (hij : i≠j) :
    ∑ k, f k=(∑ k∈(Finset.univ.erase i).erase j, f k)+f j+f i := by
  rw [←Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)]
  rw [←Finset.sum_erase_add (Finset.univ.erase i) f (by simp [Ne.symm hij] : j∈Finset.univ.erase i)]

theorem sum_same_outside_two (f g : Fin n → K) (i j : Fin n) (hij : i≠j)
    (h : ∀ k, k≠i → k≠j → f k=g k) :
    (∑ k, f k)-f i-f j=(∑ k, g k)-g i-g j := by
  rw [sum_remove_two f i j hij,sum_remove_two g i j hij]
  have he : (∑ k∈(Finset.univ.erase i).erase j, f k)=∑ k∈(Finset.univ.erase i).erase j, g k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1
  rw [he]
  ring

theorem rotated_pair_square (a b c s : K) (hcs : c^2+s^2=1) :
    (c*a+s*b)^2+(-s*a+c*b)^2=a^2+b^2 := by
  calc
    _ = (c^2+s^2)*(a^2+b^2) := by ring
    _ = _ := by rw [hcs]; ring

theorem rotate_vector_square_sum (x : Fin n → K) (i j : Fin n) (hij : i≠j)
    (c s : K) (hcs : c^2+s^2=1) :
    (∑ k, (if k=i then c*x i+s*x j else if k=j then -s*x i+c*x j else x k)^2)=
      ∑ k, (x k)^2 := by
  have h := sum_same_outside_two
    (fun k => (if k=i then c*x i+s*x j else if k=j then -s*x i+c*x j else x k)^2)
    (fun k => (x k)^2) i j hij (by intro k hi hj; simp [hi,hj])
  simp only [ite_true,Ne.symm hij,ite_false] at h
  have hp := rotated_pair_square (x i) (x j) c s hcs
  linear_combination h + hp

theorem square_sum_mul_plane (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (hij : i≠j)
    (c s : K) (hcs : c^2+s^2=1) : squareSum (A*plane i j c s)=squareSum A := by
  unfold squareSum
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [mul_plane A i j hij]
  exact rotate_vector_square_sum (A p) i j hij c s hcs

theorem square_sum_transpose_plane_mul (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (hij : i≠j)
    (c s : K) (hcs : c^2+s^2=1) : squareSum ((plane i j c s).transpose*A)=squareSum A := by
  unfold squareSum
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun p q => (A p q)^2)]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [transpose_plane_mul A i j hij]
  exact rotate_vector_square_sum (fun p => A p q) i j hij c s hcs

theorem square_sum_conjugate_plane (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (hij : i≠j)
    (c s : K) (hcs : c^2+s^2=1) :
    squareSum ((plane i j c s).transpose*A*plane i j c s)=squareSum A := by
  rw [square_sum_mul_plane _ i j hij c s hcs,square_sum_transpose_plane_mul A i j hij c s hcs]

theorem conjugated_diagonal_first (A : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (hij : i≠j) (hsym : A j i=A i j) (c s : K) :
    ((plane i j c s).transpose*A*plane i j c s) i i=
      c^2*A i i+2*c*s*A i j+s^2*A j j := by
  rw [mul_plane _ i j hij]
  simp only [ite_true]
  rw [transpose_plane_mul _ i j hij,transpose_plane_mul _ i j hij]
  simp only [ite_true,hsym]
  ring

theorem conjugated_diagonal_second (A : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (hij : i≠j) (hsym : A j i=A i j) (c s : K) :
    ((plane i j c s).transpose*A*plane i j c s) j j=
      s^2*A i i-2*c*s*A i j+c^2*A j j := by
  rw [mul_plane _ i j hij]
  simp only [Ne.symm hij,ite_false,ite_true]
  rw [transpose_plane_mul _ i j hij,transpose_plane_mul _ i j hij]
  simp only [Ne.symm hij,ite_false,ite_true,hsym]
  ring

theorem conjugated_diagonal_other (A : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (hij : i≠j) (c s : K) (k : Fin n) (hi : k≠i) (hj : k≠j) :
    ((plane i j c s).transpose*A*plane i j c s) k k=A k k := by
  rw [mul_plane _ i j hij]
  simp only [hi,hj,ite_false]
  rw [transpose_plane_mul _ i j hij]
  simp [hi,hj]

theorem rotated_block_square (a b d c s : K) (hcs : c^2+s^2=1) :
    (c^2*a+2*c*s*b+s^2*d)^2+(s^2*a-2*c*s*b+c^2*d)^2+
      2*(b*(c^2-s^2)+(d-a)*c*s)^2=a^2+d^2+2*b^2 := by
  calc
    _ = (c^2+s^2)^2*(a^2+d^2+2*b^2) := by ring
    _ = _ := by rw [hcs]; ring

/-- Only the old and new pivot entries affect the off-diagonal energy. -/
theorem plane_energy_identity (A : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (hij : i≠j) (hsym : A j i=A i j) (c s : K) (hcs : c^2+s^2=1) :
    offEnergy ((plane i j c s).transpose*A*plane i j c s)=
      offEnergy A-2*(A i j)^2+2*(A i j*(c^2-s^2)+(A j j-A i i)*c*s)^2 := by
  have h := sum_same_outside_two
    (fun k => (((plane i j c s).transpose*A*plane i j c s) k k)^2)
    (fun k => (A k k)^2) i j hij (by
      intro k hi hj
      rw [conjugated_diagonal_other A i j hij c s k hi hj])
  rw [conjugated_diagonal_first A i j hij hsym,conjugated_diagonal_second A i j hij hsym] at h
  have hp := rotated_block_square (A i i) (A i j) (A j j) c s hcs
  unfold offEnergy diagonalSquareSum
  rw [square_sum_conjugate_plane A i j hij c s hcs]
  linear_combination -h - hp

end Max2SAT.Community
