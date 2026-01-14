import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots


notation "E"  => !![1, 0; 0, 1]    -- 位数 1, det = 1,  tr = 2,  t^2 - 2t + 1
notation "-E" => !![-1, 0; 0, -1]  -- 位数 2, det = 1,  tr = -2, t^2 + 2t + 1
notation "P2" => !![0, -1; 1, -1]  -- 位数 3, det = 1,  tr = -1, t^2 + t + 1
notation "P3" => !![0, 1; -1, 0]   -- 位数 4, det = 1,  tr = 0,  t^2 + 1
notation "P4" => !![0, -1; 1, 1]   -- 位数 6, det = 1,  tr = 1,  t^2 - t + 1


open Matrix Polynomial
open Function minpoly Polynomial Set
open Finset

namespace Nat


variable (M : SpecialLinearGroup (Fin 2) ℚ)

variable {R : Type*} [CommRing R]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {A B : Type*} (A) [CommRing A] [Ring B] [Algebra A B]

attribute [local instance] Classical.propDecidable

noncomputable def charmatrix' (N : Matrix m m R) : Matrix m m R[X] :=
  Matrix.scalar m (X : R[X]) - (C : R →+* R[X]).mapMatrix N

noncomputable def charpoly' (N : Matrix m m R) : R[X] := (charmatrix N).det

noncomputable def minpoly' (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

noncomputable def cyclotomic' (n : ℕ) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose


lemma charpoly_deg_eq_two : (charpoly M.val).natDegree = 2 :=  -- 固有多項式の次数は2以下
  charpoly_natDegree_eq_dim M.val

lemma minpoly_dvd_charpoly : minpoly ℚ M.val ∣ M.val.charpoly := by -- 最小多項式は固有多項式を割り切る
  apply dvd ℚ M.val
  exact aeval_self_charpoly M.val

lemma minpoly_deg_le_two : (minpoly ℚ M.val).natDegree ≤ 2 :=  -- 最小多項式の次数は2以下
  calc
    _ ≤ (charpoly M.val).natDegree := by
      apply natDegree_le_of_dvd
      · apply minpoly_dvd_charpoly M
      ·
 apply ne_zero_of_natDegree_gt
        show 1 < (charpoly M.val).natDegree
        rw [charpoly_deg_eq_two]
        norm_num
    _ = 2 := by rw [charpoly_deg_eq_two]

def totient' (n : ℕ) : ℕ := # {a ∈ range n | n.Coprime a}

lemma cyclotomic_deg_eq_totient (n : ℕ) :
    (cyclotomic n ℚ).natDegree = totient n := by  -- 円分多項式の次数はトーシェント関数
  exact natDegree_cyclotomic n ℚ

lemma cyclotomic_eq_minpoly (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    cyclotomic n ℚ = minpoly ℚ M.val := by  -- 円分多項式と最小多項式は等しい
  sorry
  -- have h₁ : Irreducible (cyclotomic n ℚ) := by
  --   apply cyclotomic.irreducible_rat
  --   simp [h', h]
  -- have h₂ : aeval M.val (cyclotomic n ℚ) = 0 := by
  --   sorry
  -- have h₃ : Monic (cyclotomic n ℚ) := cyclotomic.monic n ℚ
  -- exact eq_of_irreducible_of_monic h₁ h₂ h₃
lemma totient_le_two  (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    totient n ≤ 2 := by  -- トーシェント関数の値は2以下
  rw [← cyclotomic_deg_eq_totient n]
  rw [cyclotomic_eq_minpoly M h h']
  exact minpoly_deg_le_two M

lemma totient_le_two_iff  (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    totient n ≤ 2 ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  constructor <;> intro h₀
  · sorry
  · fin_cases h₀ <;> decide

theorem finite_order_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rw [← totient_le_two_iff M h h']
  exact totient_le_two M h h'

theorem finite_order_matrix (h : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ∃ M : SpecialLinearGroup (Fin 2) ℚ, orderOf M.val = n := by
  simp at h
  rcases h with (rfl | rfl | rfl | rfl | rfl)
  · use 1; simp
  · use -1; sorry
  · use P2; sorry
  · use P3; sorry
  · use P4; sorry

theorem finite_order_iff (h : n = orderOf M.val) :
    IsOfFinOrder M.val ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  constructor <;> intro h'
  · exact finite_order_class M h' h
  · rw [← orderOf_ne_zero_iff]
    rw [← h]
    simp at h'
    rcases h' with (rfl | rfl | rfl | rfl | rfl) <;> norm_num
