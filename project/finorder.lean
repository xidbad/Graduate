import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

notation "E"  => !![1, 0; 0, 1]    -- 位数 1, det = 1,  tr = 2,  t^2 - 2t + 1
notation "-E" => !![-1, 0; 0, -1]  -- 位数 2, det = 1,  tr = -2, t^2 + 2t + 1
notation "P1" => !![1, 0; 0, -1]   -- 位数 2, det = -1, tr = 0,  t^2 - 1
notation "P2" => !![0, -1; 1, -1]  -- 位数 3, det = 1,  tr = -1, t^2 + t + 1
notation "P3" => !![0, 1; -1, 0]   -- 位数 4, det = 1,  tr = 0,  t^2 + 1
notation "P4" => !![0, -1; 1, 1]   -- 位数 6, det = 1,  tr = 1,  t^2 - t + 1

open Matrix Polynomial Function minpoly Set Finset Irreducible
open UniqueFactorizationMonoid

namespace Nat

variable (M : GL (Fin 2) ℚ)

variable {R : Type*} [CommRing R]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {A B : Type*} (A) [CommRing A] [Ring B] [Algebra A B]

attribute [local instance] Classical.propDecidable

notation "X" => Polynomial.X

noncomputable def charmatrix' (N : Matrix m m R) : Matrix m m R[X] :=
  Matrix.scalar m (X : R[X]) - (C : R →+* R[X]).mapMatrix N

noncomputable def charpoly' (N : Matrix m m R) : R[X] := (charmatrix N).det

lemma charpoly_deg_eq_two : (charpoly M.val).natDegree = 2 :=  -- 固有多項式の次数は2
  charpoly_natDegree_eq_dim M.val

noncomputable def minpoly' (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

lemma minpoly_dvd_charpoly : minpoly ℚ M.val ∣ charpoly M.val := by -- 最小多項式は固有多項式を割り切る
  apply dvd ℚ M.val
  exact aeval_self_charpoly M.val

lemma minpoly_deg_le_two : (minpoly ℚ M.val).natDegree ≤ 2 :=  -- 最小多項式の次数は2以下
  calc
    _ ≤ (charpoly M.val).natDegree := by
      apply natDegree_le_of_dvd
      · apply minpoly_dvd_charpoly M
      · apply ne_zero_of_natDegree_gt
        show 1 < (charpoly M.val).natDegree
        rw [charpoly_deg_eq_two]
        norm_num
    _ = 2 := by rw [charpoly_deg_eq_two]

noncomputable def cyclotomic' (n : ℕ) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose

-- 円分多項式 : φₙ(X) = ∏ (X - exp (2πik / n)) (1 ≤ k ≤ n, gcd (k, n) = 1)
-- φ₁(X) = X - 1, φ₂(X) = X + 1, φ₃(X) = (X - exp (2πi/3))(X - exp (4πi/3)) = X² + X + 1
-- φ₄(X) = (X - i)(X + i) = X² + 1, φ₆(X) = (X - exp (πi/3))(X - exp (5πi/3)) = X² - X + 1

lemma minpoly_dvd_X_pow_sub_one (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∣ X ^ n - 1 := by  -- 最小多項式はX^n - 1を割り切る
  have h₁ : aeval M.val (X ^ n - 1 : ℚ[X]) = 0 := by
    simp [h']
  apply dvd
  exact h₁

lemma irre_cyc (n : ℕ) (hn : 0 < n) (f : ℚ[X]) (hir : Irreducible f) (hdiv : f ∣ X^n - 1) :
    ∃ i ∈ n.divisors, ∃ u : ℚ[X]ˣ, f = (u.val) * cyclotomic i ℚ := by
  have h₁ : ∏ i ∈ divisors n, cyclotomic i ℚ = X ^ n - 1 := by
    apply prod_cyclotomic_eq_X_pow_sub_one hn
  rw [← h₁] at hdiv
  have hp : _root_.Prime f := prime hir
  have h_ex : ∃ i ∈ n.divisors, f ∣ cyclotomic i ℚ := by
    rw [← hp.dvd_finset_prod_iff]
    exact hdiv
  obtain ⟨i, imem, fdvd⟩ := h_ex
  --- obtain ⟨i, imem, fdvd⟩ := (Irreducible.prime hir).dvd_finset_prod_iff (g := fun d => cyclotomic d ℚ).mp hdiv
  have h₂ : Irreducible (cyclotomic i ℚ) := by
    apply cyclotomic.irreducible_rat (pos_of_mem_divisors imem)
  use i; constructor
  · exact imem
  · have h_assoc : Associated f (cyclotomic i ℚ) := associated_of_dvd hir h₂ fdvd
    rcases h_assoc with ⟨u, hu⟩
    use u⁻¹
    rw [← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]

lemma irre_cyc' (n : ℕ) (hn : 0 < n) (f : ℚ[X]) (h' : Monic f)
    (hir : Irreducible f) (hdiv : f ∣ X^n - 1) :
    ∃ i ∈ n.divisors, f = cyclotomic i ℚ := by
  rcases irre_cyc n hn f hir hdiv with ⟨i, imem, u, feq⟩
  use i, imem
  have ueq : u.val = 1 := by
    rw [feq, Monic] at h'
    have cyc_mo : Monic (cyclotomic i ℚ) := cyclotomic.monic i ℚ
    have mon : Monic u.val := Monic.of_mul_monic_right cyc_mo h'
    rw [← Monic.isUnit_iff mon]
    exact u.isUnit
  rw [ueq, one_mul] at feq
  exact feq

lemma exist_irre : ∃ g : ℚ[X], Monic g ∧ Irreducible g ∧ g ∣ minpoly ℚ M.val := by
  have h₁ : minpoly ℚ M.val ≠ 0 := ne_zero (isIntegral M.val)
  have h₂ : ¬IsUnit (minpoly ℚ M.val) := by
    rw [isUnit_iff_degree_eq_zero]
    push_neg
    have h₃ : 0 < (minpoly ℚ M.val).degree := by
      apply degree_pos (Matrix.isIntegral M.val)
    exact Ne.symm (_root_.ne_of_lt h₃)
  rcases WfDvdMonoid.exists_irreducible_factor h₂ h₁ with ⟨g, gir, gdiv⟩
  let f := normalize g
  use f
  constructor
  · apply monic_normalize (Irreducible.ne_zero gir)
  constructor
  · have h_assoc : Associated f g := Associated.symm (associated_normalize g)
    exact (Associated.irreducible_iff (id (Associated.symm h_assoc))).mp gir
  · exact normalize_dvd_iff.mpr gdiv

example : ∃ g : ℚ[X], Monic g ∧ Irreducible g ∧ g ∣ minpoly ℚ M.val := by
  apply exists_monic_irreducible_factor
  have h₂ : ¬IsUnit (minpoly ℚ M.val) := by
    rw [isUnit_iff_degree_eq_zero]
    push_neg
    have h₃ : 0 < (minpoly ℚ M.val).degree := by
      apply degree_pos (Matrix.isIntegral M.val)
    exact Ne.symm (_root_.ne_of_lt h₃)
  exact h₂

lemma exi_cyc (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) (h₀ : g ∈ normalizedFactors (minpoly ℚ M.val)) :
    ∃ i ∈ n.divisors, g = cyclotomic i ℚ := by
  have hn : 0 < n := by simp [h, h']
  rw [Polynomial.mem_normalizedFactors_iff (ne_zero (Matrix.isIntegral M.val))] at h₀
  rcases h₀ with ⟨hir, hmo, hdiv⟩
  have h₃ : minpoly ℚ M.val ∣ X^n - 1 := minpoly_dvd_X_pow_sub_one M h'
  have h₄ := dvd_trans hdiv h₃
  rcases irre_cyc' n hn g hmo hir h₄ with ⟨i, imem, geq⟩
  use i, imem

lemma deg_le_two (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    ∃ i ∈ n.divisors, (cyclotomic i ℚ).natDegree ≤ 2 := by
  rcases exist_irre M with ⟨g, hmo, hir, hdiv⟩
  have hn : 0 < n := by simp [h, h']
  have h₁ : minpoly ℚ M.val ∣ X ^ n - 1 := minpoly_dvd_X_pow_sub_one M h'
  have h₂ : g ∣ X ^ n - 1 := dvd_trans hdiv h₁
  rcases irre_cyc n hn g hir h₂ with ⟨i, imem, u, min⟩
  use i, imem
  calc
    _ ≤ (minpoly ℚ M.val).natDegree := by
      apply natDegree_le_of_dvd
      · have h₃ : cyclotomic i ℚ ∣ g := by
          simp [min]
        apply dvd_trans h₃ hdiv
      · exact ne_zero_of_finite ℚ M.val
    _ ≤ 2 := minpoly_deg_le_two M

def totient' (n : ℕ) : ℕ := # {a ∈ range n | n.Coprime a}

-- scoped notation "φ" => Nat.totient
example (n : ℕ) : φ n = # {a ∈ range n | n.Coprime a} := totient_eq_card_coprime n

lemma cyclotomic_deg_eq_totient (n : ℕ) :
    (cyclotomic n ℚ).natDegree = φ n := by  -- 円分多項式の次数はトーシェント関数
  exact natDegree_cyclotomic n ℚ

lemma totient_le_two  (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    ∃ i ∈ n.divisors, φ i ≤ 2 := by  -- トーシェント関数の値は2以下
  rcases deg_le_two M h h' with ⟨i, imem, deg⟩
  use i, imem
  rw [← cyclotomic_deg_eq_totient i]
  exact deg

lemma prime_factors (n : ℕ) (h : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
  nth_rw 1 [← factorization_prod_pow_eq_self h]
  rw [prod_factorization_eq_prod_primeFactors]

lemma totient_factorization (n : ℕ) (h : n ≠ 0) : φ n = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) := by
  rw [totient_eq_prod_factorization h]
  rfl

lemma p_cases (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) :
    ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  have hp' : Prime p := by exact prime_of_mem_primeFactors hp
  rw [totient_factorization n h] at h'
  have h₁ : p ^ (n.factorization p - 1) * (p - 1) ∣ 2 := by
    rw [← h']
    apply dvd_prod_of_mem
    exact hp
  have h₂ : p - 1 ∣ 2 := by
    exact dvd_of_mul_left_dvd h₁
  have h₃ : p - 1 ≤ 2 := by apply le_of_dvd (by norm_num) h₂
  interval_cases hu : p - 1
  · omega
  · left; omega
  · right; omega

lemma n_exist (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
  have h₁ := p_cases n h h'
  rw [totient_factorization n h] at h'
  nth_rw 1 [prime_factors n h]
  have h₂ : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    simp
    apply h₁
    assumption
  rw [prod_subset h₂ ?_]
  · rw [prod_pair]
    norm_num
  · intro p pmem pnot
    simp; right
    exact notMem_support_iff.mp pnot

lemma totient_two_eq (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n ∈ ({3, 4, 6} : Finset ℕ) := by
  have n_exist := n_exist n h h'
  rw [n_exist] at h'
  set a := n.factorization 2
  set b := n.factorization 3
  rw [totient_mul] at h'
  · have h₁ : φ (2 ^ a) ∣ 2 := by
      nth_rw 2 [← h']
      apply dvd_mul_right
    have h₂ : φ (2 ^ a) ≤ 2 := by
      apply le_of_dvd (by norm_num) h₁
    interval_cases h_two : φ (2 ^ a)
    · linarith
    · rw [totient_eq_one_iff] at h_two
      rw [one_mul] at h'
      have bneq : b ≠ 0 := by
        by_contra
        rw [this, pow_zero, totient_one] at h'
        linarith
      rcases h_two with one | two
      · rw [one, one_mul] at n_exist
        have hb : b = 1 := by
          rw [totient_prime_pow] at h'
          · simp at h'
            omega
          · decide
          · apply pos_of_ne_zero bneq
        rw [hb, pow_one] at n_exist
        simp; left; assumption
      · rw [two] at n_exist
        have hb : b = 1 := by
          rw [totient_prime_pow] at h'
          · simp at h'
            omega
          · decide
          · apply pos_of_ne_zero bneq
        rw [hb, pow_one] at n_exist
        simp; right; right; assumption
    · have h₃ : φ (3 ^ b) = 1 := by linarith [h']
      rw [totient_eq_one_iff] at h₃
      rcases h₃ with one | two
      · simp at one
        rw [one, pow_zero, mul_one] at n_exist
        have ha : a = 2 := by
          rw [totient_prime_pow] at h_two
          · simp [pow_eq_self_iff h₂] at h_two
            assumption
          · decide
          · have aneq : a ≠ 0 := by
              by_contra
              rw [this, pow_zero, totient_one] at h_two
              linarith
            apply pos_of_ne_zero aneq
        rw [ha] at n_exist
        simp; right; left; assumption
      · have hb : b = 0 ∨ b ≥ 1 := by omega
        obtain zero | one := hb
        · rw [zero, pow_zero] at two
          linarith
        · have hb' : 3 ≤ 3 ^ b :=
            calc
              3 = 3 ^ 1 := by norm_num
              _ ≤ 3 ^ b := by apply pow_le_pow; rfl; norm_num; exact one
          linarith
  · apply coprime_pow_primes <;> decide

lemma totient_le_two_iff (hn : 0 < n) : φ n ≤ 2 ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  constructor <;> intro h₀
  · have h₂ : n ≤ 6 := by
      interval_cases ht : totient n
      · simp at ht
        linarith
      · rw [totient_eq_one_iff] at ht
        rcases ht with n1 | n2
        · linarith
        · linarith
      · have h₄ : n ∈ ({3, 4, 6} : Finset ℕ) := by
          apply totient_two_eq
          · exact Nat.ne_zero_of_lt hn
          · assumption
        fin_cases h₄ <;> linarith
    interval_cases n <;> simp; contradiction
  · fin_cases h₀ <;> decide

lemma cyclotomic_four : cyclotomic 4 ℚ = X ^ 2 + 1 := by
  have h₁ : cyclotomic 4 ℚ = (X^4 - 1) /ₘ ∏ i ∈ properDivisors 4, cyclotomic i ℚ := by
      apply cyclotomic_eq_X_pow_sub_one_div (by positivity)
  have h₂ : properDivisors 4 = {1, 2} := by decide
  have h₃ : (X - 1) * (X + 1) = (X^2 - 1 : ℚ[X]) := by ring
  rw [h₂, prod_pair (by norm_num), cyclotomic_one, cyclotomic_two, h₃] at h₁
  rw [h₁, divByMonic_eq_div]
  rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd]
  · ring
  · exact X_pow_sub_C_ne_zero (by norm_num) 1
  · exact dvd_pow_sub_one_of_dvd (by norm_num)
  · exact monic_X_pow_sub (by norm_num)

lemma cyclotomic_six : cyclotomic 6 ℚ = X ^ 2 - X + 1 := by
  have h₁ : cyclotomic 6 ℚ = (X^6 - 1) /ₘ ∏ i ∈ properDivisors 6, cyclotomic i ℚ := by
      apply cyclotomic_eq_X_pow_sub_one_div (by positivity)
  have h₂ : properDivisors 6 = {1, 2, 3} := by decide
  have h₃ : (X - 1) * ((X + 1) * (X^2 + X + 1)) = (X^4 + X^3 - X - 1 : ℚ[X]) := by ring
  simp [h₂, cyclotomic_one, cyclotomic_two, cyclotomic_three, h₃] at h₁
  rw [h₁, divByMonic_eq_div]
  rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd]
  · ring
  · intro h
    have h_coeff := congr_arg (coeff · 4) h
    simp [coeff_X, coeff_one] at h_coeff
  · have h₄ : (X ^ 6 - 1 : ℚ[X]) = (X ^ 4 + X ^ 3 - X - 1) * (X ^ 2 - X + 1) := by ring
    rw [h₄]
    apply dvd_mul_right
  · have h : (X^4 + X^3 - X - 1 : ℚ[X]).natDegree = 4 := by
      compute_degree
      · norm_num
      · norm_num
    simp [Monic, leadingCoeff, h, coeff_X, coeff_one]

lemma cyc_class (n : ℕ) (hn : n > 0) (hdeg : (cyclotomic n ℚ).natDegree ≤ 2) :
    cyclotomic n ℚ ∈ ({X - 1, X + 1, X^2 + X + 1, X^2 + 1, X^2 - X + 1} : Finset ℚ[X]) := by
  rw [cyclotomic_deg_eq_totient, totient_le_two_iff] at hdeg
  simp
  fin_cases hdeg
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; left; rw [cyclotomic_four]
  · right; right; right; right; rw [cyclotomic_six]
  · exact hn

example (f : ℚ[X]) (hfdeg : f.natDegree ∈ ({1, 2} : Finset ℕ)) (hmonic : Monic f) (hnod : f.roots.Nodup)
    (H : f.factor ∈ ({X - 1, X + 1, X^2 + 1, X^2 + X + 1, X^2 - X + 1} : Finset ℚ[X])) :
    f ∈ ({X - 1, X + 1, (X - 1) * (X + 1), X^2 + 1, X^2 + X + 1, X^2 - X + 1} : Finset ℚ[X]) := by
  have h_div : f.factor ∣ f := by
    apply factor_dvd_of_natDegree_ne_zero
    intro h
    rw [h] at hfdeg; contradiction
  rcases h_div with ⟨g, hg⟩
  have h₁ : Monic f.factor := by
    simp at H
    rcases H with (h | h | h | h | h) <;> rw [h]
    · apply monic_X_sub_C
    · apply monic_X_add_C
    · apply monic_X_pow_add_C
      norm_num
    · have h₀ : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by
        compute_degree
        · norm_num
      simp [Monic, leadingCoeff, h₀, coeff_X, coeff_one]
    · have h₀ : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by
        compute_degree
        · norm_num
      simp [Monic, leadingCoeff, h₀, coeff_X, coeff_one]
  have h₂ : Monic g := by
    apply Monic.of_mul_monic_left h₁
    rw [← hg]; exact hmonic
  have fdeg : f.natDegree = f.factor.natDegree + g.natDegree := by
    nth_rw 1 [hg]
    apply natDegree_mul
    · exact Monic.ne_zero h₁
    · exact Monic.ne_zero h₂
  simp at hfdeg
  rcases hfdeg with (one | two)
  · have gdeg : g.natDegree = 0 := by
      have hactor_deg : 1 ≤ f.factor.natDegree := by
        simp at H
        rcases H with (h | h | h | h | h) <;> rw [h]
        · have h₀ : (X - 1 : ℚ[X]).natDegree = 1 := by apply natDegree_X_sub_C
          rw [h₀]
        · have h₀ : (X + 1 : ℚ[X]).natDegree = 1 := by apply natDegree_X_add_C
          rw [h₀]
        · have h₀ : (X^2 + 1 : ℚ[X]).natDegree = 2 := by
            apply natDegree_X_pow_add_C
          linarith [h₀]
        · have h₀ : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by
            compute_degree; norm_num
          linarith [h₀]
        · have h₀ : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by
            compute_degree; norm_num
          linarith [h₀]
      linarith
    have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
    have feq : f = f.factor := by rw [geq, mul_one] at hg; assumption
    rw [← feq] at H
    simp at H
    rcases H with (h | h | h | h | h) <;> simp [h]
  · simp at H
    rcases H with (h | h | h | h | h) <;> simp
    · have f.fac_deg : f.factor.natDegree = 1 := by
        rw [h]
        apply natDegree_X_sub_C
      have g_deg : g.natDegree = 1 := by linarith
      right; right; left
      rw [hg, h]
      sorry
    · sorry
    · have h₀ : (X^2 + 1 : ℚ[X]).natDegree = 2 := by
        apply natDegree_X_pow_add_C
      have gdeg : g.natDegree = 0 := by
        rw [h, h₀, two] at fdeg
        linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have feq : f = f.factor := by rw [geq, mul_one] at hg; assumption
      rw [feq]
      right; right; right; left; assumption
    · have h₀ : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by
        compute_degree; norm_num
      have gdeg : g.natDegree = 0 := by
        rw [h, h₀, two] at fdeg
        linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have feq : f = f.factor := by rw [geq, mul_one] at hg; assumption
      rw [feq]
      right; right; right; right; left; assumption
    · have h₀ : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by
        compute_degree; norm_num
      have gdeg : g.natDegree = 0 := by
        rw [h, h₀, two] at fdeg
        linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have feq : f = f.factor := by rw [geq, mul_one] at hg; assumption
      rw [feq]
      right; right; right; right; right; assumption

example (n : ℕ) (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (h₀ : f ∈ normalizedFactors (minpoly ℚ M.val)) :
    f ∈ ({X - 1, X + 1, X^2 + 1, X^2 + X + 1, X^2 - X + 1} : Finset ℚ[X]) := by
  rcases exi_cyc M h h' h₀ with ⟨i, imem, feq⟩
  rw [Polynomial.mem_normalizedFactors_iff (ne_zero (Matrix.isIntegral M.val))] at h₀
  rcases h₀ with ⟨fir, fmo, fdi⟩
  have fdeg : f.natDegree ≤ 2 :=
    calc
      _ ≤ (minpoly ℚ M.val).natDegree := by
        apply natDegree_le_of_dvd fdi (ne_zero (Matrix.isIntegral M.val))
      _ ≤ 2 := by exact minpoly_deg_le_two M
  rw [feq, cyclotomic_deg_eq_totient, totient_le_two_iff (pos_of_mem_divisors imem)] at fdeg
  rw [feq]
  simp at *
  rcases fdeg with (h | h | h | h | h)
  · left; simp [h]
  · right; left; simp [h]
  · right; right; right; left; simp [h]
  · right; right; left; rw [h, cyclotomic_four]
  · right; right; right; right; rw [h, cyclotomic_six]

lemma minfac (n : ℕ) (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    (normalizedFactors (minpoly ℚ M.val)).toFinset ⊆
    ({X - 1, X + 1, X^2 + 1, X^2 + X + 1, X^2 - X + 1} : Finset ℚ[X]) := by
  intro f h₀
  rw [Multiset.mem_toFinset] at h₀
  rcases exi_cyc M h h' h₀ with ⟨i, imem, feq⟩
  rw [Polynomial.mem_normalizedFactors_iff (ne_zero (Matrix.isIntegral M.val))] at h₀
  rcases h₀ with ⟨fir, fmo, fdi⟩
  have fdeg : f.natDegree ≤ 2 :=
    calc
      _ ≤ (minpoly ℚ M.val).natDegree := by
        apply natDegree_le_of_dvd fdi (ne_zero (Matrix.isIntegral M.val))
      _ ≤ 2 := by exact minpoly_deg_le_two M
  rw [feq, cyclotomic_deg_eq_totient, totient_le_two_iff (pos_of_mem_divisors imem)] at fdeg
  rw [feq]
  simp at *
  rcases fdeg with (h | h | h | h | h)
  · left; simp [h]
  · right; left; simp [h]
  · right; right; right; left; simp [h]
  · right; right; left; rw [h, cyclotomic_four]
  · right; right; right; right; rw [h, cyclotomic_six]

example (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∈ ({X - 1, X + 1, X^2 + X + 1, X^2 + 1, X^2 - X + 1, (X - 1)*(X + 1)} : Finset ℚ[X]) := by
  have hn : 0 < n := by simp [h, h']
  have h₁ : (minpoly ℚ M.val).natDegree ≤ 2 := minpoly_deg_le_two M
  have minfac := minfac M n h h'
  rcases exist_irre M with ⟨g, gmo, gir, gdiv⟩
  have h₂ : g ∣ X^n - 1 := dvd_trans gdiv (minpoly_dvd_X_pow_sub_one M h')
  have h₃ : g ∈ normalizedFactors (minpoly ℚ M.val) := by
    rw [Polynomial.mem_normalizedFactors_iff (ne_zero (Matrix.isIntegral M.val))]
    use gir, gmo
  have h₄ : g ∈ ({X - 1, X + 1, X ^ 2 + 1, X ^ 2 + X + 1, X ^ 2 - X + 1} : Finset ℚ[X]) := by
    exact minfac (Multiset.mem_toFinset.mpr h₃)
  have h₇ : Squarefree (X^n - 1 : ℚ[X]) := by
    apply Separable.squarefree
    apply separable_X_pow_sub_C
    rw [ne_eq, cast_eq_zero]
    intro nh; linarith
    norm_num
  have h₅ : Squarefree (minpoly ℚ M.val) := by
    apply Squarefree.squarefree_of_dvd (minpoly_dvd_X_pow_sub_one M h') h₇
  have h₆ : (normalizedFactors (minpoly ℚ M.val)).Nodup := by
    rw [← UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors (ne_zero (Matrix.isIntegral M.val))]
    exact h₅
  have h_prod : minpoly ℚ M.val = (normalizedFactors (minpoly ℚ M.val)).toFinset.prod id := by
    have h_assoc : Associated (minpoly ℚ M.val) (Multiset.prod (normalizedFactors (minpoly ℚ M.val))) := by
      apply Associated.symm (prod_normalizedFactors (ne_zero (Matrix.isIntegral M.val)))

  -- 2. 両辺が Monic であることを示して、Associated を等号に変換
    have h_eq : minpoly ℚ M.val = Multiset.prod (normalizedFactors (minpoly ℚ M.val)) := by
      apply eq_of_monic_of_associated ?_ ?_ h_assoc
      · exact minpoly.monic  (Matrix.isIntegral M.val)
      · apply monic_multiset_prod_of_monic
        intro i imem
        apply monic_normalize
        sorry

  -- 3. Nodup (h₆) を使って Multiset.prod を Finset.prod に書き換える
    nth_rw 1 [h_eq]
    sorry
  rw [prod_subset minfac] at h_prod
  · simp [h_prod]
    sorry
  · sorry

example (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (h₀ : minpoly ℚ M.val ∈ ({cyclotomic 1 ℚ, cyclotomic 2 ℚ, cyclotomic 3 ℚ, cyclotomic 4 ℚ, cyclotomic 6 ℚ, cyclotomic 1 ℚ * cyclotomic 2 ℚ} : Finset ℚ[X])) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₀
  rcases h₀ with h1 | h2 | h3 | h4 | h6 | h12
  have h₁ := minpoly_dvd_X_pow_sub_one M h'
  · left
    rw [h1] at h₁
    sorry
  · right; left
    sorry
  · right; right; left
    sorry
  · right; right; right; left
    sorry
  · right; right; right; right
    sorry
  · right; left
    sorry

theorem finite_order_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases totient_le_two M h h' with ⟨i, imem, deg⟩
  rw [totient_le_two_iff (pos_of_mem_divisors imem)] at deg
  sorry

noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℚ) (h : IsUnit A.det) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' A h

theorem finite_order_matrix (h : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ∃ (M : GL (Fin 2) ℚ), orderOf M.val = n := by
  fin_cases h
  · use 1; simp
  · use toGL P1 (by simp)
    simp [toGL]
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos
      interval_cases m
      rw [pow_one]
      tauto
  · use toGL P2 (by simp)
    simp [toGL]
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_three]
    · intro m mlt mpos
      interval_cases m
      · rw [pow_one]; tauto
      · simp [pow_two]; tauto
  · use toGL P3 (by simp)
    simp [toGL]
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · have h : (!![0, 1; -1, 0] ^ 4 : Matrix (Fin 2) (Fin 2) ℚ) = ((!![0, 1; -1, 0] ^ 2) ^ 2 : Matrix (Fin 2) (Fin 2) ℚ) := by rw [pow_mul (!![0, 1; -1, 0]) 2 2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, pow_two]
    · intro m mlt mpos
      interval_cases m
      · rw [pow_one]; tauto
      · simp [pow_two]; tauto
      · simp [pow_three]; tauto
  · use toGL P4 (by simp)
    simp [toGL]
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · have h : (!![0, -1; 1, 1] ^ 6 : Matrix (Fin 2) (Fin 2) ℚ)  = ((!![0, -1; 1, 1] ^ 2) ^ 3 : Matrix (Fin 2) (Fin 2) ℚ) := by rw [pow_mul (!![0, -1; 1, 1]) 2 3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, pow_two, pow_three]
    · intro m mlt mpos
      interval_cases m
      · rw [pow_one]; tauto
      · simp [pow_two]; tauto
      · simp [pow_three]; tauto
      · have h : (!![0, -1; 1, 1] ^ 4 : Matrix (Fin 2) (Fin 2) ℚ)  = ((!![0, -1; 1, 1] ^ 2) ^ 2 : Matrix (Fin 2) (Fin 2) ℚ) := by rw [pow_mul (!![0, -1; 1, 1]) 2 2]
        simp [h, pow_two]; tauto
      · have h : (!![0, -1; 1, 1] ^ 5 : Matrix (Fin 2) (Fin 2) ℚ)  = ((!![0, -1; 1, 1] ^ 2) * (!![0, -1; 1, 1] ^ 3) : Matrix (Fin 2) (Fin 2) ℚ) := by rw [pow_add (!![0, -1; 1, 1]) 2 3]
        simp [h, pow_two, pow_three]; tauto

#min_imports
