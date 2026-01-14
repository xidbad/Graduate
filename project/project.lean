import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option autoImplicit true

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

lemma charpoly_deg_eq_two : (charpoly M.val).natDegree = 2 :=
  charpoly_natDegree_eq_dim M.val

lemma minpoly_dvd_charpoly : minpoly ℚ M.val ∣ charpoly M.val := by
  apply dvd ℚ M.val
  exact aeval_self_charpoly M.val

lemma minpoly_deg_le_two : (minpoly ℚ M.val).natDegree ≤ 2 :=
  calc
    _ ≤ (charpoly M.val).natDegree := by
      apply natDegree_le_of_dvd
      · apply minpoly_dvd_charpoly M
      · apply ne_zero_of_natDegree_gt
        show 1 < (charpoly M.val).natDegree
        rw [charpoly_deg_eq_two]; norm_num
    _ = 2 := by rw [charpoly_deg_eq_two]

lemma minpoly_dvd_X_pow_sub_one (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∣ X ^ n - 1 := by
  have h₁ : aeval M.val (X ^ n - 1 : ℚ[X]) = 0 := by rw [h', aeval_sub, map_pow, aeval_X, pow_orderOf_eq_one, map_one, sub_self]
  apply dvd; exact h₁

lemma exist_normalizefactor : ∃ f : ℚ[X], Monic f ∧ Irreducible f ∧ f ∣ minpoly ℚ M.val := by
  apply exists_monic_irreducible_factor
  have h₂ : ¬IsUnit (minpoly ℚ M.val) := by
    rw [isUnit_iff_degree_eq_zero]; push_neg
    have h₃ : 0 < (minpoly ℚ M.val).degree := by
      apply degree_pos (Matrix.isIntegral M.val)
    exact Ne.symm (_root_.ne_of_lt h₃)
  exact h₂

lemma normalizedfactor_eq_cyclotomic (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (f : ℚ[X]) (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val) :
    ∃ i ∈ n.divisors, f = cyclotomic i ℚ := by
  have hn : 0 < n := by simp only [h', orderOf_pos_iff, h]
  have hdvd : f ∣ X^n - 1 := dvd_trans fdvd (minpoly_dvd_X_pow_sub_one M h')
  have h₀ : ∃ i ∈ n.divisors, ∃ u : ℚ[X]ˣ, f = (u.val) * cyclotomic i ℚ := by
    have h₁ : ∏ i ∈ divisors n, cyclotomic i ℚ = X ^ n - 1 := by
      apply prod_cyclotomic_eq_X_pow_sub_one hn
    rw [← h₁] at hdvd
    have h₂ : _root_.Prime f := prime firr
    have h₃ : ∃ i ∈ n.divisors, f ∣ cyclotomic i ℚ := by
      rw [← h₂.dvd_finset_prod_iff]; exact hdvd
    obtain ⟨i, imem, fdvd⟩ := h₃
    have h₄ : Irreducible (cyclotomic i ℚ) := by
      apply cyclotomic.irreducible_rat (pos_of_mem_divisors imem)
    use i; constructor
    · exact imem
    · have h_assoc : Associated f (cyclotomic i ℚ) := associated_of_dvd firr h₄ fdvd
      rcases h_assoc with ⟨u, hu⟩
      use u⁻¹
      rw [← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨i, imem, u, feq⟩ := h₀
  use i, imem
  have ueq : u.val = 1 := by
    rw [feq] at fmon
    have h₅ : Monic (cyclotomic i ℚ) := cyclotomic.monic i ℚ
    have h₆ : Monic u.val := Monic.of_mul_monic_right h₅ fmon
    rw [← Monic.isUnit_iff h₆]; exact u.isUnit
  rw [ueq, one_mul] at feq; exact feq

lemma deg_le_two (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    ∃ i ∈ n.divisors, (cyclotomic i ℚ).natDegree ≤ 2 := by
  obtain ⟨f, fmon, firr, fdvd⟩ := exist_normalizefactor M
  obtain ⟨i, imem, feq⟩ := normalizedfactor_eq_cyclotomic M h h' f fmon firr fdvd
  have hn : 0 < n := by simp only [h', orderOf_pos_iff, h]
  have h₁ : minpoly ℚ M.val ∣ X ^ n - 1 := minpoly_dvd_X_pow_sub_one M h'
  have h₂ : f ∣ X ^ n - 1 := dvd_trans fdvd h₁
  use i, imem
  calc
    _ ≤ (minpoly ℚ M.val).natDegree := by
      apply natDegree_le_of_dvd
      · rw [feq] at fdvd; exact fdvd
      · exact ne_zero_of_finite ℚ M.val
    _ ≤ 2 := minpoly_deg_le_two M

lemma cyclotomic_deg_eq_totient (n : ℕ) : (cyclotomic n ℚ).natDegree = φ n := by
  exact natDegree_cyclotomic n ℚ

lemma exist_factorization (n : ℕ) (h : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
  nth_rw 1 [← factorization_prod_pow_eq_self h, prod_factorization_eq_prod_primeFactors]

lemma totient_factorization (n : ℕ) (h : n ≠ 0) : φ n = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) := by
  rw [totient_eq_prod_factorization h]; rfl

lemma p_cases (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  have hp' : Prime p := by exact prime_of_mem_primeFactors hp
  rw [totient_factorization n h] at h'
  have h₁ : p ^ (n.factorization p - 1) * (p - 1) ∣ 2 := by
    rw [← h']; apply dvd_prod_of_mem; exact hp
  have h₂ : p - 1 ∣ 2 := dvd_of_mul_left_dvd h₁
  have h₃ : p - 1 ≤ 2 := by apply le_of_dvd (by norm_num) h₂
  interval_cases hu : p - 1
  · omega
  · left; omega
  · right; omega

lemma n_exist (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
  have h₁ := p_cases n h h'
  rw [totient_factorization n h] at h'
  nth_rw 1 [exist_factorization n h]
  have h₂ : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp; rw [Finset.mem_insert, Finset.mem_singleton]; apply h₁; assumption
  rw [prod_subset h₂ ?_]
  · rw [prod_pair]; norm_num
  · intro p pmem pnot; rw [pow_eq_one_iff]; right
    exact notMem_support_iff.mp pnot

lemma totient_eq_two (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n ∈ ({3, 4, 6} : Finset ℕ) := by
  have n_exist := n_exist n h h'
  rw [n_exist, totient_mul] at h'
  set a := n.factorization 2
  set b := n.factorization 3
  · have h₁ : φ (2 ^ a) ∣ 2 := by nth_rw 2 [← h']; apply dvd_mul_right
    have h₂ : φ (2 ^ a) ≤ 2 := le_of_dvd (by norm_num) h₁
    interval_cases h_two : φ (2 ^ a)
    · linarith
    · rw [totient_eq_one_iff] at h_two
      rw [one_mul] at h'
      have bneq : b ≠ 0 := by
        by_contra
        rw [this, pow_zero, totient_one] at h'; linarith
      rcases h_two with one | two
      · rw [one, one_mul] at n_exist
        have hb : b = 1 := by
          rw [totient_prime_pow] at h'
          · simp at h'; omega
          · decide
          · apply pos_of_ne_zero bneq
        rw [hb, pow_one] at n_exist
        rw [Finset.mem_insert]; left; assumption
      · rw [two] at n_exist
        have hb : b = 1 := by
          rw [totient_prime_pow] at h'
          · simp at h'; omega
          · decide
          · apply pos_of_ne_zero bneq
        rw [hb, pow_one] at n_exist
        simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; assumption
    · have h₃ : φ (3 ^ b) = 1 := by linarith [h']
      rw [totient_eq_one_iff] at h₃
      rcases h₃ with one | two
      · simp only [pow_eq_one_iff, OfNat.ofNat_ne_one, false_or] at one
        rw [one, pow_zero, mul_one] at n_exist
        have ha : a = 2 := by
          rw [totient_prime_pow] at h_two
          · simp [pow_eq_self_iff h₂] at h_two; assumption
          · decide
          · have aneq : a ≠ 0 := by
              by_contra
              rw [this, pow_zero, totient_one] at h_two; linarith
            apply pos_of_ne_zero aneq
        rw [ha] at n_exist
        simp only [Finset.mem_insert, Finset.mem_singleton]; right; left; assumption
      · have hb : b = 0 ∨ b ≥ 1 := by omega
        obtain zero | one := hb
        · rw [zero, pow_zero] at two; linarith
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
      · rw [totient_eq_zero] at ht; linarith [ht]
      · rw [totient_eq_one_iff] at ht
        rcases ht with n1 | n2 <;> linarith
      · have h₄ : n ∈ ({3, 4, 6} : Finset ℕ) := by
          apply totient_eq_two
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
      compute_degree <;> norm_num
    simp [Monic, leadingCoeff, h, coeff_X, coeff_one]

lemma cyclotomic_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (f : ℚ[X]) (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val) :
    f ∈ ({X - 1, X + 1, X^2 + 1, X^2 + X + 1, X^2 - X + 1} : Finset ℚ[X]) := by
  obtain ⟨i, imem, feq⟩ := normalizedfactor_eq_cyclotomic M h h' f fmon firr fdvd
  rw [feq] at fdvd
  have h₁ : (cyclotomic i ℚ).natDegree ≤ 2 :=
    calc
      _ ≤ (minpoly ℚ M.val).natDegree := natDegree_le_of_dvd fdvd (ne_zero_of_finite ℚ M.val)
      _ ≤ 2 := minpoly_deg_le_two M
  rw [cyclotomic_deg_eq_totient, totient_le_two_iff (pos_of_mem_divisors imem)] at h₁
  rw [← cyclotomic_one, ← cyclotomic_two, ← cyclotomic_three, ← cyclotomic_four, ← cyclotomic_six, feq]
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₁
  rcases h₁ with (h | h | h | h | h) <;> rw [h] <;> simp

lemma g_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) (f g : ℚ[X])
    (fmon : Monic f) (girr : Irreducible g) (fgeq : (minpoly ℚ M.val) = f * g) :
    g ∈ ({X - 1, X + 1, X^2 + 1, X^2 + X + 1, X^2 - X + 1} : Finset ℚ[X]) := by
  have gdvd : g ∣ minpoly ℚ M.val := by
    rw [fgeq]; exact dvd_mul_left g f
  have h₀ : Monic (minpoly ℚ M.val) := monic (Matrix.isIntegral M.val)
  have gmon : Monic g := by
    rw [fgeq] at h₀; exact Monic.of_mul_monic_left fmon h₀
  exact cyclotomic_class M h h' g gmon girr gdvd

lemma minpoly_classify (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∈ ({X - 1, X + 1, X^2 + X + 1, X^2 + 1, X^2 - X + 1, (X - 1)*(X + 1)} : Finset ℚ[X]) := by
  obtain ⟨f, fmon, firr, fdvd⟩ := exist_normalizefactor M
  have h₀ := cyclotomic_class M h h' f fmon firr fdvd
  rcases fdvd with ⟨g, hg⟩
  have h₁ : Monic (minpoly ℚ M.val) := monic (Matrix.isIntegral M.val)
  have h₂ : Monic g := by
    rw [hg] at h₁
    apply Monic.of_mul_monic_left fmon h₁
  have h₃ : (minpoly ℚ M.val).natDegree = f.natDegree + g.natDegree := by
    rw [hg]
    apply natDegree_mul
    · exact Monic.ne_zero fmon
    · exact Monic.ne_zero h₂
  have h₄ : (minpoly ℚ M.val).natDegree ∈ ({1, 2} : Finset ℕ) := by
    have h₅ := minpoly_deg_le_two M
    interval_cases hdeg : (minpoly ℚ M.val).natDegree
    · contrapose! hdeg
      exact ne_of_gt (minpoly.natDegree_pos (Matrix.isIntegral M.val))
    · norm_num
    · norm_num
  rw [Finset.mem_insert, Finset.mem_singleton] at h₄
  rcases h₄ with (h4 | h4)
  · have gdeg : g.natDegree = 0 := by
      have hactor_deg : 1 ≤ f.natDegree := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h₀
        rcases h₀ with (h | h | h | h | h) <;> rw [h]
        · have h1 : (X - 1 : ℚ[X]).natDegree = 1 := natDegree_X_sub_C 1
          rw [h1]
        · have h1 : (X + 1 : ℚ[X]).natDegree = 1 := natDegree_X_add_C 1
          rw [h1]
        · have h1 : (X^2 + 1 : ℚ[X]).natDegree = 2 := natDegree_X_pow_add_C
          linarith [h1]
        · have h1 : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by
            compute_degree; norm_num
          linarith [h1]
        · have h1 : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by
            compute_degree; norm_num
          linarith [h1]
      linarith
    have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
    have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; assumption
    simp only [← hf, Finset.mem_insert, Finset.mem_singleton] at h₀
    rcases h₀ with (h | h | h | h | h) <;> simp [h]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h₀
    rcases h₀ with (h1 | h1 | h | h | h)
    · have fdeg : f.natDegree = 1 := by rw [h1]; compute_degree; norm_num
      have gdeg : g.natDegree = 1 := by rw [h4, fdeg] at h₃; linarith
      simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; right; right; right
      rw [hg, h1]
      have girr : Irreducible g := by
        rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num), cast_one] at gdeg
        exact irreducible_of_degree_eq_one  gdeg
      obtain h5 := g_class M h h' f g fmon girr hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at h5
      rcases h5 with (h6 | h6 | h6 | h6 | h6)
      · rw [h6, ← h1] at hg
        have h₅ : Squarefree (minpoly ℚ M.val) := by
          have h₇ : Squarefree (X^n - 1 : ℚ[X]) := by
            apply Separable.squarefree
            apply separable_X_pow_sub_C
            rw [ne_eq, cast_eq_zero]
            intro nh
            have hn : 0 < n := by simp only [h', orderOf_pos_iff, h]
            linarith; norm_num
          apply Squarefree.squarefree_of_dvd (minpoly_dvd_X_pow_sub_one M h') h₇
        rw [squarefree_iff_no_irreducibles (ne_zero_of_finite ℚ M.val)] at h₅
        specialize h₅ f firr; rw [hg] at h₅; contrapose h₅; exact dvd_refl (f * f)
      · rw [h6]
      · rw [h6] at gdeg
        have : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
        rw [this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
        rw [this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
        rw [this] at gdeg; contradiction
    · have fdeg : f.natDegree = 1 := by rw [h1]; compute_degree; norm_num
      have gdeg : g.natDegree = 1 := by rw [h4, fdeg] at h₃; linarith
      simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; right; right; right
      rw [hg, h1]
      have girr : Irreducible g := by
        rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num), cast_one] at gdeg
        exact irreducible_of_degree_eq_one  gdeg
      obtain h5 := g_class M h h' f g fmon girr hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at h5
      rcases h5 with (h6 | h6 | h6 | h6 | h6)
      · rw [h6, mul_comm]
      · rw [h6, ← h1] at hg
        have h₅ : Squarefree (minpoly ℚ M.val) := by
          have h₇ : Squarefree (X^n - 1 : ℚ[X]) := by
            apply Separable.squarefree
            apply separable_X_pow_sub_C
            rw [ne_eq, cast_eq_zero]
            intro nh
            have hn : 0 < n := by simp only [h', orderOf_pos_iff, h]
            linarith; norm_num
          apply Squarefree.squarefree_of_dvd (minpoly_dvd_X_pow_sub_one M h') h₇
        rw [squarefree_iff_no_irreducibles (ne_zero_of_finite ℚ M.val)] at h₅
        specialize h₅ f firr; rw [hg] at h₅; contrapose h₅; exact dvd_refl (f * f)
      · rw [h6] at gdeg
        have : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
        rw [this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
        rw [this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
        rw [this] at gdeg; contradiction
    · have fdeg : f.natDegree = 2 := by rw [h]; compute_degree; norm_num
      have gdeg : g.natDegree = 0 := by rw [h4, fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; assumption
      rw [h] at hf
      simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; right; left; exact hf
    · have fdeg : f.natDegree = 2 := by rw [h]; compute_degree; norm_num
      have gdeg : g.natDegree = 0 := by rw [h4, fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; assumption
      rw [h] at hf
      simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; left; exact hf
    · have fdeg : f.natDegree = 2 := by rw [h]; compute_degree; norm_num
      have gdeg : g.natDegree = 0 := by rw [h4, fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; assumption
      rw [h] at hf
      simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; right; right; left; exact hf

lemma minpoly_cyc (h' : n = orderOf M.val)
    (h₀ : minpoly ℚ M.val ∈ ({cyclotomic 1 ℚ, cyclotomic 2 ℚ, cyclotomic 3 ℚ, cyclotomic 4 ℚ, cyclotomic 6 ℚ, cyclotomic 1 ℚ * cyclotomic 2 ℚ} : Finset ℚ[X])) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  simp at h₀
  rcases h₀ with (h0 | h0 | h0 | h0 | h0 | h0)
  · rw [Finset.mem_insert]; left; rw [h', orderOf_eq_one_iff, Units.val_eq_one]
    have h_eval := minpoly.aeval ℚ M.val
    simp only [h0, aeval_X, map_sub, aeval_one, sub_eq_zero] at h_eval
    exact (GeneralLinearGroup.ext_iff M 1).mpr fun i => congrFun (congrFun h_eval i)
  · simp only [Finset.mem_insert, Finset.mem_singleton]; right; left; rw [h']
    have h_eval := minpoly.aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · have h_M : (M : Matrix (Fin 2) (Fin 2) ℚ) = -1 := by
        simpa only [map_add, aeval_X, aeval_one, add_eq_zero_iff_eq_neg] using h_eval
      simp only [h_M, even_two, Even.neg_pow, one_pow]
    · intro m hm mpos
      interval_cases m
      have h_M : (M : Matrix (Fin 2) (Fin 2) ℚ) = -1 := by
        simpa only [map_add, aeval_X, aeval_one, add_eq_zero_iff_eq_neg] using h_eval
      rw [h_M, pow_one]; decide
  · simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; left; rw [h']
    have h_eval := minpoly.aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · have h_poly : (X^3 - 1 : ℚ[X]) = (X - 1) * (X^2 + X + 1) := by ring
      have h_aeval_3 : Polynomial.aeval M.val (X^3 - 1 : ℚ[X]) = 0 := by
        rw [h_poly, map_mul, h_eval, mul_zero]
      rw [aeval_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h_aeval_3
      exact h_aeval_3
    · intro m hm mpos
      interval_cases m
      · intro hM; rw [pow_one] at hM
        simp [hM] at h_eval; norm_num at h_eval; contradiction
      · intro hM
        simp only [map_add, map_pow, aeval_X, map_one, hM] at h_eval
        have Meq : M.val = -2 := by
          rw [add_comm 1, add_assoc] at h_eval
          have two : (1 : Matrix (Fin 2) (Fin 2) ℚ) + 1 = 2 := by norm_num
          rw [two] at h_eval; exact eq_neg_of_add_eq_zero_left h_eval
        simp only [Meq, even_two, Even.neg_pow] at hM; norm_num at hM; contradiction
  · simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; right; left; rw [h']
    have h_eval := minpoly.aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · have h_poly : (X^4 - 1 : ℚ[X]) = (X^2 + 1) * (X^2 - 1) := by ring
      have h_aeval_4 : Polynomial.aeval M.val (X^4 - 1 : ℚ[X]) = 0 := by
        rw [h_poly, map_mul, ← cyclotomic_four, h_eval, zero_mul]
      rw [aeval_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h_aeval_4
      exact h_aeval_4
    · intro m hm mpos
      interval_cases m
      · intro hM; rw [pow_one] at hM
        simp [cyclotomic_four, hM] at h_eval; norm_num at h_eval; contradiction
      · intro hM
        rw [cyclotomic_four, map_add, map_pow, aeval_X, map_one, hM] at h_eval
        norm_num at h_eval; contradiction
      · intro hM
        rw [cyclotomic_four, map_add, map_pow, aeval_X, map_one] at h_eval
        have M_pow_two : M.val ^ 2 = -1 := eq_neg_of_add_eq_zero_left h_eval
        rw [pow_add M.val 1 2, M_pow_two, pow_one, mul_neg_one, neg_eq_iff_eq_neg] at hM
        rw [hM] at h_eval; norm_num at h_eval; contradiction
  · simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; right; right; rw [h']
    have h_eval := minpoly.aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · have h_poly : (X^6 - 1 : ℚ[X]) = (X^2 - X + 1) * (X^4 + X^3 - X - 1) := by ring
      have h_aeval_6 : Polynomial.aeval M.val (X^6- 1 : ℚ[X]) = 0 := by
        rw [h_poly, map_mul, ← cyclotomic_six, h_eval, zero_mul]
      rw [aeval_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h_aeval_6
      exact h_aeval_6
    · intro m hm mpos
      interval_cases m
      · intro hM; rw [pow_one] at hM
        simp [cyclotomic_six, hM] at h_eval
      · intro hM
        rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        rw [hM, add_comm, ← add_sub_assoc, sub_eq_zero] at h_eval; norm_num at h_eval
        rw [← h_eval] at hM; norm_num at hM; contradiction
      · intro hM
        rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        have M_pow_two : M.val ^ 2 = M.val - 1 :=
          calc
            _ = M.val ^ 2 - (M.val - 1) + (M.val - 1) := by rw [sub_add_cancel]
            _ = M.val ^ 2 - M.val + 1 + (M.val - 1) := by rw [sub_add (M.val ^ 2) M.val 1]
            _ = M.val - 1 := by rw [h_eval, zero_add]
        have M_pow_three : M.val ^ 3 = -1 :=
          calc
            _ = M.val * M.val ^ 2 := by rw [pow_add M.val 1 2, pow_one]
            _ = M.val * (M.val - 1) := by rw [M_pow_two]
            _ = M.val ^ 2 - M.val := by rw [mul_sub, pow_two, mul_one]
            _ = (M.val - 1) - M.val := by rw [M_pow_two]
            _ = -1 := by rw [sub_sub, add_comm 1, sub_add_cancel_left M.val 1]
        rw [hM] at M_pow_three; contradiction
      · intro hM
        rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        have M_pow_two : M.val ^ 2 = M.val - 1 :=
          calc
            _ = M.val ^ 2 - (M.val - 1) + (M.val - 1) := by rw [sub_add_cancel]
            _ = M.val ^ 2 - M.val + 1 + (M.val - 1) := by rw [sub_add (M.val ^ 2) M.val 1]
            _ = M.val - 1 := by rw [h_eval, zero_add]
        have M_pow_four : M.val ^ 4 = - M.val :=
          calc
            M.val ^ 4 = (M.val - 1) ^ 2 := by rw [pow_mul M.val 2 2, M_pow_two]
            _ = M.val ^ 2 - 2 * M.val + 1 := by noncomm_ring
            _ = (M.val - 1) - 2 * M.val + 1 := by rw [M_pow_two]
            _ = -M.val := by noncomm_ring
        rw [M_pow_four, neg_eq_iff_eq_neg] at hM
        rw [hM] at h_eval; norm_num at h_eval; contradiction
      · intro hM
        rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        have M_pow_two : M.val ^ 2 = M.val - 1 :=
          calc
            _ = M.val ^ 2 - (M.val - 1) + (M.val - 1) := by rw [sub_add_cancel]
            _ = M.val ^ 2 - M.val + 1 + (M.val - 1) := by rw [sub_add (M.val ^ 2) M.val 1]
            _ = M.val - 1 := by rw [h_eval, zero_add]
        have M_pow_five : M.val ^ 5 = - M.val + 1 :=
          calc
            M.val ^ 5 = M.val ^ 2 * M.val ^ 2 * M.val := by noncomm_ring
            _ = (M.val - 1) * (M.val - 1) * M.val := by repeat rw [M_pow_two]
            _ = M.val ^ 2 * M.val - 2 * M.val ^ 2 + M.val := by noncomm_ring
            _ = (M.val - 1) * M.val - 2 * (M.val - 1) + M.val := by repeat rw [M_pow_two]
            _ = M.val ^ 2 - M.val - 2 * M.val + 2 + M.val := by rw [mul_sub, mul_one]; noncomm_ring
            _ = M.val - 1 - 2 * M.val + 2 := by rw [M_pow_two]; noncomm_ring
            _ = - M.val - 1 + 2 := by noncomm_ring
            _ = - M.val + 1 := by noncomm_ring; norm_num
        rw [M_pow_five, add_eq_right, neg_eq_zero] at hM
        rw [hM] at h_eval; norm_num at h_eval
  · simp only [Finset.mem_insert, Finset.mem_singleton]; right; left; rw [h']
    have h_eval := minpoly.aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · rw [map_mul, map_add, map_sub, aeval_X, map_one] at h_eval
      have : M.val ^ 2 - 1 = 0 :=
        calc
          _ = (M.val - 1) * (M.val + 1) := by noncomm_ring
          _ = 0 := h_eval
      exact sub_eq_zero.mp this
    · intro m hm mpos
      interval_cases m
      rw [pow_one]; intro hM
      have M_eval : Polynomial.aeval M.val (X - 1 : ℚ[X]) = 0 := by simp [hM]
      have h_div : minpoly ℚ M.val ∣ (X - 1 : ℚ[X]) := minpoly.dvd ℚ M.val M_eval
      rw [h0] at h_div
      have h_deg := Polynomial.degree_le_of_dvd h_div (X_sub_C_ne_zero 1)
      have h₁ : (X - 1 : ℚ[X]).degree = 1 := degree_X_sub_C 1
      have h₂ : (X + 1 : ℚ[X]).degree = 1 := degree_X_add_C 1
      rw [degree_mul, h₁, h₂] at h_deg; norm_num at h_deg

lemma finorder_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases minpoly_classify M h h' with h₀
  rw [← cyclotomic_one, ← cyclotomic_two, ← cyclotomic_three, ← cyclotomic_four, ← cyclotomic_six] at h₀
  exact minpoly_cyc M h' h₀

noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℚ) (h : IsUnit A.det) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' A h

theorem finite_order_matrix (h : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ∃ (M : GL (Fin 2) ℚ), orderOf M.val = n := by
  fin_cases h
  · use 1; rw [Units.val_one, orderOf_one]
  · use toGL P1 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'']; rw [orderOf_eq_iff (by norm_num)]
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos; interval_cases m; rw [pow_one]; tauto
  · use toGL P2 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'']; rw [orderOf_eq_iff (by norm_num)]
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_three]
    · intro m mlt mpos
      interval_cases m
      · rw [pow_one]; tauto
      · simp [pow_two]; tauto
  · use toGL P3 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'']; rw [orderOf_eq_iff (by norm_num)]
    constructor
    · rw [pow_mul (!![0, 1; -1, 0]) 2 2]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos
      interval_cases m
      · rw [pow_one]; tauto
      · simp [pow_two]; tauto
      · simp [pow_three]; tauto
  · use toGL P4 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'']; rw [orderOf_eq_iff (by norm_num)]
    constructor
    · rw [pow_mul (!![0, -1; 1, 1]) 2 3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two, pow_three]
    · intro m mlt mpos
      interval_cases m
      · rw [pow_one]; tauto
      · simp [pow_two]; tauto
      · simp [pow_three]; tauto
      · rw [pow_mul (!![0, -1; 1, 1]) 2 2]
        simp [pow_two]; tauto
      · rw [pow_add (!![0, -1; 1, 1]) 2 3]
        simp [pow_two, pow_three]; tauto

#min_imports
