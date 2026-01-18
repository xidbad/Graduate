import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option autoImplicit true

notation "E"  => !![1, 0; 0, 1]    -- 位数 1, det = 1,  tr = 2,  t^2 - 2t + 1
notation "-E" => !![-1, 0; 0, -1]  -- 位数 2, det = 1,  tr = -2, t^2 + 2t + 1
notation "P1" => !![1, 0; 0, -1]   -- 位数 2, det = -1, tr = 0,  t^2 - 1
notation "P2" => !![0, -1; 1, -1]  -- 位数 3, det = 1,  tr = -1, t^2 + t + 1
notation "P3" => !![0, 1; -1, 0]   -- 位数 4, det = 1,  tr = 0,  t^2 + 1
notation "P4" => !![0, -1; 1, 1]   -- 位数 6, det = 1,  tr = 1,  t^2 - t + 1

open Matrix Polynomial minpoly Finset Irreducible
namespace Nat

variable (M : GL (Fin 2) ℚ)

local notation "Φ" n => cyclotomic n ℚ

-- 最小多項式の次数は2以下
lemma minpoly_deg_le_two : (minpoly ℚ M.val).natDegree ≤ 2 := by
  have h₁ : (charpoly M.val).natDegree = 2 :=
    charpoly_natDegree_eq_dim M.val  -- 固有多項式の次数は行列の次元に等しい
  have h₂ : minpoly ℚ M.val ∣ charpoly M.val :=
    dvd ℚ M.val (aeval_self_charpoly M.val)  -- 固有多項式もMを根に持つ
  calc
    _ ≤ (charpoly M.val).natDegree := by
      apply natDegree_le_of_dvd h₂           -- 割り切られる側の次数の方が大きい
      · apply ne_zero_of_natDegree_gt        -- 多項式が0でない → 次数が0より大きい
        show 0 < (charpoly M.val).natDegree
        rw [h₁]; decide
    _ = 2 := by rw [h₁]

-- 最小多項式は X^n - 1 を割り切る
lemma minpoly_dvd_X_pow_sub_one (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∣ X ^ n - 1 := by
  have h₁ : aeval M.val (X ^ n - 1 : ℚ[X]) = 0 := by  -- X^n - 1もMを根に持つ
    rw [h', aeval_sub, map_pow, aeval_X, pow_orderOf_eq_one, map_one, sub_self]
  apply dvd; exact h₁

-- 最小多項式にはモニックな既約因子が存在する
lemma exist_normalizefactor : ∃ f : ℚ[X], Monic f ∧ Irreducible f ∧ f ∣ minpoly ℚ M.val := by
  apply exists_monic_irreducible_factor      -- 単元でない多項式はモニックな既約因子を持つ
  have h₁ : ¬IsUnit (minpoly ℚ M.val) := by
    rw [isUnit_iff_degree_eq_zero]; push_neg  -- 単元ならば次数は0
    have h₂ : 0 < (minpoly ℚ M.val).degree :=
      degree_pos (isIntegral M.val)           -- Mが整的(モニック多項式の根)ならば最小多項式の次数は0より大きい
    exact Ne.symm (_root_.ne_of_lt h₂)        -- 0 < a → 0 ≠ a
  exact h₁

-- 最小多項式の任意のモニックな既約因子はnの約数iについて第i円分多項式と一致する
lemma normalizedfactor_eq_cyclotomic (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (f : ℚ[X]) (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val) :
    ∃ i ∈ n.divisors, f = Φ i := by
  have npos : 0 < n := by simp only [h', orderOf_pos_iff, h]
  have hdvd : f ∣ X^n - 1 := dvd_trans fdvd (minpoly_dvd_X_pow_sub_one M h')
  rw [← prod_cyclotomic_eq_X_pow_sub_one npos] at hdvd
  have h₁ : ∃ i ∈ n.divisors, f ∣ Φ i := by
    rw [← (prime firr).dvd_finset_prod_iff]; exact hdvd
  obtain ⟨i, imem, hdvd'⟩ := h₁
  have h₂ : Irreducible (Φ i) :=
    cyclotomic.irreducible_rat (pos_of_mem_divisors imem)
  have h₃ : Associated f (Φ i) := associated_of_dvd firr h₂ hdvd'
  use i, imem
  rcases h₃ with ⟨u, feq⟩
  have ueq : u.val = 1 := by
    have h1 : Monic (Φ i) := cyclotomic.monic i ℚ
    rw [← feq] at h1
    have h2 : Monic u.val := Monic.of_mul_monic_left fmon h1
    rw [← Monic.isUnit_iff h2]; exact u.isUnit
  rw [← feq, ueq, mul_one]

-- 円分多項式の次数はオイラーのトーシェント関数と一致する
lemma cyclotomic_deg_eq_totient (n : ℕ) : (Φ n).natDegree = φ n :=
  natDegree_cyclotomic n ℚ

-- 任意の自然数nはその素因数の指数乗の積で表せる
lemma exist_factorization (n : ℕ) (h : n ≠ 0) : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
  nth_rw 1 [← factorization_prod_pow_eq_self h, prod_factorization_eq_prod_primeFactors]

-- 自然数nについてφ n = ∏ φ p^n = ∏ p^(n-1)*(p-1) が成り立つ
lemma totient_factorization (n : ℕ) (h : n ≠ 0) : φ n = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) := by
  rw [totient_eq_prod_factorization h]; rfl

-- φ n = 2 ならば n は2と3以外の素因数をもたない
lemma n_exist (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
  have h₁ : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p pmem; rw [mem_insert, mem_singleton]
    rw [totient_factorization n h] at h'
    have h1 : p ^ (n.factorization p - 1) * (p - 1) ∣ 2 := by
      rw [← h']; apply dvd_prod_of_mem; exact pmem
    have h2 : p - 1 ∣ 2 := dvd_of_mul_left_dvd h1
    have h3 : p - 1 ≤ 2 := le_of_dvd (by decide) h2
    interval_cases hu : p - 1 <;> omega
  nth_rw 1 [exist_factorization n h]
  rw [prod_subset h₁]
  · rw [prod_pair]; decide
  · intro p pmem pnot; rw [pow_eq_one_iff]; right
    exact notMem_support_iff.mp pnot

-- φ n = 2 ならば n = 3, 4, 6
lemma totient_eq_two (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n ∈ ({3, 4, 6} : Finset ℕ) := by
  have n_exist := n_exist n h h'
  rw [n_exist, totient_mul] at h'
  set a := n.factorization 2
  set b := n.factorization 3
  · have h₁ : φ (2 ^ a) ∣ 2 := by nth_rw 2 [← h']; apply dvd_mul_right
    have h₂ : φ (2 ^ a) ≤ 2 := le_of_dvd (by decide) h₁
    interval_cases h₃ : φ (2 ^ a)
    · linarith
    · rw [totient_eq_one_iff] at h₃
      rw [one_mul] at h'
      have bneq : b ≠ 0 := by
        by_contra
        rw [this, pow_zero, totient_one] at h'; linarith
      have hb : b = 1 := by
        rw [totient_prime_pow] at h'
        · simp at h'; omega
        · decide
        · exact pos_of_ne_zero bneq
      rcases h₃ with one | two
      · rw [n_exist, one, one_mul, hb, pow_one]; decide
      · rw [n_exist, two, hb, pow_one]; decide
    · rw [mul_eq_left (by decide), totient_eq_one_iff] at h'
      rcases h' with one | two
      · rw [one, mul_one] at n_exist
        have ha : a = 2 := by
          rw [totient_prime_pow] at h₃
          · simp [pow_eq_self_iff h₂] at h₃; exact h₃
          · decide
          · have aneq : a ≠ 0 := by
              by_contra
              rw [this, pow_zero, totient_one] at h₃; linarith
            apply pos_of_ne_zero aneq
        rw [n_exist, ha]; decide
      · have hb : b = 0 ∨ b ≥ 1 := by omega
        obtain zero | one := hb
        · rw [zero, pow_zero] at two; linarith
        · have hb' : 3 ≤ 3 ^ b := by
            nth_rw 1 [← pow_one 3]; exact le_pow one
          linarith
  · apply coprime_pow_primes <;> decide

-- φ n ≤ 2 は n = 1, 2, 3, 4, 6 と同値
lemma totient_le_two_iff (npos : 0 < n) : φ n ≤ 2 ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  constructor <;> intro h₁
  · have h₂ : n ≤ 6 := by
      interval_cases h₃ : totient n
      · linarith [totient_eq_zero.mp h₃]
      · rw [totient_eq_one_iff] at h₃; cases h₃ <;> linarith
      · have h₄ : n ∈ ({3, 4, 6} : Finset ℕ) := totient_eq_two n (ne_zero_of_lt npos) h₃
        fin_cases h₄ <;> linarith
    interval_cases n <;> simp; contradiction
  · fin_cases h₁ <;> decide

-- 第4円分多項式 = X ^ 2 + 1
lemma cyclotomic_four : (Φ 4) = X ^ 2 + 1 := by
  have h₁ : (Φ 4) = (X^4 - 1) /ₘ ∏ i ∈ properDivisors 4, Φ i :=
    cyclotomic_eq_X_pow_sub_one_div (by decide)
  have h₂ : properDivisors 4 = {1, 2} := by decide
  have h₃ : (X - 1) * (X + 1) = (X^2 - 1 : ℚ[X]) := by ring
  rw [h₂, prod_pair (by decide), cyclotomic_one, cyclotomic_two, h₃] at h₁
  rw [h₁, divByMonic_eq_div, EuclideanDomain.div_eq_iff_eq_mul_of_dvd]
  · ring
  · exact X_pow_sub_C_ne_zero (by decide) 1
  · exact dvd_pow_sub_one_of_dvd (by decide)
  · exact monic_X_pow_sub (by norm_num)

-- 第6円分多項式 = X ^ 2 - X + 1
lemma cyclotomic_six : (Φ 6) = X ^ 2 - X + 1 := by
  have h₁ : (Φ 6) = (X^6 - 1) /ₘ ∏ i ∈ properDivisors 6, Φ i := by
      apply cyclotomic_eq_X_pow_sub_one_div (by decide)
  have h₂ : properDivisors 6 = {1, 2, 3} := by decide
  have h₃ : (X - 1) * ((X + 1) * (X^2 + X + 1)) = (X^4 + X^3 - X - 1 : ℚ[X]) := by ring
  simp [h₂, cyclotomic_one, cyclotomic_two, cyclotomic_three, h₃] at h₁
  rw [h₁, divByMonic_eq_div, EuclideanDomain.div_eq_iff_eq_mul_of_dvd]
  · ring
  · intro h
    have h_coeff := congr_arg (coeff · 4) h
    simp [coeff_X, coeff_one] at h_coeff
  · have h₄ : (X ^ 6 - 1 : ℚ[X]) = (X ^ 4 + X ^ 3 - X - 1) * (X ^ 2 - X + 1) := by ring
    rw [h₄]
    apply dvd_mul_right
  · have h : (X^4 + X^3 - X - 1 : ℚ[X]).natDegree = 4 := by
      compute_degree <;> decide
    simp [Monic, leadingCoeff, h, coeff_X, coeff_one]

-- 最小多項式のモニックな既約因子はある円分多項式と一致する
lemma normalizedfactor_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (f : ℚ[X]) (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val) :
    f ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6} : Finset ℚ[X]) := by
  obtain ⟨i, imem, feq⟩ := normalizedfactor_eq_cyclotomic M h h' f fmon firr fdvd
  rw [feq] at fdvd
  have h₁ : (Φ i).natDegree ≤ 2 :=
    calc
      _ ≤ (minpoly ℚ M.val).natDegree := natDegree_le_of_dvd fdvd (ne_zero_of_finite ℚ M.val)
      _ ≤ 2 := minpoly_deg_le_two M
  rw [cyclotomic_deg_eq_totient, totient_le_two_iff (pos_of_mem_divisors imem)] at h₁
  fin_cases h₁ <;> simp [feq]

--
lemma g_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) (f g : ℚ[X])
    (fmon : Monic f) (girr : Irreducible g) (fgeq : (minpoly ℚ M.val) = f * g) :
    g ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6} : Finset ℚ[X]) := by
  have gdvd : g ∣ minpoly ℚ M.val := by
    rw [fgeq]; exact dvd_mul_left g f
  have h₀ : Monic (minpoly ℚ M.val) := monic (isIntegral M.val)
  have gmon : Monic g := by
    rw [fgeq] at h₀; exact Monic.of_mul_monic_left fmon h₀
  exact normalizedfactor_class M h h' g gmon girr gdvd

lemma minpoly_squarefree (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    Squarefree (minpoly ℚ M.val) := by
  have h₇ : Squarefree (X^n - 1 : ℚ[X]) := by
    apply Separable.squarefree
    apply separable_X_pow_sub_C
    rw [ne_eq, cast_eq_zero]
    intro nh
    have hn : 0 < n := by simp only [h', orderOf_pos_iff, h]
    linarith; decide
  apply Squarefree.squarefree_of_dvd (minpoly_dvd_X_pow_sub_one M h') h₇

example (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) (f g : ℚ[X])
    (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val)
    (fgeq : (minpoly ℚ M.val) = f * g) :
    g ∈ ({1, Φ 1, Φ 2} : Finset ℚ[X]) := by
  have h₀ := normalizedfactor_class M h h' f fmon firr fdvd
  have gdvd : g ∣ minpoly ℚ M.val := by
    rw [fgeq]; exact dvd_mul_left g f
  have h₁ : Monic (minpoly ℚ M.val) := monic (isIntegral M.val)
  have gmon : Monic g := by
    rw [fgeq] at h₁; exact Monic.of_mul_monic_left fmon h₁
  have h₃ : (minpoly ℚ M.val).natDegree = f.natDegree + g.natDegree := by
    rw [fgeq]
    apply natDegree_mul
    · exact Monic.ne_zero fmon
    · exact Monic.ne_zero gmon
  have h₄ : (minpoly ℚ M.val).natDegree ∈ ({1, 2} : Finset ℕ) := by
    have h₅ := minpoly_deg_le_two M
    interval_cases hdeg : (minpoly ℚ M.val).natDegree
    · contrapose! hdeg
      exact ne_of_gt (natDegree_pos (isIntegral M.val))
    · decide
    · decide
  rw [mem_insert, mem_singleton] at h₄
  rcases h₄ with (h4 | h4)
  · have gdeg : g.natDegree = 0 := by
      have hactor_deg : 1 ≤ f.natDegree := by
        simp only [mem_insert, mem_singleton] at h₀
        rcases h₀ with (h | h | h | h | h) <;> rw [h]
        · have h1 : (Φ 1).natDegree = 1 := by
            rw [cyclotomic_one]; exact natDegree_X_sub_C 1
          rw [h1]
        · have h1 : (Φ 2).natDegree = 1 := by
            rw [cyclotomic_two]; exact natDegree_X_add_C 1
          rw [h1]
        · have h1 : (Φ 3).natDegree = 2 := by
            rw [cyclotomic_three]; compute_degree; decide
          linarith [h1]
        · have h1 : (Φ 4).natDegree = 2 := by
            rw [cyclotomic_four]; exact natDegree_X_pow_add_C
          linarith [h1]
        · have h1 : (Φ 6).natDegree = 2 := by
            rw [cyclotomic_six]; compute_degree; decide
          linarith [h1]
      linarith
    have geq : g = 1 := eq_one_of_monic_natDegree_zero gmon gdeg
    have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at fgeq; exact fgeq
    rw [mem_insert]; left; exact geq
  · sorry


lemma minpoly_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6, (Φ 1)*(Φ 2)} : Finset ℚ[X]) := by
  obtain ⟨f, fmon, firr, fdvd⟩ := exist_normalizefactor M
  have h₀ := normalizedfactor_class M h h' f fmon firr fdvd
  rcases fdvd with ⟨g, hg⟩
  have h₁ : Monic (minpoly ℚ M.val) := monic (isIntegral M.val)
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
      exact ne_of_gt (natDegree_pos (isIntegral M.val))
    · decide
    · decide
  rw [mem_insert, mem_singleton] at h₄
  rcases h₄ with (h4 | h4)
  · have gdeg : g.natDegree = 0 := by
      have hactor_deg : 1 ≤ f.natDegree := by
        simp only [mem_insert, mem_singleton] at h₀
        rcases h₀ with (h | h | h | h | h) <;> rw [h]
        · have h1 : (Φ 1).natDegree = 1 := by
            rw [cyclotomic_one]; exact natDegree_X_sub_C 1
          rw [h1]
        · have h1 : (Φ 2).natDegree = 1 := by
            rw [cyclotomic_two]; exact natDegree_X_add_C 1
          rw [h1]
        · have h1 : (Φ 3).natDegree = 2 := by
            rw [cyclotomic_three]; compute_degree; decide
          linarith [h1]
        · have h1 : (Φ 4).natDegree = 2 := by
            rw [cyclotomic_four]; exact natDegree_X_pow_add_C
          linarith [h1]
        · have h1 : (Φ 6).natDegree = 2 := by
            rw [cyclotomic_six]; compute_degree; decide
          linarith [h1]
      linarith
    have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
    have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; exact hg
    simp only [← hf, mem_insert, mem_singleton] at h₀
    rcases h₀ with (h | h | h | h | h) <;> simp [h]
  · simp only [mem_insert, mem_singleton] at h₀
    rcases h₀ with (h1 | h1 | h | h | h)
    · have fdeg : f.natDegree = 1 := by rw [h1, cyclotomic_one]; compute_degree; decide
      have gdeg : g.natDegree = 1 := by rw [h4, fdeg] at h₃; linarith
      simp only [mem_insert, mem_singleton]; right; right; right; right; right
      rw [hg, h1]
      have girr : Irreducible g := by
        rw [← degree_eq_iff_natDegree_eq_of_pos (by decide), cast_one] at gdeg
        exact irreducible_of_degree_eq_one  gdeg
      obtain h5 := g_class M h h' f g fmon girr hg
      simp only [mem_insert, mem_singleton] at h5
      rcases h5 with (h6 | h6 | h6 | h6 | h6)
      · rw [h6, ← h1] at hg
        have h₅ : Squarefree (minpoly ℚ M.val) := minpoly_squarefree M h h'
        rw [squarefree_iff_no_irreducibles (ne_zero_of_finite ℚ M.val)] at h₅
        specialize h₅ f firr; rw [hg] at h₅; contrapose h₅; exact dvd_refl (f * f)
      · rw [h6, cyclotomic_one, cyclotomic_two]
      · rw [h6] at gdeg
        have : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_three, this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_four, this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_six, this] at gdeg; contradiction
    · have fdeg : f.natDegree = 1 := by rw [h1, cyclotomic_two]; compute_degree; decide
      have gdeg : g.natDegree = 1 := by rw [h4, fdeg] at h₃; linarith
      simp only [mem_insert, mem_singleton]; right; right; right; right; right
      rw [hg, h1]
      have girr : Irreducible g := by
        rw [← degree_eq_iff_natDegree_eq_of_pos (by decide), cast_one] at gdeg
        exact irreducible_of_degree_eq_one  gdeg
      obtain h5 := g_class M h h' f g fmon girr hg
      simp only [mem_insert, mem_singleton] at h5
      rcases h5 with (h6 | h6 | h6 | h6 | h6)
      · rw [h6, mul_comm]
      · rw [h6, ← h1] at hg
        have h₅ : Squarefree (minpoly ℚ M.val) := minpoly_squarefree M h h'
        rw [squarefree_iff_no_irreducibles (ne_zero_of_finite ℚ M.val)] at h₅
        specialize h₅ f firr; rw [hg] at h₅; contrapose h₅; exact dvd_refl (f * f)
      · rw [h6] at gdeg
        have : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_three, this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_four, this] at gdeg; contradiction
      · rw [h6] at gdeg
        have : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_six, this] at gdeg; contradiction
    · have fdeg : f.natDegree = 2 := by rw [h, cyclotomic_three]; compute_degree; decide
      have gdeg : g.natDegree = 0 := by rw [h4, fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; exact hg
      rw [h] at hf
      simp only [mem_insert, mem_singleton]; right; right; left; exact hf
    · have fdeg : f.natDegree = 2 := by rw [h, cyclotomic_four]; compute_degree; decide
      have gdeg : g.natDegree = 0 := by rw [h4, fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; exact hg
      rw [h] at hf
      simp only [mem_insert, mem_singleton]; right; right; right; left; exact hf
    · have fdeg : f.natDegree = 2 := by rw [h, cyclotomic_six]; compute_degree; decide
      have gdeg : g.natDegree = 0 := by rw [h4, fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero h₂ gdeg
      have hf : minpoly ℚ M.val = f := by rw [geq, mul_one] at hg; exact hg
      rw [h] at hf
      simp only [mem_insert, mem_singleton]; right; right; right; right; left; exact hf

lemma minpoly_cyc_order (h' : n = orderOf M.val)
    (h₀ : minpoly ℚ M.val ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6, (Φ 1) * (Φ 2)} : Finset ℚ[X])) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  simp at h₀
  rcases h₀ with (h0 | h0 | h0 | h0 | h0 | h0)
  · rw [mem_insert]; left; rw [h', orderOf_eq_one_iff, Units.val_eq_one]
    have h_eval := aeval ℚ M.val
    simp only [h0, aeval_X, map_sub, aeval_one, sub_eq_zero] at h_eval
    exact (GeneralLinearGroup.ext_iff M 1).mpr fun i => congrFun (congrFun h_eval i)
  · simp only [mem_insert, mem_singleton]; right; left; rw [h']
    have h_eval := aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_M : M.val= -1 := by
        simpa only [map_add, aeval_X, aeval_one, add_eq_zero_iff_eq_neg] using h_eval
      simp only [h_M, even_two, Even.neg_pow, one_pow]
    · intro m hm mpos
      interval_cases m
      have h_M : M.val= -1 := by
        simpa only [map_add, aeval_X, aeval_one, add_eq_zero_iff_eq_neg] using h_eval
      rw [h_M, pow_one]; decide
  · simp only [mem_insert, mem_singleton]; right; right; left; rw [h']
    have h_eval := aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_poly : (X^3 - 1 : ℚ[X]) = (X - 1) * (X^2 + X + 1) := by ring
      have h_aeval_3 : aeval M.val (X^3 - 1 : ℚ[X]) = 0 := by
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
  · simp only [mem_insert, mem_singleton]; right; right; right; left; rw [h']
    have h_eval := aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_poly : (X^4 - 1 : ℚ[X]) = (X^2 + 1) * (X^2 - 1) := by ring
      have h_aeval_4 : aeval M.val (X^4 - 1 : ℚ[X]) = 0 := by
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
  · simp only [mem_insert, mem_singleton]; right; right; right; right; rw [h']
    have h_eval := aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_poly : (X^6 - 1 : ℚ[X]) = (X^2 - X + 1) * (X^4 + X^3 - X - 1) := by ring
      have h_aeval_6 : aeval M.val (X^6- 1 : ℚ[X]) = 0 := by
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
  · simp only [mem_insert, mem_singleton]; right; left; rw [h']
    have h_eval := aeval ℚ M.val
    rw [h0] at h_eval
    rw [orderOf_eq_iff (by decide)]
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
      have M_eval : aeval M.val (X - 1 : ℚ[X]) = 0 := by simp [hM]
      have h_div : minpoly ℚ M.val ∣ (X - 1 : ℚ[X]) := dvd ℚ M.val M_eval
      rw [h0] at h_div
      have h_deg := degree_le_of_dvd h_div (X_sub_C_ne_zero 1)
      have h₁ : (X - 1 : ℚ[X]).degree = 1 := degree_X_sub_C 1
      have h₂ : (X + 1 : ℚ[X]).degree = 1 := degree_X_add_C 1
      rw [degree_mul, h₁, h₂] at h_deg; norm_num at h_deg

lemma finorder_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases minpoly_class M h h' with h₀
  exact minpoly_cyc_order M h' h₀

noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℚ) (h : IsUnit A.det) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' A h

theorem finite_order_matrix (h : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ∃ (M : GL (Fin 2) ℚ), orderOf M.val = n := by
  fin_cases h
  · use 1; rw [Units.val_one, orderOf_one]
  · use toGL P1 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos; interval_cases m; rw [pow_one]; decide
  · use toGL P2 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_three]
    · intro m mlt mpos; interval_cases m
      · rw [pow_one]; decide
      · simp [pow_two]; decide
  · use toGL P3 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · rw [pow_mul (!![0, 1; -1, 0]) 2 2]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos; interval_cases m
      · rw [pow_one]; decide
      · simp [pow_two]; decide
      · simp [pow_three]; decide
  · use toGL P4 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · rw [pow_mul (!![0, -1; 1, 1]) 2 3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two, pow_three]
    · intro m mlt mpos; interval_cases m
      · rw [pow_one]; decide
      · simp [pow_two]; decide
      · simp [pow_three]; decide
      · rw [pow_mul (!![0, -1; 1, 1]) 2 2]
        simp [pow_two]; decide
      · rw [pow_add (!![0, -1; 1, 1]) 2 3]
        simp [pow_two, pow_three]; decide

#min_imports
