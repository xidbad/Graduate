import Mathlib.LinearAlgebra.Matrix.CharPoly.Minpoly
import Mathlib.FieldTheory.Minpoly.Basic


notation "E"  => !![1, 0; 0, 1]    -- 位数 1, det = 1,  tr = 2,  t^2 - 2t + 1
notation "-E" => !![-1, 0; 0, -1]  -- 位数 2, det = 1,  tr = -2, t^2 + 2t + 1
notation "P1" => !![1, 0; 0, -1]   -- 位数 2, det = -1, tr = 0,  t^2 - 1
notation "P2" => !![0, -1; 1, -1]  -- 位数 3, det = 1,  tr = -1, t^2 + t + 1
notation "P3" => !![0, 1; -1, 0]   -- 位数 4, det = 1,  tr = 0,  t^2 + 1
notation "P4" => !![0, -1; 1, 1]   -- 位数 6, det = 1,  tr = 1,  t^2 - t + 1

notation "t" => (Polynomial.X : Polynomial ℚ)

open Matrix Polynomial
open Function minpoly Polynomial Set


lemma det_one (M : Matrix (Fin 2) (Fin 2) ℚ) (h : ∃ n ≥ 1, M^n = 1) :
    (det M = 1) ∨ (det M = -1) := by
  rcases h with ⟨n, nge, finiteorder⟩
  have h₁ : det (M^n) = 1 := by simp [finiteorder]
  rw [det_pow, pow_eq_one_iff_of_ne_zero] at h₁
  obtain one | ⟨neg, even⟩ := h₁
  · exact Or.inl one
  · exact Or.inr neg
  · linarith

lemma charpoly_two_by (M : Matrix (Fin 2) (Fin 2) ℚ) :
    M.charpoly = t^2 - (C M.trace)*t + (C M.det) := by -- exact charpoly_fin_two ℚ
  have trace : M.trace = M 0 0 + M 1 1 := by simp [trace]
  rw [trace, charpoly]
  have t00 : M.charmatrix 0 0 = t - C (M 0 0) := by simp
  have t01 : M.charmatrix 0 1 =   - C (M 0 1) := by simp
  have t10 : M.charmatrix 1 0 =   - C (M 1 0) := by simp
  have t11 : M.charmatrix 1 1 = t - C (M 1 1) := by simp
  repeat rw [det_fin_two]
  rw [t00, t01, t10, t11]
  simp
  ring

lemma trace_classification_one (M : Matrix (Fin 2) (Fin 2) ℚ)
          (h : ∃ n ≥ 1, M^n = 1) (h' : det M = 1) :
        (trace M = 2) ∨ (trace M = -2) ∨ (trace M = -1) ∨
        (trace M = 0) ∨ (trace M = 1) := by
  rcases h with ⟨n, nge, finiteorder⟩
  have charpolyM : M.charpoly = t^2 - (C (trace M))*t + (C (det M)) := charpoly_two_by M
  rw [h'] at charpolyM
  simp at charpolyM
  sorry

lemma trace_classification_neg (M : Matrix (Fin 2) (Fin 2) ℚ)
        (h : ∃ n ≥ 1, M^n = 1) (h' : det M = -1) :
        (trace M = 0) := by
  rcases h with ⟨n, nge, finiteorder⟩
  have charpolyM : M.charpoly = t^2 - (C (trace M))*t + (C (det M)) := charpoly_two_by M
  rw [h'] at charpolyM
  simp at charpolyM
  sorry

theorem charpoly_classification (M : Matrix (Fin 2) (Fin 2) ℚ) (h : ∃ n ≥ 1, M^n = 1) :
          (charpoly M = (t - 1)*(t - 1)) ∨
          (charpoly M = (t + 1)*(t + 1)) ∨
          (charpoly M = (t + 1)*(t - 1)) ∨
          (charpoly M = t^2 + t + 1) ∨
          (charpoly M = t^2 + 1) ∨
          (charpoly M = t^2 - t + 1) := by
  have det1orneg : (det M = 1) ∨ (det M = -1) := det_one M h
  have charpolyM : M.charpoly = t^2 - (C (trace M))*t + (C (det M)) := charpoly_two_by M
  cases det1orneg with
  | inl det1 =>
    have possible_traces : (trace M = 2) ∨ (trace M = -2) ∨ (trace M = -1) ∨ (trace M = 0) ∨ (trace M = 1) := trace_classification_one M h det1
    cases possible_traces with
    | inl trace2 =>
      left
      calc
        _ = t^2 - (C (trace M))*t + (C (det M)) := by rw [charpolyM]
        _ = t^2 - 2*t + 1 := by rw [trace2, det1]; norm_num; rfl
        _ = (t - 1)*(t - 1) := by ring
    | inr rest1 =>
      cases rest1 with
      | inl trace_neg2 =>
        right; left
        calc
          _ = t^2 - (C (trace M))*t + (C (det M)) := by rw [charpolyM]
          _ = t^2 + 2*t + 1 := by rw [trace_neg2, det1]; norm_num; rfl
          _ = (t + 1)*(t + 1) := by ring
      | inr rest2 =>
        cases rest2 with
        | inl trace_neg1 =>
          right; right; right; left
          calc
            _ = t^2 - (C (trace M))*t + (C (det M)) := by rw [charpolyM]
            _ = t^2 + t + 1 := by rw [trace_neg1, det1]; norm_num
            _ = t^2 + t + 1 := by ring
        | inr rest3 =>
          cases rest3 with
          | inl trace0 =>
            right; right; right; right; left
            calc
              _ = t^2 - (C (trace M))*t + (C (det M)) := by rw [charpolyM]
              _ = t^2 + 1 := by rw [trace0, det1]; norm_num
              _ = t^2 + 1 := by ring
          | inr trace1 =>
            right; right; right; right; right
            calc
              _ = t^2 - (C (trace M))*t + (C (det M)) := by rw [charpolyM]
              _ = t^2 - t + 1 := by rw [trace1, det1]; norm_num
              _ = t^2 - t + 1 := by ring
  | inr detneg1 =>
    have possible_traces_neg : (trace M = 0) := trace_classification_neg M h detneg1
    right; right; left
    calc
      _ = t^2 - (C (trace M))*t + (C (det M)) := by rw [charpolyM]
      _ = t^2 - 0*t - 1 := by rw [possible_traces_neg, detneg1]; norm_num; ring
      _ = (t + 1)*(t - 1) := by ring

lemma charpoly_classification_eq (M : Matrix (Fin 2) (Fin 2) ℚ)
    (h : ∃ n ≥ 1, M^n = 1) (α : ℚ) (h' : M = scalar _ α) :
    (charpoly M = (t - 1)*(t - 1)) ∨ (charpoly M = (t + 1)*(t + 1)) := by
  rcases h with ⟨n, ⟨hn, hm⟩⟩
  have h₁ : charpoly M = (t - C α)*(t - C α) := by
    simp [h', charpoly]; ring
  have h₂ : α ^ n = 1 := by
    rw [h'] at hm
    apply ext_iff.mpr at hm
    simp at hm
    rcases hm with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [← h1, diagonal_pow, diagonal_apply]
    simp
  have h₃ : α = 1 ∨ α = -1 := by
    rw [pow_eq_one_iff_of_ne_zero] at h₂
    rcases h₂ with (one | ⟨neg, even⟩)
    · exact Or.inl one
    · exact Or.inr neg
    · linarith
  rcases h₃ with one | neg
  · left; rw [one] at h₁; exact h₁
  · right; simp [neg] at h₁; assumption

lemma charpoly_classification_neq (M : Matrix (Fin 2) (Fin 2) ℚ)
      (h : ∃ n ≥ 1, M^n = 1) (h' : ∀ α : ℚ, M ≠ scalar _ α) :
      (charpoly M = t^2 - 1) ∨
      (charpoly M = t^2 + t + 1) ∨
      (charpoly M = t^2 + 1) ∨
      (charpoly M = t^2 - t + 1) := by
  obtain ⟨n, hn, hm⟩ := h
  have h₁ : minpoly ℚ M ∣ t^n - 1 := by
    apply minpoly.dvd_iff.mpr
    simp [hm]
  have h₂ : minpoly ℚ M ∣ charpoly M := minpoly_dvd_charpoly M
  have h₃ : (charpoly M).natDegree = 2 := by exact Matrix.charpoly_natDegree_eq_dim M
  have nonzerochar : M.charpoly ≠ 0 := by sorry
    -- apply Polynomial.ne_zero_of_natDegree_gt
    -- show 1 < M.charpoly.natDegree
    -- rw [auxchar]
    -- norm_num
  have h₄ : (minpoly ℚ M).natDegree ≤ (charpoly M).natDegree := by apply natDegree_le_of_dvd h₂ nonzerochar
  rw [h₃] at h₄
  sorry

lemma need_eq (a b : ℚ) (h : a ≠ 0) : t = (C a⁻¹) * ((C a)*t + (C b)) + (C (-b/a)) := by
    ring; simp
    rw [← Polynomial.C_mul]
    rw [inv_mul_cancel₀ h]
    simp

lemma charpoly_eq_minpoly (M : Matrix (Fin 2) (Fin 2) ℚ)
    (h : ∃ n ≥ 1, M^n = 1) (h' : ∀ α : ℚ, M ≠ scalar _ α) :
    M.charpoly = minpoly ℚ M :=  by
  have auxchar: M.charpoly.natDegree = 2 := by
    exact Matrix.charpoly_natDegree_eq_dim M
  have nonzerochar : M.charpoly ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt
    show 1 < M.charpoly.natDegree
    rw [auxchar]
    norm_num
  have monicchar : Monic M.charpoly := by exact Matrix.charpoly_monic M
  set p := minpoly ℚ M
  have minmonic : Monic p := by
    refine monic ?_
    exact Matrix.isIntegral M
  have aux0 : p ≠ 0 := by exact ne_zero_of_finite ℚ M
  have aux3 : p.natDegree ≥ 0 := by exact Nat.zero_le p.natDegree
  have aux1 : p ∣ M.charpoly := by
    apply Matrix.minpoly_dvd_charpoly
  have aux2 : p.natDegree ≥ 2 := by
    by_contra! H
    let α := p.coeff 1
    let β := p.coeff 0
    have eq_p : p = (C α)*t + (C β) := by
        refine eq_X_add_C_of_natDegree_le_one ?_
        apply Nat.le_of_lt_succ at H
        assumption
    have min_poly : aeval M p = 0 := by
      rw [← minpoly.dvd_iff]
    rw [eq_p] at min_poly
    have αnezero : α ≠ 0 := by
      by_contra! Hα
      rw [Hα] at min_poly
      simp at min_poly
      rw [Hα, min_poly] at eq_p
      simp at eq_p
      contradiction
    have : M = (Matrix.scalar _ (-β/α)) := by
      calc
      _ = aeval M t := by exact Eq.symm (aeval_X M)
      _ = aeval M ((C α⁻¹)*((C α)*t + (C β)) + (C (-β/α))) := by
        rw [← need_eq α β αnezero]
      _ = aeval M ((C α⁻¹)*((C α)*t + (C β))) + aeval M (C (-β/α)) := by rw [aeval_add]
      _ = (aeval M (C α⁻¹)) * (aeval M ((C α)*t + (C β))) + aeval M (C (-β/α)) :=
        by rw [← aeval_mul]
      _ = (aeval M (C α⁻¹))*0 + aeval M (C (-β/α)) := by rw [min_poly]
      _ = aeval M (C (-β/α)) := by simp
      _ = (Matrix.scalar _ (-β/α)) := by apply aeval_C
    specialize h' (-β/α)
    contradiction
  have ass : Associated p M.charpoly := by
    refine associated_of_dvd_of_natDegree_le aux1 nonzerochar ?_
    rw [auxchar]
    linarith
  rcases ass with ⟨s, Hs⟩
  rw [← Hs]
  -- sorry
  apply ext_iff.mp at Hs
  specialize Hs M.charpoly.natDegree
  have degs: (s:ℚ[X]).natDegree = 0 := by exact natDegree_coe_units s
  have degp : p.natDegree = 2 := by
    apply le_antisymm
    · rw [← auxchar]
      apply natDegree_le_of_dvd aux1 nonzerochar
    ·  assumption
  rw [auxchar] at Hs
  have leading : (p*↑s).coeff (p.natDegree + (↑s : ℚ[X]).natDegree) = (p.coeff p.natDegree)*((↑s:ℚ[X]).coeff (↑s:ℚ[X]).natDegree) := by
    apply Polynomial.natDegree_add_coeff_mul
  rw [degp, degs] at leading
  simp at leading
  rw [Hs] at leading
  have monicp : p.coeff 2 = 1 := by
    rw [← degp];apply minmonic
  have monicchar : M.charpoly.coeff M.charpoly.natDegree = 1 := by exact monicchar
  rw [auxchar] at monicchar
  rw [monicchar,monicp] at leading
  simp at leading
  have sthis : (↑s:ℚ[X]) = (C ((↑s:ℚ[X]).coeff 0)) := by
    exact eq_C_of_natDegree_eq_zero degs
  rw [← leading] at sthis
  rw [sthis]
  simp

lemma minpoly_eq (M : Matrix (Fin 2) (Fin 2) ℚ) (h : ∃ n ≥ 1, M^n = 1)
    (α : ℚ) (h' : M = scalar _ α) :
    (minpoly ℚ M = t - 1) ∨ (minpoly ℚ M = t + 1) := by
  rcases h with ⟨n, ⟨hn, hm⟩⟩
  have h₁ : minpoly ℚ M = (t - C α) := by
    rw [h']
    simp [minpoly]
    sorry
  have h₂ : α ^ n = 1 := by
    rw [h'] at hm
    apply ext_iff.mpr at hm
    simp at hm
    rcases hm with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [← h1, diagonal_pow, diagonal_apply]
    simp
  have h₃ : α = 1 ∨ α = -1 := by
    rw [pow_eq_one_iff_of_ne_zero] at h₂
    rcases h₂ with (one | ⟨neg, even⟩)
    · exact Or.inl one
    · exact Or.inr neg
    · linarith
  obtain (one | neg) := h₃
  · left; rw [one] at h₁; exact h₁
  · simp [neg] at h₁; exact Or.inr h₁

lemma minpoly_neq (M : Matrix (Fin 2) (Fin 2) ℚ)
    (h : ∃ n ≥ 1, M^n = 1) (h' : ∀ α : ℚ, M ≠ scalar _ α) :
    (minpoly ℚ M = t^2 - 1) ∨
    (minpoly ℚ M = t^2 + t + 1) ∨
    (minpoly ℚ M = t^2 + 1) ∨
    (minpoly ℚ M = t^2 - t + 1) := by
  rw [← charpoly_eq_minpoly M h h']
  exact charpoly_classification_neq M h h'

lemma charpoly_dvd (M : Matrix (Fin 2) (Fin 2) ℚ) (n : ℕ) (hn : n ≥ 1)
    (h : M^n = 1) (h' : ∀ α : ℚ, M ≠ scalar _ α) :
    charpoly M ∣ t^n - 1 := by
  have h₁ : charpoly M = minpoly ℚ M := charpoly_eq_minpoly M ⟨n, hn, h⟩ h'
  rw [h₁]
  apply minpoly.dvd_iff.mpr
  simp [h]

-- 上の定理から考えられる固有多項式を調べる

theorem conjugate_classification (M : Matrix (Fin 2) (Fin 2) ℚ) (h : ∃ n ≥ 1, M^n = 1) :
        (∃ P : Matrix (Fin 2) (Fin 2) ℚ, P⁻¹*M*P = E) ∨
        (∃ P : Matrix (Fin 2) (Fin 2) ℚ, P⁻¹*M*P = -E) ∨
        (∃ P : Matrix (Fin 2) (Fin 2) ℚ, P⁻¹*M*P = P1) ∨
        (∃ P : Matrix (Fin 2) (Fin 2) ℚ, P⁻¹*M*P = P2) ∨
        (∃ P : Matrix (Fin 2) (Fin 2) ℚ, P⁻¹*M*P = P3) ∨
        (∃ P : Matrix (Fin 2) (Fin 2) ℚ, P⁻¹*M*P = P4) := by
  have det1orneg : (det M = 1) ∨ (det M = -1) := det_one M h
  rcases h with ⟨n, nge, finiteorder⟩
  · left; use 1
    simp
    sorry
