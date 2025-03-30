import Mathlib

open Nat
open Finset
open Polynomial

theorem IDT_65 (n : ℕ) (hn : Even n)(hp: Even n) : ∑ k in range (n + 1),
    (n.choose k) ^ 2 * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (n / 2) * (n.choose (n / 2)) := by
  obtain ⟨k, hk⟩ := hn
  have h1 : (Polynomial.X - (1 : Polynomial ℝ)) ^ n * (Polynomial.X + 1) ^ n =
      (Polynomial.X ^ 2 - 1) ^ (n) := by
    ring_nf
  have h2 : ∀ i ∈ Icc 0 n , ((Polynomial.X ^ 2 - (1 : Polynomial ℝ)) ^ n).coeff (2 * i) =
      (-1 : ℝ) ^ i * (n.choose i) := by
      intro i hi
      rw [sub_pow]
      simp only [one_pow, mul_one, finset_sum_coeff, coeff_mul_natCast, ← pow_mul]
      calc
      _ = ∑ x ∈ range (n + 1), (-1 : ℝ) ^ (x + n) * ↑(n.choose x) * (X ^ (2 * x)).coeff (2 * i) := by
        congr! 1 with x hx
        have : ((-1) ^ (x + n) : ℝ[X]) * X ^ (2 * x) = C ((-1) ^ (x + n) : ℝ) * X ^ (2 * x) := by
          simp only [map_pow, map_neg, map_one]
        rw [this, Polynomial.coeff_C_mul_X_pow]
        aesop
      _ = (-1 : ℝ) ^ i * n.choose i := by
        simp at hi
        simp only [coeff_X_pow, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, mul_ite, mul_one,
          mul_zero, sum_ite_eq, mem_range]
        simp [pow_add]
        rw [Even.neg_one_pow hp, mul_one]
        simp_all only [ite_eq_left_iff, not_lt, zero_eq_mul, pow_eq_zero_iff', neg_eq_zero,
          one_ne_zero, ne_eq, false_and, Nat.cast_eq_zero, false_or]
        intro _
        linarith
  have h2' : ((Polynomial.X - (1 : Polynomial ℝ)) ^ n * (Polynomial.X + 1) ^ n).coeff (n) =
      ∑ k in range (n + 1),
    (n.choose k) ^ 2 * (-1 : ℝ) ^ k := by
    let f : ℕ → ℕ → ℝ := fun x y => (((Polynomial.X - (1 : Polynomial ℝ)) ^ n).coeff x * ((Polynomial.X + (1 : Polynomial ℝ)) ^ n).coeff y)
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ f]
    simp [f]
    congr! 1 with k hk
    rw [Polynomial.coeff_X_add_one_pow]
    have t1: n.choose (n - k) = n.choose k := by
      refine choose_symm ?hk
      exact mem_range_succ_iff.mp hk
    rw[t1]
    rw[mul_comm]
    have t2: (n.choose k)*(n.choose k)= (n.choose k) ^ 2 := by
      exact Eq.symm (Nat.pow_two (n.choose k))
    have t3: ((Polynomial.X - (1 : Polynomial ℝ)) ^ n).coeff k = n.choose k * (-1:ℝ)^k:= by
      rw[sub_pow]
      simp only [one_pow, mul_one, finset_sum_coeff, coeff_mul_natCast, ← pow_mul]
      calc
      _ = ∑ x ∈ range (n + 1), (-1 : ℝ) ^ (x + n) * ↑(n.choose x) * (X ^ x).coeff k := by
        congr! 1 with x hx
        have m1 : ((-1) ^ (x + n) : ℝ[X]) * X ^ (x) = C ((-1) ^ (x + n) : ℝ) * X ^ (x) := by
          simp only [map_pow, map_neg, map_one]
        rw[m1]
        rw[Polynomial.coeff_C_mul_X_pow]
        aesop
      _ = (-1 : ℝ) ^ k * n.choose k := by
        simp only [coeff_X_pow, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, mul_ite, mul_one,
          mul_zero, sum_ite_eq, mem_range]
        simp [pow_add]
        rw [Even.neg_one_pow hp, mul_one]
        simp_all only [ite_eq_left_iff, not_lt, zero_eq_mul, pow_eq_zero_iff', neg_eq_zero,
          one_ne_zero, ne_eq, false_and, Nat.cast_eq_zero, false_or]
        exact fun a => (fun {n k} => choose_eq_zero_iff.mpr) a
      _ = n.choose k * (-1:ℝ)^k := by
        linarith
    rw[t3]
    rw[←mul_assoc]
    ring_nf
  have h3 : n / 2 ∈ Icc 0 n := by
    simp only [mem_Icc, zero_le, true_and]
    rw [hk, ← two_mul, mul_comm]
    omega
  specialize h2 (n / 2) h3
  rw [← h2', ← h2, h1, show 2 * (n / 2) = n by omega]

-- def p : Nat := by
--   have h0 : sorry := sorry
--   have h1 : sorry := sorry
--   have h2 : sorry := sorry
--   have h3 : sorry := sorry
--   have h4 : sorry := sorry
--   have h5 : h0 -> h1 -> h2 -> h3 -> h4 -> Nat := sorry
--   exact h5 h4 h3 h2 h1 h0


-- theorem IDT_65' (n : ℕ) (hn : Even n)(hp: Even n) : ∑ k in range (n + 1),
--     (n.choose k) ^ 2 * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (n / 2) * (n.choose (n / 2)) := by
--   obtain ⟨k, hk⟩ := hn
--   let t1 := (Polynomial.X - (1 : Polynomial ℝ)) ^ n * (Polynomial.X + 1) ^ n =
--       (Polynomial.X ^ 2 - 1) ^ (n)
--   let t2 := ∀ i ∈ Icc 0 n , ((Polynomial.X ^ 2 - (1 : Polynomial ℝ)) ^ n).coeff (2 * i) =
--       (-1 : ℝ) ^ i * (n.choose i)
--   let t3 := ((Polynomial.X - (1 : Polynomial ℝ)) ^ n * (Polynomial.X + 1) ^ n).coeff (n) =
--       ∑ k in range (n + 1),
--     (n.choose k) ^ 2 * (-1 : ℝ) ^ k
--   let t4 := n / 2 ∈ Icc 0 n
--   have h1 : t1 := by
--     sorry
--   have h2 : t2 := by
--       sorry
--   have h2' : t3 := by
--     sorry
--   have h3 : t4  := by
--     sorry
--   have h5 : t1 -> t2 -> t3 -> t4 := sorry
--   specialize h2 (n / 2) h3
--   rw [← h2', ← h2, h1, show 2 * (n / 2) = n by omega]

-- import Mathlib.Data.Polynomial.Div

-- open Polynomial

-- -- 定义两个多项式 p 和 q
-- def p := (Polynomial.X ^ 11 : Polynomial ℤ)
-- def q := (Polynomial.X ^ 6 - 3 * Polynomial.X ^ 5 + Polynomial.X ^ 4
--           - 3 * Polynomial.X ^ 3 - Polynomial.X ^ 2 - 3 * Polynomial.X + 1 : Polynomial ℤ)

-- -- 定义伪除函数
-- def pseudo_div (f g : Polynomial ℤ) : Polynomial ℤ × Polynomial ℤ :=
--   let d := leadingCoeff g
--   let n := degree g
--   -- 使用 Polynomial.pseudo_div_mod_by_monic (f.gcd g) 得到 (quotient, remainder)
--   let (quot, rem) := Polynomial.pseudoDivModByMonic f (monicPolynomial g)
--   -- 返回结果
--   (d^n * quot, rem)

-- #eval pseudo_div p q
