import Mathlib
import Aesop
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open BigOperators Real Nat Topology Rat

lemma aux (x : ℂ) (m n : ℕ) (hmn : m < n) : x ^ m / x ^ n = 1 / x ^ (n - m) := by
  by_cases h : x = 0
  simp [h, zero_pow (n := n) (by omega), zero_pow (n := n - m) (by omega)]
  rw [div_eq_div_iff (by simp [h]) (by simp [h]), ← pow_add, one_mul]
  congr
  omega

theorem amc12a_2019_p21 (x : ℂ) (h₀ : x = (1 + Complex.I) / Real.sqrt 2) :
  ((∑ k : ℤ in Finset.Icc 1 12, x ^ k ^ 2) * (∑ k : ℤ in Finset.Icc 1 12, 1 / x ^ k ^ 2)) = 36 := by
  -- h₁将f求和展开
  have h₁ : ∑ k :ℤ in Finset.Icc 1 12, x ^ k ^ 2 = x^144 + x^121 + x^100 + x^81 + x^64 + x^49 + x^36 + x^25 + x^16 + x^9 + x^4 + x := by
    have l₁ : ∑ k : ℤ in Finset.Icc 1 12, x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 11,  x ^ k ^ 2 + x^144:= by
      have m₀: 1 ≤ 12:= by
        norm_num
      have m₀': ∑ k : ℕ in Finset.Icc 1 (11+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 11, x ^ k ^ 2 + x^12^2:= by
        apply Finset.sum_Icc_succ_top m₀
      exact m₀'
    have l₂ : ∑ k : ℤ in Finset.Icc 1 11,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 10,  x ^ k ^ 2 + x^121 := by
      have m₁: 1 ≤ 11:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (10+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 10, x ^ k ^ 2 + x^11^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₃ : ∑ k : ℤ in Finset.Icc 1 10,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 9,  x ^ k ^ 2 + x^100 := by
      have m₁: 1 ≤ 10:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (9+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 9, x ^ k ^ 2 + x^10^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₄ : ∑ k : ℤ in Finset.Icc 1 9,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 8,  x ^ k ^ 2 + x^81 := by
      have m₁: 1 ≤ 9:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (8+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 8, x ^ k ^ 2 + x^9^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₅ : ∑ k : ℤ in Finset.Icc 1 8,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 7,  x ^ k ^ 2 + x^64 := by
      have m₁: 1 ≤ 8:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (7+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 7, x ^ k ^ 2 + x^8^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₆ : ∑ k : ℤ in Finset.Icc 1 7,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 6,  x ^ k ^ 2 + x^49:= by
      have m₁: 1 ≤ 7:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (6+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 6, x ^ k ^ 2 + x^7^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₇ : ∑ k : ℤ in Finset.Icc 1 6,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 5,  x ^ k ^ 2 + x^36:= by
      have m₁: 1 ≤ 6:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (5+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 5, x ^ k ^ 2 + x^6^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₈ : ∑ k : ℤ in Finset.Icc 1 5,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 4,  x ^ k ^ 2 + x^25:= by
      have m₁: 1 ≤ 5:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (4+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 4, x ^ k ^ 2 + x^5^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₉ : ∑ k : ℤ in Finset.Icc 1 4,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 3,  x ^ k ^ 2 + x^16:= by
      have m₁: 1 ≤ 4:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (3+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 3, x ^ k ^ 2 + x^4^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₁' : ∑ k : ℤ in Finset.Icc 1 3,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 2,  x ^ k ^ 2 + x^9:= by
      have m₁: 1 ≤ 3:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (2+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 2, x ^ k ^ 2 + x^3^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₂' : ∑ k : ℤ in Finset.Icc 1 2,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 1,  x ^ k ^ 2 + x^4:= by
      have m₁: 1 ≤ 2:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (1+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 1, x ^ k ^ 2 + x^2^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₃' : ∑ k : ℤ in Finset.Icc 1 1,  x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 0,  x ^ k ^ 2 + x^1:= by
      have m₁: 1 ≤ 1:= by
        norm_num
      have m₁': ∑ k : ℕ in Finset.Icc 1 (0+1), x ^ k ^ 2 = ∑ k : ℤ in Finset.Icc 1 0, x ^ k ^ 2 + x^1^2:= by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₄' : ∑ k : ℤ in Finset.Icc 1 0,  x ^ k ^ 2 = 0 := by
      exact rfl
    rw[l₁, l₂, l₃, l₄, l₅, l₆, l₇, l₈, l₉, l₁', l₂',l₃',l₄']
    ring
  -- h₂将g求和展开
  have h₂ : ∑ k : ℤ in Finset.Icc 1 12, 1 / x ^ k ^ 2 = 1/x + 1/x^4 + 1/x^9 + 1/x^16 + 1/x^25 + 1/x^36 + 1/x^49 + 1/x^64 + 1/x^81 + 1/x^100 + 1/x^121 + 1/x^144 := by
    have l₁: ∑ k : ℤ in Finset.Icc 1 12, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 11, 1 / x ^ k ^ 2 + 1/x^144 := by
      have m₁ : 1 ≤ 12 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (11+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 11, 1 / x ^ k ^ 2 + 1/x^12^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₂: ∑ k : ℤ in Finset.Icc 1 11, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 10, 1 / x ^ k ^ 2 + 1/x^121 := by
      have m₁ : 1 ≤ 11 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (10+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 10, 1 / x ^ k ^ 2 + 1/x^11^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₃: ∑ k : ℤ in Finset.Icc 1 10, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 9, 1 / x ^ k ^ 2 + 1/x^100 := by
      have m₁ : 1 ≤ 10 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (9+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 9, 1 / x ^ k ^ 2 + 1/x^10^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₄: ∑ k : ℤ in Finset.Icc 1 9, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 8, 1 / x ^ k ^ 2 + 1/x^81 := by
      have m₁ : 1 ≤ 9 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (8+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 8, 1 / x ^ k ^ 2 + 1/x^9^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₅: ∑ k : ℤ in Finset.Icc 1 8, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 7, 1 / x ^ k ^ 2 + 1/x^64 := by
      have m₁ : 1 ≤ 8 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (7+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 7, 1 / x ^ k ^ 2 + 1/x^8^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₆: ∑ k : ℤ in Finset.Icc 1 7, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 6, 1 / x ^ k ^ 2 + 1/x^49 := by
      have m₁ : 1 ≤ 7 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (6+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 6, 1 / x ^ k ^ 2 + 1/x^7^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₇: ∑ k : ℤ in Finset.Icc 1 6, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 5, 1 / x ^ k ^ 2 + 1/x^36 := by
      have m₁ : 1 ≤ 6 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (5+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 5, 1 / x ^ k ^ 2 + 1/x^6^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₈: ∑ k : ℤ in Finset.Icc 1 5, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 4, 1 / x ^ k ^ 2 + 1/x^25 := by
      have m₁ : 1 ≤ 5 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (4+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 4, 1 / x ^ k ^ 2 + 1/x^5^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₉: ∑ k : ℤ in Finset.Icc 1 4, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 3, 1 / x ^ k ^ 2 + 1/x^16 := by
      have m₁ : 1 ≤ 4 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (3+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 3, 1 / x ^ k ^ 2 + 1/x^4^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₁': ∑ k : ℤ in Finset.Icc 1 3, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 2, 1 / x ^ k ^ 2 + 1/x^9 := by
      have m₁ : 1 ≤ 3 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (2+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 2, 1 / x ^ k ^ 2 + 1/x^3^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₂': ∑ k : ℤ in Finset.Icc 1 2, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 1, 1 / x ^ k ^ 2 + 1/x^4 := by
      have m₁ : 1 ≤ 2 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (1+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 1, 1 / x ^ k ^ 2 + 1/x^2^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₃': ∑ k : ℤ in Finset.Icc 1 1, 1 / x ^ k ^ 2 = ∑ k : ℤ  in Finset.Icc 1 0, 1 / x ^ k ^ 2 + 1/x^1:= by
      have m₁ : 1 ≤ 1 := by
        norm_num
      have m₁': ∑ k : ℕ  in Finset.Icc 1 (0+1), 1 / x ^ k ^ 2 = ∑ k : ℕ in Finset.Icc 1 0, 1 / x ^ k ^ 2 + 1/x^1^2 := by
        apply Finset.sum_Icc_succ_top m₁
      exact m₁'
    have l₄': ∑ k : ℤ  in Finset.Icc 1 0, 1 / x ^ k ^ 2 = 0 := by
      exact rfl
    rw[l₁, l₂, l₃, l₄, l₅, l₆, l₇, l₈, l₉, l₁', l₂',l₃',l₄']
    ring
  rw[h₁]
  rw[h₂]
  have h₃ : x^144 + x^121 + x^100 + x^81 + x^64 + x^49 + x^36 + x^25 + x^16 + x^9 + x^4 + x = (x^4 + 1)*(x^140-x^136+x^132-x^128+x^124-x^120+x^117+x^116-x^113-x^112+x^109+x^108-x^105-x^104+x^101+x^100-x^97+x^93-x^89+x^85-x^81+2*x^77-2*x^73+2*x^69-2*x^65+2*x^61+x^60-2*x^57-x^56+2*x^53+x^52-2*x^49-x^48+3*x^45+x^44-3*x^41-x^40+3*x^37+x^36-3*x^33+3*x^29-3*x^25+4*x^21-4*x^17+4*x^13+x^12-4*x^9-x^8+5*x^5+x^4-5*x) + 6*x := by
   ring
  have h₄ : 1/x + 1/x^4 + 1/x^9 + 1/x^16 + 1/x^25 + 1/x^36 + 1/x^49 + 1/x^64 + 1/x^81 + 1/x^100 + 1/x^121 + 1/x^144 =(x^143 + x^140 + x^135 + x^128 + x^119 + x^108 + x^95 + x^80 + x^63 + x^44 + x^23 + 1)/x^144 := by
    simp only [_root_.add_div]
    simp [aux]
  have h₅ : x^143 + x^140 + x^135 + x^128 + x^119 + x^108 + x^95 + x^80 + x^63 + x^44 + x^23 + 1 = (x^4 + 1)*(x^139 + x^136 - x^135 - x^132 + 2*x^131 + x^128 - 2*x^127 + 2*x^123 - 2*x^119 + 3*x^115 - 3*x^111 + 3*x^107 + x^104 - 3*x^103 - x^100 + 3*x^99 + x^96 - 3*x^95 - x^92 + 4*x^91 + x^88 - 4*x^87 - x^84 + 4*x^83 + x^80 - 4*x^79 + 4*x^75 - 4*x^71 + 4*x^67 - 4*x^63 + 5*x^59 - 5*x^55 + 5*x^51 - 5*x^47 + 5*x^43 + x^40 - 5*x^39 - x^36 + 5*x^35 + x^32 - 5*x^31 - x^28 + 5*x^27 + x^24 - 5*x^23 - x^20 + 6*x^19 + x^16 - 6*x^15 - x^12 + 6*x^11 + x^8 - 6*x^7 - x^4 + 6*x^3 + 1)-6*x^3 := by
    ring
  have h₆ : x^144 = (x^140 - x^136 + x^132 - x^128 + x^124 - x^120 + x^116 - x^112 + x^108 - x^104 + x^100 - x^96 + x^92 - x^88 + x^84 - x^80 + x^76 - x^72 + x^68 - x^64 + x^60 - x^56 + x^52 - x^48 + x^44 - x^40 + x^36 - x^32 + x^28 - x^24 + x^20 - x^16 + x^12 - x^8 + x^4 - 1)*(x^4+1) + 1 := by
    ring
  have h₇ : x^4 + 1 = 0 := by
    rw[h₀]
    have t₂ : ((1 + Complex.I) / Real.sqrt 2) ^ 4 = (1 + Complex.I)^4/ (Real.sqrt 2)^4 := by
      exact div_pow (1 + Complex.I) (Real.sqrt 2) 4
    have t₃: (1 + Complex.I)^2 = 1 + 2*Complex.I + (Complex.I)^2 := by
      ring
    rw[t₂]
    have t₄: (1 + Complex.I)^4 = (1 + Complex.I)^2 * (1 + Complex.I)^2:= by
      ring
    rw[t₄]
    rw[t₃]
    rw[Complex.I_sq]
    ring_nf
    rw[Complex.I_sq]

    have t₆: (Real.sqrt 2 : ℂ)⁻¹^4 * 4= 1 := by
      have t₇ : (Real.sqrt 2 : ℂ)⁻¹^4 =((Real.sqrt 2 : ℂ)^4)⁻¹:= by
        ring
      rw[t₇]
      have t₈ : (Real.sqrt 2 : ℂ)^4 = 4 := by
        have t₉ : (Real.sqrt 2 : ℂ)^2 = Real.sqrt 2^2 := by
          rw[pow_two]
        have l₁ : (Real.sqrt 2 : ℂ)^4 = (Real.sqrt 2 : ℂ)^2 * (Real.sqrt 2 : ℂ)^2 := by
          ring
        rw[l₁]
        rw[t₉]
        have l₂ : (Real.sqrt 2:ℂ)^2 = 2 := by
          simp [← Complex.ofReal_pow]
        rw[l₂]
        ring
      rw[t₈]
      ring
    rw[mul_assoc, t₆]
    ring
  have h₈ : -(6 * x * (6 * x ^ 3)) = -36*(x^4 + 1) + 36 := by
    ring
  have h₃' : (x^4 + 1)*(x^140-x^136+x^132-x^128+x^124-x^120+x^117+x^116-x^113-x^112+x^109+x^108-x^105-x^104+x^101+x^100-x^97+x^93-x^89+x^85-x^81+2*x^77-2*x^73+2*x^69-2*x^65+2*x^61+x^60-2*x^57-x^56+2*x^53+x^52-2*x^49-x^48+3*x^45+x^44-3*x^41-x^40+3*x^37+x^36-3*x^33+3*x^29-3*x^25+4*x^21-4*x^17+4*x^13+x^12-4*x^9-x^8+5*x^5+x^4-5*x) + 6*x = 6*x := by
    rw[h₇]
    norm_num
  have h₅' : (x^4 + 1)*(x^139 + x^136 - x^135 - x^132 + 2*x^131 + x^128 - 2*x^127 + 2*x^123 - 2*x^119 + 3*x^115 - 3*x^111 + 3*x^107 + x^104 - 3*x^103 - x^100 + 3*x^99 + x^96 - 3*x^95 - x^92 + 4*x^91 + x^88 - 4*x^87 - x^84 + 4*x^83 + x^80 - 4*x^79 + 4*x^75 - 4*x^71 + 4*x^67 - 4*x^63 + 5*x^59 - 5*x^55 + 5*x^51 - 5*x^47 + 5*x^43 + x^40 - 5*x^39 - x^36 + 5*x^35 + x^32 - 5*x^31 - x^28 + 5*x^27 + x^24 - 5*x^23 - x^20 + 6*x^19 + x^16 - 6*x^15 - x^12 + 6*x^11 + x^8 - 6*x^7 - x^4 + 6*x^3 + 1)-6*x^3 = -6*x^3 := by
    rw[h₇]
    norm_num
  have h₆' : (x^140 - x^136 + x^132 - x^128 + x^124 - x^120 + x^116 - x^112 + x^108 - x^104 + x^100 - x^96 + x^92 - x^88 + x^84 - x^80 + x^76 - x^72 + x^68 - x^64 + x^60 - x^56 + x^52 - x^48 + x^44 - x^40 + x^36 - x^32 + x^28 - x^24 + x^20 - x^16 + x^12 - x^8 + x^4 - 1)*(x^4+1) + 1 = 1 := by
    rw[h₇]
    norm_num
  rw[h₃]
  rw[h₄]
  rw[h₅]
  rw[h₆]
  rw[h₃']
  rw[h₅']
  rw[h₆']
  simp
  rw[h₈]
  rw[h₇]
  norm_num
