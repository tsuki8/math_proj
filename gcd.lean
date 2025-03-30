import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

-- theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n^2 + 4*n) (14 * n^2 + 3*n) = n := by
--   have h₁:((-2:ℤ))*(21*n + 4) + (3)*(14*n+3) = 1 := by
--     ring_nf
--   have h₂: Nat.gcd (21*n + 4) (14 * n + 3) = 1 := by
--     have l₁: 1 ∣  Nat.gcd (21*n + 4) (14 * n + 3) := by
--       exact Nat.one_dvd ((21 * n + 4).gcd (14 * n + 3))
--     have t₁: Nat.gcd (21*n + 4) (14 * n + 3)  ∣ (21*n + 4) := by
--       exact Nat.gcd_dvd_left (21 * n + 4) (14 * n + 3)
--     have t₁': (Nat.gcd (21*n + 4) (14 * n + 3) :ℤ)  ∣ ((21*n + 4) :ℤ):= by
--       exact Int.ofNat_dvd_left.mpr t₁
--     have t₂: Nat.gcd (21*n + 4) (14 * n + 3) ∣ (14 * n + 3) := by
--       exact Nat.gcd_dvd_right (21 * n + 4) (14 * n + 3)
--     have t₂': ( Nat.gcd (21*n + 4) (14 * n + 3):ℤ) ∣ ((14 * n + 3):ℤ) := by
--       exact Int.ofNat_dvd_left.mpr t₂
--     have t₃:  (Nat.gcd (21*n + 4) (14 * n + 3):ℤ) ∣ ((-2:ℤ)*(21*n + 4) + (3)*(14*n+3)) := by
--       refine (Int.dvd_add_right ?H).mpr ?_
--       · exact Dvd.dvd.mul_left t₁' (-2)
--       · exact Dvd.dvd.mul_left t₂' 3
--     have l₂: Nat.gcd (21*n + 4) (14 * n + 3) ∣ 1 := by
--       rw[h₁] at t₃
--       exact Int.ofNat_dvd.mp t₃
--     exact Eq.symm (Nat.dvd_antisymm l₁ l₂)
--   have h₃: 21 * n^2 + 4*n = n * (21*n + 4) := by
--     ring
--   have h₄: 14 * n^2 + 3*n = n * (14*n + 3) := by
--     ring
--   rw[h₃,h₄]
--   rw[gcd_mul_left]
--   rw[h₂]
--   ring


-- theorem imo_1959_p11 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (11 * n^2 + 4*n) (14 * n^2 + 3*n) = n := by
--   have h₁:((14/23:ℝ))*(11*n + 4) + ((-11/23):ℝ)*(14*n+3) = 1 := by
--     ring_nf
--   have h₂: Nat.gcd (11*n + 4) (14 * n + 3) = 1 := by
--     have l₁: 1 ∣  Nat.gcd (11*n + 4) (14 * n + 3) := by
--       exact Nat.one_dvd ((11 * n + 4).gcd (14 * n + 3))
--     have t₁: Nat.gcd (11*n + 4) (14 * n + 3)  ∣ (11*n + 4) := by
--       exact Nat.gcd_dvd_left (11 * n + 4) (14 * n + 3)
--     have t₁': (Nat.gcd (11*n + 4) (14 * n + 3) :ℤ)  ∣ ((11*n + 4) :ℤ):= by
--       sorry
--     have t₂: Nat.gcd (11*n + 4) (14 * n + 3) ∣ (14 * n + 3) := by
--       exact Nat.gcd_dvd_right (11 * n + 4) (14 * n + 3)
--     have t₂': ( Nat.gcd (11*n + 4) (14 * n + 3):ℤ) ∣ ((14 * n + 3):ℤ) := by
--       sorry
--     have t₃:  (Nat.gcd (11*n + 4) (14 * n + 3):ℤ) ∣ （((14/23:ℝ)*(11*n + 4) + ((-11/23):ℝ)*(14*n+3)) := by
--       sorry
--     have l₂: Nat.gcd (11*n + 4) (14 * n + 3) ∣ 1 := by
--       rw[h₁] at t₃
--       sorry
--     exact Eq.symm (Nat.dvd_antisymm l₁ l₂)
--   have h₃: 11 * n^2 + 4*n = n * (11*n + 4) := by
--     ring
--   have h₄: 14 * n^2 + 3*n = n * (14*n + 3) := by
--     ring
--   rw[h₃,h₄]
--   rw[gcd_mul_left]
--   rw[h₂]
--   ring



-- theorem aa : Nat.gcd 2 4 = 2 := by
--   ring

theorem mathd_numbertheory_169 : Nat.gcd 20! 200000 = 40000 := by
  exact rfl



lemma trys (x : ℕ) : Nat.gcd (11 * x*2 + 4 + 4) (14*x + 3) = (1) := by
  have h₁:((-2:ℤ))*(21*x + 4) + ((3:ℤ))*(14*x + 3) = 1 := by
    ring_nf
  have h₂: Nat.gcd (21*x + 4) (14*x + 3) = 1 := by
    have l₁: 1 ∣  Nat.gcd (21*x + 4) (14*x + 3) := by
      exact Nat.one_dvd ((21*x + 4).gcd (14*x + 3))
    have t₁: Nat.gcd (21*x + 4) (14*x + 3)  ∣ (21*x + 4) := by
      exact Nat.gcd_dvd_left (21*x + 4) (14*x + 3)
    have t₁': (Nat.gcd (21*x + 4) (14*x + 3) :ℤ)  ∣ ((21*x + 4) :ℤ):= by
      exact Int.ofNat_dvd_left.mpr t₁
    have t₂: Nat.gcd (21*x + 4) (14*x + 3) ∣ (14*x + 3) := by
      exact Nat.gcd_dvd_right (21*x + 4) (14*x + 3)
    have t₂': ( Nat.gcd (21*x + 4) (14*x + 3):ℤ) ∣ ((14*x + 3):ℤ) := by
      exact Int.ofNat_dvd_left.mpr t₂
    have t₃:  (Nat.gcd (21*x + 4) (14*x + 3):ℤ) ∣ ((-2:ℤ)*(21*x + 4) + ((3:ℤ))*(14*x + 3)) := by
      refine (Int.dvd_add_right ?H).mpr ?_
      · exact Dvd.dvd.mul_left t₁' (-2)
      · exact Dvd.dvd.mul_left t₂' (3)
    have l₂: Nat.gcd (21*x + 4) (14*x + 3) ∣ 1 := by
      rw[h₁] at t₃
      exact Int.ofNat_dvd.mp t₃
    exact Eq.symm (Nat.dvd_antisymm l₁ l₂)
  have h₃: (21*x + 4) = (1) * (21*x + 4) := by
    ring
  have h₄: (14*x + 3) = (1) * (14*x + 3) := by
    ring
  rw[h₃,h₄]
  rw[gcd_mul_left]
  rw[h₂]

lemma gcd_number: Nat.gcd 20! 2 = 2 := by
  exact rfl

lemma test(x :ℝ)(h: y=1): 3 * x ^ 2 + -1 * y + 5 = 0 := by
  simp
  rw[h]
  ring_nf


lemma gcd_number1: Nat.gcd 6432 132 = 12 := by
  exact rfl

lemma gcd_number2 : Nat.gcd 180 168 = 12 := by
  exact rfl

theorem mathd_numbertheory_188 : Nat.gcd 180 168 = 12 := by
  exact gcd_number2
