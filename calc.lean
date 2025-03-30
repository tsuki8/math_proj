import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

open Real BigOperators

theorem sum_inequality : ∑ k in Finset.Icc 2 10000, 1 / sqrt k < 198 := by
  -- 第一步：将求和与积分关联
  have h_sum_le_int : ∑ k in Finset.Icc 2 10000, 1 / sqrt k ≤ ∫ x in (1:ℝ)..10000, 1 / sqrt x := by
    refine' sum_le_integral_of_nonneg_antitone _ _ _
    · intro k hk
      exact inv_nonneg.mpr (sqrt_nonneg k)
    · intro a b ha hb hab
      exact inv_le_inv_of_le (sqrt_pos.mpr (by linarith)) (sqrt_le_sqrt hab)
    · intro k hk
      rw [mem_Icc] at hk
      have hk1 : 1 ≤ (k:ℝ) - 1 := by linarith [hk.1]
      rw [integral_inv_sqrt (k-1) k (by linarith [hk.1]) (by linarith [hk.1])]
      simp only [one_div]
      rw [← sub_pos]
      have : sqrt (↑k) - sqrt (↑k - 1) = 1 / (sqrt (↑k) + sqrt (↑k - 1)) := by
        field_simp; ring
      rw [this]
      apply div_pos
      · norm_num
      · apply add_pos <;> exact sqrt_pos.mpr (by linarith [hk.1])

  -- 第二步：计算定积分
  have h_int : ∫ x in (1:ℝ)..10000, 1 / sqrt x = 2 * (sqrt 10000 - sqrt 1) := by
    rw [integral_inv_sqrt 1 10000 zero_lt_one (by norm_num)]
    simp only [one_div]
    field_simp

  -- 第三步：计算数值上界
  have h_sqrt10000 : sqrt 10000 = 100 := by
    exact sqrt_eq_iff_sq_eq.mpr (by norm_num)

  have h_sqrt1 : sqrt 1 = 1 := sqrt_one

  rw [h_int, h_sqrt10000, h_sqrt1] at h_sum_le_int
  simp at h_sum_le_int  -- 现在h_sum_le_int : ∑ ... ≤ 198

  -- 第四步：证明严格不等式
  refine' lt_of_le_of_ne h_sum_le_int _
  intro h_eq
  -- 如果等于198，那么所有不等式估计都必须取等
  -- 但1/√k在区间(k-1,k)上是严格递减的，所以严格小于积分
  -- 因此不可能等于198
  have h_contra : ∑ k in Finset.Icc 2 10000, 1 / sqrt k < ∫ x in (1:ℝ)..10000, 1 / sqrt x := by
    apply sum_lt_integral_of_nonneg_antitone _ _ _
    · intro k hk
      exact inv_nonneg.mpr (sqrt_nonneg k)
    · intro a b ha hb hab
      exact inv_le_inv_of_le (sqrt_pos.mpr (by linarith)) (sqrt_le_sqrt hab)
    · intro k hk
      rw [mem_Icc] at hk
      have hk1 : 1 ≤ (k:ℝ) - 1 := by linarith [hk.1]
      rw [integral_inv_sqrt (k-1) k (by linarith [hk.1]) (by linarith [hk.1])]
      simp only [one_div]
      rw [← sub_pos]
      have : sqrt (↑k) - sqrt (↑k - 1) = 1 / (sqrt (↑k) + sqrt (↑k - 1)) := by
        field_simp; ring
      rw [this]
      apply div_pos
      · norm_num
      · apply add_pos <;> exact sqrt_pos.mpr (by linarith [hk.1])
    · use 2
      constructor
      · rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩
      · have : ∫ x in (1:ℝ)..2, 1 / sqrt x = 2 * (sqrt 2 - 1) := by
          rw [integral_inv_sqrt 1 2 zero_lt_one (by norm_num)]
          simp only [one_div]
          field_simp
        rw [this]
        have : 1 / sqrt 2 < 2 * (sqrt 2 - 1) := by
          rw [div_lt_iff (sqrt_pos.mpr (by norm_num))]
          have : sqrt 2 ≈ 1.41421356237 := by norm_num
          linarith
        exact this

  rw [h_eq] at h_contra
  rw [h_int, h_sqrt10000, h_sqrt1] at h_contra
  simp at h_contra
  linarith
