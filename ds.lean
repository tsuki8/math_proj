import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat



theorem amc12a_2008_p4 : (∏ k in Finset.Icc (1 : ℕ) 501, ((4 : ℝ) * k + 4) / (4 * k)) = 502 := by
  -- 将乘积展开为连分数
  have h_prod : (∏ k in Finset.Icc (1 : ℕ) 501, ((4 : ℝ) * k + 4) / (4 * k)) =
                ∏ k in Finset.Icc (1 : ℕ) 501, ((k + 1) / k) := by
    refine Finset.prod_congr rfl (fun k hk => ?_)
    field_simp
    ring

  -- 计算连分数的值
  have h_telescope : ∏ k in Finset.Icc 1 501, ((k + 1) / k) = 502 := by
    refine Finset.prod_telescope (fun k => (k + 1) / k) 1 501 ?_
    intro k
    field_simp
    ring

  -- 结合结果
  rw [h_prod, h_telescope]
