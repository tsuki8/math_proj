import Mathlib

theorem mathd_algebra_116 (k x : ℝ) (h₀ : x = (13 - Real.sqrt 131) / 4)    (h₁ : 2 * x ^ 2 - 13 * x + k = 0) : k = 19 / 4 := by
  rw[h₀] at h₁
  norm_num
  have h₂: k = -2*((13 - Real.sqrt 131)/4)^2 + 13*((13 - Real.sqrt 131)/4) := by
    linarith
  rw[h₂]
  have h₃: -2*((13 - Real.sqrt 131)/4)^2 = -75/2 + 13*(Real.sqrt (131)/4) := by
    ring_nf
    have h₄: (Real.sqrt 131)^2 = 131 := by
      norm_num
    rw[h₄]
    rw[add_comm, ← add_assoc]
    norm_num
  rw[h₃]
  norm_num
  rw[add_comm, ← add_assoc]
  have h₅: (13 - Real.sqrt 131)/4 = 13/4 - Real.sqrt 131/4 := by
    rw[div_sub_div_same]
  rw[h₅]
  rw[mul_sub]
  ring
