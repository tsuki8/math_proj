import Mathlib
open Real

lemma T (b: ℝ): 3 * b ^ 2 + 2 * b + 1 = 57 → b = 4 ∨ b = - 14 / 3 := fun h ↦ by
  have : 3 * (b - 4) * (b - (- 14 / 3)) + 57 = 57 := by
    nth_rw 2 [← h]
    ring
  simpa [sub_eq_zero] using this

