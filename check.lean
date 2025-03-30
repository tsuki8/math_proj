import Mathlib

theorem cycle_cons_of_ne_nil {α : Type _} {l : List α} (h : l ≠ []) : cycle l = l ++ cycle l  := by sorry