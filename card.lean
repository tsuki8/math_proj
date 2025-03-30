import Mathlib
open Real Polynomial

noncomputable def P: ℝ[X] := C 3 * X ^ 2 + C 2 * X - C 56

lemma T: P.roots = { 4, -14/3 } := by
  have HP: P ≠ 0 := by
    intro H0
    have H1: P.eval 1 = - 51 := by
      unfold P; simp; norm_num
    rw [H0] at H1; simp at H1
  have H0 := Polynomial.card_roots HP
  have H1: P.degree = 2 := by
    unfold P
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    . rw [Polynomial.degree_add_eq_left_of_degree_lt]
      . simp
      . simp
    . simp
      rw [Polynomial.degree_add_eq_left_of_degree_lt]
      . simp
      . simp
  rw [H1] at H0
  simp at H0
  have H3: 4 ∈ P.roots := by
    simp [HP]
    unfold P; simp; norm_num
  have H4: - 14 / 3 ∈ P.roots := by
    simp [HP]
    unfold P; simp; norm_num
  have H5: {4, -14/3} ⊆ P.roots := by
    intro x Hx; simp at Hx
    obtain Hx | Hx := Hx <;> subst x <;> assumption
  refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ H0)
  rw [Multiset.le_iff_subset]; assumption
  simp; norm_num
