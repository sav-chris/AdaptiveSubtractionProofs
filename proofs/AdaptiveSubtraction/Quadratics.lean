import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def quadratic_vertex (a h k x : ℝ) : ℝ := a * (x - h) ^ 2 + k

def quadratic (a b c x : ℝ) : ℝ := a * (x ^ 2) + b * x + c

lemma quadratic_eq_vertex_form (a b c : ℝ) (ha : a ≠ 0) :
    ∀ x, quadratic a b c x = quadratic_vertex a (-b / (2 * a)) (c - b ^ 2 / (4 * a)) x := by
  intro x
  unfold quadratic quadratic_vertex
  have h1 : (x - (-b / (2 * a))) ^ 2 = x ^ 2 + (b / a) * x + (b ^ 2) / (4 * a ^ 2) := by
    field_simp [ha]
    ring
  rw [h1]
  field_simp [ha]
  ring


theorem vertex_quadratic_minimizer (a h k : ℝ) (ha : 0 < a) :
  ∀ x, quadratic_vertex a h k x ≥ quadratic_vertex a h k h := by
  intro x
  have h1 : 0 ≤ (x - h)^2 := sq_nonneg _
  have h2 : 0 ≤ a * (x - h)^2 := mul_nonneg (le_of_lt ha) h1
  calc
    a * (x - h)^2 + k ≥ 0 + k := add_le_add_right h2 k
    _ = a * (h - h)^2 + k := by simp only [zero_add, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]


noncomputable def quadratic_minimizer_point (a b : ℝ) : ℝ := -b / (2 * a)

noncomputable def quadratic_minimum (a b c : ℝ) : ℝ :=
  quadratic a b c (quadratic_minimizer_point a b)


theorem quadratic_minimizer (a b c : ℝ) (ha : 0 < a) :
  ∀ p : ℝ, quadratic a b c p ≥ quadratic_minimum a b c := by
  let h := -b / (2 * a)
  let k := c - b^2 / (4 * a)
  have h_eq : ∀ p, quadratic a b c p = quadratic_vertex a h k p :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  have h_min := vertex_quadratic_minimizer a h k ha
  intro p
  unfold quadratic_minimum
  unfold quadratic_minimizer_point
  rw [h_eq p, h_eq h]
  exact h_min p



theorem add_sub_cancel_thrm (a b : ℝ) : a + b - b = a := by
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_neg_cancel, add_zero]


lemma quadratic_vertex_minimizer_explicit
    (a b c β d : ℝ) (ha : 0 < a)
    (hβ : β = -(1/2) * b)
    (hd : d = β / a) :
    a * d ^ 2 + b * d + c ≤
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c := by

  let lhs_1 := a * d ^ 2 + b * d
  have h_add_ineq_1 : a * d ^ 2 + b * d + c = lhs_1 + c := rfl

  let lhs_2 := a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a))
  have h_add_ineq_2 : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = lhs_2 + c := rfl

  rw [h_add_ineq_1, h_add_ineq_2] at *

  simp only [add_le_add_iff_right]

  unfold lhs_1 lhs_2

  have simplify_rhs_1 :  a * (-b / (2 * a)) ^ 2 = b^2 /(4*a) := by
      rw [pow_two]
      rw [neg_div, neg_mul_neg, ←pow_two]
      field_simp
      ring

  rw [simplify_rhs_1]

  have simplify_rhs_2 :  b * (-b / (2 * a)) = - b^2 / (2 * a) := by
    rw [←mul_div_assoc]
    ring

  rw [simplify_rhs_2]

  have simplify_rhs_3 : b ^ 2 / (4 * a) + -b ^ 2 / (2 * a) = - b^2 / (4*a) := by
    field_simp
    ring

  rw [simplify_rhs_3]

  rw [hd]

  have lhs_final :  a * (β / a) ^ 2 + b * (β / a) = - (β^2)/a := by
    rw [pow_two]
    ring_nf
    rw [hβ]
    simp only [one_div, neg_mul, even_two, Even.neg_pow, inv_pow]
    field_simp
    ring

  rw [ lhs_final]
  rw [hβ]
  simp only [one_div, neg_mul, even_two, Even.neg_pow, ge_iff_le]

  rw [pow_two]
  ring_nf
  rfl
