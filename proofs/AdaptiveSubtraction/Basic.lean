import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith


import Mathlib.Data.Finset.Basic

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Linear

import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts


import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory

open scoped BigOperators
open Set Real Filter Topology
open Function

open Classical
open scoped NNReal ENNReal
open List
open MeasureTheory


def quadratic_vertex (a h k x : ℝ) : ℝ := a * (x - h) ^ 2 + k

theorem vertex_quadratic_has_minimum (a h k : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, quadratic_vertex a h k x ≥ quadratic_vertex a h k x₀ := by
  use h
  intro x
  unfold quadratic_vertex
  have h1 : 0 ≤ (x - h) ^ 2 := sq_nonneg (x - h)
  have h2 : 0 ≤ a * (x - h) ^ 2 := mul_nonneg (le_of_lt ha) h1
  calc
    a * (x - h) ^ 2 + k ≥ 0 + k := add_le_add_right h2 k
    _ = a * (h - h) ^ 2 + k := by simp_all only
    [
      mul_nonneg_iff_of_pos_left,
      zero_add,
      sub_self,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      mul_zero
    ]



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


theorem quadratic_has_minimum (a b c : ℝ) (ha : 0 < a) :
    ∃ x₀, ∀ x, quadratic a b c x ≥ quadratic a b c x₀ := by
  let h := -b / (2 * a)
  let k := c - b ^ 2 / (4 * a)
  obtain ⟨x₀, hx₀⟩ := vertex_quadratic_has_minimum a h k ha
  have h_eq : ∀ x, quadratic a b c x = quadratic_vertex a h k x :=
    quadratic_eq_vertex_form a b c (ne_of_gt ha)
  use x₀
  intro x
  rw [h_eq x, h_eq x₀]
  exact hx₀ x


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


abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂



def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D


noncomputable def p_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
  gradDot dI dB D / gradDot dB dB D




lemma symmetry_grad (dI dB : Gradient)(D : Finset Pixel) : gradDot dI dB D = gradDot dB dI D := by
  unfold gradDot
  apply Finset.sum_congr rfl
  intro x hx
  simp only
  rw [mul_comm (dI x).1 (dB x).1, mul_comm (dI x).2 (dB x).2]


theorem add_sub_cancel_thrm (a b : ℝ) : a + b - b = a := by
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_neg_cancel, add_zero]


theorem add_lt_right_thrm {a b c : ℝ} (h : a + c < b + c) : a < b := by
  have h₁ : (a + c) - c < (b + c) - c := sub_lt_sub_right h c

  have h₂ : (a + c) - c = a := by
    rw [sub_eq_add_neg]
    rw [add_assoc]
    simp_all only [add_lt_add_iff_right, add_sub_cancel_right, add_neg_cancel, add_zero]

  have h₃ : (b + c) - c = b := by
    rw [add_sub_cancel_thrm]

  rw [h₂, h₃] at h₁

  exact h₁

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
    ring
    rw [hβ]
    simp only [one_div, neg_mul, even_two, Even.neg_pow, inv_pow]
    field_simp
    ring

  rw [ lhs_final]
  rw [hβ]
  simp only [one_div, neg_mul, even_two, Even.neg_pow, ge_iff_le]

  rw [pow_two]
  ring
  rfl


theorem R_has_minimum_at_ρ_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ ρ : ℝ, R dI dB D ρ ≥ R dI dB D (p_opt dI dB D) := by
    let a := gradDot dB dB D
    let beta := gradDot dB dI D
    let b := -2 * beta
    let c := gradDot dI dI D
    let d := p_opt dI dB D
    have ha    : a = gradDot dB dB D := rfl
    have hbeta : beta = gradDot dB dI D := rfl
    have hb    : b = -2 * beta := rfl
    have hc    : c = gradDot dI dI D := rfl
    have hd    : d = p_opt dI dB D := rfl
    have hz : 0 < a := h

    have R_eq (p : ℝ) : R dI dB D p = c - 2 * p * beta + p ^ 2 * a := by
      unfold R
      rw [←ha, ←hbeta, ←hc]

    have rhs_eq_quad (p : ℝ) : c - 2 * p * beta + p ^ 2 * a = quadratic a b c p := by
      rw [hb]
      unfold quadratic
      ring

    rw [R_eq]

    unfold R

    rw [rhs_eq_quad]

    have lhs_eq_quad (p : ℝ) :
      gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D =
      quadratic a b c p :=
      by
        rw [←hc, ←hbeta, ←ha, hb]
        unfold quadratic
        ring

    intro p
    rw [lhs_eq_quad]

    rw[←hd]

    have h_quad_ineq : quadratic a b c d ≥ quadratic_minimum a b c :=
      quadratic_minimizer a b c hz d

    apply ge_trans
    apply quadratic_minimizer a b c hz p

    unfold quadratic_minimum quadratic_minimizer_point quadratic

    have hβ : beta = -(1/2) * b := by
      simp_all only [neg_mul, implies_true, ge_iff_le, one_div, mul_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        inv_mul_cancel_left₀, neg_neg, a, beta, b, c, d]

    have hd_1 : d = beta / a := by
      rw [hd]
      rw [hbeta]
      rw [ha]
      rw [p_opt]
      rw [symmetry_grad]

    apply quadratic_vertex_minimizer_explicit a b c beta d hz hβ hd_1



noncomputable def ρ_opt_1d
  (I B : ℝ → ℝ)
  (Ω : Set ℝ) : ℝ :=
  (∫ x in Ω, deriv I x • deriv B x) / (∫ x in Ω, (deriv B x)^2)

noncomputable def edginess (I B : ℝ → ℝ) (Ω : Set ℝ) (ρ : ℝ) : ℝ :=
  ∫ x in Ω, (deriv (λ x => I x - ρ • B x)) x ^ 2

/-
theorem minimise_edginess
  (I B : ℝ → ℝ)
  (Ω : Set ℝ)
  (hΩ : MeasurableSet Ω)
  (hI : DifferentiableOn ℝ I Ω)
  (hB : DifferentiableOn ℝ B Ω)
  (hB_nonzero : ∫ x in Ω, (deriv B x)^2 ≠ 0) :
  ∀ ρ : ℝ, edginess I B Ω (ρ_opt_1d I B Ω) ≤ edginess I B Ω ρ := by
    rw [edginess]
    unfold edginess
    trace_state
    --rw [deriv_add, DifferentiableAt.const_mul]
    sorry
-/

lemma scalar_mul_differentiable_within
  (B : ℝ → ℝ)
  (Ω : Set ℝ)
  (ρ x : ℝ)
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x :=
DifferentiableWithinAt.const_smul (hB x hx) ρ


lemma f_differentiable_within
  (I : ℝ → ℝ)
  (Ω : Set ℝ)
  (hI : DifferentiableOn ℝ I Ω)
  (x : ℝ)
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma deriv_distribute
  (I B : ℝ → ℝ)
  (Ω : Set ℝ)
  (hI : DifferentiableOn ℝ I Ω)
  (hB : DifferentiableOn ℝ B Ω)
:
  ∀ (ρ x : ℝ), x ∈ Ω → Ω ∈ 𝓝 x → deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
:= by
  intros ρ x hx hn
  let f := I
  let g := λ x ↦ ρ • B x

  have hf : DifferentiableWithinAt ℝ f Ω x := f_differentiable_within I Ω hI x hx
  have hg : DifferentiableWithinAt ℝ g Ω x := scalar_mul_differentiable_within B Ω ρ x hB hx
  have hf' : DifferentiableAt ℝ f x := hf.differentiableAt hn
  have hg' : DifferentiableAt ℝ g x := hg.differentiableAt hn

  have hB' : DifferentiableAt ℝ B x := (hB x hx).differentiableAt hn

  have deriv_h : deriv (λ x ↦ f x - g x) x = deriv f x - deriv g x := by
    apply deriv_sub hf' hg'

  rw [deriv_h]

  unfold f g

  have scalar_mul : deriv (λ x ↦ ρ • B x) x = ρ • deriv B x := by
    simp_all only
    [
      smul_eq_mul,
      differentiableAt_const,
      DifferentiableAt.fun_mul,
      deriv_fun_sub,
      deriv_fun_mul,
      deriv_const',
      zero_mul,
      zero_add,
      f,
      g
    ]

  rw [scalar_mul]
