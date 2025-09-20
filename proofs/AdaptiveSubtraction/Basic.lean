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


abbrev Pixel := ℕ × ℕ
abbrev Gradient := Pixel → ℝ × ℝ

def gradDot (f g : Gradient) (D : Finset Pixel) : ℝ :=
  ∑ x ∈ D,
    let (fx₁, fx₂) := f x
    let (gx₁, gx₂) := g x
    fx₁ * gx₁ + fx₂ * gx₂



def R (dI dB : Gradient) (D : Finset Pixel) (p : ℝ) : ℝ :=
  gradDot dI dI D - 2 * p * gradDot dB dI D + p ^ 2 * gradDot dB dB D


noncomputable def ρ_opt (dI dB : Gradient) (D : Finset Pixel) : ℝ :=
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


theorem R_has_minimum_at_ρ_opt
  (dI dB : Gradient) (D : Finset Pixel)
  (h : 0 < gradDot dB dB D) :
  ∀ ρ : ℝ, R dI dB D ρ ≥ R dI dB D (ρ_opt dI dB D) := by
    let a := gradDot dB dB D
    let beta := gradDot dB dI D
    let b := -2 * beta
    let c := gradDot dI dI D
    let d := ρ_opt dI dB D
    have ha    : a = gradDot dB dB D := rfl
    have hbeta : beta = gradDot dB dI D := rfl
    have hb    : b = -2 * beta := rfl
    have hc    : c = gradDot dI dI D := rfl
    have hd    : d = ρ_opt dI dB D := rfl
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
      rw [ρ_opt]
      rw [symmetry_grad]

    apply quadratic_vertex_minimizer_explicit a b c beta d hz hβ hd_1



noncomputable def ρ_opt_1d
  (I B : ℝ → ℝ)
  (Ω : Set ℝ) : ℝ :=
  (∫ x in Ω, deriv I x • deriv B x) / (∫ x in Ω, (deriv B x)^2)

noncomputable def edginess (I B : ℝ → ℝ) (Ω : Set ℝ) (ρ : ℝ) : ℝ :=
  ∫ x in Ω, ((deriv (λ x => I x - ρ • B x)) x ) ^ 2



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


lemma deriv_distribute'
    (I B : ℝ → ℝ)
    (Ω : Set ℝ)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (x : Ω)
    (hΩ : Ω ∈ 𝓝 (x : ℝ))
:
    deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
:=
    deriv_distribute I B Ω hI hB ρ ↑x x.prop hΩ


lemma deriv_distribute'''
  (I B : ℝ → ℝ)
  (Ω : Set ℝ)
  (hI : DifferentiableOn ℝ I Ω)
  (hB : DifferentiableOn ℝ B Ω)
  (x : Ω)
  (hn : Ω ∈ 𝓝 (x : ℝ))
:
  ∀ (ρ : ℝ), deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
:= by
  intros ρ
  let f := I
  let g := λ x ↦ ρ • B x

  have hf : DifferentiableWithinAt ℝ f Ω x := f_differentiable_within I Ω hI x x.prop
  have hg : DifferentiableWithinAt ℝ g Ω x := scalar_mul_differentiable_within B Ω ρ x hB x.prop
  have hf' : DifferentiableAt ℝ f x := hf.differentiableAt hn
  have hg' : DifferentiableAt ℝ g x := hg.differentiableAt hn

  have hB' : DifferentiableAt ℝ B x := (hB ↑x x.prop).differentiableAt hn

  have deriv_h : deriv (λ x ↦ f x - g x) ↑x  = deriv f ↑x  - deriv g ↑x := by
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


lemma deriv_distribute_square
  (I B : ℝ → ℝ)
  (Ω : Set ℝ)
  (hI : DifferentiableOn ℝ I Ω)
  (hB : DifferentiableOn ℝ B Ω)
  (x : Ω)
  (hn : Ω ∈ 𝓝 (x : ℝ))
:
  ∀ (ρ : ℝ), deriv (λ x ↦ I x - ρ • B x) x ^ 2 = (deriv I x - ρ • deriv B x ) ^ 2
:= by
    intro ρ
    rw [deriv_distribute''' I B Ω hI hB x hn]



noncomputable def c_coef (I : ℝ → ℝ) (Ω : Set ℝ) : ℝ := (∫ x in Ω, deriv I x) ^ 2

noncomputable def b_coef (I B : ℝ → ℝ) (Ω : Set ℝ) : ℝ := - 2 • ∫ x in Ω, deriv I x • deriv B x

noncomputable def a_coef ( B : ℝ → ℝ) (Ω : Set ℝ) : ℝ := ∫ x in Ω, deriv B x ^ 2


noncomputable def edginess_polynomial (I B : ℝ → ℝ) (Ω : Set ℝ) (ρ : ℝ) : ℝ :=
  --(∫ x in Ω, (deriv I x) )  - (2 • ρ • ∫ x in Ω, (deriv I x) • (deriv B x)) + ρ ^ 2 • ∫ x in Ω, (deriv B x)^2
  (quadratic  (a_coef B Ω ) (b_coef I B Ω ) (c_coef I Ω) ρ )




lemma deriv_f_g
    (f g : ℝ → ℝ)
    (Ω : Set ℝ)
    (x : ℝ )
    (hf : DifferentiableOn ℝ f Ω)
    (hg : DifferentiableOn ℝ g Ω)
    (hΩ_open : IsOpen Ω)
    ( hx : x ∈ Ω )
:
    deriv (f - g) x = deriv f x - deriv g x
:= by
{
    have hn : Ω ∈ 𝓝 x := hΩ_open.mem_nhds hx
    have hfx : DifferentiableAt ℝ f x := hf.differentiableAt hn
    have hgx : DifferentiableAt ℝ g x := hg.differentiableAt hn

    exact deriv_sub hfx hgx
}


lemma deriv_distributes
    (I B : ℝ → ℝ)
    (x : ℝ )
    (Ω : Set ℝ)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ )
    (hΩ_open : IsOpen Ω)
    ( hΩ : x ∈ Ω )
:
    deriv (λ x ↦ I x - ρ • B x) x ^ 2 = (λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x ^ 2
:= by
{
    apply congrArg (λ y => y ^ 2)

    let f := I
    let g := λ x ↦ ρ • B x

    let gg := λ x ↦ ρ • (deriv B x)

    have hn : Ω ∈ 𝓝 x := hΩ_open.mem_nhds hΩ
    have hf : DifferentiableWithinAt ℝ f Ω x := f_differentiable_within I Ω hI x hΩ
    have hg : DifferentiableWithinAt ℝ g Ω x := scalar_mul_differentiable_within B Ω ρ x hB hΩ
    have hf' : DifferentiableAt ℝ f x := hf.differentiableAt hn
    have hg' : DifferentiableAt ℝ g x := hg.differentiableAt hn
    have hB' : DifferentiableAt ℝ B x := (hB x hΩ).differentiableAt hn

    change deriv (λ x => f x - g x) x = (λ x ↦ (deriv f x ) - ρ • (deriv B x) ) x

    change deriv (λ x => f x - g x) x = (λ x ↦ (deriv f x ) - (gg x) ) x

    have ρBh : (deriv g x) = gg x := by
    {
        unfold gg
        unfold g
        simp_all only [smul_eq_mul, deriv_const_mul_field', f, g]
    }
    simp only [←ρBh]

    change deriv (f - g ) x = (deriv f x) - (deriv g x)

    rw [deriv_sub]

    apply hf'
    apply hg'
}

noncomputable def func_on_Ω
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (ρ : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (x : {x // x ∈ Ω}) : ℝ
:=
    deriv (λ z ↦ I z - ρ • B z) x.val ^ 2



noncomputable def func_dist_on_Ω
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (ρ : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (x : {x // x ∈ Ω}) : ℝ
:=
    (deriv I x.val - ρ • deriv B x.val) ^ 2


noncomputable def func_on_ℝ
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (ρ : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (x : ℝ) : ℝ
:=
    if hx : x ∈ Ω then
      func_on_Ω I B w h ρ Ω ⟨x, hx⟩
    else
      0

noncomputable def int_on_func
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (ρ : ℝ)
    (Ω : Set ℝ := Set.Ioo w h) : ℝ
:=
    ∫ x in Ω, func_on_ℝ I B w h ρ Ω x



lemma deriv_distributes_over_sub_within_integral
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, deriv (λ x ↦ I x - ρ • B x) x ^ 2 =
    ∫ x in Ω, ((λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x) ^ 2
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (deriv B x)

    apply integral_congr_ae

    have h_diff : DifferentiableOn ℝ (λ x ↦ I x - ρ • B x) Ω :=
      hI.sub (hB.const_smul ρ)

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within I Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within B Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change deriv (λ x => f x - g x) a = (λ x ↦ (deriv f x ) - ρ • (deriv B x) ) a

        change deriv (λ x => f x - g x) a = (λ x ↦ (deriv f x ) - (gg x) ) a

        have ρBh : (deriv g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, deriv_const_mul_field', f, g]
        }
        simp only [←ρBh]

        change deriv (f - g ) a = (deriv f a) - (deriv g a)

        rw [deriv_sub]

        apply hf'
        apply hg'
    }

    filter_upwards [h_deriv_eq] with x hx
    simp only [hx]
}


lemma expand_squared_term
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ((λ x ↦ (deriv I x ) - ρ • (deriv B x) ) x ) ^ 2 =
    ∫ x in Ω, (deriv I x)^2 - 2 • ρ • (deriv I x) • ( deriv B x) + (ρ • deriv B x)^2
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (deriv B x)

    apply integral_congr_ae

    have h_diff : DifferentiableOn ℝ (λ x ↦ I x - ρ • B x) Ω :=
      hI.sub (hB.const_smul ρ)

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        deriv (λ x ↦ I x - ρ • B x) x = deriv I x - ρ • deriv B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within I Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within B Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change deriv (λ x => f x - g x) a = (λ x ↦ (deriv f x ) - ρ • (deriv B x) ) a

        change deriv (λ x => f x - g x) a = (λ x ↦ (deriv f x ) - (gg x) ) a

        have ρBh : (deriv g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, deriv_const_mul_field', f, g]
        }
        simp only [←ρBh]

        change deriv (f - g ) a = (deriv f a) - (deriv g a)

        rw [deriv_sub]

        apply hf'
        apply hg'
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring
}


lemma integral_distributes_over_addition
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ (x : ℝ) in Ω, deriv I x ^ 2 - ρ * (deriv I x * deriv B x) * 2 + (ρ * deriv B x) ^ 2 = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, deriv I x) ^ 2
:= by
{
    let f := λ x ↦ deriv I x ^ 2
    let g := λ x ↦ ρ * (deriv I x * deriv B x) * 2
    let h := λ x ↦ (ρ * deriv B x) ^ 2
    change ∫ (x : ℝ) in Ω, f x - (g x) + ((ρ * deriv B x) ^ 2) = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, deriv I x) ^ 2

    change ∫ (x : ℝ) in Ω, (f x) - (g x) + (h x) = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, deriv I x) ^ 2

    have dist_int_fgh
    :
        ∫ (x : ℝ) in Ω, (f x) - (g x) + (h x) = (∫ (x : ℝ) in Ω, (f x)) - (∫ (x : ℝ) in Ω, (g x)) + ∫ (x : ℝ) in Ω, (h x)
    := by
    {

        simp only [sub_add_eq_add_sub]
        trace_state

        sorry
    }

    rw  [dist_int_fgh]

    change ((∫ (x : ℝ) in Ω, f x) - ∫ (x : ℝ) in Ω, g x) + ∫ (x : ℝ) in Ω, h x = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, deriv I x) ^ 2

    have f_eq : (∫ (x : ℝ) in Ω, deriv I x) ^ 2 = ∫ (x : ℝ) in Ω, (f x)
    := by
    {

        sorry
    }

    rw [f_eq]

    have h_eq : (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 = ∫ (x : ℝ) in Ω, (h x)
    := by
    {
        sorry
    }

    rw [h_eq]

    have g_eq : -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) = -∫ (x : ℝ) in Ω, (g x)
    := by
    {
        sorry
    }

    rw [g_eq]

    let F := ∫ (x : ℝ) in Ω, f x
    let G := ∫ (x : ℝ) in Ω, g x
    let H := ∫ (x : ℝ) in Ω, h x

    change F - G + H = H - G + F
    ring
}


theorem edginess_polynomial_eq
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
:
    ∀ ρ : ℝ, edginess I B Ω ρ = edginess_polynomial I B Ω ρ
:= by
{
    unfold edginess edginess_polynomial
    intro ρ
    unfold quadratic
    unfold a_coef b_coef c_coef
    ring_nf

    rw [(deriv_distributes_over_sub_within_integral I B w h Ω hM hI hB ρ hΩ_open )]

    rw [(expand_squared_term I B w h Ω hM hI hB ρ hΩ_open )]

    ring_nf
    simp_all only [smul_eq_mul, Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat, mul_neg]

    have ρB_squared : (λ x ↦ (ρ * deriv B x ) )^ 2 = λ x ↦ ρ ^ 2 * (deriv B x) ^ 2 := by
    {
        funext x
        ring_nf
        simp_all only [Pi.pow_apply]
        simp only [mul_pow]
    }

    have rest_lemma :
        ∫ (x : ℝ) in Ω, deriv I x ^ 2 - ρ * (deriv I x * deriv B x) * 2 + (ρ * deriv B x) ^ 2 = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, deriv I x) ^ 2
    := by
    {
        rw [ (integral_distributes_over_addition I B w h Ω hM hI hB ρ hΩ_open) ]
    }

    apply rest_lemma
}


theorem edginess_is_quadratic
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
:
    ∀ (ρ : ℝ), edginess I B Ω ρ = (quadratic (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω) ρ)
:= by
{
    intro ρ
    rw [(edginess_polynomial_eq I B w h Ω hM hI hB hΩ_open)]
    unfold edginess_polynomial
    rfl
}


lemma rho_opt_eq_minimizer_point
  (I B : ℝ → ℝ)
  (Ω : Set ℝ)
  (hB_nonzero : ∫ x in Ω, (deriv B x)^2 > 0)
:
    ρ_opt_1d I B Ω = quadratic_minimizer_point (a_coef B Ω) (b_coef I B Ω)
:= by
{
    unfold ρ_opt_1d quadratic_minimizer_point a_coef b_coef
    field_simp [hB_nonzero]
    ring_nf
}


theorem minimized_edginess
    (I B : ℝ → ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hB_nonzero : ∫ x in Ω, (deriv B x)^2 > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
:
    edginess I B Ω (ρ_opt_1d I B Ω) = quadratic_minimum (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω)
:= by
{
    rw [(edginess_polynomial_eq I B w h Ω hM hI hB hΩ )]
    unfold edginess_polynomial
    unfold quadratic_minimum
    rw [(rho_opt_eq_minimizer_point I B Ω hB_nonzero)]
}




theorem minimise_edginess
    (I B : ℝ → ℝ)
    --(Ω : Set ℝ)
    (w h : ℝ)
    (Ω : Set ℝ := Set.Ioo w h)
    (hM: MeasurableSet Ω)
    (hB_nonzero : ∫ x in Ω, (deriv B x)^2 > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
:
    ∀ (ρ : ℝ), edginess I B Ω (ρ_opt_1d I B Ω) ≤ edginess I B Ω ρ := by
{
    let lhs := edginess I B Ω (ρ_opt_1d I B Ω)
    change ∀ (ρ : ℝ), lhs ≤ edginess I B Ω ρ

    have ha_pos : 0 < a_coef B Ω := by
      unfold a_coef
      exact hB_nonzero

    have h_lhs_eq_min : lhs = quadratic_minimum (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω) := by
    {
        apply (minimized_edginess I B w h Ω hM hB_nonzero hI hB hΩ)
    }

    intro ρ
    rw [(edginess_is_quadratic I B w h Ω hM hI hB hΩ)]
    rw [h_lhs_eq_min]
    apply quadratic_minimizer (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω) ha_pos
}
