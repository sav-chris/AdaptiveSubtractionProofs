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
import Mathlib.Order.RelClasses
import Mathlib.Analysis.InnerProductSpace.Basic -- product notation ⟪ ⟫

open scoped BigOperators
open Set Real Filter Topology
open Function
open Classical
open scoped NNReal ENNReal
open List
open MeasureTheory
open scoped InnerProductSpace --Inner products

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

--TO DO: what to do with this?
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
    rw [deriv_distribute I B Ω hI hB x hn]

noncomputable def c_coef (I : ℝ → ℝ) (Ω : Set ℝ) : ℝ := (∫ x in Ω, (deriv I x) ^ 2)

noncomputable def b_coef (I B : ℝ → ℝ) (Ω : Set ℝ) : ℝ := - 2 • ∫ x in Ω, deriv I x • deriv B x

noncomputable def a_coef ( B : ℝ → ℝ) (Ω : Set ℝ) : ℝ := ∫ x in Ω, deriv B x ^ 2

noncomputable def edginess_polynomial (I B : ℝ → ℝ) (Ω : Set ℝ) (ρ : ℝ) : ℝ :=
  --(∫ x in Ω, (deriv I x) ^ 2 )  - (2 • ρ • ∫ x in Ω, (deriv I x) • (deriv B x)) + ρ ^ 2 • (∫ x in Ω, (deriv B x) ^ 2 )
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

lemma deriv_distributes_over_sub_within_integral
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
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
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
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

lemma distribute_integral_fgh
    (f g h : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (hIf : Integrable f (volume.restrict Ω))
    (hIg : Integrable g (volume.restrict Ω))
    (hIh : Integrable h (volume.restrict Ω))
:
    ∫ (x : ℝ) in Ω, (f x) - (g x) + (h x) = (∫ (x : ℝ) in Ω, (f x)) - (∫ (x : ℝ) in Ω, (g x)) + ∫ (x : ℝ) in Ω, (h x)
:= by
{
    let ff := λ x ↦ (f x) - (g x)

    have hIff : Integrable ff (volume.restrict Ω) := by
    {
        dsimp [ff]
        exact hIf.sub hIg
    }

    change ∫ (x : ℝ) in Ω, (ff x) + (h x) = (∫ (x : ℝ) in Ω, (f x)) - (∫ (x : ℝ) in Ω, (g x)) + ∫ (x : ℝ) in Ω, (h x)

    rw [(integral_add hIff hIh)]

    unfold ff
    rw [(integral_sub hIf hIg)]
}

def image_and_background_are_edgable
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
:=
    let f := λ x ↦ deriv I x ^ 2
    let g := λ x ↦ (deriv I x * deriv B x)
    let h := λ x ↦ (deriv B x) ^ 2
    Integrable f (volume.restrict Ω) ∧ Integrable g (volume.restrict Ω) ∧ Integrable h (volume.restrict Ω)


lemma integral_distributes_over_addition
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (ρ : ℝ)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    ∫ (x : ℝ) in Ω, deriv I x ^ 2 - ρ * (deriv I x * deriv B x) * 2 + (ρ * deriv B x) ^ 2 = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + ∫ (x : ℝ) in Ω, (deriv I x) ^ 2
:= by
{
    let f := λ x ↦ deriv I x ^ 2
    let g := λ x ↦ ρ * (deriv I x * deriv B x) * 2
    let h := λ x ↦ (ρ * deriv B x) ^ 2
    change ∫ (x : ℝ) in Ω, f x - (g x) + ((ρ * deriv B x) ^ 2) = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, (deriv I x) ^ 2)

    change ∫ (x : ℝ) in Ω, (f x) - (g x) + (h x) = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, (deriv I x) ^ 2)

    rcases h_edgable with ⟨hIf, hIg, hIh⟩

    have hIg_scaled: Integrable g (volume.restrict Ω) := by
    {
        unfold g
        let fx := λ x ↦ (deriv I x * deriv B x)
        let Ρ : ℝ := 2 * ρ
        change Integrable (λ x ↦ ρ * (fx x) * 2 ) (volume.restrict Ω)
        have h_factor : (λ x ↦ ρ * (fx x) * 2) = λ x ↦ Ρ * (fx x) := by
        {
            funext x
            dsimp [Ρ]
            ring
        }
        rw [h_factor]
        apply Integrable.const_mul
        unfold fx
        apply hIg
    }
    have hIh_scaled : Integrable h (volume.restrict Ω) := by
    {
        unfold h
        let fx := λ x ↦ (deriv I x * deriv B x)
        let Ρ : ℝ := ρ ^ 2
        change Integrable (fun x ↦ (ρ * deriv B x) ^ 2) (volume.restrict Ω)
        have h_factor : (λ x ↦ (ρ * deriv B x) ^ 2) = λ x ↦ (ρ ^2) * (deriv B x) ^ 2 := by
        {
            funext x
            dsimp [Ρ]
            ring
        }
        rw [h_factor]
        apply Integrable.const_mul
        apply hIh
    }

    rw [(distribute_integral_fgh f g h lower upper Ω hIf hIg_scaled hIh_scaled)]

    have f_eq : (∫ (x : ℝ) in Ω, (deriv I x) ^ 2) = ∫ (x : ℝ) in Ω, (f x)
    := by
    {
        rfl
    }

    rw [f_eq]

    have h_eq : (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 = ∫ (x : ℝ) in Ω, (h x)
    := by
    {
        let h := λ x ↦ (ρ * deriv B x) ^ 2

        change (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 = ∫ (x : ℝ) in Ω, (h x)

        unfold h

        have h_unfold : (λ x ↦ (h x)) = λ x ↦ ((ρ ^ 2) * (deriv B x) ^ 2) := by
        {
            unfold h
            ext x
            rw [mul_pow]
        }

        rw [h_unfold]
        rw [mul_comm]
        rw [integral_const_mul]
    }

    rw [h_eq]

    have g_eq : -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) = -∫ (x : ℝ) in Ω, (g x)
    := by
    {
        let g := λ x ↦ ρ * (deriv I x * deriv B x) * 2

        change -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) = -∫ (x : ℝ) in Ω, (g x)

        have g_unfold : (λ x ↦ (g x)) = λ x ↦ 2 * ρ * (deriv I x * deriv B x) := by
        {
            unfold g
            ext x
            ring
        }

        rw [g_unfold]
        rw [integral_const_mul]
        ring
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
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    ∀ ρ : ℝ, edginess I B Ω ρ = edginess_polynomial I B Ω ρ
:= by
{
    unfold edginess edginess_polynomial
    intro ρ
    unfold quadratic
    unfold a_coef b_coef c_coef
    ring_nf

    rw [(deriv_distributes_over_sub_within_integral I B lower upper Ω hM hI hB ρ hΩ_open )]

    rw [(expand_squared_term I B lower upper Ω hM hI hB ρ hΩ_open )]

    ring_nf
    simp_all only [smul_eq_mul, Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat, mul_neg]

    have rest_lemma :
        ∫ (x : ℝ) in Ω, (deriv I x ^ 2) - ρ * (deriv I x * deriv B x) * 2 + (ρ * deriv B x) ^ 2 = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, (deriv I x) ^ 2)
    := by
    {
        rw [ (integral_distributes_over_addition I B lower upper Ω ρ h_edgable) ]
    }

    apply rest_lemma
}

theorem edginess_is_quadratic
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    ∀ (ρ : ℝ), edginess I B Ω ρ = (quadratic (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω) ρ)
:= by
{
    intro ρ
    rw [(edginess_polynomial_eq I B lower upper Ω hM hI hB hΩ_open h_edgable)]
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
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (hM: MeasurableSet Ω)
    (hB_nonzero : ∫ x in Ω, (deriv B x)^2 > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    edginess I B Ω (ρ_opt_1d I B Ω) = quadratic_minimum (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω)
:= by
{
    rw [(edginess_polynomial_eq I B lower upper Ω hM hI hB hΩ h_edgable)]
    unfold edginess_polynomial
    unfold quadratic_minimum
    rw [(rho_opt_eq_minimizer_point I B Ω hB_nonzero)]
}


theorem edginess_minimisation_theorem
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (hM: MeasurableSet Ω)
    (hB_nonzero : ∫ x in Ω, (deriv B x)^2 > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
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
        apply (minimized_edginess I B lower upper Ω hM hB_nonzero hI hB hΩ h_edgable)
    }

    intro ρ
    rw [(edginess_is_quadratic I B lower upper Ω hM hI hB hΩ h_edgable)]
    rw [h_lhs_eq_min]
    apply quadratic_minimizer (a_coef B Ω) (b_coef I B Ω) (c_coef I Ω) ha_pos
}

---------------------------------------------------------------------------

def Ioo_nd (n : ℕ ) (w l : Fin n → ℝ) : Set (Fin n → ℝ) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


def image_and_background_are_edgable_ND
    {n : ℕ}
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
: Prop :=
    let f := λ x ↦ ‖fderiv ℝ I x‖^2
    let g := λ x ↦ ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)
    let h := λ x ↦ ‖fderiv ℝ B x‖^2
    Integrable f (volume.restrict Ω) ∧ Integrable g (volume.restrict Ω) ∧ Integrable h (volume.restrict Ω)


noncomputable def edginess_ND {n}
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (ρ : ℝ) : ℝ :=
  ∫ x in Ω, ‖fderiv ℝ (λ x => I x - ρ • B x) x‖^2


noncomputable def ρ_opt_nd {n : ℕ}
  (I B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
: ℝ :=
  ∫ x in Ω, (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) / (∫ x in Ω, ‖fderiv ℝ B x‖^2)


noncomputable def c_coef_nd {n : ℕ}
  (I : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper)) : ℝ
    := (∫ x in Ω, (‖fderiv ℝ I x‖) ^ 2)


noncomputable def b_coef_nd {n : ℕ}
  (I B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper)) : ℝ
    := - 2 • ∫ x in Ω, ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)

noncomputable def a_coef_nd {n : ℕ}
  ( B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper)) : ℝ
    := ∫ x in Ω, ‖fderiv ℝ B x‖ ^ 2


noncomputable def edginess_polynomial_ND {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (ρ : ℝ)
: ℝ :=
    (quadratic (a_coef_nd B lower upper Ω ) (b_coef_nd I B lower upper Ω ) (c_coef_nd I lower upper Ω) ρ )


lemma f_differentiable_within_nd {n : ℕ }
  (I : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  Fin n → ℝ)
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd {n : ℕ }
  (B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
  (ρ : ℝ)
  (x : Fin n → ℝ)
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ



lemma deriv_distributes_over_sub_within_integral_nd {n : ℕ}
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖fderiv ℝ (λ x ↦ I x - ρ • B x) x‖^2 =
    ∫ x in Ω, ‖(λ x ↦ fderiv ℝ I x - ρ • fderiv ℝ B x) x‖^2
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)

    apply integral_congr_ae

    have h_diff : DifferentiableOn ℝ (λ x ↦ I x - ρ • B x) Ω :=
      hI.sub (hB.const_smul ρ)

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, deriv_const_mul_field', f, g]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }

    filter_upwards [h_deriv_eq] with x hx
    simp only [hx]
}



lemma expand_squared_term_nd {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖fderiv ℝ I x - ρ • fderiv ℝ B x‖^2 =
    ∫ x in Ω, ‖fderiv ℝ I x‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • ‖fderiv ℝ B x‖^2
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (fderiv ℝ B x)

    apply integral_congr_ae

    have h_diff : DifferentiableOn ℝ (λ x ↦ I x - ρ • B x) Ω :=
      hI.sub (hB.const_smul ρ)

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        fderiv ℝ (λ x ↦ I x - ρ • B x) x = fderiv ℝ I x - ρ • fderiv ℝ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - ρ • (fderiv ℝ B x) ) a

        change fderiv ℝ (λ x => f x - g x) a = (λ x ↦ (fderiv ℝ f x ) - (gg x) ) a

        have ρBh : (fderiv ℝ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, deriv_const_mul_field', f, g]
        }
        simp only [←ρBh]

        change fderiv ℝ (f - g ) a = (fderiv ℝ f a) - (fderiv ℝ g a)

        rw [fderiv_sub]

        apply hf'
        apply hg'
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring
}



lemma integral_distributes_over_addition_nd {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (ρ : ℝ)
    (h_edgable : (image_and_background_are_edgable_ND I B lower upper Ω ) )
:
    ∫ x in Ω, ‖fderiv ℝ I x‖^2 - 2 • ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1) + (ρ • ‖fderiv ℝ B x‖)^2 =
    (∫ x in Ω, ‖fderiv ℝ B x‖^2) * ρ^2
    - ρ * (2 * ∫ x in Ω, ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1))
    + ∫ x in Ω, ‖fderiv ℝ I x‖^2
:= by
{
    let f := λ x ↦ ‖fderiv ℝ I x‖ ^ 2
    let g := λ x ↦ 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1))
    let h := λ x ↦ (ρ * ‖fderiv ℝ B x‖) ^ 2

    --change ∫ (x : Fin n → ℝ) in Ω, (f x) - 2 • ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1) + (ρ • ‖fderiv ℝ B x‖) ^ 2 = (∫ (x : Fin n → ℝ) in Ω, ‖fderiv ℝ B x‖ ^ 2) * ρ ^ 2 - ρ * (2 * ∫ (x : Fin n → ℝ) in Ω, ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + ∫ (x : Fin n → ℝ) in Ω, ‖fderiv ℝ I x‖ ^ 2

    --change ∫ (x : Fin n → ℝ) in Ω, (f x) - 2 • ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1) + (h x) = (∫ (x : Fin n → ℝ) in Ω, ‖fderiv ℝ B x‖ ^ 2) * ρ ^ 2 - ρ * (2 * ∫ (x : Fin n → ℝ) in Ω, ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + ∫ (x : Fin n → ℝ) in Ω, ‖fderiv ℝ I x‖ ^ 2

    change ∫ (x : Fin n → ℝ) in Ω, (f x) - (g x) + (h x) = (∫ (x : Fin n → ℝ) in Ω, ‖fderiv ℝ B x‖ ^ 2) * ρ ^ 2 - ρ * (2 * ∫ (x : Fin n → ℝ) in Ω, ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + ∫ (x : Fin n → ℝ) in Ω, ‖fderiv ℝ I x‖ ^ 2

    rcases h_edgable with ⟨hIf, hIg, hIh⟩

    have hIg_scaled : Integrable g (volume.restrict Ω) := by
    {
      unfold g
      let fx := λ x ↦ ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)
      let Ρ : ℝ := 2 • ρ

      change Integrable (λ x ↦ Ρ * fx x) (volume.restrict Ω)
      have h_factor : (λ x ↦ 2 • ρ • fx x) = λ x ↦ Ρ * fx x := by
      {
        funext x
        dsimp [Ρ]
        ring
      }
      rw [h_factor]
      apply Integrable.const_mul
      unfold fx
      exact hIg
    }

/-
    have hIg_scaled: Integrable g (volume.restrict Ω) := by
    {
        unfold g
        let fx := λ x ↦ (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1))
        let Ρ : ℝ := 2 * ρ
        change Integrable (λ x ↦ ρ * (fx x) * 2 ) (volume.restrict Ω)
        have h_factor : (λ x ↦ ρ * (fx x) * 2) = λ x ↦ Ρ * (fx x) := by
        {
            funext x
            dsimp [Ρ]
            ring
        }
        rw [h_factor]
        apply Integrable.const_mul
        unfold fx
        apply hIg
    } -/
    have hIh_scaled : Integrable h (volume.restrict Ω) := by
    {
        unfold h
        let fx := λ x ↦ ( ‖fderiv ℝ I x‖ * ‖fderiv ℝ B x‖)
        let Ρ : ℝ := ρ ^ 2
        change Integrable (fun x ↦ (ρ * ‖fderiv ℝ B x‖) ^ 2) (volume.restrict Ω)
        have h_factor : (λ x ↦ (ρ * ‖fderiv ℝ B x‖) ^ 2) = λ x ↦ (ρ ^2) * (‖fderiv ℝ B x‖) ^ 2 := by
        {
            funext x
            dsimp [Ρ]
            ring
        }
        rw [h_factor]
        apply Integrable.const_mul
        apply hIh
    }

    rw [(distribute_integral_fgh f g h lower upper Ω hIf hIg_scaled hIh_scaled)]

    have f_eq : (∫ (x : ℝ) in Ω, (deriv I x) ^ 2) = ∫ (x : ℝ) in Ω, (f x)
    := by
    {
        rfl
    }

    rw [f_eq]

    have h_eq : (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 = ∫ (x : ℝ) in Ω, (h x)
    := by
    {
        let h := λ x ↦ (ρ * deriv B x) ^ 2

        change (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 = ∫ (x : ℝ) in Ω, (h x)

        unfold h

        have h_unfold : (λ x ↦ (h x)) = λ x ↦ ((ρ ^ 2) * (deriv B x) ^ 2) := by
        {
            unfold h
            ext x
            rw [mul_pow]
        }

        rw [h_unfold]
        rw [mul_comm]
        rw [integral_const_mul]
    }

    rw [h_eq]

    have g_eq : -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) = -∫ (x : ℝ) in Ω, (g x)
    := by
    {
        let g := λ x ↦ ρ * (deriv I x * deriv B x) * 2

        change -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) = -∫ (x : ℝ) in Ω, (g x)

        have g_unfold : (λ x ↦ (g x)) = λ x ↦ 2 * ρ * (deriv I x * deriv B x) := by
        {
            unfold g
            ext x
            ring
        }

        rw [g_unfold]
        rw [integral_const_mul]
        ring
    }

    rw [g_eq]

    let F := ∫ (x : ℝ) in Ω, f x
    let G := ∫ (x : ℝ) in Ω, g x
    let H := ∫ (x : ℝ) in Ω, h x

    change F - G + H = H - G + F
    ring
}

theorem edginess_polynomial_eq_nd {n : ℕ}
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable_ND I B lower upper Ω ) )
:
    ∀ ρ : ℝ, edginess_ND I B lower upper Ω ρ = edginess_polynomial_ND I B lower upper Ω ρ
:= by
{
    unfold edginess_ND edginess_polynomial_ND
    intro ρ
    unfold quadratic
    unfold a_coef_nd b_coef_nd c_coef_nd
    ring_nf

    rw [(deriv_distributes_over_sub_within_integral_nd I B lower upper Ω hM hI hB ρ hΩ_open )]
    rw [(expand_squared_term_nd I B lower upper Ω hM hI hB ρ hΩ_open )]

    ring_nf
    simp_all only [smul_eq_mul, Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat, mul_neg]

    -- ‖ fderiv ℝ I x ‖ ^ 2
    -- (fderiv ℝ I x) • (fderiv ℝ I x)

    have rest_lemma :
        ∫ (x : (Fin n → ℝ)) in Ω, ( ‖fderiv ℝ I x‖ ^ 2 ) - ρ * (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) * 2 + (ρ * ‖fderiv ℝ B x‖) ^ 2 = (∫ (x : (Fin n → ℝ)) in Ω, ‖fderiv ℝ B x‖ ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : (Fin n → ℝ)) in Ω, ∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1))) + (∫ (x : (Fin n → ℝ)) in Ω, (‖fderiv ℝ I x‖) ^ 2)
    := by
    {
        rw [ ( integral_distributes_over_addition_nd I B lower upper Ω ρ h_edgable) ]
    }

    apply rest_lemma
}



lemma rho_opt_eq_minimizer_point_ND {n : ℕ}
  (I B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
  (hB_nonzero : ∫ x in Ω, (‖fderiv ℝ B x‖)^2 > 0)
:
    ρ_opt_nd I B lower upper Ω = quadratic_minimizer_point (a_coef_nd B lower upper Ω) (b_coef_nd I B lower upper Ω)
:= by
{
    unfold ρ_opt_nd quadratic_minimizer_point a_coef_nd b_coef_nd
    field_simp [hB_nonzero]
    ring_nf
}



theorem minimized_edginess_ND
    {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hB_nonzero : ∫ x in Ω, ‖fderiv ℝ B x‖^2 > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable_ND I B lower upper Ω ) )
:
    edginess_ND I B lower upper Ω (ρ_opt_nd I B lower upper Ω) = quadratic_minimum (a_coef_nd B lower upper Ω) (b_coef_nd I B lower upper Ω) (c_coef_nd I lower upper Ω)
:= by
{
    rw [(edginess_polynomial_eq_nd I B lower upper Ω hM hI hB hΩ h_edgable)]
    unfold edginess_polynomial_ND
    unfold quadratic_minimum
    rw [(rho_opt_eq_minimizer_point_ND I B lower upper Ω hB_nonzero)]
}



theorem edginess_is_quadratic_nd {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable_ND I B lower upper Ω ) )
:
    ∀ (ρ : ℝ), edginess_ND I B lower upper Ω ρ = (quadratic (a_coef_nd B lower upper Ω) (b_coef_nd I B lower upper Ω) (c_coef_nd I lower upper Ω) ρ)
:= by
{
    intro ρ
    rw [(edginess_polynomial_eq_nd I B lower upper Ω hM hI hB hΩ_open h_edgable)]
    unfold edginess_polynomial_ND
    rfl
}

theorem edginess_minimisation_theorem_ND
  {n : ℕ}
  (I B : (Fin n → ℝ) → ℝ)
  (lower upper : (Fin n → ℝ))
  (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
  (hM : MeasurableSet Ω)
  (hB_nonzero : ∫ x in Ω, ‖fderiv ℝ B x‖^2 > 0)
  (hI : DifferentiableOn ℝ I Ω)
  (hB : DifferentiableOn ℝ B Ω)
  (hΩ : IsOpen Ω)
  (h_edgable : image_and_background_are_edgable_ND I B lower upper Ω)
:
    ∀ (ρ : ℝ), edginess_ND I B lower upper Ω (ρ_opt_nd I B lower upper Ω) ≤ edginess_ND I B lower upper Ω ρ
:= by
{
    let lhs := edginess_ND I B lower upper Ω (ρ_opt_nd I B lower upper Ω)
    change ∀ (ρ : ℝ), lhs ≤ edginess_ND I B lower upper Ω ρ

    have ha_pos : 0 < a_coef_nd B lower upper Ω := by
      unfold a_coef_nd
      exact hB_nonzero

    have h_lhs_eq_min : lhs = quadratic_minimum (a_coef_nd B lower upper Ω) (b_coef_nd I B lower upper Ω) (c_coef_nd I lower upper Ω) := by
    {
        apply (minimized_edginess_ND I B lower upper Ω hM hB_nonzero hI hB hΩ h_edgable)
    }

    intro ρ
    rw [(edginess_is_quadratic_nd I B lower upper Ω hM hI hB hΩ h_edgable)]
    rw [h_lhs_eq_min]
    apply quadratic_minimizer (a_coef_nd B lower upper Ω) (b_coef_nd I B lower upper Ω) (c_coef_nd I lower upper Ω) ha_pos
}
