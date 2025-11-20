import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Data.Finset.Basic

import AdaptiveSubtraction.Edginess

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace


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
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
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

/-
def inner_prod
    {n : ℕ}
    ( u v : (Fin n → ℝ) →L[ℝ] ℝ)
:= ∑ i, (u) (Pi.single i 1) * (v) (Pi.single i 1)


variable {n : ℕ}
variable (x y : Fin n → ℝ)


--(inner x y)
-- ⟪x, y⟫

-- https://leanprover-community.github.io/mathlib_docs/analysis/inner_product_space/basic.html#norm_sub_sq
-- norm_sub_sq

example : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ( inner x y ) := by
{
    apply norm_sub_sq
}


lemma vec_formula
    (n : ℕ)
    ( u v : (Fin n → ℝ) →L[ℝ] ℝ)
:
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (2 • ∑ i, (u) (Pi.single i 1) * (v) (Pi.single i 1) ) + ‖v‖ ^ 2
    --‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (2 • (inner_prod u v) ) + ‖v‖ ^ 2
:= by
{
    --rw [←norm_sub_sq_real]
    --let w := u - v
    --change ‖w‖ ^ 2 = ‖u‖ ^ 2 - (2 • ∑ i, (u) (Pi.single i 1) * (v) (Pi.single i 1) )  + ‖v‖ ^ 2
    --rw [←norm_eq_sqrt_re_inner]

    have h_dot_2(w : (Fin n → ℝ) →L[ℝ] ℝ) : ‖w‖ ^ 2 = ∑ i, (w) (Pi.single i 1) * (w) (Pi.single i 1)
    := by
    {
        --unfold DenselyNormedField.toNontriviallyNormedField
        --unfold Real.denselyNormedField
        unfold norm_abs_sub_abs

        trace_state


    }

    trace_state

}

-/

noncomputable def inner_prod_2ab_term
    {n : ℕ}
    (ρ : ℝ)
    (u : (Fin n → ℝ) →L[ℝ] ℝ)
    (B : (Fin n → ℝ) → ℝ)
    (x : (Fin n → ℝ))
:=
    (ρ • ∑ i, (u) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1))


noncomputable def ρ_dot_U
    {n : ℕ }
    (ρ : ℝ )
    (u : (Fin n → ℝ) →L[ℝ] ℝ)
    (i : Fin n )
:= ρ • u (Pi.single i 1)


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
            simp_all only [smul_eq_mul, f, g]
            rw [← fderiv_const_smul]
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
            rfl
            simp_all only [differentiableAt_const, DifferentiableAt.fun_mul]
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
    ring_nf
    trace_state

    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖fderiv ℝ B x‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) * 2 + ρ ^ 2 • ‖fderiv ℝ B x‖ ^ 2
    rw [v_sq_h]

    have h_unorm
        {n : ℕ} (w : (Fin n → ℝ) →L[ℝ] ℝ)
    :
        (norm w) ^ 2 = ‖w‖ ^ 2
    := by
    {
        rfl
    }

    have h_ρ_factor
        (ρ : ℝ)
        (u : (Fin n → ℝ) →L[ℝ] ℝ)
        (B : (Fin n → ℝ) → ℝ)
        (x : Fin n → ℝ)
    :
        (inner_prod_2ab_term ρ u B x) = (∑ i, (u) (Pi.single i 1) • ρ • (fderiv ℝ B x) (Pi.single i 1))
    := by
    {
        unfold inner_prod_2ab_term
        trace_state
        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (Pi.single x_1 1) • (fderiv ℝ B x) (Pi.single x_1 1) = ∑ x_1, u (Pi.single x_1 1) • ρ • (fderiv ℝ B x) (Pi.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (Pi.single x_1 1)

        change ∑ x_1, ρ • u (Pi.single x_1 1) • (c x_1) = ∑ x_1, u (Pi.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (Pi.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖u - v‖ ^ 2 = (norm u) ^ 2 - (ρ • ∑ i, (u) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖u - v‖ ^ 2 = (norm u) ^ 2 - (inner_prod_2ab_term ρ u B x) • 2 + ‖v‖ ^ 2

    trace_state
    rw [(h_ρ_factor ρ u B x)]

    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (Pi.single i 1) • v (Pi.single i 1)) • 2 + ‖v‖ ^ 2


    have h_1 : InnerProductSpace ℝ ((Fin n → ℝ) →L[ℝ] ℝ) := by
    {
        sorry
    }


    rw [(norm_sub_sq_real) ]

    simp
    ring_nf


    let a := (∑ x, u (Pi.single x 1) * v (Pi.single x 1))
    let b := ⟪u, v⟫_ℝ

    change b * 2 = a * 2


    have h₂ : (2 : ℝ) ≠ 0 := by norm_num

    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]

    ring

    unfold a b


    change (inner ℝ u v ) = ∑ x, u (Pi.single x 1) * v (Pi.single x 1)

    unfold inner
    trace_state

}

lemma expand_squared (n : ℕ )( x y : (Fin n → ℝ) →L[ℝ] ℝ ) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * (∑ i, ( x - y ) (Pi.single i 1) • (x - y) (Pi.single i 1)) + ‖y‖ * ‖y‖
:= by
{

    sorry

}
