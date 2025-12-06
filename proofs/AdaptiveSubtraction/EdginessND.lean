import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Data.Finset.Basic

import AdaptiveSubtraction.Edginess

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace

open scoped BigOperators

-- Rename Hypercube
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


/-

noncomputable def grad {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  λ i ↦ fderiv ℝ f x (Pi.single i 1)

noncomputable def gradNorm {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ‖grad f x‖
-/

/-
example {n : ℕ} (I B : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ℝ :=
  inner (grad I x) (grad B x)
-/

/-
example (n : ℕ) (x : Fin n → ℝ) :
    --‖x‖ = Real.sqrt (∑ i, (x i)^2 ) := by
    (Norm.norm x) = Real.sqrt (∑ i, (x i)^2 ) := by
    {
        unfold Norm.norm
        trace_state

    }
-/

/-
classical
    have hx : ∀ i, x (Pi.single i 1) = x.toContinuousLinearMap.restrictScalars ℝ (Pi.single i 1) := by intro i; rfl

    funext
    trace_state
  -- Now the left-hand side is exactly the ℓ² norm of the coordinate vector
    --simpa [Real.normSq_eq_real_inner, EuclideanSpace.norm_sq_eq_sum_sq]

-/

-- ‖T‖₂

/-
lemma expand_squared_term_nd_euclid {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖ (fderiv ℝ I x) - ρ • (fderiv ℝ B x ) ‖₂^2 =
    ∫ x in Ω, ‖ (fderiv ℝ I x) ‖₂^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • ‖ (fderiv ℝ B x) ‖₂^2
:= by
{
    sorry
}-/


/-(lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := Ioo_nd n lower upper)
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    -/


/-
lemma expand_squared_term_nd {n : ℕ }
    (I B : (Fin n → ℝ) → ℝ)
    --(I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : (Fin n → ℝ))
    (Ω : Set (Fin n → ℝ) := (Ioo_nd n lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
    --(e : (Fin n → ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
:
--    ∫ x in Ω, (Norm.norm ((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) ))^2 =
--    ∫ x in Ω, (Norm.norm (fderiv ℝ I x) )^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • (Norm.norm (fderiv ℝ B x) )^2

    ∫ x in Ω, ‖fderiv ℝ I x - ρ • fderiv ℝ B x‖^2 =
    ∫ x in Ω, ‖fderiv ℝ I x‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (Pi.single i 1) * (fderiv ℝ B x) (Pi.single i 1)) + (ρ^2) • ‖fderiv ℝ B x‖^2
--    ∫ x in Ω, ‖fderiv ℝ I x - ρ • fderiv ℝ B x‖^2 =
--    ∫ x in Ω, ‖fderiv ℝ I x‖^2 - 2 • ρ • ⟪ fderiv ℝ I x , fderiv ℝ B x⟫   + (ρ^2) • ‖fderiv ℝ B x‖^2


    --∫ x in Ω, ‖grad I x - ρ • grad B x‖^2 =
    --∫ x in Ω, ‖grad I x‖^2 - 2 • ρ • (∑ i, (grad I x) (Pi.single i 1) * (grad B x) (Pi.single i 1)) + (ρ^2) • ‖grad B x‖^2

    --∫ x in Ω, ‖grad I x - ρ • grad B x‖^2 = ∫ x in Ω, ‖grad I x‖^2 - 2 • ρ • (inner (grad I x) (grad B x)) + (ρ^2) • ‖grad B x‖^2
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
    #check Norm (Fin n → ℝ)

    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) * 2 + ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2
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


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u) (Pi.single i 1) • (fderiv ℝ B x) (Pi.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term ρ u B x) • 2 + ‖v‖ ^ 2

    trace_state
    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (Pi.single i 1) • v (Pi.single i 1)) • 2 + ‖v‖ ^ 2
    trace_state

    --change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - ⟪u, v⟫_ℝ  • 2 + ‖v‖ ^ 2

    --let E := ((Fin n → ℝ) →L[ℝ] ℝ)  -- ≃ₗᵢ[ℝ] (Fin n → ℝ)
                -- re ⟪x, x⟫
                --rw [←inner_self_eq_norm_sq]

    have h_1 : InnerProductSpace ℝ ((Fin n → ℝ) →L[ℝ] ℝ) := by
        refine
        {
            inner               := λ x y ↦ (∑ i, x (Pi.single i 1) • y (Pi.single i 1))
            --inner               := λ x y ↦ ⟪x, y⟫_ℝ
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, x (Pi.single i 1) • x (Pi.single i 1))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, x (Pi.single i 1) • x (Pi.single i 1))
                --unfold norm
                trace_state
                sorry
            }
            conj_inner_symm     := sorry
            add_left            := sorry
            smul_left           := sorry

        }





    trace_state
    rw [(norm_sub_sq_real) ]

    simp
    ring_nf


    let a := (∑ x, u (Pi.single x 1) * v (Pi.single x 1))
    let b := ⟪u, v⟫_ℝ

    change b * 2 = a * 2


    have h₂ : (2 : ℝ) ≠ 0 := by norm_num

    rw [←mul_right_inj' (by norm_num : (1/2 : ℝ) ≠ 0)]
    trace_state
    ring_nf
    trace_state

    unfold a b


    change (inner ℝ u v ) = ∑ x, u (Pi.single x 1) * v (Pi.single x 1)

    unfold inner


    trace_state

}
-/



def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


example (x : EuclideanSpace ℝ (Fin 3)) : ‖x‖ = Real.sqrt (∑ i, (x i)^2) := by
{
    simp only [Norm.norm, Real.sqrt_eq_rpow]
    simp only
    [
        OfNat.ofNat_ne_zero,
        ↓reduceIte,
        ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat,
        rpow_ofNat,
        sq_abs,
        one_div
    ]
}


noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1))


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ

-- set_option diagnostics true

--  EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
noncomputable def grad {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n)) := (fderiv ℝ f x)



lemma expand_squared_term_nd {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((fderiv ℝ I x) - ρ • (fderiv ℝ B x ) )‖^2 =
    --∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • ⟪fderiv ℝ I x, fderiv ℝ B x⟫_ℝ + (ρ^2) • ‖(fderiv ℝ B x)‖^2

    ∫ x in Ω, ‖(fderiv ℝ I x)‖^2 - 2 • ρ • (∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) * (fderiv ℝ B x) (EuclideanSpace.single i 1)) + (ρ^2) • ‖(fderiv ℝ B x)‖^2
:= by
{

    let f := λ x ↦ (I x)
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
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
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


    let u := fderiv ℝ I x
    let v := ρ • fderiv ℝ B x

    have v_sq_h : ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (fderiv ℝ I x) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) * 2 + ρ ^ 2 • ‖(fderiv ℝ B x)‖ ^ 2
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
        (u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (x : EuclideanSpace ℝ (Fin n))
    :
        (inner_prod_2ab_term_euclidean ρ u B x) = (∑ i, (u) (EuclideanSpace.single i 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single i 1))
    := by
    {
        unfold inner_prod_2ab_term_euclidean
        trace_state
        rw [Finset.smul_sum]

        change ∑ (x_1 : Fin n), ρ • u (EuclideanSpace.single x_1 1) • (fderiv ℝ B x) (EuclideanSpace.single x_1 1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        let c (x_1 : Fin n ) := (fderiv ℝ B x) (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • u (EuclideanSpace.single x_1 1) • (c x_1) = ∑ x_1, u (EuclideanSpace.single x_1 1) • ρ • (c x_1)

        let d (x_1 : Fin n ) := u (EuclideanSpace.single x_1 1)

        change ∑ x_1, ρ • (d x_1) • (c x_1) = ∑ x_1, (d x_1) • ρ • (c x_1)

        rw [Finset.sum_congr]
        rfl

        intro x h

        let d_ : ℝ := (d x)
        let c_ : ℝ := (c x)

        change ρ • d_ • c_ = d_ • ρ • c_
        rw [smul_comm]
    }


    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ∑ i, (u) (EuclideanSpace.single i 1) • (fderiv ℝ B x) (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2
    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (inner_prod_2ab_term_euclidean ρ u B x) • 2 + ‖v‖ ^ 2

    trace_state
    rw [(h_ρ_factor ρ u B x)]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    have h_inner_prod_space : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    {
        refine
        {
            inner               := λ x y ↦ (∑ i, x (EuclideanSpace.single i 1) • y (EuclideanSpace.single i 1))
            --inner               := λ x y ↦ ⟪x, y⟫_ℝ
            norm_sq_eq_re_inner := by
            {
                intro x
                change ‖x‖ ^ 2 = RCLike.re (∑ i, x (EuclideanSpace.single i 1) • x (EuclideanSpace.single i 1))

                rw [pow_two]

                change ‖x‖ * ‖x‖ = RCLike.re (∑ i, x (EuclideanSpace.single i 1) • x (EuclideanSpace.single i 1))
                -- unfold norm
                simp only [Norm.norm]


                --simp_all only [smul_eq_mul, ContinuousLinearMap.fderiv, ae_restrict_eq, implies_true, map_sum,
                --  RCLike.mul_re, RCLike.re_to_real, RCLike.im_to_real, mul_zero, sub_zero, v]

                --rw [inner_self_eq_sum]

                trace_state
            }
            conj_inner_symm     := sorry
            add_left            := sorry
            smul_left           := sorry

        }
    }


    rw [(norm_sub_sq_real) ]

    trace_state

    change ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 = ‖u‖ ^ 2 - (∑ i, u (EuclideanSpace.single i 1) • v (EuclideanSpace.single i 1)) • 2 + ‖v‖ ^ 2

    abel

    trace_state
    --unfold Norm.norm
    --unfold inner
    trace_state


}
