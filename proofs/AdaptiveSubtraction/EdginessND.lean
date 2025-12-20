import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

import AdaptiveSubtraction.Quadratics

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace

open scoped BigOperators


notation "∇" => gradient


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


/-
\begin{definition}[Image and Background Are Edgable]
Let $n \in \mathbb{N}$, and let
\[
I,\, B : \mathbb{R}^n \to \mathbb{R}
\]
be scalar fields on Euclidean space.
For lower and upper bounds
\[
\mathrm{lower},\, \mathrm{upper} \in \mathbb{R}^n,
\]
let
\[
\Omega := \mathrm{hypercube}(\mathrm{lower},\, \mathrm{upper}) \subseteq \mathbb{R}^n .
\]

Define the functions
\[
f(x) := \langle \nabla I(x),\, \nabla I(x) \rangle,
\qquad
g(x) := \langle \nabla I(x),\, \nabla B(x) \rangle,
\qquad
h(x) := \langle \nabla B(x),\, \nabla B(x) \rangle .
\]

We say that the \emph{image and background are edgable} if
\[
\text{$f$ is integrable on $\Omega$} \;\wedge\;
\text{$g$ is integrable on $\Omega$} \;\wedge\;
\text{$h$ is integrable on $\Omega$},
\]
that is,
\[
f,\, g,\, h \in L^1(\Omega,\, \mathrm{d}x).
\]
\end{definition}
-/
def image_and_background_are_edgable
    {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
: Prop :=
    let f := λ x ↦ ⟪∇ I x, ∇ I x⟫_ℝ
    let g := λ x ↦ ⟪∇ I x, ∇ B x⟫_ℝ
    let h := λ x ↦ ⟪∇ B x, ∇ B x⟫_ℝ
    Integrable f (volume.restrict Ω) ∧ Integrable g (volume.restrict Ω) ∧ Integrable h (volume.restrict Ω)


noncomputable def edginess
    {n}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ) : ℝ
:=
    ∫ x in Ω, ‖∇ (λ x => I x - ρ • B x) x‖^2


noncomputable def ρ_opt {n : ℕ}
  (I B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
: ℝ :=
    ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ / ∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ


noncomputable def c_coef {n : ℕ}
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper)) : ℝ
:=
    ∫ x in Ω, ⟪∇ I x, ∇ I x⟫_ℝ


noncomputable def b_coef {n : ℕ}
  (I B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper)) : ℝ
:=
    - 2 • ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ


noncomputable def a_coef {n : ℕ}
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper :  EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper)) : ℝ
:=
    ∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ


noncomputable def edginess_polynomial {n : ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ)
: ℝ :=
    (quadratic (a_coef B lower upper Ω ) (b_coef I B lower upper Ω ) (c_coef I lower upper Ω) ρ )


lemma scalar_mul_differentiable_within {n : ℕ }
  (B : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (ρ : ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hB : DifferentiableOn ℝ B Ω)
  (hx : x ∈ Ω)
: DifferentiableWithinAt ℝ (λ x ↦ ρ • B x) Ω x  := DifferentiableWithinAt.const_smul (hB x hx) ρ



lemma grad_const_mul
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hB :  DifferentiableAt ℝ B a)
:
    ∇ (fun x => ρ • B x) a = ρ • (∇ B a)
:= by
{
    simp only [gradient]

    let f := λ x ↦ (B x)
    have hf :  DifferentiableAt ℝ f a := by
    {
        unfold f
        fun_prop
    }

    change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x => ρ • (f x)) a) =
  ρ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f a)

    have hhf : (fderiv ℝ (fun x => ρ • (f x)) a) = ρ • (fderiv ℝ f a) := by
    {
        rw [← (fderiv_const_smul hf ρ)]
        rfl
    }

    simp only [hhf]
    simp_all only [smul_eq_mul, map_smul, f]
}


lemma grad_f_sub_g
    {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : EuclideanSpace ℝ (Fin n))
    (hf :  DifferentiableAt ℝ f a)
    (hg :  DifferentiableAt ℝ g a)
:
    ∇ (f - g) a = ∇ f a - ∇ g a
:= by
{
    simp only [gradient]
    rw [fderiv_sub hf hg]
    simp_all only [map_sub]
}


lemma deriv_distributes_over_sub_within_integral {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω  : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM : MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ  : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖∇ (λ x ↦ I x - ρ • B x) x‖^2 =
    ∫ x in Ω, ‖(λ x ↦ ∇ I x - ρ • ∇ B x) x‖^2
:= by
{
    let f := I
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (∇ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        ∇ (λ x ↦ I x - ρ • B x) x = ∇ I x - ρ • ∇ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change ∇ (λ x => f x - g x) a = (λ x ↦ (∇ f x ) - ρ • (∇ B x) ) a

        change ∇ (λ x => f x - g x) a = (λ x ↦ (∇ f x ) - (gg x) ) a

        have ρBh : (∇ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [f, g]

            unfold gradient

            let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            change R (fderiv ℝ (fun x ↦ ρ • B x) a) = ρ • R (fderiv ℝ B a)

            have hhf : (fderiv ℝ (fun x => ρ • (B x)) a) = ρ • (fderiv ℝ B a) := by
            {
                rw [← (fderiv_const_smul hB' ρ)]
                rfl
            }

            simp only [hhf]
            simp_all only [smul_eq_mul, differentiableAt_const, DifferentiableAt.fun_mul, map_smul, R]
        }
        simp only [←ρBh]
        change ∇ (f - g ) a = (∇ f a) - (∇ g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    simp only [hx]
}


lemma expand_squared_term {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (ρ : ℝ)
    (hΩ_open : IsOpen Ω)
:
    ∫ x in Ω, ‖((∇ I x) - ρ • (∇ B x ) )‖^2 =
    ∫ x in Ω, ‖∇ I x‖^2 - 2 • ρ • ⟪∇ I x , ∇ B x⟫_ℝ + (ρ^2) • ‖∇ B x‖^2
:= by
{

    let f := λ x ↦ (I x)
    let g := λ x ↦ ρ • B x
    let gg := λ x ↦ ρ • (∇ B x)

    apply integral_congr_ae

    have h_deriv_eq
    :
        ∀ᵐ x ∂(volume.restrict Ω),
        ∇ (λ x ↦ I x - ρ • B x) x = ∇ I x - ρ • ∇ B x
    := by
    {
        filter_upwards [self_mem_ae_restrict hM] with a hΩ

        have hn : Ω ∈ 𝓝 a := hΩ_open.mem_nhds hΩ
        have hf : DifferentiableWithinAt ℝ f Ω a := hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within B lower upper Ω ρ a hB hΩ
        have hf' : DifferentiableAt ℝ f a := hf.differentiableAt hn
        have hg' : DifferentiableAt ℝ g a := hg.differentiableAt hn
        have hB' : DifferentiableAt ℝ B a := (hB a hΩ).differentiableAt hn

        change ∇ (λ x ↦ f x - g x) a = (λ x ↦ (∇ f x ) - ρ • (∇ B x) ) a

        change ∇ (λ x ↦ f x - g x) a = (λ x ↦ (∇ f x ) - (gg x) ) a

        have ρBh : (∇ g a) = gg a := by
        {
            unfold gg
            unfold g
            simp_all only [smul_eq_mul, f, g]
            simp only [← smul_eq_mul]
            simp only [(grad_const_mul B ρ a hB')]
        }
        simp only [←ρBh]

        change ∇ (f - g ) a = (∇ f a) - (∇ g a)

        apply (grad_f_sub_g f g a hf' hg')
    }

    filter_upwards [h_deriv_eq] with x hx
    ring_nf
    simp only [smul_eq_mul]
    ring_nf


    let u := ∇ I x
    let v := ρ • ∇ B x

    have v_sq_h : ρ ^ 2 • ‖(∇ B x)‖ ^ 2 = ‖v‖ ^ 2 := by
    {
        unfold v
        rw [norm_smul]
        simp_all only [smul_eq_mul, ae_restrict_eq, Real.norm_eq_abs]
        rw [mul_pow]
        simp_all only [sq_abs]
    }

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) * 2 + ρ ^ 2 • ‖(∇ B x)‖ ^ 2
    rw [v_sq_h]

    change ‖(u - v)‖ ^ 2 = ‖u‖ ^ 2 - (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) • 2 + ‖v‖ ^ 2

    have h_inner : (ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ ) = ⟪u, v⟫_ℝ := by
    {
        unfold u v
        simp [inner_smul_right]
    }

    rw [h_inner]
    simp only [norm_sub_sq_real, smul_eq_mul, mul_comm]
}


lemma distribute_integral_fgh {n : ℕ }
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hIf : Integrable f (volume.restrict Ω))
    (hIg : Integrable g (volume.restrict Ω))
    (hIh : Integrable h (volume.restrict Ω))
:
    ∫ x in Ω, (f x) - (g x) + (h x) = (∫ x in Ω, (f x)) - (∫ x in Ω, (g x)) + ∫ x in Ω, (h x)
:= by
{
    let ff := λ x ↦ (f x) - (g x)

    have hIff : Integrable ff (volume.restrict Ω) := by
    {
        dsimp [ff]
        exact hIf.sub hIg
    }

    change ∫ x in Ω, (ff x) + (h x) = (∫ x in Ω, (f x)) - (∫ x in Ω, (g x)) + ∫ x in Ω, (h x)

    rw [(integral_add hIff hIh)]

    unfold ff
    rw [(integral_sub hIf hIg)]
}


noncomputable def I_Squared_Term
    {n:ℕ} (I : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    ⟪ ∇ I x, ∇ I x ⟫_ℝ


noncomputable def IB_Squared_Term_Norm
    {n:ℕ} (I : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    ‖∇ I x‖ ^ 2

noncomputable def B_Squared_Term_Norm
    {n:ℕ} (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (ρ : ℝ )
:=
    ρ ^ 2 * ‖∇ B x‖ ^ 2


noncomputable def IB_Term
    {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (ρ : ℝ)
:=
    ρ * ⟪ ∇ I x, ∇ B x ⟫_ℝ * 2


noncomputable def B_Squared_Term
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (ρ : ℝ)
:=
    (ρ^2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ



noncomputable def Int_I_Squared_Term{n : ℕ}
    (I : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    ∫ x in Ω, ⟪ ∇ I x, ∇ I x ⟫_ℝ



noncomputable def Int_IB_Term {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    (ρ * (2 * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ ))


noncomputable def Int_B_Squared_Term{n:ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    (∫ x in Ω, ⟪ ∇ B x, ∇ B x ⟫_ℝ) * ρ ^ 2


noncomputable def Int_B_Squared_Term_ρ{n:ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    ρ ^ 2 * ∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ

noncomputable def Int_IB_inner_Term_2{n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:=
    (ρ * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ) * 2


lemma integral_distributes_over_addition {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ))
:
    ∫ x in Ω, ( (I_Squared_Term I x) - (IB_Term I B x ρ ) + (B_Squared_Term B x ρ) ) =  (Int_B_Squared_Term B ρ lower upper Ω) - (Int_IB_Term I B ρ lower upper Ω) + (Int_I_Squared_Term I lower upper Ω)
:= by
{
    let f := λ x ↦ ⟪ ∇ I x, ∇ I x ⟫_ℝ
    let g := λ x ↦ ρ * ⟪ ∇ I x, ∇ B x ⟫_ℝ * 2
    let h := λ x ↦ (ρ ^ 2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ

    unfold I_Squared_Term IB_Term B_Squared_Term Int_B_Squared_Term Int_IB_Term Int_I_Squared_Term

    change ∫ x in Ω, (f x) - (g x) + (ρ ^ 2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ = (∫ x in Ω, ⟪ ∇ B x, ∇ B x ⟫_ℝ) * ρ ^ 2 + -(ρ * (2 * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ)) + (∫ x in Ω, ⟪ ∇ I x, ∇ I x ⟫_ℝ)

    change ∫ x in Ω, (f x) - (g x) + (h x) = (∫ x in Ω, ⟪ ∇ B x, ∇ B x ⟫_ℝ) * ρ ^ 2 + -(ρ * (2 * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ)) + (∫ x in Ω, ⟪ ∇ I x, ∇ I x ⟫_ℝ)

    rcases h_edgable with ⟨hIf, hIg, hIh⟩

    have hIg_scaled: Integrable g (volume.restrict Ω) := by
    {
        unfold g
        let fx := λ x ↦ ⟪ ∇ I x, ∇ B x ⟫_ℝ
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
        let fx := λ x ↦ ⟪ ∇ I x, ∇ B x ⟫_ℝ
        let Ρ : ℝ := ρ ^ 2
        change Integrable (fun x ↦ (ρ^2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ) (volume.restrict Ω)
        apply Integrable.const_mul
        exact hIh
    }

    rw [(distribute_integral_fgh f g h lower upper Ω hIf hIg_scaled hIh_scaled)]

    have f_eq : (∫ x in Ω, ⟪ ∇ I x, ∇ I x ⟫_ℝ) = ∫ x in Ω, (f x)
    := by
    {
        rfl
    }

    rw [f_eq]

    have h_eq : (∫ x in Ω, ⟪ ∇ B x, ∇ B x ⟫_ℝ) * ρ ^ 2 = ∫ x in Ω, (h x)
    := by
    {
        let h := λ x ↦ (ρ^2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ

        change (∫ x in Ω, ⟪ ∇ B x, ∇ B x ⟫_ℝ) * ρ ^ 2 = ∫ x in Ω, (h x)

        unfold h

        have h_unfold : (λ x ↦ (h x)) = λ x ↦ ((ρ ^ 2) * ⟪ ∇ B x, ∇ B x ⟫_ℝ) := by
        {
            unfold h
            ext x
            ring
        }

        rw [h_unfold]
        rw [mul_comm]
        rw [integral_const_mul]
    }

    rw [h_eq]

    have g_eq : -(ρ * (2 * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ)) = -∫ x in Ω, (g x)
    := by
    {
        let g := λ x ↦ ρ * (⟪ ∇ I x, ∇ B x ⟫_ℝ) * 2

        change -(ρ * (2 * ∫ x in Ω, ⟪ ∇ I x, ∇ B x ⟫_ℝ)) = -∫ x in Ω, (g x)

        have g_unfold : (λ x ↦ (g x)) = λ x ↦ 2 * ρ * ⟪ ∇ I x, ∇ B x ⟫_ℝ := by
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

    let F := ∫ x in Ω, f x
    let G := ∫ x in Ω, g x
    let H := ∫ x in Ω, h x

    change F - G + H = H - G + F
    ring
}


noncomputable def IB_Inner
    {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    ⟪ ∇ I x, ∇ B x ⟫_ℝ


lemma inner_prod_eq_norm_lemma_2
    {n: ℕ }
    (I : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n) )
:
    (I_Squared_Term I x) = (IB_Squared_Term_Norm I x)
:= by
{
    unfold I_Squared_Term IB_Squared_Term_Norm
    exact real_inner_self_eq_norm_sq (∇ I x)
}


lemma B_inner_prod_eq_norm_lemma
    {n: ℕ }
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n) )
    (ρ : ℝ)
:
    (B_Squared_Term_Norm B x ρ ) = (B_Squared_Term B x ρ)
:= by
{
    unfold B_Squared_Term_Norm B_Squared_Term
    ring_nf

    rw [mul_eq_mul_left_iff]
    left
    simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
}


lemma swap_terms
    {n: ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ)
:
    -Int_IB_inner_Term_2 I B ρ lower upper Ω + Int_B_Squared_Term_ρ B ρ lower upper Ω  = Int_B_Squared_Term_ρ B ρ lower upper Ω - Int_IB_inner_Term_2 I B ρ lower upper Ω
:= by
{
    simp only [add_comm, sub_eq_add_neg]
}

lemma swap_terms_2
    {n: ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ)
:
    Int_IB_inner_Term_2 I B ρ lower upper Ω = (Int_IB_Term I B ρ lower upper Ω)
:= by
{
    unfold Int_IB_inner_Term_2 Int_IB_Term
    ring
}

lemma swap_terms_3
    {n: ℕ }
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (ρ : ℝ)
:
    Int_B_Squared_Term_ρ B ρ lower upper Ω = Int_B_Squared_Term B ρ lower upper Ω
:= by
{
    unfold Int_B_Squared_Term_ρ Int_B_Squared_Term
    ring
}


theorem edginess_polynomial_eq
    {n : ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    ∀ ρ : ℝ, edginess I B lower upper Ω ρ = edginess_polynomial I B lower upper Ω ρ
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
    simp_all only [smul_eq_mul ]

    change ∫ x in Ω, ‖∇ I x‖ ^ 2 - ρ * ⟪∇ I x, ∇ B x⟫_ℝ * 2 + ρ ^ 2 * ‖∇ B x‖ ^ 2 = (-((ρ * ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ) * 2) + ρ ^ 2 * ∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ) + ∫ x in Ω, ⟪∇ I x, ∇ I x⟫_ℝ

    change ∫ x in Ω, (IB_Squared_Term_Norm I x) - (IB_Term I B x ρ ) + (B_Squared_Term_Norm B x ρ) = (-((Int_IB_inner_Term_2 I B ρ lower upper Ω) ) + (Int_B_Squared_Term_ρ B ρ lower upper Ω) ) + (Int_I_Squared_Term I lower upper Ω)

    ring_nf

    change ∫ x in Ω, ( IB_Squared_Term_Norm I x - IB_Term I B x ρ + B_Squared_Term_Norm B x ρ) = -(Int_IB_inner_Term_2 I B ρ lower upper Ω) + (Int_B_Squared_Term_ρ B ρ lower upper Ω) + (Int_I_Squared_Term I lower upper Ω)

    simp only [← inner_prod_eq_norm_lemma_2]

    simp only [B_inner_prod_eq_norm_lemma]

    simp only [swap_terms]

    simp only [swap_terms_2]

    rw [(swap_terms_3 B lower upper Ω ρ )]

    rw [ (integral_distributes_over_addition I B lower upper Ω ρ h_edgable) ]
}



theorem edginess_is_quadratic
    {n : ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ_open : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    ∀ (ρ : ℝ), edginess I B lower upper Ω ρ = (quadratic (a_coef B lower upper Ω) (b_coef I B lower upper Ω) (c_coef I lower upper Ω) ρ)
:= by
{
    intro ρ
    rw [(edginess_polynomial_eq I B lower upper Ω hM hI hB hΩ_open h_edgable)]
    unfold edginess_polynomial
    rfl
}

lemma factor_BB
    {n : ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (BB : ℝ )
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:
    (∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ • BB⁻¹) = BB⁻¹ • (∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ )
:= by
{
    let IBB : ℝ := BB⁻¹
    let f := λ x ↦ ⟪∇ I x, ∇ B x⟫_ℝ
    change (∫ x in Ω, (f x) • IBB) = IBB • ((∫ x in Ω, (f x)) )
    simp_all only [smul_eq_mul]
    rw [integral_mul_const, mul_comm]
}

lemma rho_opt_eq_minimizer_point
    {n : ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hB_nonzero : ∫ x in Ω, ⟪ ∇ B x, ∇ B x⟫_ℝ > 0)
:
    ρ_opt I B lower upper Ω = quadratic_minimizer_point (a_coef B lower upper Ω) (b_coef I B lower upper Ω)
:= by
{
    unfold ρ_opt quadratic_minimizer_point a_coef b_coef
    field_simp [hB_nonzero]
    ring_nf

    change  ((∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ)) * (∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ * (∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ)⁻¹) * 2 = (∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ) * 2
    ring_nf
    simp_all only [gt_iff_lt, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false]

    set BB := (∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ) with hBB

    set IB : ℝ := ∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, ⟪∇ I x, ∇ B x⟫_ℝ with hIB
    change (∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ) * ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ * (∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ)⁻¹ = ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ
    change BB * ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ * BB⁻¹ = ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ

    change BB * ∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ * BB⁻¹ = IB

    have hBBne : BB ≠ 0 := ne_of_gt hB_nonzero

    change BB * (∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ * BB⁻¹) = IB

    change BB • (∫ x in Ω, ⟪∇ I x, ∇ B x⟫_ℝ • BB⁻¹) = IB
    simp only [(factor_BB I B BB lower upper Ω )]

    change BB • BB⁻¹ • IB = IB

    simp_all only [ne_eq, smul_eq_mul, not_false_eq_true, mul_inv_cancel_left₀, BB, IB]
}



theorem minimized_edginess
    {n: ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hB_nonzero : ∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    edginess I B lower upper Ω (ρ_opt I B lower upper Ω) = quadratic_minimum (a_coef B lower upper Ω) (b_coef I B lower upper Ω) (c_coef I lower upper Ω)
:= by
{
    rw [(edginess_polynomial_eq I B lower upper Ω hM hI hB hΩ h_edgable)]
    unfold edginess_polynomial
    unfold quadratic_minimum
    rw [(rho_opt_eq_minimizer_point I B lower upper Ω hB_nonzero)]
}



theorem edginess_minimisation_theorem
    {n: ℕ }
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hM: MeasurableSet Ω)
    (hB_nonzero :  ∫ x in Ω, ⟪∇ B x, ∇ B x⟫_ℝ > 0)
    (hI : DifferentiableOn ℝ I Ω)
    (hB : DifferentiableOn ℝ B Ω)
    (hΩ : IsOpen Ω)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ) )
:
    ∀ (ρ : ℝ), edginess I B lower upper Ω (ρ_opt I B lower upper Ω) ≤ edginess I B lower upper Ω ρ := by
{
    let lhs := edginess I B lower upper Ω (ρ_opt I B lower upper Ω)
    change ∀ (ρ : ℝ), lhs ≤ edginess I B lower upper Ω ρ

    have ha_pos : 0 < a_coef B lower upper Ω := by
      unfold a_coef
      exact hB_nonzero

    have h_lhs_eq_min : lhs = quadratic_minimum (a_coef B lower upper Ω) (b_coef I B lower upper Ω) (c_coef I lower upper Ω) := by
    {
        apply (minimized_edginess I B lower upper Ω hM hB_nonzero hI hB hΩ h_edgable)
    }

    intro ρ
    rw [(edginess_is_quadratic I B lower upper Ω hM hI hB hΩ h_edgable)]
    rw [h_lhs_eq_min]
    apply quadratic_minimizer (a_coef B lower upper Ω) (b_coef I B lower upper Ω) (c_coef I lower upper Ω) ha_pos
}
