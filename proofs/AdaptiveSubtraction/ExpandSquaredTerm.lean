import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set Real Filter Topology
open MeasureTheory
open scoped InnerProductSpace
open scoped BigOperators


notation "∇" => gradient


def hypercube {n : ℕ } (w l : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ∀ i, w i < x i ∧ x i < l i}


noncomputable def inner_prod_2ab_term_euclidean
    {n : ℕ}
    (ρ : ℝ)
    (u : EuclideanSpace ℝ (Fin n) )
    (B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
:=
    ρ • ⟪u , (∇ B x) ⟫_ℝ


lemma f_differentiable_within_nd_euclidean {n : ℕ }
  (I : EuclideanSpace ℝ (Fin n) → ℝ)
  (lower upper : EuclideanSpace ℝ (Fin n))
  (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
  (hI : DifferentiableOn ℝ I Ω)
  (x :  EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Ω)
  : DifferentiableWithinAt ℝ (λ x ↦ I x) Ω x := hI x hx


lemma scalar_mul_differentiable_within_nd_euclidean {n : ℕ }
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

/-
\begin{lemma}
Let $n \in \mathbb{N}$,
$I, B : \mathbb{R}^n \to \mathbb{R}$,
let
\[
\Omega = \{x \in \mathbb{R}^n \mid w_i < x_i < \ell_i \text{ for all } i\},
\]
and assume that
$I$ and $B$ are differentiable on $\Omega$,
$\Omega$ is measurable and open,
and $\rho \in \mathbb{R}$.

Then
\[
\int_{\Omega} \left\| \nabla I(x) - \rho \, \nabla B(x) \right\|^2 \, dx
=
\int_{\Omega}
\left(
\|\nabla I(x)\|^2
-
2\rho \, \langle \nabla I(x), \nabla B(x) \rangle
+
\rho^2 \|\nabla B(x)\|^2
\right) dx .
\]

\end{lemma}

-/
lemma expand_squared_term_nd {n : ℕ}
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
    ∫ x in Ω, ‖(∇ I x)‖^2 - 2 • ρ • ⟪(∇ I x ) , (∇ B x )⟫_ℝ + (ρ^2) • ‖(∇ B x)‖^2
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
        have hf : DifferentiableWithinAt ℝ f Ω a := f_differentiable_within_nd_euclidean I lower upper Ω hI a hΩ
        have hg : DifferentiableWithinAt ℝ g Ω a := scalar_mul_differentiable_within_nd_euclidean B lower upper Ω ρ a hB hΩ
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
