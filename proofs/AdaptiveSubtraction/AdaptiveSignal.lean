import AdaptiveSubtraction.Edginess

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure

open Set
open MeasureTheory
open InnerProductSpace
open scoped InnerProductSpace
open scoped Topology Filter

/-
https://proofassistants.stackexchange.com/a/6555/6134

https://proofassistants.stackexchange.com/a/5397/6134

https://proofassistants.stackexchange.com/a/5158/6134

-/

def G_0
    {n:ℕ}
    (τ : ℝ) --radius
:
    Set (EuclideanSpace ℝ (Fin n))
:=
    { p | ∀ i, |p i| ≤ τ }


def G
    {n:ℕ}
    (x : EuclideanSpace ℝ (Fin n)) --centre
    (τ : ℝ) --radius
:
    Set (EuclideanSpace ℝ (Fin n))
:=
    { p | (p - x) ∈ G_0 τ }


noncomputable def Ψ
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)) )
:
    ℝ
:=
    (∫ x in Ω, (f x)) / (∫ _ in Ω, 1)


lemma G_eq_G_0
    {n:ℕ}
    (τ : ℝ) --radius
:
    (G_0 τ) = (G (0:EuclideanSpace ℝ (Fin n))  τ)
:= by
{
    unfold G_0 G
    simp only [sub_zero, setOf_mem_eq]
    unfold G_0
    rfl
}

noncomputable def G_abs {n:ℕ}
    (x : EuclideanSpace ℝ (Fin n)) --centre
    (τ : ℝ) --radius
:
    ℝ
:=
    ∫ _ in (G x τ), 1


noncomputable def Ω_abs {n:ℕ}
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:
    ℝ
:=
    ∫ _ in Ω, 1


noncomputable def ρ { n: ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) --centre
    (τ : ℝ) --radius
:
    ℝ
:=
    (∫ p in (G x τ), ⟪ ∇ I p,  ∇ B p ⟫_ℝ) / (∫ p in (G x τ), ⟪ ∇ B p,  ∇ B p ⟫_ℝ)

noncomputable def μ {n : ℕ }
    (x : EuclideanSpace ℝ (Fin n)) --centre
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : ℝ) -- radius
:
    ℝ
:=
    (1 / (G_abs x τ )) • ∫ p in (G x τ), (I p) - (ρ I B x τ) • (B p)


noncomputable def ρ_full
    {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:
    ℝ
:=
    (∫ p in Ω, ⟪ ∇ I p,  ∇ B p ⟫_ℝ) / (∫ p in Ω, ⟪ ∇ B p,  ∇ B p ⟫_ℝ )


noncomputable def μ_full
    {n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:
    ℝ
:=
    (1 / (Ω_abs lower upper Ω)) • ∫ p in Ω, (I p) - (ρ_full I B lower upper Ω) • (B p)


noncomputable def S{n:ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
:
    ℝ
:=
    (μ_full I B lower upper Ω) + (1/ G_abs x τ ) • ∫ p in (G x τ), ( (I x) - (ρ I B p τ) • (B x) - (μ p I B τ) )


lemma Ψ_linear_operator_add
    {n : ℕ }
    (f h : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) )
    (hf : Integrable f (volume.restrict Ω))
    (hh : Integrable h (volume.restrict Ω))
:
    (Ψ ( λ p ↦ (f p) + (h p) ) Ω) = (Ψ ( λ p ↦ (f p) ) Ω) + (Ψ ( λ p ↦ (h p) ) Ω)
:= by
{
    unfold Ψ

    have h₁ :
        (∫ x in Ω, f x + h x) = (∫ x in Ω, f x) + (∫ x in Ω, h x)
    := by
    {
        --simp_all only
        refine integral_add hf hh
    }

    simp only [h₁, add_div]
}

lemma Ψ_linear_operator_scale
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) )
    (α : ℝ )
    (hΩ : volume.real Ω ≠ 0)
:
    (Ψ ( λ p ↦ α • (f p) ) Ω) = α • (Ψ ( λ p ↦ (f p) ) Ω)
:= by
{
    unfold Ψ

    simp_all only
    [
        smul_eq_mul,
        integral_const,
        MeasurableSet.univ,
        measureReal_restrict_apply,
        univ_inter,
        mul_one
    ]

    let vol := volume.real Ω
    change (∫ x in Ω, α * f x) / vol = α * ((∫ x in Ω, f x) / vol)

    have hΩ_local : vol ≠ 0 := by
    {
        simp_all only [ne_eq, not_false_eq_true, vol]
    }
    field_simp [hΩ_local]

    exact integral_const_mul α f
}


noncomputable def S_Ψ{n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
:
    ℝ
:=
    (μ_full I B  lower upper Ω) + (I x) - (Ψ (λ p ↦ (ρ I B p τ) • (B x)) (G x τ )) - (Ψ (λ p ↦ (μ p I B τ)) (G x τ ) )


noncomputable def S_Ψ_1{n : ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (lower upper : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
:
    ℝ
:=
    (μ_full I B lower upper Ω) +
    (I x) -
    (B x) • (Ψ (λ p ↦ (ρ I B p τ)) (G x τ )) -
    (Ψ
      (
        λ p ↦
        (Ψ
          (λ q ↦ (I q))
          (G p τ)
        )
      )
      (G x τ)
    ) -
    (Ψ
      (λ p ↦ (ρ I B p τ) •
        (Ψ
          (λ q ↦ (B q))
          (G p τ )
        )
      )
      (G x τ )
    )


lemma G_vol_translates
    {n : ℕ }
    (τ : ℝ )
    (hτ: τ > 0 )
:
    ∀ (x : EuclideanSpace ℝ (Fin n)), (G_abs x τ) = (G_abs (0 : EuclideanSpace ℝ (Fin n)) τ)
:= by
{
    intro x
    simp only [gt_iff_lt] at hτ
    unfold G_abs
    unfold G

    simp only [sub_zero, setOf_mem_eq]

    change  ∫ x in {p | p - x ∈ G_0 τ}, 1 = ∫ x in G_0 τ, 1
    simp only [sub_eq_add_neg]

    let vol : Set (EuclideanSpace ℝ (Fin n)) := (G_0 τ)

    change ∫ x in {p | p + -x ∈ vol}, 1 = ∫ x in vol, 1

    let a := -x
    change ∫ x in {p | p + a ∈ vol}, 1 = ∫ x in vol, 1

    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one]

    change volume.real ((λ p ↦ p + a) ⁻¹' vol) = volume.real vol

    change (volume ((fun p ↦ p + a) ⁻¹' vol)).toReal = (volume vol).toReal

    simp only [measure_preimage_add_right]
}


lemma volsEqual
    {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ )
    (hτ : τ > 0)
:
    ∫ (_ : EuclideanSpace ℝ (Fin n)) in (G (n := n) x τ ), (1 : ℝ) =
    ∫ (_ : EuclideanSpace ℝ (Fin n)) in (G_0 (n := n) τ ), (1 : ℝ)
:= by
{
    simp only [gt_iff_lt] at hτ
    unfold G

    simp only [sub_eq_add_neg]

    let vol : Set (EuclideanSpace ℝ (Fin n)) := (G_0 τ)

    change ∫ (x : EuclideanSpace ℝ (Fin n)) in {p | p + -x ∈ vol}, 1 = ∫ (x : EuclideanSpace ℝ (Fin n)) in vol, 1

    let a := -x

    change ∫ (x : EuclideanSpace ℝ (Fin n)) in {p | p + a ∈ vol}, 1 = ∫ (x : EuclideanSpace ℝ (Fin n)) in vol, 1

    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one]

    change volume.real ((λ p ↦ p + a) ⁻¹' vol) = volume.real vol

    change (volume ((fun p ↦ p + a) ⁻¹' vol)).toReal = (volume vol).toReal

    simp only [measure_preimage_add_right]
}


/-
The Euclidean ball of radius `τ` is contained in the cube `G_0 τ`,
since each coordinate of a point is bounded by its L2 norm.
-/
lemma ball_subset_G_0
    {n : ℕ}
    (τ : ℝ)
:
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) τ ⊆ G_0 τ := by
{
    intro p hp
    simp [EuclideanSpace.norm_eq] at hp
    intro i
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ p.ofLp j ^ 2 := by
    {
        intro j hj
        exact sq_nonneg (p.ofLp j)
    }
    have hsum : p.ofLp i ^ 2 ≤ ∑ j : Fin n, p.ofLp j ^ 2 := by
    {
        simpa using Finset.single_le_sum hnonneg (Finset.mem_univ i)
    }
    have habs : |p.ofLp i| ≤ Real.sqrt (∑ j : Fin n, p.ofLp j ^ 2) := by
    {
        simpa using Real.abs_le_sqrt hsum
    }
    linarith
}

/-
The cube `G_0 τ` has positive volume.
-/
lemma G_0_volume_pos
    {n : ℕ}
    (τ : ℝ)
    (hτ : τ > 0)
:
    0 < volume (G_0 (n := n) τ)
:= by
{
    have hpos : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) τ) := by
    {
        simpa using Metric.measure_ball_pos _ _ hτ
    }
    have hsubset := ball_subset_G_0 (n := n) τ
    exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono hsubset)
}


lemma G_0_subset_closedBall
    {n : ℕ}
    (τ : ℝ)
    (hτ : 0 ≤ τ)
:
    G_0 (n := n) τ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (τ * Real.sqrt n)
:= by
{
    intro p hp
    simp only [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Real.norm_eq_abs]
    have hbound : ∀ i : Fin n, |p i| ^ 2 ≤ τ ^ 2 := by
    {
        intro i
        have h : |p i| ≤ τ := hp i
        nlinarith [abs_nonneg (p i)]
    }
    have hsum : ∑ i : Fin n, |p i| ^ 2 ≤ ∑ i : Fin n, τ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hbound i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc Real.sqrt (∑ i : Fin n, |p i| ^ 2)
        ≤ Real.sqrt ((n : ℝ) * τ ^ 2) := Real.sqrt_le_sqrt hsum
      _ = τ * Real.sqrt n := by
      {
        rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (n:ℝ)), Real.sqrt_sq hτ]
        ring
      }
}

lemma G_0_volume_lt_top
    {n : ℕ}
    (τ : ℝ)
    (hτ : 0 < τ)
:
    volume (G_0 (n := n) τ) < ⊤
:= by
{
    have hsub := G_0_subset_closedBall (n := n) τ hτ.le
    have hcompact : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (τ * Real.sqrt n)) :=
        isCompact_closedBall 0 (τ * Real.sqrt n)
    exact lt_of_le_of_lt (measure_mono hsub) hcompact.measure_lt_top
}


/-
Ψ(f, Gn(x)) = Ψ(p → f (p + x), Gn(0))
-/
theorem Ψ_translates
    {n : ℕ}
    (f : (EuclideanSpace ℝ (Fin n)) → ℝ )
    --(Ω : Set (EuclideanSpace ℝ (Fin n)))
    (τ : ℝ)
    (hτ: τ > 0 )
    (x : EuclideanSpace ℝ (Fin n))
:
    Ψ f (G x τ) = Ψ (λ p ↦ f (p + x)) (G_0 τ)
:= by
{
    unfold Ψ

    change (∫ (x : EuclideanSpace ℝ (Fin n)) in G x τ, f x) / ∫ (x : EuclideanSpace ℝ (Fin n)) in G x τ, 1 = (∫ (x_1 : EuclideanSpace ℝ (Fin n)) in G_0 τ, (fun p ↦ f (p + x)) x_1) / ∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, 1
    change (∫ (x : EuclideanSpace ℝ (Fin n)) in G x τ, f x) / (G_abs x τ) = (∫ (x_1 : EuclideanSpace ℝ (Fin n)) in G_0 τ, (fun p ↦ f (p + x)) x_1) / ∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, 1

    simp only [G_abs, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one]

    have hG_translates : volume.real (G_0 (n := n) τ) = volume.real (G x τ) := by
    {
        unfold G
        change volume.real (G_0 τ) = volume.real ((fun p ↦ p - x) ⁻¹' (G_0 τ))
        let xr := - x
        change volume.real (G_0 τ) = volume.real ((fun p : EuclideanSpace ℝ (Fin n) ↦ p + xr) ⁻¹' (G_0 τ))
        simp only [Measure.real, measure_preimage_add_right]
    }

    simp only [hG_translates]

    let d : ℝ := volume.real (G x τ)
    change (∫ (x : EuclideanSpace ℝ (Fin n)) in G x τ, f x) / d = (∫ (x_1 : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x_1 + x)) / d

    have hpos' (hτ_1 : τ > 0 ) : (0 : ℝ ) < volume.real (G x τ) := by
    {
        have hGabs_eq : G_abs x τ = volume.real (G x τ) := by
        {
            unfold G_abs
            simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
                univ_inter, smul_eq_mul, mul_one]
        }

        have hGabs0_eq : G_abs (0 : EuclideanSpace ℝ (Fin n)) τ = volume.real (G_0 (n := n) τ) := by
        {
            unfold G_abs
            rw [← G_eq_G_0]
            simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
                univ_inter, smul_eq_mul, mul_one]
        }

        have hpos0 : (0:ℝ) < volume.real (G_0 (n := n) τ) := by
        {
            have hpos_meas := G_0_volume_pos (n := n) τ hτ_1
            have hlt_top := G_0_volume_lt_top (n := n) τ hτ_1
            simp only [Measure.real]
            exact ENNReal.toReal_pos (ne_of_gt hpos_meas) (ne_of_lt hlt_top)
        }

        rw [← hGabs_eq, G_vol_translates τ hτ_1 x, hGabs0_eq]
        exact hpos0
    }

    have hd : d ≠ 0 := by
    {
        unfold d
        exact ne_of_gt (hpos' hτ)
    }
    field_simp [hd]

    simp only [gt_iff_lt] at hτ
    unfold G

    simp only [sub_eq_add_neg]

    let vol : Set (EuclideanSpace ℝ (Fin n)) := (G_0 τ)

    change ∫ (x : EuclideanSpace ℝ (Fin n)) in {p | p + -x ∈ vol}, f x = ∫ (x_1 : EuclideanSpace ℝ (Fin n)) in vol, f (x_1 + x)

    let a := -x

    change ∫ (x : EuclideanSpace ℝ (Fin n)) in {p | p + a ∈ vol}, f x = ∫ (p : EuclideanSpace ℝ (Fin n)) in vol, f (p + x)

    simp_all only [ne_eq, d, vol, a]

    have hMP : MeasureTheory.MeasurePreserving (fun p : EuclideanSpace ℝ (Fin n) => p + a) volume volume :=
    MeasureTheory.measurePreserving_add_right volume a

    have hME : MeasurableEmbedding (fun p : EuclideanSpace ℝ (Fin n) => p + a) :=
        (MeasurableEquiv.addRight a).measurableEmbedding

    have hkey := hMP.setIntegral_preimage_emb hME (fun z => f (z - a)) vol
    simp only [add_sub_cancel_right] at hkey

    simp_all only [forall_const, sub_neg_eq_add, a, vol]
    exact hkey
}


noncomputable def Ψ_vec
    {n : ℕ}
    (F : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
:
    (EuclideanSpace ℝ (Fin n))
:=
    (1 / (∫ _ in Ω, (1 : ℝ))) • (∫ x in Ω, F x)

noncomputable def lambda_expression
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    --(x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
:=
    λ x ↦ Ψ_vec (λ p ↦ ∇ f (p + x)) (G_0 τ)


lemma lambda_scalar_mul
    {n : ℕ}
    (vol : ℝ )
    (FF : EuclideanSpace ℝ (Fin n) → ℝ )
    (x : EuclideanSpace ℝ (Fin n))
    (h1_vol_ne : 1 / vol ≠ 0)
    (h_diff : DifferentiableAt ℝ FF x)
:
    ∇ (λ x1 ↦ vol⁻¹ * (FF x1) ) x = vol⁻¹ • ∇ (λ x1 ↦ (FF x1) ) x
:= by
{
    classical

    -- First rewrite the scalar multiplication into the form `c • FF x1`
    have h_vol_pull : (λ x1 ↦ vol⁻¹ * FF x1) = (vol⁻¹) • (λ x1 ↦  FF x1) := by
    {
        funext x1
        simp_all only [one_div, ne_eq, inv_eq_zero]
        simp_all only [Pi.smul_apply, smul_eq_mul]
    }

    simp only [h_vol_pull]

    let FF_fun := fun x1 ↦ FF x1
    let inv_vol := vol⁻¹
    have h_nz : inv_vol ≠ 0 := by
    {
        simp only [ne_eq]
        simp_all only [one_div, ne_eq, inv_eq_zero, not_false_eq_true, inv_vol]
    }
    change ∇ (inv_vol • FF_fun) x = inv_vol • ∇ (FF_fun) x

    unfold gradient

    rw [fderiv_const_smul]

    simp only [map_smul]

    have h_FF_diff : DifferentiableAt ℝ FF_fun x := by
    {
        simp_all only [one_div, ne_eq, inv_eq_zero, not_false_eq_true, inv_vol, FF_fun]
    }
    simp only [h_FF_diff]
}


lemma gradient_translate
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p x : EuclideanSpace ℝ (Fin n))
    (hf : DifferentiableAt ℝ f (p + x))
:
    ∇ (λ x1 ↦ f (p + x1)) x = ∇ f (p + x)
:= by
{
    -- 1. Unfold the definition of gradient to expose fderiv
    simp_rw [gradient]
    congr 1

    -- 2. Rewrite the translated function as a composition
    have h_comp : (λ x1 ↦ f (p + x1)) = f ∘ (λ x1 ↦ p + x1) := by rfl
    rw [h_comp]

    -- 3. Apply the Fréchet chain rule
    rw [fderiv_comp x hf (differentiableAt_id.const_add p)]

    -- 4. Clean up the derivative of (p + x1) which is the identity map
    rw [fderiv_const_add]
    change (fderiv ℝ f (p + x)).comp (fderiv ℝ id x) = fderiv ℝ f (p + x)
    rw [fderiv_id]

    exact ContinuousLinearMap.comp_id _
}

lemma gradient_Ψ_fixed_domain
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
    (hτ : 0 < τ)
    (h_diff_func : DifferentiableAt ℝ (λ x1 ↦ ∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x + x1)) x)
    (h_grad_integral_swap : ∇ (λ x1 ↦ ∫ (p : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (p + x1)) x = ∫ (p : EuclideanSpace ℝ (Fin n)) in G_0 τ, ∇ f (p + x))
:
    ∇ (λ x1 ↦ Ψ (λ p ↦ f (p + x1)) (G_0 τ)) x = Ψ_vec (λ p ↦ ∇ f (p + x)) (G_0 τ)
:= by
{
    -- First, unfold the definitions
    unfold Ψ Ψ_vec

    -- Simplify the integrals of constants
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one]

    -- Let vol be the volume of G_0 τ
    let vol := volume.real (G_0 (n := n) τ)

    -- Show vol > 0
    have hvol_pos : 0 < vol := by
    {
        have hG0_pos := G_0_volume_pos (n := n) τ hτ
        have hG0_lt_top := G_0_volume_lt_top (n := n) τ hτ
        exact ENNReal.toReal_pos (ne_of_gt hG0_pos) (ne_of_lt hG0_lt_top)
    }
    have hvol_ne : vol ≠ 0 := ne_of_gt hvol_pos

    change  ∇ (λ x1 ↦ (∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x + x1)) / vol) x = (1 / vol) • ∫ (x_1 : EuclideanSpace ℝ (Fin n)) in G_0 τ, ∇ f (x_1 + x)

    have h_div : (λ x1 ↦ (∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x + x1)) / vol) =
                 (λ x1 ↦ (1 / vol) • ∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x + x1)) := by
    {
        ext x1
        simp_all only [ne_eq, one_div, smul_eq_mul]
        rw [@inv_mul_eq_div]
    }


    rw [h_div]
    have h1_vol_ne : (1 / vol) ≠ 0 := one_div_ne_zero hvol_ne
    simp_all only [ne_eq, one_div, smul_eq_mul, inv_eq_zero, not_false_eq_true]

    let FF := λ x1 ↦ ∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x + x1)
    change ∇ (fun x1 ↦ vol⁻¹ * (FF x1) ) x  = vol⁻¹ • ∫ (x_1 : EuclideanSpace ℝ (Fin n)) in G_0 τ, ∇ f (x_1 + x)

    rw [lambda_scalar_mul]

    let lhs := ∇ (fun x1 ↦ FF x1) x
    let rhs := ∫ (x_1 : EuclideanSpace ℝ (Fin n)) in G_0 τ, ∇ f (x_1 + x)
    let inv_vol : ℝ := vol⁻¹

    have h_nz : inv_vol ≠ 0 := by
        simp only [ne_eq, inv_eq_zero, not_false_eq_true, inv_vol, vol, hvol_ne]

    change inv_vol • lhs = inv_vol • rhs

    simp [inv_vol, h_nz]

    unfold lhs rhs FF

    change ∇ (λ x1 ↦ ∫ (p : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (p + x1) ) x = ∫ (p : EuclideanSpace ℝ (Fin n)) in G_0 τ, ∇ f (p + x)

    rw [h_grad_integral_swap]

    simp_all only
    [
        one_div,
        ne_eq,
        inv_eq_zero,
        not_false_eq_true,
        vol
    ]
    unfold FF

    simp only [h_diff_func]
}


lemma grad_Ψ_distributes
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : ℝ)
    (hτ : τ > 0)
    (x : EuclideanSpace ℝ (Fin n))
    (h_diff_func : DifferentiableAt ℝ (λ x1 ↦ ∫ (x : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (x + x1)) x)
    (h_grad_integral_swap : ∇ (λ x1 ↦ ∫ (p : EuclideanSpace ℝ (Fin n)) in G_0 τ, f (p + x1)) x = ∫ (p : EuclideanSpace ℝ (Fin n)) in G_0 τ, ∇ f (p + x))
:
    ∇ (λ x1 ↦ (Ψ f (G x1 τ))) x = Ψ_vec (λ p ↦ (∇ f (p + x))) (G_0 τ)
:= by
{
    simp_rw [Ψ_translates f τ hτ]

    rw [gradient_Ψ_fixed_domain f x τ hτ h_diff_func h_grad_integral_swap]
}



theorem S_in_terms_of_Ψ
    {n:ℕ}
    (I B : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
    (lower upper :  EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)) := (hypercube lower upper))
    (hτ: τ > 0 )
:
    (S I B x τ lower upper Ω) = (μ_full I B lower upper Ω) + (I x) - (Ψ (λ p ↦ ((ρ I B x τ) • (B x))) (G x τ)) - (Ψ (λ p ↦ (μ p I B τ)) (G x τ))
:= by
{
    unfold S

    let mu_full : ℝ := μ_full I B lower upper Ω
    let lhs : ℝ := (1 / G_abs x τ) • ∫ (p : EuclideanSpace ℝ (Fin n)) in G x τ, I x - ρ I B p τ • B x - μ p I B τ
    change mu_full + lhs = mu_full + I x - Ψ (fun p ↦ ρ I B x τ • B x) (G x τ) - Ψ (fun p ↦ μ p I B τ) (G x τ)

    let rhs_1 : ℝ := Ψ (fun p ↦ μ p I B τ) (G x τ)
    change mu_full + lhs = mu_full + I x - Ψ (fun p ↦ ρ I B x τ • B x) (G x τ) - rhs_1

    let rhs_2 := Ψ (fun p ↦ ρ I B x τ • B x) (G x τ)
    change mu_full + lhs = mu_full + I x - rhs_2 - rhs_1

    let neg_mu_full := -mu_full

    have h_neg_mu : mu_full = -neg_mu_full
        := by
    {
        simp_all only [neg_neg, mu_full, neg_mu_full]
    }

    rw [@eq_sub_iff_add_eq]
    rw [@eq_sub_iff_add_eq]

    change mu_full + lhs + rhs_1 + rhs_2 = mu_full + I x
    simp only [h_neg_mu]

    change -(-mu_full) + lhs + rhs_1 + rhs_2 = -neg_mu_full + I x
    ring_nf

    rw [@eq_neg_add_iff_add_eq]

    unfold neg_mu_full

    ring_nf

    have h_lhs : lhs =  Ψ (λ p ↦ I x - ρ I B p τ • B x - μ p I B τ) (G x τ) := by
    {
        unfold lhs Ψ
        trace_state
        sorry
    }

    rw [h_lhs]

    let f := λ p ↦ I x - ρ I B p τ • B x - μ p I B τ
    let g := λ p ↦ - ρ I B p τ • B x - μ p I B τ
    change Ψ (f) (G x τ) + rhs_1 + rhs_2 = I x

    have h_fg : f = (λ p ↦ I x) + λ p ↦ (g p) := by
    {
        unfold f g
        simp only [smul_eq_mul, neg_mul]
        funext
        simp only [Pi.add_apply]
        simp [sub_eq_add_neg, add_comm, add_left_comm]
    }

    rw [h_fg]

    have hI : Integrable (λ p ↦ I x)  (volume.restrict (G x τ)) := sorry
    have hg : Integrable g (volume.restrict (G x τ)) := sorry

    simp only [add_assoc]
    let rhs := rhs_1 + rhs_2

    change Ψ ((fun p ↦ I x) + fun p ↦ g p) (G x τ) + rhs = I x

    have h_fun :
        ((fun p ↦ I x) + fun p ↦ g p) = (fun p ↦ I x + g p)
    := by
    {
        funext p
        simp
    }

    rw [h_fun]


    rw [(Ψ_linear_operator_add (λ p ↦ I x) g (G x τ) hI hg )]

    have hΩ : volume.real (G x τ) ≠ 0 := by
    {
          -- first rewrite the integrals as volume.real
        have h_int_Gx :
            ∫ (_ : EuclideanSpace ℝ (Fin n)) in G (n := n) x τ, (1 : ℝ)
            = volume.real (G (n := n) x τ) := by
            simp [integral_const, measureReal_restrict_apply,
                MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]

        have h_int_G0 :
            ∫ (_ : EuclideanSpace ℝ (Fin n)) in G_0 (n := n) τ, (1 : ℝ)
            = volume.real (G_0 (n := n) τ) := by
            simp [integral_const, measureReal_restrict_apply,
                MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]

        -- use your volsEqual lemma
        have h_eq :=
            volsEqual (n := n) x τ hτ

        -- rewrite both sides to volume.real
        have h_vol_eq :
            volume.real (G (n := n) x τ) = volume.real (G_0 (n := n) τ) := by
            simpa [h_int_Gx, h_int_G0] using h_eq

        -- positivity of volume on G_0 τ
        have h_pos_vol_G0 :
            0 < volume (G_0 (n := n) τ) :=
            G_0_volume_pos (n := n) τ hτ

        -- turn that into nonzero real volume
        have h_pos_real_G0 :
            volume.real (G_0 (n := n) τ) ≠ 0 := by
            -- volume.real Ω = (volume Ω).toReal, and positive measure gives positive toReal
            have : 0 < volume.real (G_0 (n := n) τ) := by
            {
                have hpos_meas := G_0_volume_pos (n := n) τ hτ
                have hlt_top := G_0_volume_lt_top (n := n) τ hτ
                simp only [Measure.real]
                exact ENNReal.toReal_pos (ne_of_gt hpos_meas) (ne_of_lt hlt_top)
            }
            exact ne_of_gt this

        -- finally transport nonzeroness along equality
        exact h_vol_eq ▸ h_pos_real_G0
    }

    have h_lam_id
    :
        (fun p : EuclideanSpace ℝ (Fin n) ↦ I x) = (fun p : EuclideanSpace ℝ (Fin n) ↦ I x • (1 : ℝ))
    := by
    {
        funext p
        simp
    }

    rw [h_lam_id]

    change Ψ (fun p ↦ I x • 1) (G x τ) + Ψ (fun p ↦ g p) (G x τ) + rhs = I x
    rw [(Ψ_linear_operator_scale (λ p ↦ 1) (G x τ) (I x) hΩ)]

    have h_psi_one: Ψ (fun p ↦ 1) (G x τ) = 1 := by
    {
        unfold Ψ

        have hvol : volume.real (G x τ) ≠ 0 := by
            exact hΩ

        simp [integral_const, hvol]
    }

    simp only [h_psi_one, smul_eq_mul, mul_one]

    --apply add_left_cancel

    let neg_I := - I x

    change I x + Ψ (fun p ↦ g p) (G x τ) + rhs = I x

    have h_neg_I
    :
        I x = -neg_I
    := by
    {
        simp_all only [neg_neg, neg_I]
    }

    simp only [h_neg_I]
    rw [@eq_neg_iff_add_eq_zero]

    ring_nf

    unfold g

    let left := λ p ↦ -ρ I B p τ • B x
    let right := λ p ↦ -μ p I B τ
    -- Ψ (fun p ↦ -ρ I B p τ • B x - μ p I B τ) (G x τ) + rhs = 0
    change Ψ (λ p ↦ left p + right p) (G x τ) + rhs = 0

    have hleft : Integrable left (volume.restrict (G x τ)) := sorry
    have hright : Integrable right (volume.restrict (G x τ)) := sorry

    rw [(Ψ_linear_operator_add left right (G x τ) hleft hright )]

    trace_state

    -- Ψ (fun p ↦ 1) (G x τ)

    /-
     Ψ_linear_operator_scale
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω :  Set (EuclideanSpace ℝ (Fin n)) )
    (α : ℝ )
    (hΩ : volume.real Ω ≠ 0)
    -/
    --unfold rhs_1 rhs_2


    --(fun p ↦ I x - ρ I B p τ * B x - μ p I B τ)
    -- rw? [Ψ_linear_operator_add]
    trace_state


    --change ((1 / G_abs x τ) • ∫ (p : EuclideanSpace ℝ (Fin n)) in G x τ, I x - ρ I B p τ • B x - μ p I B τ) +
    --   Ψ (fun p ↦ μ p I B τ) (G x τ) + Ψ (fun p ↦ ρ I B x τ • B x) (G x τ) = I x

    trace_state




}
