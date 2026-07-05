import AdaptiveSubtraction.Edginess

import Mathlib.Analysis.Calculus.ParametricIntegral
--import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open MeasureTheory
open scoped InnerProductSpace

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
    simp only
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
        simp_all only
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

/-
∀ x,  |G(x)| = |G(0)|
-/
lemma G_vol_translates_1
    {n : ℕ }
    (τ : ℝ )
    (hτ: τ > 0 )
    (x : EuclideanSpace ℝ (Fin n))
:
    (G_abs x τ) = (G_abs (0 : EuclideanSpace ℝ (Fin n)) τ)
:= by
{
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


noncomputable def Ψ_vec
    {n : ℕ}
    (F : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
:
    EuclideanSpace ℝ (Fin n)
:=
    (1 / (∫ _ in Ω, (1 : ℝ))) • (∫ x in Ω, F x)


noncomputable def Ψ_vec_1
    {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
:
    EuclideanSpace ℝ (Fin n)
:=
    EuclideanSpace.equiv (Fin n) ℝ |>.symm (fun i ↦ Ψ (fun x ↦ F x i) Ω)

noncomputable def Ψ_vec_2
    {n : ℕ}
    (F : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
:
    EuclideanSpace ℝ (Fin n)
:=
    EuclideanSpace.equiv (Fin n) ℝ |>.symm (λ i ↦ Ψ (λ x ↦ F x i) Ω)

lemma foo
    {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : (volume.real Ω) > 0)
    (i : Fin n)
:
    (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, F x).ofLp i = ∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, (F x).ofLp i
:= by
{
    /-
    -- 1. Represent the coordinate projection as a ContinuousLinearMap
    let proj : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.linearProjectionLoop i

    -- 2. Rewrite the left hand side explicitly using this map
    change proj (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, F x) = ∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, proj (F x)

    -- 3. Commute the integral and the continuous linear map
    exact ContinuousLinearMap.integral_apply proj

    simpa using (MeasureTheory.integral_apply (μ := volume.restrict Ω) (f := F) i)

    have hproj : Continuous (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp i) :=
      (EuclideanSpace.proj i).continuous
    --rw [← (EuclideanSpace.proj i).integral_comp_comm]
        -- .ofLp i is (EuclideanSpace.proj i) as a ContinuousLinearMap
    -- ContinuousLinearMap.integral_comp_comm pulls a CLM outside an integral
    have key := (EuclideanSpace.proj i (𝕜 := ℝ)).integral_comp_comm (f := F) (μ := volume.restrict Ω)
    -- key : (EuclideanSpace.proj i) (∫ x, F x) = ∫ x, (EuclideanSpace.proj i) (F x)
    exact key
    -/
    sorry
}

lemma Ψ_vec_eq_Ψ_vec_2
    {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    --(hΩ : (volume.real Ω) > 0)
:
    Ψ_vec F Ω = Ψ_vec_2 F Ω
:= by
{
    /-
    -- unfold both definitions
    unfold Ψ_vec Ψ_vec_2 Ψ

    -- extensionality: two vectors are equal iff all coordinates are equal
    ext i
    simp_all only
    [
        integral_const,
        MeasurableSet.univ,
        measureReal_restrict_apply,
        univ_inter,
        smul_eq_mul,
        mul_one,
        one_div,
        PiLp.smul_apply,
        PiLp.continuousLinearEquiv_symm_apply
    ]
    trace_state
    --change (volume.real Ω)⁻¹ * (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, F x).ofLp i = (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, (F x).ofLp i) / volume.real Ω
    let lhs := (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, F x).ofLp i
    let d := volume.real Ω
    let rhs := (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, (F x).ofLp i)

    change d⁻¹ * lhs = rhs / d
    ring_nf
    simp only [mul_eq_mul_left_iff, inv_eq_zero]

    have hd : d ≠ 0 := by
        have := hΩ
        -- hΩ : volume.real Ω > 0
        -- so d = volume.real Ω
        exact ne_of_gt this

    simp_all only [gt_iff_lt, ne_eq, or_false, d, lhs, rhs]
    --simpa using (integral_apply (fun x => F x) i)
    --simpa [lhs, rhs] using (integral_apply (fun x => F x) i)

    change (∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, F x).ofLp i = ∫ (x : EuclideanSpace ℝ (Fin n)) in Ω, (F x).ofLp i
    trace_state
    -/
    sorry

    -- evaluate the i-th coordinate of the left-hand side
    -- (1 / vol) • ∫ F  →  (1 / vol) * ∫ (F x i)
    --simp [EuclideanSpace.smul_apply, integral_apply, div_eq_inv_mul,
    --      mul_comm, mul_left_comm, mul_assoc]
}

/-
lemma Ψ_vec_eq_Ψ_components
    {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (i : Fin n)
:
    (Ψ_vec F Ω) i = Ψ (λ x ↦ F x i) Ω
:= by
{
    simp [Ψ_vec, Ψ, EuclideanSpace.smul_apply, integral_apply, div_eq_inv_mul, mul_comm]
}
-/


/-

noncomputable def Ψ
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)) )
:
    ℝ
:=
    (∫ x in Ω, (f x)) / (∫ _ in Ω, 1)

-/


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


noncomputable def Ψ_region
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : ℝ)
    --(Ω : Set (EuclideanSpace ℝ (Fin n)))

:
    EuclideanSpace ℝ (Fin n) → ℝ
:=
    (λ x1 ↦ (Ψ f (G x1 τ)))



lemma gradient_Ψ_fixed_domain_1
    {n : ℕ }
    (f :
        EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℝ (Fin n) → ℝ)
    )
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
:
    (∇
        (λ x1 ↦
            (Ψ
                (λ p ↦
                    ((f p) x1)
                )
                (G_0 τ)
            )
        )
        x
    )
    =
    (Ψ_vec
        (λ p ↦
            (∇
                (λ x1 ↦
                    ((f p) x1)
                )
                x
            )
        )
        (G_0 τ)
    )
:= by
{

}



lemma vec_component
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (x2 : EuclideanSpace ℝ (Fin n))
    (i : Fin n)
:
    (∇
        (λ x1 =>
            ((f x2) x1)
        )
        x
    ).ofLp i
    =
    (fderiv ℝ (λ x1 => (f x2) x1) x) (PiLp.single i 1)
    --(fderiv ℝ (λ x1 => (f x2) x1) x)
:= by
{
    -- simpa using (gradient_apply (f := λ x1 => (f x2) x1) (x := x) (i := i))



}


lemma Ψ_lambda
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ )
    (i : Fin n)
:
    (∇
        (λ x1 ↦
            (Ψ
                (λ p ↦
                    ((f p) x1)
                )
                (G_0 τ)
            )
        )
        x
    ).ofLp i
    =
    (Ψ
        (λ x_1 ↦
            (∇
                (λ x1 =>
                    ((f x_1) x1)
                )
                x
            ).ofLp i
        )
        (G_0 τ)
    )
:= by
{
    /-
    (∇ g x).ofLp i = (fderiv ℝ g x) (PiLp.single i 1)
    (∇ (λ x1 ↦ (f x_1) x1) x).ofLp i

    -/




}


lemma gradient_Ψ_fixed_domain
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (τ : ℝ )
    -- (+ integrability/differentiability hypotheses)
    --(h_diff : ∀ p, DifferentiableAt ℝ (fun x1 ↦ g p x1) x)
    --(h_integrable : Integrable (fun p ↦ ∇ (fun x1 ↦ g p x1) x) (G_0 τ)) -- Type matching your measure/domain
    --(h_bound : ∀ x' ∈ Neighbor_of x, ∀ p, ‖∇ (fun t ↦ g p t) x'‖ ≤ BoundFunction p) -- For Lebesgue Dominated Convergence
:
    ∇ ( λ x1 ↦ Ψ (λ p ↦ (f p) x1) (G_0 τ)) x = Ψ_vec (λ p ↦ ∇ (λ x1 ↦ f p x1) x) (G_0 τ)
:= by
{
    let rhs := (λ p ↦ ∇ (λ x1 ↦ f p x1) x)
    change ∇ ( λ x1 ↦ Ψ (λ p ↦ f p x1) (G_0 τ)) x = Ψ_vec rhs (G_0 τ)
    have hτ : τ > 0 := sorry

    simp only [(Ψ_vec_eq_Ψ_vec_2 rhs (G_0 τ))]

    unfold Ψ_vec_2
    let lhs := (fun x1 ↦ Ψ (fun p ↦ f p x1) (G_0 τ))

    change ∇ lhs x = (EuclideanSpace.equiv (Fin n) ℝ).symm λ i ↦ Ψ (λ x ↦ (rhs x).ofLp i) (G_0 τ)
    ext i
    unfold lhs rhs
    simp only [PiLp.continuousLinearEquiv_symm_apply]
    trace_state
    unfold gradient
    trace_state
    change ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x1 ↦ Ψ (fun p ↦ f p x1) (G_0 τ)) x)).ofLp i = Ψ (fun x_1 ↦ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (fun x1 ↦ f x_1 x1) x)).ofLp i) (G_0 τ)
    trace_state
    --change (∇ (fun x1 ↦ Ψ (fun p ↦ f p x1) (G_0 τ)) x).ofLp i = Ψ (fun x_1 ↦ (∇ (fun x1 ↦ f x_1 x1) x).ofLp i) (G_0 τ)


    --have h_comp : (λ x1 ↦ f (x1)) = f ∘ (λ x1 ↦ x1) := by rfl
    --rw [h_comp]

    sorry
    /-
    --apply [←(Ψ_vec_eq_Ψ_vec_2 rhs (G_0 τ ) (G_0_volume_pos τ hτ)) ]
    --simp_all only [gt_iff_lt, PiLp.continuousLinearEquiv_symm_apply, rhs]

    -- Step 1: Expose the underlying fderiv structures
    simp_rw [gradient]
    trace_state

    -- Step 2: Extract the Riesz Isomorphism (InnerProductSpace.toDual) outside the operator
    -- This requires a lemma stating that Ψ_vec commutes with linear maps, e.g., `Ψ_vec (L ∘ f) = L (Ψ_vec f)`
    rw [← Ψ_vec_continuousLinearMap_commute]
    congr 1

    -- Step 3: Swap the derivative and the integral/operator
    -- This will resolve via your local variation of `hasFDerivAt_integral_of_dominated_loc`
    exact fderiv_Ψ_commute g x (G_0 τ) h_diff h_bound
    -/

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

lemma grad_Ψ_distributes
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f)
    (τ : ℝ)
    (hτ : τ > 0)
    (x : EuclideanSpace ℝ (Fin n))

:
    ∇ (λ x1 ↦ (Ψ f (G x1 τ))) x = Ψ_vec (λ p ↦ (∇ f (p + x))) (G_0 τ)
:= by
{
    simp_rw [Ψ_translates f τ hτ]
    rw [gradient_Ψ_fixed_domain]
    congr 1
    ext p
    rw [← gradient_translate f p x (hf (p + x))]
}

lemma grad_Ψ_distributes_6
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)) )
    (τ : ℝ)
    (hτ : τ > 0)
    (x : EuclideanSpace ℝ (Fin n))
:
    ∇ (λ x1 ↦ (Ψ f (G x1 τ))) x = Ψ_vec (λ p ↦ (∇ f (p + x))) (G_0 τ)
:= by
{
    let lhs : EuclideanSpace ℝ (Fin n) → ℝ := λ x1 ↦  (Ψ f (G x1 τ))
    change ∇ (lhs) x = Ψ_vec (λ p ↦ (∇ f (p + x))) (G_0 τ)
    trace_state

    --have hGtrans(x1 : EuclideanSpace ℝ (Fin n)) : (Ψ f (G x1 τ)) = (Ψ f (G 0 τ)) := by
    have hGtrans(x1 : EuclideanSpace ℝ (Fin n)) : lhs = λ x1 ↦ (Ψ f (G_0 τ)) := by
    {
        unfold lhs
        trace_state
        --rw [(G_vol_translates τ hτ )]
        sorry
    }
    simp only [(hGtrans x)]
    trace_state

    unfold Ψ_vec
    --simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one, one_div]
    --refine PiLp.ext ?_
    unfold Ψ
    --simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one]
    --simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter, smul_eq_mul, mul_one, one_div]
    --apply [(G_vol_translates τ hτ )]
    simp only [(hGtrans x ) ]
    trace_state

}


/-
    change  (volume {p | p + a ∈ vol}).toReal = (volume vol).toReal
    trace_state
    -/
--∇ (Ψ f (G x τ )) =  Ψ ∇ f (p + x) (G 0 τ )

    --(x : EuclideanSpace ℝ (Fin n))
lemma grad_Ψ
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)) )
    (τ : ℝ)
    (hτ : τ > 0)
    (x : EuclideanSpace ℝ (Fin n))

:
    ∇ (λ x ↦ Ψ f (G x τ)) x = Ψ (λ p ↦ ∇ (λ (y : EuclideanSpace ℝ (Fin n)) ↦ f y) (p + x)) (G_0 τ)

    --∇ (λ y ↦ Ψ f (G y τ)) = Ψ λ x ↦ ∇ (f x) (G 0 τ)
 --(Ψ (λ p ↦ ∇ (λ x ↦ (f (p + x)))) (G 0 τ) )

    /-
    ∇ (λ x ↦ Ψ f (G x τ )) =
    --(

            --λ x ↦
    (Ψ
        (λ p ↦ (∇ (λ x ↦ f (p + x) )))
        (G 0 τ )
    )
    -/

    --)
    --∇ (λ x ↦ Ψ f (G x τ )) = ∇ (λ x ↦ Ψ (λ p ↦ (f (p + x) )) (G 0 τ ))
    /-
    ∇ (λ x ↦ Ψ f (G x τ )) =
    (∇
        (
            λ x ↦
            (Ψ
                (λ p ↦ (f (p + x) ))
                (G 0 τ )
            )
        )
    )
    -/
    --∇ (λ x ↦ Ψ f (G x τ )) = (Ψ (λ p ↦ (∇ (λ x ↦ (f (p + x)) ) )) (G 0 τ ) )

/-
    (Ψ
        (
            λ x ↦
            (∇
                λ (p : EuclideanSpace ℝ (Fin n)) ↦ (f (p + x) )
            )
        )
        (G 0 τ )
    )
    -/
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

    trace_state

    let vol(q : EuclideanSpace ℝ (Fin n)) := volume.real (G q τ)

    trace_state

    change (∇ λ x ↦ (∫ x in G x τ, f x) / (vol x) ) = ∇ λ x ↦ (∫ p in G 0 τ, f (p + x)) / (vol 0)

    trace_state


    --change (∫ x in Ω, α * f x) / vol = α * ((∫ x in Ω, f x) / vol)
/-
    have hΩ_local : vol ≠ 0 := by
    {
        simp_all only [ne_eq, (vol q)]
        trace_state
    }
    field_simp [hΩ_local] -/
    --simp_all only [gt_iff_lt]

    trace_state


}



/-
lemma grad_Ψ
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n)) )
    (τ : ℝ)
    (hτ : τ > 0)
    (x : EuclideanSpace ℝ (Fin n))
:
    ∇ (λ x1 ↦ (Ψ f (G x1 τ))) x = Ψ_vec (λ p ↦ (∇ f (p + x))) (G_0 τ)
:= by
{
    exact grad_Ψ_let f Ω τ hτ x
}
-/



lemma gradient_translate_1
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p x : EuclideanSpace ℝ (Fin n))
    (hf : DifferentiableAt ℝ f (p + x))
:
    ∇ (fun x1 ↦ f (p + x1)) x = ∇ f (p + x)
:= by
{
    have hshift : HasFDerivAt (fun x1 => p + x1) (ContinuousLinearMap.id ℝ _) x := by
        have := (hasFDerivAt_id ℝ x).const_add p
        simp [add_comm] at this
        exact this
    have hcomp := hf.hasFDerivAt.comp x hshift
    simp [gradient, hcomp.fderiv]
}

lemma gradient_translate_2
    {n : ℕ }
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p x : EuclideanSpace ℝ (Fin n))
    (hf : DifferentiableAt ℝ f (p + x))
:
    ∇ (fun x1 ↦ f (p + x1)) x = ∇ f (p + x)
:= by
    have hshift : HasFDerivAt (fun x1 => p + x1) (ContinuousLinearMap.id ℝ _) x := by
        have := (hasFDerivAt_id x).const_add p
        simp [add_comm] at this
        exact this
    have hcomp := hf.hasFDerivAt.comp x hshift
    simp [gradient, hcomp.fderiv]
