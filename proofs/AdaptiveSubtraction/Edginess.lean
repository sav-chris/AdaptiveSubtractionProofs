import Mathlib.Analysis.Calculus.Deriv.Basic
import AdaptiveSubtraction.Quadratics

open Topology
open MeasureTheory

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


noncomputable def I_Squared_Term(I : ℝ → ℝ)(x : ℝ) := deriv I x ^ 2
noncomputable def IB_Term(I B : ℝ → ℝ)(x ρ : ℝ) := ρ * (deriv I x * deriv B x) * 2
noncomputable def B_Squared_Term(B : ℝ → ℝ)(x ρ : ℝ) := (ρ * deriv B x) ^ 2

noncomputable def Int_I_Squared_Term(I : ℝ → ℝ)(lower upper : ℝ)(Ω : Set ℝ := Set.Ioo lower upper) := ∫ (x : ℝ) in Ω, deriv I x ^ 2
noncomputable def Int_IB_Term(I B : ℝ → ℝ)(ρ : ℝ)(lower upper : ℝ)(Ω : Set ℝ := Set.Ioo lower upper) := (ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x))
noncomputable def Int_B_Squared_Term(B : ℝ → ℝ)(ρ : ℝ)(lower upper : ℝ)(Ω : Set ℝ := Set.Ioo lower upper) := (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2

noncomputable def Int_IB_Term_2(I B : ℝ → ℝ)(ρ : ℝ)(lower upper : ℝ)(Ω : Set ℝ := Set.Ioo lower upper) := (ρ * ∫ (x : ℝ) in Ω, deriv I x * deriv B x) * 2

lemma integral_distributes_over_addition
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (ρ : ℝ)
    (h_edgable : (image_and_background_are_edgable I B lower upper Ω ))
:
    ∫ (x : ℝ) in Ω, ( (I_Squared_Term I x) - (IB_Term I B x ρ ) + (B_Squared_Term B x ρ) ) =  (Int_B_Squared_Term B ρ lower upper Ω) - (Int_IB_Term I B ρ lower upper Ω) + (Int_I_Squared_Term I lower upper Ω)
:= by
{
    let f := λ x ↦ deriv I x ^ 2
    let g := λ x ↦ ρ * (deriv I x * deriv B x) * 2
    let h := λ x ↦ (ρ * deriv B x) ^ 2

    unfold I_Squared_Term IB_Term B_Squared_Term Int_B_Squared_Term Int_IB_Term Int_I_Squared_Term

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


lemma Int_IB_Term_sub
    (I B : ℝ → ℝ)
    (lower upper : ℝ)
    (Ω : Set ℝ := Set.Ioo lower upper)
    (ρ : ℝ )
:
    (Int_IB_Term_2 I B ρ lower upper Ω) = (Int_IB_Term I B ρ lower upper Ω)
:= by
{
    unfold Int_IB_Term Int_IB_Term_2
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
    simp_all only [smul_eq_mul ]

    have rest_lemma :
        ∫ (x : ℝ) in Ω, (deriv I x ^ 2) - ρ * (deriv I x * deriv B x) * 2 + (ρ * deriv B x) ^ 2 = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 + -(ρ * (2 * ∫ (x : ℝ) in Ω, deriv I x * deriv B x)) + (∫ (x : ℝ) in Ω, (deriv I x) ^ 2)
    := by
    {
        change ∫ (x : ℝ) in Ω, ( (I_Squared_Term I x) - (IB_Term I B x ρ ) + (B_Squared_Term B x ρ) ) =  (Int_B_Squared_Term B ρ lower upper Ω) - (Int_IB_Term I B ρ lower upper Ω) + (Int_I_Squared_Term I lower upper Ω)
        rw [ (integral_distributes_over_addition I B lower upper Ω ρ h_edgable) ]
    }

    change ∫ (x : ℝ) in Ω, deriv I x ^ 2 - ρ * (deriv I x * deriv B x) * 2 + (ρ * deriv B x) ^ 2 = (∫ (x : ℝ) in Ω, deriv B x ^ 2) * ρ ^ 2 - (ρ * ∫ (x : ℝ) in Ω, deriv I x * deriv B x) * 2 + ∫ (x : ℝ) in Ω, deriv I x ^ 2
    change ∫ (x : ℝ) in Ω, (I_Squared_Term I x) - (IB_Term I B x ρ) + (B_Squared_Term B x ρ) = (Int_B_Squared_Term B ρ lower upper Ω) - (ρ * ∫ (x : ℝ) in Ω, deriv I x * deriv B x) * 2 + (Int_I_Squared_Term I lower upper Ω)

    change ∫ (x : ℝ) in Ω, (I_Squared_Term I x) - (IB_Term I B x ρ) + (B_Squared_Term B x ρ) = (Int_B_Squared_Term B ρ lower upper Ω) - (Int_IB_Term_2 I B ρ lower upper Ω) + (Int_I_Squared_Term I lower upper Ω)
    simp only [(Int_IB_Term_sub I B lower upper Ω ρ)]

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
