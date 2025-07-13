/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Distributions

This file defines distributions, which are continuous linear functionals that take in as test
functions those `ℝ → E` that are smooth functions with rapidly decreasing iterated derivatives.
(The space of all these test functions is called the Schwartz space `𝓢(ℝ, E)`.)

`E` can be a normed vector space over `ℝ` or `ℂ`, and the continuous linear functionals are also
required to output values in `ℝ` or `ℂ` respectively.

## Important Results
- `Distribution.ofLinear`: constructs a distribution from a linear functional `F` and some
  conditions that implies that `F` is continuous.

## Examples
- `Distribution.diracDelta`: takes in a direction `v : E`, and returns the Dirac delta distribution
  in that direction. Given the test function `η`, `diracDelta v η = ⟨v, η 0⟩`.
- `Distribution.diracDelta'`: a slight generalisation of `diracDelta` where the inner product
  `⟨v, ─⟩` is replaced by a continuous linear map `E →L[𝕜] 𝕜`.

-/

open SchwartzMap NNReal MeasureTheory

noncomputable section

/-- A distribution on `E` (normed vector space over `𝕜`) is a continuous linear map
`𝓢(ℝ, E) →L[𝕜] 𝕜` where `𝒮(ℝ, E)` is the Schwarz space of smooth functions `ℝ → E` with rapidly
decreasing iterated derivatives. This is notated as `ℝ →d[𝕜] E`. -/
abbrev Distribution (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] : Type :=
  𝓢(ℝ, E) →L[𝕜] 𝕜

@[inherit_doc] notation:25 "ℝ→d[" 𝕜:25 "] " E:0 => Distribution 𝕜 E

variable (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Distribution

section NormedSpace

variable [NormedSpace 𝕜 E]

/-- We construct a distribution from the following data:
1. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` that will be explained later.
2. We take a linear map `f` that evaluates the given Schwartz function `η`. At this stage we don't
   need `f` to be continuous.
3. Recall that a Schwartz function `η` satisfies a bound
   `|x|ᵏ * ‖(dⁿ/dxⁿ) η‖ < Mₙₖ` where `Mₙₖ : ℝ` only depends on `(k, n) : ℕ × ℕ`.
4. This step is where `s` is used: for each test function `η`, the norm `‖f η‖` is required to be
   bounded by `C * (|x|ᵏ * ‖(dⁿ/dxⁿ) η‖)` for some `x : ℝ` and for some `(k, n) ∈ s`, where
   `C ≥ 0` is a global scalar.
-/
def ofLinear (s : Finset (ℕ × ℕ)) (f : 𝓢(ℝ, E) →ₗ[𝕜] 𝕜)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(ℝ, E), ∃ (k : ℕ) (n : ℕ) (x : ℝ), (k, n) ∈ s ∧
      ‖f η‖ ≤ C * (|x| ^ k * ‖iteratedDeriv n η x‖)) : ℝ→d[𝕜] E :=
  mkCLMtoNormedSpace f (by simp) (by simp) <| by
    obtain ⟨C, hC, hf⟩ := hf
    refine ⟨s, C, hC, fun η ↦ ?_⟩
    obtain ⟨k, n, x, hkn, hη⟩ := hf η
    have hs : s.Nonempty := ⟨(k, n), hkn⟩
    refine hη.trans <| mul_le_mul_of_nonneg_left ((le_seminorm' 𝕜 k n η x).trans ?_) hC
    rw [Seminorm.finset_sup_apply]
    refine (NNReal.coe_le_coe (r₁ := ⟨SchwartzMap.seminorm 𝕜 k n η, apply_nonneg _ _⟩)).2 ?_
    convert s.le_sup hkn
      (f := fun kn : ℕ × ℕ ↦ (⟨SchwartzMap.seminorm 𝕜 kn.1 kn.2 η, apply_nonneg _ _⟩ : ℝ≥0))

@[simp] lemma ofLinear_apply (s : Finset (ℕ × ℕ)) (f : 𝓢(ℝ, E) →ₗ[𝕜] 𝕜)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(ℝ, E), ∃ (k : ℕ) (n : ℕ) (x : ℝ), (k, n) ∈ s ∧
      ‖f η‖ ≤ C * (|x| ^ k * ‖iteratedDeriv n η x‖))
    (η : 𝓢(ℝ, E)) :
    ofLinear 𝕜 E s f hf η = f η :=
  rfl

/-- Dirac delta given a continuous linear function `dir : E →L[𝕜] 𝕜`. This is a generalisation of
`diracDelta` which takes in a specified direction `v`, and evaluate the test function `η` to give
`⟨v, η a⟩`. Here `dir` acts like `⟨v, ─⟩`. -/
def diracDelta' (dir : E →L[𝕜] 𝕜) (a : ℝ) : ℝ→d[𝕜] E :=
  dir.comp (delta 𝕜 E a)

@[simp] lemma diracDelta'_apply (dir : E →L[𝕜] 𝕜) (a : ℝ) (η : 𝓢(ℝ, E)) :
    diracDelta' 𝕜 E dir a η = dir (η a) :=
  rfl

end NormedSpace


section InnerProductSpace

variable [InnerProductSpace 𝕜 E]

/-- Dirac delta given a direction `v`. It evaluates a test function `η` to give `⟨v, η a⟩`.
For a generalisation repalcing `⟨v, ─⟩` with a continuous linear function, use `diracDelta'`. -/
def diracDelta (v : E) (a : ℝ) : ℝ→d[𝕜] E :=
  diracDelta' 𝕜 E (innerSL 𝕜 v) a

@[simp] lemma diracDelta_apply (v : E) (a : ℝ) (η : 𝓢(ℝ, E)) :
    diracDelta 𝕜 E v a η = inner 𝕜 v (η a) :=
  rfl

end InnerProductSpace


section RCLike

/-- Definition of derivative of distribution: Let `f` be a distribution. Then its derivative is
`f'` where given a test function `η`, `f' η := -f(η')`. -/
def derivative : (ℝ→d[𝕜] 𝕜) →ₗ[𝕜] (ℝ→d[𝕜] 𝕜) where
  toFun f := (ContinuousLinearEquiv.neg 𝕜).toContinuousLinearMap.comp <| f.comp <|
    SchwartzMap.derivCLM 𝕜
  map_add' f₁ f₂ := by simp
  map_smul' c f := by simp

@[simp] lemma derivative_apply (f : ℝ→d[𝕜] 𝕜) (η : 𝓢(ℝ, 𝕜)) :
    f.derivative 𝕜 η = -f (SchwartzMap.derivCLM 𝕜 η) :=
  rfl

/-- Polynomial growth: a sufficient condition (assuming measurability) for a function to be made
into a distribution. -/
@[fun_prop] structure PolynomialGrowth (f : ℝ → 𝕜) : Prop where
  (measurable : AEStronglyMeasurable f)
  (bounded : ∃ (a C : ℝ) (n : ℕ), ∀ᵐ x : ℝ, ‖f x‖ ≤ C + a * ‖x‖ ^ n)

attribute [fun_prop] PolynomialGrowth.measurable

lemma PolynomialGrowth.bounded_norm {f : ℝ → 𝕜} (hfp : PolynomialGrowth 𝕜 f) :
    ∃ (a C : ℝ) (n : ℕ), ∀ᵐ x : ℝ, ‖f x‖ ≤ ‖C‖ + ‖a‖ * ‖x‖ ^ n :=
  let ⟨a, C, n, hf⟩ := hfp.bounded
  ⟨a, C, n, hf.mono fun x hfx ↦ hfx.trans <| (Real.le_norm_self _).trans <|
    (norm_add_le _ _).trans_eq <| by simp⟩

lemma integrable_add_mul_pow_mul_rpow_neg_add_two (C a : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ (‖C‖ + ‖a‖ * ‖x‖ ^ n) * (1 + ‖x‖) ^ (-↑(n + 2) : ℝ)) :=
  ((integrable_rpow_neg_one_add_norm_sq (r := 2) (by simp)).const_mul (‖C‖ + ‖a‖)).mono
    (by fun_prop) <| .of_forall fun x ↦ calc
  ‖(‖C‖ + ‖a‖ * ‖x‖ ^ n) * (1 + ‖x‖) ^ (-↑(n + 2) : ℝ)‖
    = ‖C‖ * (1 + ‖x‖) ^ (-↑(n + 2) : ℤ) + ‖a‖ * (‖x‖ * (1 + ‖x‖)⁻¹) ^ n * (1 + ‖x‖) ^ (-2 : ℤ) :=
      by rw [← Int.cast_natCast, ← Int.cast_neg, Real.rpow_intCast, Real.norm_eq_abs,
        abs_eq_self.2 (by positivity), add_mul, add_right_inj, mul_pow, inv_pow,
        ← zpow_natCast, ← zpow_natCast, ← zpow_neg, mul_assoc, mul_assoc, mul_assoc,
        ← zpow_add₀ (by positivity), Nat.cast_add, neg_add, Nat.cast_two]
  _ ≤ ‖C‖ * (1 + ‖x‖) ^ (-2 : ℤ) + ‖a‖ * 1 * (1 + ‖x‖) ^ (-2 : ℤ) :=
      add_le_add (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (le_add_of_nonneg_right
          (norm_nonneg x)) (by omega)) (norm_nonneg C))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by positivity) (mul_inv_le_one_of_le₀ (by linarith)
            (by positivity))) (norm_nonneg a)) (by positivity))
  _ = (‖C‖ + ‖a‖) * ((1 + ‖x‖) ^ 2)⁻¹ := by rw [add_mul, mul_one, zpow_neg, zpow_two, ← sq]
  _ ≤ (‖C‖ + ‖a‖) * (1 + ‖x‖ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left ((inv_le_inv₀ (by positivity) (by positivity)).2
        (by rw [add_sq, one_pow, mul_one]; have := norm_nonneg x; linarith)) (by positivity)
  _ = ‖(‖C‖ + ‖a‖) * (1 + ‖x‖ ^ 2) ^ (-2 / 2 : ℝ)‖ :=
      by rw [neg_div_self two_ne_zero, Real.rpow_neg_one, Real.norm_eq_abs (_ * _),
        abs_eq_self.2 (by positivity)]

@[fun_prop] lemma _root_.MeasureTheory.AEStronglyMeasurable.posPart {α β : Type*}
    {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    [TopologicalSpace β] [Lattice β] [AddGroup β] [ContinuousSup β] [IsTopologicalAddGroup β]
    {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable f⁺ μ :=
  by convert hf.sup aestronglyMeasurable_zero using 1

@[fun_prop] lemma continuous_one_add_abs_zpow (n : ℤ) : Continuous fun x : ℝ ↦ (1 + |x|) ^ n :=
  Continuous.zpow₀ (by fun_prop) _ fun a ↦ Or.inl <| by positivity

@[fun_prop] lemma continuous_one_add_abs_rpow (n : ℝ) : Continuous fun x : ℝ ↦ (1 + |x|) ^ n :=
  Continuous.rpow (by fun_prop) (by fun_prop) fun a ↦ Or.inl <| by positivity

instance PolynomialGrowth.hasTemperateGrowth (f : ℝ → ℝ)
    [hfp : Fact (PolynomialGrowth ℝ f)] :
    (volume.withDensity (ENNReal.ofReal ∘ f)).HasTemperateGrowth :=
  let ⟨a, C, n, hf⟩ := hfp.out.bounded_norm
  ⟨n + 2, (integrable_withDensity_iff_integrable_smul₀'
      (ENNReal.measurable_ofReal.comp_aemeasurable hfp.1.1.aemeasurable)
      (.of_forall fun x ↦ ENNReal.ofReal_lt_top)).2 <|
    (integrable_add_mul_pow_mul_rpow_neg_add_two C a n).mono
      (by convert hfp.1.1.posPart.mul (continuous_one_add_abs_rpow _).aestronglyMeasurable using 2)
      (hf.mono fun x hx ↦ by
        rw [smul_eq_mul, norm_mul, norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_eq_self.2 (by positivity), abs_eq_self.2 (by positivity),
          Function.comp_apply, ENNReal.toReal_ofReal']
        exact max_le ((le_abs_self _).trans hx) (by positivity))⟩

/-- An auxiliary definition. Given function `f` with polynomial growth, we construct a distribution
from the positive part, with `posPart f hf η = ∫ x, (max (f x) 0) * η x`. -/
def posPart (f : ℝ → ℝ) (hfp : PolynomialGrowth ℝ f) : ℝ→d[ℝ] ℝ :=
  have := Fact.mk hfp
  integralCLM ℝ (.withDensity volume (ENNReal.ofReal ∘ f))

end RCLike


section Complex

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Definition of Fourier transform of distribution: Let `f` be a distribution. Then its Fourier
transform is `F(f)` where given a test function `η`, `F(f)(η) := f(F(η))`. -/
def fourierTransform : (ℝ→d[ℂ] E) →ₗ[ℂ] (ℝ→d[ℂ] E) where
  toFun f := f.comp <| SchwartzMap.fourierTransformCLM ℂ (E := E) (V := ℝ)
  map_add' f₁ f₂ := by simp
  map_smul' c f := by simp

@[simp] lemma fourierTransform_apply (f : ℝ→d[ℂ] E) (η : 𝓢(ℝ, E)) :
    fourierTransform E f η = f (SchwartzMap.fourierTransformCLM ℂ η) :=
  rfl

end Complex

end Distribution
