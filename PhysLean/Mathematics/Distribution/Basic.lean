/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Distributions

This file defines distributions `E →d[𝕜] F`, which is a way to generalise functions `E → F`.
Mathematically, a distribution `u : E →d[𝕜] F` takes in a test function `η : E → 𝕜` that is smooth
with rapidly decreasing iterated derivatives, and outputs a value in `F`. This operation is required
to be linear and continuous. Note that the space of test functions is called the Schwartz space and
is denoted `𝓢(E, 𝕜)`.

`E` is required to be a normed vector space over `ℝ`, and `F` can be a normed vector space over `ℝ`
or `ℂ` (which is the field denoted `𝕜`).

## Important Results
- `Distribution.derivative` and `Distribution.fourierTransform` allow us to make sense of these
  operations that might not make sense a priori on general functions.

## Examples
- `Distribution.diracDelta`: Dirac delta distribution at a point `a : E` is a distribution
  that takes in a test function `η : 𝓢(E, 𝕜)` and outputs `η a`.

## TODO
- In the future, any function of polynomial growth can be interpreted as a distribution. This will
  be helpful for defining the distributions that correspond to `H` (Heaviside step function), or
  `cos(x)`.
- Generalise `derivative` to higher dimensional domain.

-/

open SchwartzMap NNReal MeasureTheory

noncomputable section

/-- An `F`-valued distribution on `E` (where `E` is a normed vector space over `ℝ` and `F` is a
normed vector space over `𝕜`) is a continuous linear map `𝓢(E, 𝕜) →L[𝕜] F` where `𝒮(E, 𝕜)` is
the Schwartz space of smooth functions `E → 𝕜` with rapidly decreasing iterated derivatives. This
is notated as `E →d[𝕜] F`.

This should be seen as a generalisation of functions `E → F`. -/
abbrev Distribution (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace 𝕜 F] : Type :=
  𝓢(E, 𝕜) →L[𝕜] F

@[inherit_doc] notation:25 E:arg "→d[" 𝕜:25 "] " F:arg => Distribution 𝕜 E F

variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace Distribution

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace 𝕜 F]

/-- We construct a distribution from the following data:
1. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` that will be explained later.
2. We take a linear map `u` that evaluates the given Schwartz function `η`. At this stage we don't
   need `u` to be continuous.
3. Recall that a Schwartz function `η` satisfies a bound
   `‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖ < Mₙₖ` where `Mₙₖ : ℝ` only depends on `(k, n) : ℕ × ℕ`.
4. This step is where `s` is used: for each test function `η`, the norm `‖u η‖` is required to be
   bounded by `C * (‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖)` for some `x : ℝ` and for some `(k, n) ∈ s`, where
   `C ≥ 0` is a global scalar.
-/
def ofLinear (s : Finset (ℕ × ℕ)) (u : 𝓢(E, 𝕜) →ₗ[𝕜] F)
    (hu : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(E, 𝕜), ∃ (k : ℕ) (n : ℕ) (x : E), (k, n) ∈ s ∧
      ‖u η‖ ≤ C * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n η x‖)) : E →d[𝕜] F :=
  mkCLMtoNormedSpace u (by simp) (by simp) <| by
    obtain ⟨C, hC, hu⟩ := hu
    refine ⟨s, C, hC, fun η ↦ ?_⟩
    obtain ⟨k, n, x, hkn, hη⟩ := hu η
    have hs : s.Nonempty := ⟨(k, n), hkn⟩
    refine hη.trans <| mul_le_mul_of_nonneg_left ((le_seminorm 𝕜 k n η x).trans ?_) hC
    rw [Seminorm.finset_sup_apply]
    refine (NNReal.coe_le_coe (r₁ := ⟨SchwartzMap.seminorm 𝕜 k n η, apply_nonneg _ _⟩)).2 ?_
    convert s.le_sup hkn
      (f := fun kn : ℕ × ℕ ↦ (⟨SchwartzMap.seminorm 𝕜 kn.1 kn.2 η, apply_nonneg _ _⟩ : ℝ≥0))

@[simp] lemma ofLinear_apply (s : Finset (ℕ × ℕ)) (u : 𝓢(E, 𝕜) →ₗ[𝕜] F)
    (hu : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(E, 𝕜), ∃ (k : ℕ) (n : ℕ) (x : E), (k, n) ∈ s ∧
      ‖u η‖ ≤ C * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n η x‖))
    (η : 𝓢(E, 𝕜)) :
    ofLinear 𝕜 s u hu η = u η :=
  rfl

/-- Dirac delta distribution `diracDelta 𝕜 a : E →d[𝕜] 𝕜` takes in a test function `η : 𝓢(E, 𝕜)`
and outputs `η a`. Intuitively this is an infinite density at a single point `a`. -/
def diracDelta (a : E) : E →d[𝕜] 𝕜 :=
  delta 𝕜 𝕜 a

@[simp] lemma diracDelta_apply (a : E) (η : 𝓢(E, 𝕜)) :
    diracDelta 𝕜 a η = η a :=
  rfl

/-- Dirac delta in a given direction `v : F`. `diracDelta' 𝕜 a v` takesn in a test function
`η : 𝓢(E, 𝕜)` and outputs `η a • v`. Intuitively this is an infinitely intense vector field
at a single point `a` pointing at the direction `v`. -/
def diracDelta' (a : E) (v : F) : E →d[𝕜] F :=
  ContinuousLinearMap.smulRight (diracDelta 𝕜 a) v

@[simp] lemma diracDelta'_apply (a : E) (v : F) (η : 𝓢(E, 𝕜)) :
    diracDelta' 𝕜 a v η = η a • v :=
  rfl

end NormedSpace


section RCLike

/-- Definition of derivative of distribution: Let `u` be a distribution. Then its derivative is
`u'` where given a test function `η`, `u' η := -u(η')`. This agrees with the distribution generated
by the derivative of a differentiable function (with suitable conditions) (to be defined later),
because of integral by parts (where the boundary conditions are `0` by the test functions being
rapidly decreasing). -/
def derivative : (ℝ →d[𝕜] 𝕜) →ₗ[𝕜] (ℝ →d[𝕜] 𝕜) where
  toFun u := (ContinuousLinearEquiv.neg 𝕜).toContinuousLinearMap.comp <| u.comp <|
    SchwartzMap.derivCLM 𝕜
  map_add' u₁ u₂ := by simp
  map_smul' c u := by simp

@[simp] lemma derivative_apply (u : ℝ→d[𝕜] 𝕜) (η : 𝓢(ℝ, 𝕜)) :
    u.derivative 𝕜 η = -u (derivCLM 𝕜 η) :=
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

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ F]

variable (E F) in
/-- Definition of Fourier transform of distribution: Let `u` be a distribution. Then its Fourier
transform is `F{u}` where given a test function `η`, `F{u}(η) := u(F{η})`. -/
def fourierTransform : (E →d[ℂ] F) →ₗ[ℂ] (E →d[ℂ] F) where
  toFun u := u.comp <| fourierTransformCLM ℂ (E := ℂ) (V := E)
  map_add' u₁ u₂ := by simp
  map_smul' c u := by simp

@[simp] lemma fourierTransform_apply (u : E →d[ℂ] F) (η : 𝓢(E, ℂ)) :
    u.fourierTransform E F η = u (fourierTransformCLM ℂ η) :=
  rfl

end Complex

end Distribution
