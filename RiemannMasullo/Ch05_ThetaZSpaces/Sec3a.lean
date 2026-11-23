module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import RiemannMasullo.ForMathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec4
public import Mathlib.Analysis.Distribution.Support

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
public import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Non-archimedean principal values and distributions supported at the origin

Masullo, §5.3.1–5.3.2, pp. 240–249.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions NNReal NumberField.AdeleRing SchwartzMap TensorProduct

namespace RiemannMasullo

/-- A series whose terms are dominated, seminorm by seminorm, by summable real sequences is
summable in a complete space whose topology is given by those seminorms, and each seminorm of
its sum is at most the sum of the dominating sequence. -/
private theorem realSchwartzFlatQuotient_strongDual_summable {𝕜 E ι : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (x : ℕ → E) (u : ι → ℕ → ℝ)
    (hu : ∀ i, Summable (u i)) (hx : ∀ i n, p i (x n) ≤ u i n) :
    Summable x ∧ ∀ i, p i (∑' n, x n) ≤ ∑' n, u i n := by
  have hu0 (i : ι) (n : ℕ) : 0 ≤ u i n := (apply_nonneg _ _).trans (hx i n)
  have hsum : Summable x := by
    rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
    intro e he
    obtain ⟨⟨I, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp he
    have hv (i : ι) : ∃ s : Finset ℕ, ∀ t : Finset ℕ, Disjoint t s → ∑ n ∈ t, u i n < r := by
      obtain ⟨s, hs⟩ := (hu i).vanishing (Metric.ball_mem_nhds (0 : ℝ) hr)
      refine ⟨s, fun t ht ↦ ?_⟩
      have := hs t ht
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans_lt this
    choose s hs using hv
    refine ⟨I.biUnion s, fun t ht ↦ hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    refine Seminorm.finset_sup_apply_lt hr fun i hi ↦ ?_
    calc p i (∑ n ∈ t, x n) ≤ ∑ n ∈ t, p i (x n) :=
          Finset.le_sum_of_subadditive (p i) (map_zero _).le (map_add_le_add _) _ _
      _ ≤ ∑ n ∈ t, u i n := Finset.sum_le_sum fun n _ ↦ hx i n
      _ < r := hs i t (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem s hi) ht)
  refine ⟨hsum, fun i ↦ ?_⟩
  have ht := ((hp.continuous_seminorm i).tendsto _).comp hsum.hasSum
  refine le_of_tendsto' ht fun t ↦ ?_
  calc p i (∑ n ∈ t, x n) ≤ ∑ n ∈ t, p i (x n) :=
        Finset.le_sum_of_subadditive (p i) (map_zero _).le (map_add_le_add _) _ _
    _ ≤ ∑ n ∈ t, u i n := Finset.sum_le_sum fun n _ ↦ hx i n
    _ ≤ ∑' n, u i n := (hu i).sum_le_tsum t fun n _ ↦ hu0 i n

/-- The derivatives at zero of a real power, viewed as a complex function. -/
private theorem realSchwartzFlatQuotient_strongDual_pow (n j : ℕ) :
    iteratedDeriv j (fun x : ℝ ↦ (x : ℂ) ^ n) 0 = if j = n then (n.factorial : ℂ) else 0 := by
  have h : ∀ j, iteratedDeriv j (fun x : ℝ ↦ (x : ℂ) ^ n) =
      fun x : ℝ ↦ (n.descFactorial j : ℂ) * (x : ℂ) ^ (n - j) := by
    intro j
    induction j with
    | zero => funext x; simp
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have := (h1.pow (n - j)).const_mul (n.descFactorial j : ℂ)
      rw [show (fun x : ℝ ↦ (n.descFactorial j : ℂ) * (x : ℂ) ^ (n - j)) =
        fun y ↦ (n.descFactorial j : ℂ) * ((fun y : ℝ ↦ (y : ℂ)) ^ (n - j)) y from rfl,
        this.deriv, Nat.descFactorial_succ, Nat.sub_sub, mul_one]
      push_cast
      ring
  rw [h j]
  rcases lt_trichotomy j n with hj | rfl | hj
  · simp [hj.ne, Nat.sub_ne_zero_of_lt hj]
  · simp [Nat.descFactorial_self]
  · simp [hj.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hj]

/-- `y ↦ yⁿ χ(y)` is a Schwartz function. -/
private theorem realSchwartzFlatQuotient_strongDual_exists_bump (χ : ContDiffBump (0 : ℝ))
    (n : ℕ) : ∃ G : 𝓢(ℝ, ℂ), ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ) := by
  have hc : HasCompactSupport (fun y : ℝ ↦ (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) :=
    (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left
  exact ⟨hc.toSchwartzMap ((Complex.ofRealCLM.contDiff.pow n).mul
    (Complex.ofRealCLM.contDiff.comp χ.contDiff)), fun _ ↦ rfl⟩

/-- `y ↦ yⁿ χ(y)` vanishes outside `[-1, 1]` when `χ` does. -/
private theorem realSchwartzFlatQuotient_strongDual_bump_tsupport (χ : ContDiffBump (0 : ℝ))
    (hχ : χ.rOut ≤ 1) (n : ℕ) (G : 𝓢(ℝ, ℂ)) (hG : ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) :
    tsupport (G : ℝ → ℂ) ⊆ Metric.closedBall 0 1 := by
  rw [show (G : ℝ → ℂ) = fun y : ℝ ↦ (y : ℂ) ^ n * ((χ y : ℝ) : ℂ) from funext hG]
  refine tsupport_mul_subset_right.trans ((tsupport_comp_subset Complex.ofReal_zero _).trans ?_)
  rw [χ.tsupport_eq]
  exact Metric.closedBall_subset_closedBall hχ

/-- `x ↦ εⁿ G(x / ε)` is a Schwartz function when `G` has compact support. -/
private theorem realSchwartzFlatQuotient_strongDual_exists_scaled (G : 𝓢(ℝ, ℂ))
    (hG : HasCompactSupport (G : ℝ → ℂ)) (n : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    ∃ ψ : 𝓢(ℝ, ℂ), ∀ x, ψ x = (ε : ℂ) ^ n * G (ε⁻¹ * x) :=
  ⟨HasCompactSupport.toSchwartzMap (f := fun x ↦ (ε : ℂ) ^ n * G (ε⁻¹ * x))
    ((hG.comp_smul (inv_ne_zero hε)).mul_left (f := fun _ ↦ (ε : ℂ) ^ n))
    (contDiff_const.mul ((G.smooth ⊤).comp (contDiff_const.mul contDiff_id))), fun _ ↦ rfl⟩

/-- For `m < n` and `ε ≤ 1`, every seminorm of order `m` of `x ↦ xⁿ χ(x / ε)` is at most `ε`
times a bound that does not depend on `ε`. -/
private theorem realSchwartzFlatQuotient_strongDual_scaled_seminorm (χ : ContDiffBump (0 : ℝ))
    (hχ : χ.rOut ≤ 1) (n m k : ℕ) (hmn : m < n) (G ψ : 𝓢(ℝ, ℂ))
    (hG : ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hψ : ∀ x, ψ x = (ε : ℂ) ^ n * G (ε⁻¹ * x)) :
    SchwartzMap.seminorm ℂ k m ψ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by
  have hGb (y : ℝ) : ‖iteratedDeriv m (G : ℝ → ℂ) y‖ ≤ SchwartzMap.seminorm ℂ 0 m G := by
    have h := SchwartzMap.le_seminorm' ℂ 0 m G y
    rwa [pow_zero, one_mul] at h
  have hC : 0 ≤ SchwartzMap.seminorm ℂ 0 m G := apply_nonneg _ _
  refine SchwartzMap.seminorm_le_bound' ℂ k m _ (by positivity) fun x ↦ ?_
  have hd : iteratedDeriv m (ψ : ℝ → ℂ) x =
      (ε : ℂ) ^ n * ((ε⁻¹) ^ m • iteratedDeriv m (G : ℝ → ℂ) (ε⁻¹ * x)) := by
    rw [show (ψ : ℝ → ℂ) = fun x ↦ (ε : ℂ) ^ n * G (ε⁻¹ * x) from funext hψ,
      iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_smul ((G.smooth ⊤).of_le (mod_cast le_top))]
  have hpow : ε ^ n * (ε⁻¹) ^ m ≤ ε := by
    rw [← pow_sub_mul_pow ε hmn.le, mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow,
      mul_one]
    calc ε ^ (n - m) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by omega)
      _ = ε := pow_one ε
  rw [hd, norm_mul, norm_smul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hε, abs_of_pos (inv_pos.mpr hε)]
  by_cases hx : |x| ≤ 1
  · calc |x| ^ k * (ε ^ n * ((ε⁻¹) ^ m * ‖iteratedDeriv m (G : ℝ → ℂ) (ε⁻¹ * x)‖))
        ≤ 1 * ((ε ^ n * (ε⁻¹) ^ m) * SchwartzMap.seminorm ℂ 0 m G) := by
          rw [← mul_assoc (ε ^ n)]
          gcongr
          · exact pow_le_one₀ (abs_nonneg x) hx
          · exact hGb _
      _ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by
          rw [one_mul]
          gcongr
  · have hout : ε⁻¹ * x ∉ tsupport (G : ℝ → ℂ) := by
      intro h
      have := realSchwartzFlatQuotient_strongDual_bump_tsupport χ hχ n G hG h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
        inv_mul_le_iff₀ hε] at this
      exact hx (by nlinarith [abs_nonneg x])
    have h0 : iteratedDeriv m (G : ℝ → ℂ) (ε⁻¹ * x) = 0 := by
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_eq_zero]
      by_contra hne
      exact hout (support_iteratedFDeriv_subset m hne)
    rw [h0, norm_zero, mul_zero, mul_zero, mul_zero]
    positivity


set_option quotPrecheck false

open scoped UniformConvergence in
/-- Pulling back the strong dual of a quotient is an embedding when every bounded set of the
quotient is the image of a bounded set. -/
private theorem realSchwartzFlatQuotient_strongDual_isEmbedding {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] (K : Submodule 𝕜 E)
    (h : ∀ B : Set (E ⧸ K), Bornology.IsVonNBounded 𝕜 B →
      ∃ S : Set E, Bornology.IsVonNBounded 𝕜 S ∧ B ⊆ K.mkQ '' S) :
    IsEmbedding (fun T : StrongDual 𝕜 (E ⧸ K) ↦ T.comp K.mkQL) := by
  let A := {s : Set E | Bornology.IsVonNBounded 𝕜 s}
  let B := {s : Set (E ⧸ K) | Bornology.IsVonNBounded 𝕜 s}
  let R (f : (E ⧸ K) →ᵤ[B] 𝕜) : E →ᵤ[A] 𝕜 :=
    UniformOnFun.ofFun A (UniformOnFun.toFun B f ∘ K.mkQL)
  have hRc : UniformContinuous R :=
    UniformOnFun.precomp_uniformContinuous (f := K.mkQL) (𝔖 := B) (𝔗 := A)
      (fun _ hs ↦ hs.image K.mkQL)
  have hR : IsUniformInducing R := by
    refine isUniformInducing_iff'.mpr ⟨hRc, ?_⟩
    conv_rhs => rw [UniformOnFun.uniformity_eq]
    refine le_iInf₂ fun s hs ↦ le_iInf₂ fun V hV ↦ ?_
    obtain ⟨S, hS, hsS⟩ := h s hs
    rw [le_principal_iff]
    refine ⟨_, UniformOnFun.gen_mem_uniformity (α := E) (β := 𝕜) (𝔖 := A) (hs := hS) (hV := hV),
      fun fg hfg y hy ↦ ?_⟩
    obtain ⟨x, hx, rfl⟩ := hsS hy
    exact hfg x hx
  let ie := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 A
  let iq := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 B
  have hpull : IsUniformInducing (fun T : StrongDual 𝕜 (E ⧸ K) ↦ T.comp K.mkQL) :=
    (IsUniformInducing.of_comp_iff ie).mp (hR.comp iq)
  refine ⟨hpull.isInducing, fun T T' hT ↦ ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := K.mkQ_surjective y
  exact congrArg (fun L : StrongDual 𝕜 E ↦ L x) hT

section FinitePlace

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Fᵥ(" v ")" => HeightOneSpectrum.adicCompletion F v
local notation "Uᵥ(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "vval(" v ")" => (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ)))

/-- Paper: Lemma 5.3.1.1, p. 240.
The difference of a local test function and its inverse-unit pullback is linear. -/
theorem finitePlaceDifference_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ f - schwartzBruhatUnitTranslate π f) := by
  have hT : IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ schwartzBruhatUnitTranslate π f) := by
    refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
    · exact Subtype.ext (funext fun x ↦ rfl)
    · exact Subtype.ext (funext fun x ↦ rfl)
  exact (LinearMap.id - hT.mk' _).isLinear

/-- Paper: Lemma 5.3.1.1, p. 240.
The local difference subtracts pullback by multiplication by the inverse of the chosen unit
in the local field. The lemma applies this definition to uniformizers. -/
def finitePlaceDifference (v : V) (π : Fᵥ(v)ˣ) : ℬ(Fᵥ(v)) →ₗ[ℂ] ℬ(Fᵥ(v)) :=
  (finitePlaceDifference_isLinear v π).mk' _

/-- Paper: Lemma 5.3.1.1, p. 240.
The difference of the integer-ring indicator at a uniformizer is the integer-unit indicator.
Deviation: The integer-ring indicator is represented by the trivial standard Gaussian of §3.4. -/
theorem finitePlaceDifference_integerIndicator (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (x : Fᵥ(v)) :
    finitePlaceDifference v π (finiteStandardGaussian v 1) (Multiplicative.ofAdd x) =
      (Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ)).indicator (fun _ ↦ (1 : ℂ)) x := by
  classical
  have hG (y : Fᵥ(v)) : finiteStandardGaussian v 1 (Multiplicative.ofAdd y) =
      (v.adicCompletionIntegers F : Set Fᵥ(v)).indicator (fun _ ↦ (1 : ℂ)) y := by
    change finiteStandardGaussianValue v 1 y = _
    unfold finiteStandardGaussianValue
    exact ite_eq_left fun u _ ↦ rfl
  have hval : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hmem (y : Fᵥ(v)) : y ∈ Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ) ↔ vval(v) y = 1 := by
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨u, hu, rfl⟩
      exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
    · have hy0 : y ≠ 0 := fun h0 ↦ by simp [h0] at hy
      exact ⟨Units.mk0 y hy0,
        HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩
  have hπx : vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) = WithZero.exp (1 : ℤ) * vval(v) x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval, ← WithZero.exp_neg, neg_neg]
  change finiteStandardGaussian v 1 (Multiplicative.ofAdd x) -
    finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) = _
  rw [hG, hG]
  rcases lt_trichotomy (vval(v) x) 1 with h | h | h
  · have h1 : vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      have h2 := (WithZero.lt_mul_exp_iff_le (x := vval(v) x * WithZero.exp (1 : ℤ)) (y := 1)
        one_ne_zero).mp
      rw [one_mul] at h2
      rw [hπx, mul_comm]
      exact h2 (mul_lt_mul_of_pos_right h (by simp))
    rw [indicator_of_mem (show x ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.le),
      indicator_of_mem (show _ ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_notMem fun hx ↦ h.ne ((hmem x).mp hx), sub_self]
  · have h1 : ¬ vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      rw [hπx, h, mul_one]
      simp
    rw [indicator_of_mem (show x ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.le),
      indicator_of_notMem (show _ ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_mem ((hmem x).mpr h), sub_zero]
  · have h1 : ¬ vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      rw [hπx, not_le]
      exact h.trans_le (le_mul_of_one_le_left zero_le (by simp))
    rw [indicator_of_notMem (show x ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.not_ge),
      indicator_of_notMem (show _ ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_notMem fun hx ↦ h.ne' ((hmem x).mp hx), sub_zero]

private theorem finitePlaceDifference_injective_aux (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (g : Fᵥ(v) → ℂ) (hlc : IsLocallyConstant g)
    (hcs : HasCompactSupport g) (hg : ∀ x, g x = g ((↑π⁻¹ : Fᵥ(v)) * x)) : g = 0 := by
  have hval : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hv1 : vval(v) π.val < 1 := by
    rw [hval, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hpow (n : ℕ) (x : Fᵥ(v)) : g ((π : Fᵥ(v)) ^ n * x) = g x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, ih, hg (π * x), Units.inv_mul_cancel_left]
  let := Valued.toNontriviallyNormedField (Fᵥ(v)) _
  have hn : ‖(π : Fᵥ(v))‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hv1
  have hconst (x : Fᵥ(v)) : g x = g 0 := by
    have ht : Tendsto (fun n : ℕ ↦ (π : Fᵥ(v)) ^ n * x) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).mul_const x
    have h := (hlc.continuous.tendsto 0).comp ht
    simp only [Function.comp_def, hpow] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  funext x
  by_contra hx
  have hc : support g = univ := eq_univ_of_forall fun y ↦ by
    rw [mem_support, hconst y, ← hconst x]; exact hx
  have hK : IsCompact (univ : Set Fᵥ(v)) := by
    have := hcs.isCompact
    rwa [tsupport, hc, closure_univ] at this
  exact noncompact_univ _ hK

private theorem finitePlaceDifference_injective (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) : Function.Injective (finitePlaceDifference v π) := by
  intro f f' hf
  have hg (x : Fᵥ(v)) : f (Multiplicative.ofAdd x) - f' (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) -
        f' (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) := by
    have h := congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd x)) hf
    change f (Multiplicative.ofAdd x) - f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) =
      f' (Multiplicative.ofAdd x) - f' (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) at h
    linear_combination h
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff F v
    (fun x ↦ f (Multiplicative.ofAdd x))).1 ⟨f, fun _ ↦ rfl⟩
  obtain ⟨hlc', hcs'⟩ := (mem_finitePlaceSchwartz_iff F v
    (fun x ↦ f' (Multiplicative.ofAdd x))).1 ⟨f', fun _ ↦ rfl⟩
  have h0 := finitePlaceDifference_injective_aux v π hπ
    (fun x ↦ f (Multiplicative.ofAdd x) - f' (Multiplicative.ofAdd x)) (hlc.sub hlc')
    (hcs.sub hcs') hg
  refine Subtype.ext (funext fun y ↦ ?_)
  have hy := congrFun h0 (Multiplicative.toAdd y)
  exact sub_eq_zero.mp hy

private theorem finestLocallyConvex_isEmbedding_of_injective {E : Type*} [AddCommGroup E]
    [Module ℂ E] (D : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex E)
    (hD : Function.Injective D) : IsEmbedding D := by
  have : T2Space (FinestLocallyConvex E) := finestLocallyConvex_t2 E
  obtain ⟨L, hL⟩ := D.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hD)
  have hLD : Function.LeftInverse L D := fun f ↦ LinearMap.congr_fun hL f
  exact Topology.IsEmbedding.of_leftInverse hLD
    (continuous_of_finestLocallyConvex E L) (continuous_of_finestLocallyConvex E D)

/-- Paper: Lemma 5.3.1.1, p. 240.
For each fixed uniformizer the local difference is a topological embedding. -/
theorem finitePlaceDifference_isEmbedding (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    IsEmbedding (finitePlaceDifference v π) := by
  have heq := finitePlaceSchwartz_finestTopology F v
  have h := finestLocallyConvex_isEmbedding_of_injective (E := ℬ(Fᵥ(v)))
    (finitePlaceDifference v π) (finitePlaceDifference_injective v π hπ)
  exact (congrArg (fun t ↦ @IsEmbedding ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t
    (fun f ↦ finitePlaceDifference v π f)) heq).mpr h

/-- Paper: Lemma 5.3.1.1, pp. 240–241.
The range of the difference for a fixed uniformizer is closed on the full test space. -/
theorem finitePlaceDifference_isClosed_range (v : V) (π : Fᵥ(v)ˣ)
    (_hπ : vval(v).IsUniformizer π.val) :
    IsClosed (Set.range (finitePlaceDifference v π)) := by
  have heq := finitePlaceSchwartz_finestTopology F v
  have h := finestLocallyConvex_submodule_isClosed (E := ℬ(Fᵥ(v)))
    (LinearMap.range (finitePlaceDifference v π))
  exact (congrArg (fun t ↦ @IsClosed ℬ(Fᵥ(v)) t (Set.range (finitePlaceDifference v π)))
    heq).mpr h

-- TODO(paper-gap): ERRATA R7 gives the failure of independence and range on the whole space.

/-- Paper: Lemma 5.3.1.1, p. 240.
The local difference on integer-unit-invariant functions is independent of the uniformizer.
Deviation: The independence claim is restricted to integer-unit invariants by ERRATA R7. -/
theorem finitePlaceDifference_eq_of_unitInvariant (v : V) (π π' : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (hπ' : vval(v).IsUniformizer π'.val) (f : ℬ(Fᵥ(v)))
    (hf : ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) :
    finitePlaceDifference v π f = finitePlaceDifference v π' f := by
  have hu : π * π'⁻¹ ∈ Uᵥ(v) :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ.val, ← hπ'.val]
      exact mul_inv_cancel₀ hπ'.val_ne_zero)
  refine Subtype.ext (funext fun x ↦ ?_)
  have h : f (Multiplicative.ofAdd ((↑(π * π'⁻¹)⁻¹ : Fᵥ(v)) * ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))) =
      f (Multiplicative.ofAdd ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd)) :=
    congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))) (hf _ hu)
  rw [← mul_assoc, ← Units.val_mul, show (π * π'⁻¹)⁻¹ * π'⁻¹ = π⁻¹ by
    rw [mul_inv_rev, inv_inv, mul_right_comm, mul_inv_cancel, one_mul]] at h
  exact congrArg (fun a ↦ f x - a) h

/-- A test vanishing at zero meets only finitely many valuation shells in its support. -/
private theorem finitePlaceDifference_range_on_unitInvariants_finite (v : V) (f : ℬ(Fᵥ(v)))
    (h₀ : f (Multiplicative.ofAdd 0) = 0) :
    ∃ I : Finset ℤ, ∀ x : Fᵥ(v), f (Multiplicative.ofAdd x) ≠ 0 → (vval(v) x).log ∈ I := by
  classical
  let k (x : Fᵥ(v)) := f (Multiplicative.ofAdd x)
  obtain ⟨hl, hc⟩ := (mem_finitePlaceSchwartz_iff F v k).1 ⟨f, fun _ ↦ rfl⟩
  have hclosed : IsClosed (support k) := (hl.isClopen_fiber 0).isOpen.isClosed_compl
  have hcomp : IsCompact (support k) := hclosed.closure_eq ▸ hc
  let : CompactSpace (support k) := isCompact_iff_compactSpace.mp hcomp
  let a (x : support k) := (vval(v) x.val).log
  have ha : IsLocallyConstant a := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hx : x.val ≠ 0 := fun h ↦ x.property (h ▸ h₀)
    have hv := Valued.locally_const ((Valuation.ne_zero_iff vval(v)).mpr hx)
    filter_upwards [continuous_subtype_val.continuousAt hv] with y hy
    exact congrArg WithZero.log hy
  exact ⟨ha.range_finite.toFinset, fun x hx ↦ ha.range_finite.mem_toFinset.mpr ⟨⟨x, hx⟩, rfl⟩⟩

private theorem finitePlaceDifference_range_on_unitInvariants_radial (v : V) (f : ℬ(Fᵥ(v)))
    (hf : ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) (x y : Fᵥ(v))
    (hx : x ≠ 0) (hy : y ≠ 0) (he : vval(v) x = vval(v) y) :
    f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd y) := by
  let u := Units.mk0 x hx / Units.mk0 y hy
  have hu : u ∈ Uᵥ(v) := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    (show vval(v) (x / y) = 1 by rw [map_div₀, he, div_self ((Valuation.ne_zero_iff _).mpr hy)])
  have h := congrArg (fun g : ℬ(Fᵥ(v)) ↦ g (Multiplicative.ofAdd y)) (hf u⁻¹ (Uᵥ(v).inv_mem hu))
  simpa only [schwartzBruhatUnitTranslate_apply, inv_inv, Units.val_div_eq_div_val,
    Units.val_mk0, div_mul_cancel₀ _ hy, u] using h

private theorem finitePlaceDifference_range_on_unitInvariants_ball (v : V) (n : ℤ) (c : ℂ) :
    ∃ g : ℬ(Fᵥ(v)), ∀ x : Fᵥ(v), g (Multiplicative.ofAdd x) =
      if vval(v) x ≤ WithZero.exp n then c else 0 := by
  classical
  obtain ⟨t, ht⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp n)
  have ht₀ : t ≠ 0 := fun h ↦ WithZero.exp_ne_zero (ht.symm.trans (h ▸ map_zero _))
  refine ⟨c • schwartzBruhatUnitTranslate (Units.mk0 t ht₀) (finiteStandardGaussian v 1), fun x ↦ ?_⟩
  have hx : t⁻¹ * x ∈ v.adicCompletionIntegers F ↔ vval(v) x ≤ WithZero.exp n := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, ht, inv_mul_le_one₀]
    exact zero_lt_iff.mpr WithZero.exp_ne_zero
  change c * finiteStandardGaussianValue v 1 (t⁻¹ * x) = _
  unfold finiteStandardGaussianValue
  rw [ite_eq_left (show ∀ u ∈ Uᵥ(v), (1 : QuasiCharacter Fᵥ(v)ˣ) u = 1 from fun _ _ ↦ rfl)]
  by_cases h : t⁻¹ * x ∈ v.adicCompletionIntegers F
  · rw [indicator_of_mem h, mul_one, ite_eq_left (hx.mp h)]
  · rw [indicator_of_notMem h, mul_zero, ite_eq_right (fun hv ↦ h (hx.mpr hv))]

private theorem finitePlaceDifference_range_on_unitInvariants_step (m n : ℤ) (c : ℂ) :
    (if WithZero.exp m ≤ WithZero.exp n then c else 0) -
      (if WithZero.exp 1 * WithZero.exp m ≤ WithZero.exp n then c else 0) =
      if n = m then c else 0 := by
  simp only [← WithZero.exp_add, WithZero.exp_le_exp]
  split_ifs <;> first | omega | simp_all

/-- Paper: Lemma 5.3.1.1, p. 240.
The image of the integer-unit-invariant subspace under the local difference consists of the
integer-unit-invariant functions vanishing at zero.
Deviation: The domain and the evaluation kernel are restricted by ERRATA R7. -/
theorem finitePlaceDifference_range_on_unitInvariants (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    finitePlaceDifference v π '' {f | ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f} =
      {f | (∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) ∧
        f (Multiplicative.ofAdd 0) = 0} := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩
    have h (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) (y : Fᵥ(v)) :
        f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y)) = f (Multiplicative.ofAdd y) :=
      congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd y)) (hf u hu)
    constructor
    · intro u hu
      apply Subtype.ext
      funext x
      change f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) -
        f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd))) = _
      exact congrArg₂ (· - ·) (h u hu x.toAdd)
        ((congrArg (fun z ↦ f (Multiplicative.ofAdd z))
          (mul_left_comm (↑π⁻¹ : Fᵥ(v)) (↑u⁻¹ : Fᵥ(v)) x.toAdd)).trans
            (h u hu ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
    · change f (Multiplicative.ofAdd 0) - f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * 0)) = 0
      simp
  · rintro f ⟨hf, h₀⟩
    have H := finitePlaceDifference_range_on_unitInvariants_finite (F := F) v f h₀
    let I := H.choose
    have hI := H.choose_spec
    choose t ht using fun n : ℤ ↦ v.valuedAdicCompletion_surjective F (WithZero.exp n)
    let c (n : ℤ) := f (Multiplicative.ofAdd (t n))
    choose b hb using fun n : ℤ ↦ finitePlaceDifference_range_on_unitInvariants_ball (F := F) v n (c n)
    -- Each weighted ball contributes its boundary shell under the difference.
    let g := ∑ n ∈ I, b n
    have hg (x : Fᵥ(v)) : g (Multiplicative.ofAdd x) =
        ∑ n ∈ I, if vval(v) x ≤ WithZero.exp n then c n else 0 := by
      calc
        _ = ∑ n ∈ I, b n (Multiplicative.ofAdd x) :=
          map_sum ((LinearMap.proj (Multiplicative.ofAdd x)).comp
            (schwartzBruhatSubmodule (Multiplicative Fᵥ(v))).subtype) b I
        _ = _ := Finset.sum_congr rfl fun i _ ↦ hb i x
    refine ⟨g, ?_, ?_⟩
    · intro u hu
      have hu₁ := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (Uᵥ(v).inv_mem hu)
      apply Subtype.ext
      funext x
      change g (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) = g (Multiplicative.ofAdd x.toAdd)
      rw [hg, hg, map_mul, hu₁, one_mul]
    · have hπv : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
        (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.valuedAdicCompletion_surjective F)))
      have hπi : vval(v) (↑π⁻¹ : Fᵥ(v)) = WithZero.exp 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hπv, ← WithZero.exp_neg, neg_neg]
      apply Subtype.ext
      funext x
      change g (Multiplicative.ofAdd x.toAdd) -
        g (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)) = f (Multiplicative.ofAdd x.toAdd)
      by_cases hx : x.toAdd = 0
      · simp only [hx, mul_zero, sub_self, h₀]
      let m := (vval(v) x.toAdd).log
      have hm : WithZero.exp m = vval(v) x.toAdd :=
        WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)
      rw [hg, hg, map_mul, hπi, ← hm, ← Finset.sum_sub_distrib]
      simp only [finitePlaceDifference_range_on_unitInvariants_step, Finset.sum_ite_eq']
      by_cases hi : m ∈ I
      · rw [ite_eq_left hi]
        have htm : t m ≠ 0 := fun e ↦ WithZero.exp_ne_zero ((ht m).symm.trans (e ▸ map_zero _))
        exact finitePlaceDifference_range_on_unitInvariants_radial (F := F) v f hf _ _ htm hx ((ht m).trans hm)
      · exact (ite_eq_right hi).trans (not_ne_iff.mp (fun h ↦ hi (hI _ h))).symm

-- TODO(paper-gap): At the trivial quasi-character, the eigendistribution in (5.3.1.3)
-- is a multiple of Dirac evaluation and vanishes on the integer-unit indicator.
-- For a nontrivial unramified character the unit-shell and integer-ring
-- normalizations differ by the following factor.

/-- Paper: (5.3.1.3), p. 240.
An eigendistribution normalized on the integer ring as in §3.4 takes the value
one minus the weight of the uniformizer on the unit shell.
Deviation: The shell normalization requires dividing by this factor when it is nonzero. -/
theorem finiteEigendistribution_unitShell (v : V) (π : Fᵥ(v)ˣ)
    (_hπ : vval(v).IsUniformizer π.val) (c : QuasiCharacter Fᵥ(v)ˣ)
    (T : StrongDual ℂ ℬ(Fᵥ(v))) (hT : T ∈ schwartzBruhatEigendistributions (R := Fᵥ(v)) c)
    (hnorm : T (finiteStandardGaussian v 1) = 1) :
    T (finitePlaceDifference v π (finiteStandardGaussian v 1)) = 1 - c π := by
  let f : ℬ(Fᵥ(v)) := finiteStandardGaussian v 1
  change T (f - schwartzBruhatUnitTranslate π f) = 1 - c π
  have heigen : ∀ (g : Fᵥ(v)ˣ) (h : ℬ(Fᵥ(v))),
      T (schwartzBruhatUnitTranslate g h) = c g * T h := hT
  calc
    _ = T f - T (schwartzBruhatUnitTranslate π f) := map_sub T _ _
    _ = T f - c π * T f := congrArg (fun a ↦ T f - a) (heigen π f)
    _ = 1 - c π := by rw [show T f = 1 from hnorm, mul_one]

local instance instMeasurableSpaceAdicUnitsSec3a (v : V) : MeasurableSpace Fᵥ(v)ˣ :=
  borel _

local notation "μᵥ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
Weil's local principal value subtracts the uniformizer translate of the normalized
integer-unit average. -/
def finitePlacePrincipalValueFun (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) : ℂ :=
  f x - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
    ∫ u in Uᵥ(v), f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
      ∂μᵥ(v)

/-- Paper: Lemma 5.3.1.3, p. 241.
The local Haar mass on integer units is positive and finite, and the scalar orbit integrals
defining the principal value exist. -/
theorem finitePlacePrincipalValue_integrable (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) :
    0 < μᵥ(v).real Uᵥ(v) ∧
      IntegrableOn
        (fun u : Fᵥ(v)ˣ ↦
          f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))))
        Uᵥ(v) μᵥ(v) := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : (μᵥ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hO : IsOpen (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  refine ⟨ENNReal.toReal_pos (hO.measure_pos _ ⟨1, Uᵥ(v).one_mem⟩).ne' hK.measure_lt_top.ne, ?_⟩
  refine ContinuousOn.integrableOn_compact hK (Continuous.continuousOn ?_)
  exact (schwartzBruhat_continuous f).comp (continuous_ofAdd.comp
    ((Units.continuous_val.comp continuous_inv).mul continuous_const))

/-- The unit average of a locally constant compactly supported function, after scaling by a
fixed unit, is again locally constant with compact support. -/
private theorem finitePlacePrincipalValue_mem_average {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [MeasurableSpace Kˣ] [OpensMeasurableSpace Kˣ]
    (μ : Measure Kˣ) (U : Set Kˣ) (hO : IsOpen U) (hK : IsCompact U) (c : Kˣ) (F0 : K → ℂ)
    (hlc : IsLocallyConstant F0) (hcs : HasCompactSupport F0) :
    IsLocallyConstant (fun y : K ↦ ∫ u in U, F0 ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * y)) ∂μ) ∧
      HasCompactSupport (fun y : K ↦ ∫ u in U, F0 ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * y)) ∂μ) := by
  have hinv : Continuous fun u : Kˣ ↦ (↑u⁻¹ : K) := Units.continuous_val.comp continuous_inv
  refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_, ?_⟩
  · have hΦ : IsLocallyConstant fun p : K × Kˣ ↦
        (F0 ((↑p.2⁻¹ : K) * ((↑c⁻¹ : K) * p.1)), F0 ((↑p.2⁻¹ : K) * ((↑c⁻¹ : K) * x))) :=
      (hlc.comp_continuous ((hinv.comp continuous_snd).mul
        (continuous_const.mul continuous_fst))).prodMk
        (hlc.comp_continuous ((hinv.comp continuous_snd).mul continuous_const))
    obtain ⟨A, B, hA, -, hxA, hUB, hAB⟩ := generalized_tube_lemma isCompact_singleton hK
      (hΦ {q | q.1 = q.2}) (fun p hp ↦ by
        obtain ⟨hp1, -⟩ := hp
        change F0 _ = F0 _
        rw [Set.mem_singleton_iff.mp hp1])
    exact ⟨A, hA, hxA rfl, fun x' hx' ↦
      setIntegral_congr_fun hO.measurableSet fun u hu ↦
        hAB (show ((x', u) : K × Kˣ) ∈ A ×ˢ B from ⟨hx', hUB hu⟩)⟩
  · refine HasCompactSupport.intro
      ((hK.prod hcs.isCompact).image (f := fun p : Kˣ × K ↦ (↑c : K) * ((↑p.1 : K) * p.2))
        (continuous_const.mul ((Units.continuous_val.comp continuous_fst).mul continuous_snd)))
      fun x hx ↦ setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
    by_contra hne
    refine hx ⟨(u, (↑u⁻¹ : K) * ((↑c⁻¹ : K) * x)), ⟨hu, subset_tsupport _ hne⟩, ?_⟩
    change (↑c : K) * ((↑u : K) * ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * x))) = x
    rw [Units.mul_inv_cancel_left, Units.mul_inv_cancel_left]

/-- Paper: Lemma 5.3.1.3, p. 241.
The formula for the local principal value produces a Schwartz–Bruhat test function. -/
theorem finitePlacePrincipalValue_mem (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValueFun v π f ∈ schwartzBruhatSubmodule (Multiplicative Fᵥ(v)) :=
  by
  have hlc := (mem_finitePlaceSchwartz_iff F v (fun y ↦ f (Multiplicative.ofAdd y))).mp
    ⟨f, fun _ ↦ rfl⟩
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have hO : IsOpen (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  have h := finitePlacePrincipalValue_mem_average μᵥ(v) _ hO hK π _ hlc.1 hlc.2
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v _).mpr h
  have heq : finitePlacePrincipalValueFun v π f =
      (f : Multiplicative Fᵥ(v) → ℂ) -
        (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ • (g : Multiplicative Fᵥ(v) → ℂ) :=
    funext fun x ↦ by
      change _ = f x - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ * g (Multiplicative.ofAdd x.toAdd)
      rw [hg]
      rfl
  rw [heq]
  exact Submodule.sub_mem _ (show schwartzBruhatSubmodule _ from f).property
    (Submodule.smul_mem _ _ (show schwartzBruhatSubmodule _ from g).property)

local notation "pvBundle(" v ", " π ")" =>
  (fun f : ℬ(Fᵥ(v)) ↦
    (⟨finitePlacePrincipalValueFun v π f, finitePlacePrincipalValue_mem v π f⟩ : ℬ(Fᵥ(v))))

/-- Paper: Lemma 5.3.1.3, p. 241.
The bundled local averaging formula is linear. -/
theorem finitePlacePrincipalValue_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (pvBundle(v, π)) := by
  refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
  · refine Subtype.ext (funext fun x ↦ ?_)
    have hf := (finitePlacePrincipalValue_integrable v π f x).2
    have hg := (finitePlacePrincipalValue_integrable v π g x).2
    change finitePlacePrincipalValueFun v π (f + g) x =
      finitePlacePrincipalValueFun v π f x + finitePlacePrincipalValueFun v π g x
    unfold finitePlacePrincipalValueFun
    simp only [show ∀ y, (f + g) y = f y + g y from fun _ ↦ rfl]
    rw [integral_add hf hg]
    ring
  · refine Subtype.ext (funext fun x ↦ ?_)
    change finitePlacePrincipalValueFun v π (c • f) x = c * finitePlacePrincipalValueFun v π f x
    unfold finitePlacePrincipalValueFun
    simp only [show ∀ y, (c • f) y = c * f y from fun _ ↦ rfl]
    rw [integral_const_mul]
    ring

/-- Paper: Lemma 5.3.1.3, p. 241.
The local principal value formula is continuous. -/
theorem finitePlacePrincipalValue_continuous (v : V) (π : Fᵥ(v)ˣ) :
    @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) _ _
      ((finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))).toFun := by
  let E := FinestLocallyConvex ℬ(Fᵥ(v))
  let L : E →ₗ[ℂ] E := (finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))
  apply (congrArg (fun t ↦ @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t L.toFun)
    (finitePlaceSchwartz_finestTopology F v)).mpr
  have h := finestLocallyConvex_withSeminorms ℬ(Fᵥ(v))
  haveI : IsTopologicalAddGroup E := h.isTopologicalAddGroup
  exact h.continuous_of_continuous_comp L fun p ↦ h.continuous_seminorm (p.comp L)

/-- Paper: Definition 5.3.1.2, p. 241.
The principal value is the identity minus the uniformizer pullback of the trivial-isotype
projection. A uniformizer is chosen from the discrete local valuation. -/
def finitePlacePrincipalValue (v : V) : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) :=
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  ⟨(finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π)),
    finitePlacePrincipalValue_continuous v π⟩

/-- A left-invariant set integral is unchanged by left translation by an element that
preserves the set. -/
private theorem finitePlacePrincipalValue_spec_setIntegral_mul_left {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Set G)
    (hS : MeasurableSet S) (g : G → ℂ) (w : G) (hw : ∀ u, w * u ∈ S ↔ u ∈ S) :
    ∫ u in S, g (w * u) ∂μ = ∫ u in S, g u ∂μ := by
  rw [← integral_indicator hS, ← integral_indicator hS,
    ← integral_mul_left_eq_self (S.indicator g) w]
  congr 1
  funext u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((hw u).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h ↦ hu ((hw u).mp h))]

/-- The scalar principal-value formula does not depend on the choice of uniformizer, by left
invariance of the multiplicative Haar measure on the integer units. -/
private theorem finitePlacePrincipalValue_spec_indep (v : V) (π π' : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (hπ' : vval(v).IsUniformizer π'.val) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) :
    finitePlacePrincipalValueFun v π f x = finitePlacePrincipalValueFun v π' f x := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsMulLeftInvariant := by
    unfold finiteLocalMultiplicativeTamagawaMeasure
    infer_instance
  have hu : π * π'⁻¹ ∈ Uᵥ(v) :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ.val, ← hπ'.val]
      exact mul_inv_cancel₀ hπ'.val_ne_zero)
  have hw : π'⁻¹ * π ∈ Uᵥ(v) := mul_comm π π'⁻¹ ▸ hu
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  unfold finitePlacePrincipalValueFun
  congr 2
  refine Eq.trans ?_ (finitePlacePrincipalValue_spec_setIntegral_mul_left μᵥ(v) _ hU
    (fun u : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))))
    (π'⁻¹ * π) (fun u ↦ Subgroup.mul_mem_cancel_left _ hw))
  congr 1
  funext u
  rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  group

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
The scalar formula for the operator works with every choice of uniformizer. -/
theorem finitePlacePrincipalValue_spec (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    ∀ (f : ℬ(Fᵥ(v))) (x : Multiplicative Fᵥ(v)),
      finitePlacePrincipalValue v f x = finitePlacePrincipalValueFun v π f x := by
  intro f x
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact finitePlacePrincipalValue_spec_indep v (Units.mk0 (h.choose : Fᵥ(v))
    h.choose_spec.ne_zero) π h.choose_spec hπ f x

open Classical in
/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
Weil's operator is uniquely specified by acting as the local difference on the trivial isotype
and as the identity on every nontrivial integer-unit isotype. Both formulas preserve the
corresponding isotype. -/
theorem finitePlacePrincipalValue_unique (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    let obeys := fun P : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) ↦
      ∀ (χ : PontryaginDual Uᵥ(v)) (f : ℬ(Fᵥ(v))),
        (∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val f = (χ u : ℂ) • f) →
        P f = if χ = 1 then finitePlaceDifference v π f else f
    obeys (finitePlacePrincipalValue v) ∧
      ∀ P, obeys P → P = finitePlacePrincipalValue v := by sorry

/-- The principal value is injective: a test in its kernel is invariant under the integer
units and under the uniformizer, so it vanishes. -/
private theorem finitePlacePrincipalValue_isClosedEmbedding_injective (v : V) :
    Function.Injective (finitePlacePrincipalValue v) := by
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  have hπ : vval(v).IsUniformizer π.val := h.choose_spec
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsMulLeftInvariant := by
    unfold finiteLocalMultiplicativeTamagawaMeasure
    infer_instance
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  intro f f' hff'
  set k := f - f' with hk
  have hP : ∀ x, k x = (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
        ∂μᵥ(v) := by
    intro x
    have h0 : finitePlacePrincipalValue v k = 0 := by rw [hk, map_sub, hff', sub_self]
    have h1 := finitePlacePrincipalValue_spec v π hπ k x
    rw [h0] at h1
    unfold finitePlacePrincipalValueFun at h1
    exact (sub_eq_zero.mp h1.symm)
  have hpos := (finitePlacePrincipalValue_integrable v π k 1).1
  have hm : (μᵥ(v).real Uᵥ(v) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  -- invariance of the average
  have hI : ∀ (w : Fᵥ(v)ˣ), w ∈ Uᵥ(v) → ∀ y : Fᵥ(v),
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((w : Fᵥ(v)) * y))) ∂μᵥ(v) =
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y)) ∂μᵥ(v) := by
    intro w hw y
    have hw' : w⁻¹ ∈ Uᵥ(v) := Subgroup.inv_mem _ hw
    rw [← finitePlacePrincipalValue_spec_setIntegral_mul_left μᵥ(v) _ hU
      (fun u : Fᵥ(v)ˣ ↦ k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y))) w⁻¹
      (fun u ↦ Subgroup.mul_mem_cancel_left _ hw')]
    congr 1
    funext u
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    ring_nf
  have hinv : ∀ (w : Fᵥ(v)ˣ), w ∈ Uᵥ(v) → ∀ y : Fᵥ(v),
      k (Multiplicative.ofAdd ((w : Fᵥ(v)) * y)) = k (Multiplicative.ofAdd y) := by
    intro w hw y
    rw [hP, hP]
    congr 1
    change ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) *
      ((↑π⁻¹ : Fᵥ(v)) * ((w : Fᵥ(v)) * y)))) ∂μᵥ(v) =
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * y))) ∂μᵥ(v)
    rw [mul_left_comm, hI w hw]
  have hstep : ∀ x : Fᵥ(v), k (Multiplicative.ofAdd x) =
      k (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) := by
    intro x
    rw [hP]
    change (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ * ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) *
      ((↑π⁻¹ : Fᵥ(v)) * x))) ∂μᵥ(v) = _
    rw [setIntegral_congr_fun hU (g := fun _ ↦ k (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)))
      fun u hu ↦ hinv u⁻¹ (Subgroup.inv_mem _ hu) _, setIntegral_const, Complex.real_smul]
    field_simp
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff F v
    (fun x ↦ k (Multiplicative.ofAdd x))).1 ⟨k, fun _ ↦ rfl⟩
  have h0 := finitePlaceDifference_injective_aux v π hπ _ hlc hcs hstep
  refine sub_eq_zero.mp (SchwartzBruhat.ext fun y ↦ ?_)
  exact congrFun h0 (Multiplicative.toAdd y)

/-- Paper: Lemma 5.3.1.3, p. 241.
Weil's local principal value is a topological embedding with closed range. -/
theorem finitePlacePrincipalValue_isClosedEmbedding (v : V) :
    IsClosedEmbedding (finitePlacePrincipalValue v) := by
  have heq := finitePlaceSchwartz_finestTopology F v
  have h := finestLocallyConvex_isEmbedding_of_injective (E := ℬ(Fᵥ(v)))
    (finitePlacePrincipalValue v).toLinearMap
    (finitePlacePrincipalValue_isClosedEmbedding_injective v)
  have hemb : IsEmbedding (finitePlacePrincipalValue v) :=
    (congrArg (fun t ↦ @IsEmbedding ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t
      (fun f ↦ finitePlacePrincipalValue v f)) heq).mpr h
  have hc := finestLocallyConvex_submodule_isClosed (E := ℬ(Fᵥ(v)))
    (LinearMap.range (finitePlacePrincipalValue v).toLinearMap)
  have hcl : IsClosed (Set.range (finitePlacePrincipalValue v)) :=
    (congrArg (fun t ↦ @IsClosed ℬ(Fᵥ(v)) t (Set.range (finitePlacePrincipalValue v)))
      heq).mpr hc
  exact ⟨hemb, hcl⟩

private theorem finitePlacePrincipalValue_range_integral {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (K : Subgroup G) (a : G) (ha : a ∈ K) (f : G → ℂ) :
    ∫ x in K, f (a * x) ∂μ = ∫ x in K, f x ∂μ := by
  have he : (fun x : G ↦ a * x) ⁻¹' (K : Set G) = K := by
    ext x
    simp only [mem_preimage]
    constructor
    · intro h
      have := K.mul_mem (K.inv_mem ha) h
      simpa using this
    · exact K.mul_mem ha
  have hp := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding f (K : Set G)
  rw [he] at hp
  exact hp

private theorem finitePlacePrincipalValue_range_zero (v : V) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValue v f (Multiplicative.ofAdd 0) = 0 := by
  let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  rw [finitePlacePrincipalValue_spec v π h.choose_spec]
  unfold finitePlacePrincipalValueFun
  simp only [show (Multiplicative.ofAdd (0 : Fᵥ(v))).toAdd = 0 from rfl, mul_zero,
    setIntegral_const, Complex.real_smul]
  have hm : (μᵥ(v).real Uᵥ(v) : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v π f (Multiplicative.ofAdd 0)).1.ne'
  field_simp
  ring

private theorem finitePlacePrincipalValue_range_invariant (v : V) (f : ℬ(Fᵥ(v))) :
    ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u (f - finitePlacePrincipalValue v f) =
      f - finitePlacePrincipalValue v f := by
  intro u hu
  let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  letI : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  let : (μᵥ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  apply Subtype.ext
  funext x
  change (f - finitePlacePrincipalValue v f) (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) = _
  change f _ - finitePlacePrincipalValue v f _ = f x - finitePlacePrincipalValue v f x
  have hp1 := finitePlacePrincipalValue_spec v π h.choose_spec f
    (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd))
  have hp2 := finitePlacePrincipalValue_spec v π h.choose_spec f x
  apply (congrArg₂ (fun a b : ℂ ↦
    f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) - a = f x - b) hp1 hp2).mpr
  unfold finitePlacePrincipalValueFun
  have hi := finitePlacePrincipalValue_range_integral (μᵥ(v)) Uᵥ(v) u hu
    (fun a : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))))
  have hi' : (∫ a : Fᵥ(v)ˣ in Uᵥ(v),
      f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)))) ∂μᵥ(v)) =
      ∫ a : Fᵥ(v)ˣ in Uᵥ(v), f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))) ∂μᵥ(v) := by
    convert hi using 1
    congr 1
    funext a
    simp only [mul_inv_rev, Units.val_mul]
    ring
  change _ - (_ - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
      (∫ a : Fᵥ(v)ˣ in Uᵥ(v), f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)))) ∂μᵥ(v))) = _
  rw [hi']
  ring

/-- Paper: Lemmas 5.3.1.1 and 5.3.1.3, pp. 240–241.
Weil's operator maps onto all tests vanishing at zero.
Deviation: The full evaluation kernel belongs to the averaged operator from (5.3.1.5). -/
theorem finitePlacePrincipalValue_range (v : V) :
    Set.range (finitePlacePrincipalValue v) =
      {f : ℬ(Fᵥ(v)) | f (Multiplicative.ofAdd 0) = 0} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact finitePlacePrincipalValue_range_zero v g
  · intro hf
    let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
    have hb : (f - finitePlacePrincipalValue v f) ∈
        {f | (∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) ∧ f (Multiplicative.ofAdd 0) = 0} := by
      refine ⟨finitePlacePrincipalValue_range_invariant v f, ?_⟩
      change f (Multiplicative.ofAdd 0) - finitePlacePrincipalValue v f (Multiplicative.ofAdd 0) = 0
      exact sub_eq_zero.mpr (hf.trans (finitePlacePrincipalValue_range_zero v f).symm)
    have hb' := (Set.ext_iff.mp (finitePlaceDifference_range_on_unitInvariants v π h.choose_spec)
      (f - finitePlacePrincipalValue v f)).mpr hb
    obtain ⟨g, hg, hge⟩ := hb'
    have hP : finitePlacePrincipalValue v g = finitePlaceDifference v π g := by
      have huniq := (finitePlacePrincipalValue_unique v π h.choose_spec).1 1 g
      have hh : ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val g = ((1 : PontryaginDual Uᵥ(v)) u : ℂ) • g := by
        intro u
        simpa using hg u.val u.property
      simpa only [if_pos rfl, ite_true] using huniq hh
    refine ⟨f + g, ?_⟩
    calc
      finitePlacePrincipalValue v (f + g) = finitePlacePrincipalValue v f + finitePlacePrincipalValue v g := map_add _ _ _
      _ = finitePlacePrincipalValue v f + (f - finitePlacePrincipalValue v f) := congrArg (finitePlacePrincipalValue v f + ·) (hP.trans hge)
      _ = f := by abel

end FinitePlace

section AdelicPrincipalValue

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬₛ(" S ")" => ℬ(SAdeleRing F S)
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)

open Classical in
variable (F) in
/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value applies the local operators in the selected finite factors.
Deviation: The tensor decomposition is the one from the Lean version of Proposition 2.1.4.1. -/
def sAdelePrincipalValue {S S₀ : Finset V} (_h₀ : S₀ ⊆ S) : ℬₛ(S) →ₗ[ℂ] ℬₛ(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] w : S, ℬ(w.val.adicCompletion F))
  let P : W →ₗ[ℂ] W := PiTensorProduct.map (R := ℂ) fun w : S ↦
    if w.val ∈ S₀ then (finitePlacePrincipalValue w.val).toLinearMap else LinearMap.id
  let idArch : ℬ(InfiniteAdeleRing F) →ₗ[ℂ] ℬ(InfiniteAdeleRing F) := LinearMap.id
  e.toLinearMap.comp ((TensorProduct.map idArch P).comp e.symm.toLinearMap)

variable (F) in
/-- Paper: Definition 5.3.1.4(2), p. 242.
The global principal value acts in the S₀-local factor and leaves the complementary factor
unchanged. -/
def adelePrincipalValue (S₀ : Finset V) : ℬ(𝔸[F]) →ₗ[ℂ] ℬ(𝔸[F]) :=
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose
  let idTail : ℬ(FiniteAdeleTail F S₀) →ₗ[ℂ] ℬ(FiniteAdeleTail F S₀) := LinearMap.id
  e.toLinearMap.comp
    ((TensorProduct.map (sAdelePrincipalValue F (Finset.Subset.refl S₀)) idTail).comp
      e.symm.toLinearMap)

private theorem sAdelePrincipalValue_tmul_aux {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (p : ι → Prop) [DecidablePred p] (T : ∀ i, D i →L[ℂ] D i) (f : A) (g : ∀ i, D i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map fun i ↦
      if p i then (T i).toLinearMap else LinearMap.id
    let I : A →ₗ[ℂ] A := LinearMap.id
    (e.toLinearMap.comp ((TensorProduct.map I P).comp e.symm.toLinearMap))
      (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) = e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, if p i then T i (g i) else g i)) := by
  intro W P I
  change e (TensorProduct.map I P (e.symm (e _))) = e _
  erw [e.symm_apply_apply, TensorProduct.map_tmul]
  apply congrArg e
  apply congrArg (TensorProduct.tmul ℂ f)
  exact (PiTensorProduct.map_tprod _ g).trans (congrArg (PiTensorProduct.tprod ℂ)
    (funext fun i ↦ DFunLike.ite_apply (P := p i) (T i).toLinearMap LinearMap.id (g i)))

open Classical in
/-- Paper: Definition 5.3.1.4(1), p. 242.
On pure tensors the S-local operator acts by the local principal value in each selected factor. -/
theorem sAdelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePrincipalValue F h₀ (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) =
      e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w)) := by
  intro e
  unfold sAdelePrincipalValue
  with_reducible
    exact sAdelePrincipalValue_tmul_aux e (fun w : S ↦ w.val ∈ S₀)
      (fun w ↦ finitePlacePrincipalValue w.val) f g

/-- Paper: Definition 5.3.1.4(2), p. 242.
Through any stage containing S₀ the global operator acts as the S-local operator on the stage
factor and as the identity on the tail. -/
theorem adelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬₛ(S)) (g : ℬ(FiniteAdeleTail F S)) :
    let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
    adelePrincipalValue F S₀ (e (f ⊗ₜ[ℂ] g)) = e (sAdelePrincipalValue F h₀ f ⊗ₜ[ℂ] g) :=
  by sorry

/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value is a topological embedding with closed range. -/
theorem sAdelePrincipalValue_isClosedEmbedding {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    IsClosedEmbedding (sAdelePrincipalValue F h₀) := by sorry

/-- Paper: Definition 5.3.1.4(2), p. 242.
The global principal value is a topological embedding with closed range. -/
theorem adelePrincipalValue_isClosedEmbedding (S₀ : Finset V) :
    IsClosedEmbedding (adelePrincipalValue F S₀) := by sorry

local instance instMeasurableSpaceAdicUnitsSec3aKernel (v : V) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

/-- The unit of the S-local adele ring that is the given local unit at `v` and `1` at every
other place of `S`; translating by it rescales only the `v`-coordinate of the argument. -/
private def adelicPrincipalValueLocalUnit {S : Finset V} (v : S)
    (c : (v.val.adicCompletion F)ˣ) : (SAdeleRing F S)ˣ := by
  classical
  refine Units.mk (1, Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.val)
    (1, Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.inv) ?_ ?_
  · refine Prod.ext (by simp) (funext fun w => ?_)
    by_cases h : w = v
    · subst h
      simp [Function.update_apply, Units.mul_inv]
    · simp [Function.update_apply, h]
  · refine Prod.ext (by simp) (funext fun w => ?_)
    by_cases h : w = v
    · subst h
      simp [Function.update_apply, Units.inv_mul]
    · simp [Function.update_apply, h]

/-- S-local theta of a translate is S-local theta evaluated at the inverse-translated idele. -/
private theorem sAdelePrincipalValue_preserves_thetaKernel_translate
    {S : Finset V} (g x : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x =
      sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp
    (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t => congrArg (fun y => f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (d t).val x.val)

/-- The inverse of the local unit rescales only the `v`-coordinate. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_fst {S : Finset V} (v : S)
    (c : (v.val.adicCompletion F)ˣ) (y : SAdeleRing F S) :
    (((adelicPrincipalValueLocalUnit v c)⁻¹ : (SAdeleRing F S)ˣ).val * y).1 = y.1 := by
  change (1 : InfiniteAdeleRing F) * y.1 = y.1
  exact one_mul _

private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_self {S : Finset V} (v : S)
    (c : (v.val.adicCompletion F)ˣ) (y : SAdeleRing F S) :
    (((adelicPrincipalValueLocalUnit v c)⁻¹ : (SAdeleRing F S)ˣ).val * y).2 v =
      (↑c⁻¹ : v.val.adicCompletion F) * y.2 v := by
  classical
  change Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.inv v * y.2 v = _
  rw [Function.update_self]
  rfl

private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_ne {S : Finset V} (v : S)
    (c : (v.val.adicCompletion F)ˣ) (y : SAdeleRing F S) {w : S} (h : w ≠ v) :
    (((adelicPrincipalValueLocalUnit v c)⁻¹ : (SAdeleRing F S)ˣ).val * y).2 w = y.2 w := by
  classical
  change Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.inv w * y.2 w = _
  rw [Function.update_of_ne h, one_mul]

private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_continuous {S : Finset V} (v : S) :
    Continuous fun c : (v.val.adicCompletion F)ˣ => adelicPrincipalValueLocalUnit v c := by
  classical
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun c : (v.val.adicCompletion F)ˣ =>
      ((1 : InfiniteAdeleRing F),
        Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.val)
    exact continuous_const.prodMk (continuous_const.update v Units.continuous_val)
  · change Continuous fun c : (v.val.adicCompletion F)ˣ =>
      ((1 : InfiniteAdeleRing F),
        Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.inv)
    exact continuous_const.prodMk (continuous_const.update v
      (Units.continuous_val.comp continuous_inv))


/-- The orbit integrand of a test is integrable over the integer units. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_integrableOn {S : Finset V} (v : S) (π : (v.val.adicCompletion F)ˣ)
    (g : ℬₛ(S)) (y : SAdeleRing F S) :
    IntegrableOn (fun u : (v.val.adicCompletion F)ˣ => g (Multiplicative.ofAdd
      (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y))) ((HeightOneSpectrum.adicCompletionIntegers F v.val).units : Set (v.val.adicCompletion F)ˣ) (finiteLocalMultiplicativeTamagawaMeasure F v.val) := by
  have : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  have : ((finiteLocalMultiplicativeTamagawaMeasure F v.val)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  have hK : IsCompact ((HeightOneSpectrum.adicCompletionIntegers F v.val).units : Set (v.val.adicCompletion F)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v.val))
  refine ContinuousOn.integrableOn_compact hK (Continuous.continuousOn ?_)
  exact (schwartzBruhat_continuous g).comp (continuous_ofAdd.comp
    ((Units.continuous_val.comp (continuous_inv.comp ((sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_continuous v).comp
      (continuous_const.mul continuous_id)))).mul continuous_const))

/-- On a pure tensor, the single-place principal value has the orbit-average formula. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_tmul {S : Finset V} (v : S) (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F))
    (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)) (y : SAdeleRing F S) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
        (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd y) =
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd y) - (((finiteLocalMultiplicativeTamagawaMeasure F v.val)).real ((HeightOneSpectrum.adicCompletionIntegers F v.val).units : Set (v.val.adicCompletion F)ˣ) : ℂ)⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units : Set (v.val.adicCompletion F)ˣ), e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y)) ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val) := by
  classical
  intro e
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  have h1 := sAdelePrincipalValue_tmul (Finset.singleton_subset_iff.mpr v.property) a g
  have hsplit : ∀ G : ∀ w : S, ℬ(w.val.adicCompletion F), ∀ z : SAdeleRing F S,
      (∀ w, w ≠ v → G w (Multiplicative.ofAdd (z.2 w)) = g w (Multiplicative.ofAdd (y.2 w))) →
      ∏ w, G w (Multiplicative.ofAdd (z.2 w)) = G v (Multiplicative.ofAdd (z.2 v)) *
        ∏ w ∈ Finset.univ.erase v, g w (Multiplicative.ofAdd (y.2 w)) := by
    intro G z hG
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
    congr 1
    exact Finset.prod_congr rfl fun w hw => hG w (Finset.ne_of_mem_erase hw)
  have hne : ∀ w : S, w ≠ v → w.val ∉ ({v.val} : Finset V) := fun w hw hmem =>
    hw (Subtype.ext (Finset.mem_singleton.mp hmem))
  have hL : sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
      (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd y) =
        (a (Multiplicative.ofAdd y.1)) * (finitePlacePrincipalValue v.val (g v) (Multiplicative.ofAdd (y.2 v)) * ∏ w ∈ Finset.univ.erase v, g w (Multiplicative.ofAdd (y.2 w))) := by
    refine (congrArg (fun φ : ℬₛ(S) => φ (Multiplicative.ofAdd y)) h1).trans
      ((he a _ y).trans ?_)
    rw [hsplit _ y (fun w hw => by rw [if_neg (hne w hw)]), if_pos (Finset.mem_singleton_self _)]
  have hE : e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd y) =
      (a (Multiplicative.ofAdd y.1)) * (g v (Multiplicative.ofAdd (y.2 v)) * ∏ w ∈ Finset.univ.erase v, g w (Multiplicative.ofAdd (y.2 w))) :=
    (he a g y).trans (by rw [hsplit g y (fun _ _ => rfl)])
  have hR' : ∀ u : (v.val.adicCompletion F)ˣ,
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd
        (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y)) =
      ((a (Multiplicative.ofAdd y.1)) * ∏ w ∈ Finset.univ.erase v, g w (Multiplicative.ofAdd (y.2 w))) * g v (Multiplicative.ofAdd
        ((↑u⁻¹ : v.val.adicCompletion F) * ((↑π⁻¹ : v.val.adicCompletion F) * y.2 v))) := by
    intro u
    refine (he a g _).trans ?_
    rw [sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_fst, hsplit _ _ (fun w hw => by rw [sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_ne v _ y hw]),
      sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_self, mul_inv_rev, Units.val_mul, mul_assoc]
    ring
  have hI : ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
        Set (v.val.adicCompletion F)ˣ), e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val) =
      ((a (Multiplicative.ofAdd y.1)) * ∏ w ∈ Finset.univ.erase v, g w (Multiplicative.ofAdd (y.2 w))) * ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
        Set (v.val.adicCompletion F)ˣ), g v (Multiplicative.ofAdd
        ((↑u⁻¹ : v.val.adicCompletion F) * ((↑π⁻¹ : v.val.adicCompletion F) * y.2 v)))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val) :=
    (integral_congr_ae (Eventually.of_forall hR')).trans (integral_const_mul _ _)
  refine hL.trans (Eq.trans ?_ (congrArg₂ (fun A B => A - ((finiteLocalMultiplicativeTamagawaMeasure
    F v.val).real ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
      Set (v.val.adicCompletion F)ˣ) : ℂ)⁻¹ * B) hE hI).symm)
  rw [finitePlacePrincipalValue_spec v.val π hπ]
  unfold finitePlacePrincipalValueFun
  simp only [toAdd_ofAdd]
  ring

/-- A property of the target of a tensor equivalence that is stable under sums and scalar
multiples and holds on pure tensors holds everywhere. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_induction {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B) (Pr : B → Prop)
    (hadd : ∀ f g, Pr f → Pr g → Pr (f + g)) (hsmul : ∀ (r : ℂ) f, Pr f → Pr (r • f))
    (hpure : ∀ (a : A) (g : ∀ i, D i), Pr (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (f : B) : Pr f := by
  have hall : ∀ t : A ⊗[ℂ] (⨂[ℂ] i, D i), Pr (e t) := by
    intro t
    refine TensorProduct.inductionOn (motive := fun t => Pr (e t)) t ?_ ?_
    · intro a w
      refine PiTensorProduct.induction_on (motive := fun w => Pr (e (a ⊗ₜ[ℂ] w))) w ?_ ?_
      · intro r g
        have hx : e (a ⊗ₜ[ℂ] (r • PiTensorProduct.tprod ℂ g)) =
            r • e (a ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ g)) := by
          exact (congrArg e ((TensorProduct.mk ℂ A (⨂[ℂ] i, D i) a).map_smul r
            (PiTensorProduct.tprod ℂ g))).trans (map_smul e r _)
        exact (congrArg Pr hx).mpr (hsmul r _ (hpure a g))
      · intro w₁ w₂ h₁ h₂
        have hx : e (a ⊗ₜ[ℂ] (w₁ + w₂)) = e (a ⊗ₜ[ℂ] w₁) + e (a ⊗ₜ[ℂ] w₂) := by
          exact (congrArg e ((TensorProduct.mk ℂ A (⨂[ℂ] i, D i) a).map_add
            (w₁ : ⨂[ℂ] i, D i) w₂)).trans (map_add e _ _)
        exact (congrArg Pr hx).mpr (hadd _ _ h₁ h₂)
    · intro t₁ t₂ h₁ h₂
      exact (congrArg Pr (map_add e t₁ t₂)).mpr (hadd _ _ h₁ h₂)
  exact (congrArg Pr (e.apply_symm_apply f)).mp (hall (e.symm f))

/-- The single-place principal value has the orbit-average formula at every point. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton_apply {S : Finset V} (v : S) (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F))
    (f : ℬₛ(S)) (y : SAdeleRing F S) :
    sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f (Multiplicative.ofAdd y) =
      f (Multiplicative.ofAdd y) - ((finiteLocalMultiplicativeTamagawaMeasure F v.val).real
          ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
            Set (v.val.adicCompletion F)ˣ) : ℂ)⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
            Set (v.val.adicCompletion F)ˣ), f (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val) := by
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
  let Pr : ℬₛ(S) → Prop := fun f => P f (Multiplicative.ofAdd y) =
      f (Multiplicative.ofAdd y) - ((finiteLocalMultiplicativeTamagawaMeasure F v.val).real
          ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
            Set (v.val.adicCompletion F)ˣ) : ℂ)⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
            Set (v.val.adicCompletion F)ˣ), f (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val)
  have hzero : Pr 0 := by
    change P 0 (Multiplicative.ofAdd y) = (0 : ℂ) - _ * ∫ _ in _, (0 : ℂ) ∂_
    rw [map_zero, integral_zero, mul_zero, sub_zero]
    rfl
  have hadd : ∀ f g, Pr f → Pr g → Pr (f + g) := by
    intro f g hf hg
    change P (f + g) (Multiplicative.ofAdd y) = (f (Multiplicative.ofAdd y) +
      g (Multiplicative.ofAdd y)) - _ * ∫ u in _, (f (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y)) +
        g (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y))) ∂_
    rw [map_add, integral_add (sLocalAdelicTheta_sAdelePrincipalValue_singleton_integrableOn v π f y) (sLocalAdelicTheta_sAdelePrincipalValue_singleton_integrableOn v π g y)]
    change P f (Multiplicative.ofAdd y) + P g (Multiplicative.ofAdd y) = _
    rw [hf, hg]
    ring
  have hsmul : ∀ (r : ℂ) f, Pr f → Pr (r • f) := by
    intro r f hf
    change P (r • f) (Multiplicative.ofAdd y) = r * f (Multiplicative.ofAdd y) -
      _ * ∫ u in _, r * f (Multiplicative.ofAdd
          (((adelicPrincipalValueLocalUnit v (π * u))⁻¹ : (SAdeleRing F S)ˣ).val * y)) ∂_
    rw [map_smul, integral_const_mul]
    change r * P f (Multiplicative.ofAdd y) = _
    rw [hf]
    ring
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have hpure : ∀ (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)),
      Pr (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := fun a g => sLocalAdelicTheta_sAdelePrincipalValue_singleton_tmul v π hπ a g y
  exact sLocalAdelicTheta_sAdelePrincipalValue_singleton_induction e Pr hadd hsmul hpure f

/-- Paper: (5.3.1.9), p. 242.
The single-place operator at `v` is `1` minus the normalized average over the integer units at
`v` of the translates by the reciprocal uniformizer times the unit, and S-local theta turns this
into the same recipe on the theta function: theta of the principal value at one place is theta of
the test minus the normalized average, over the integer units at that place, of theta of its
translates. This is the analytic content of (5.3.1.9): the theta sum over the S-units is exchanged
with the integral over the compact group of integer units, as in the proof of the formula for the
global theta function in one place in `Ch11_ShellStructure.Sec2a`. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton {S : Finset V} (v : S)
    (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F))
    (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
    sLocalAdelicTheta F S
        (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f) x =
      sLocalAdelicTheta F S f x -
        ((finiteLocalMultiplicativeTamagawaMeasure F v.val).real
          ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
            Set (v.val.adicCompletion F)ˣ) : ℂ)⁻¹ *
          ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
              Set (v.val.adicCompletion F)ˣ),
            sLocalAdelicTheta F S
              (schwartzBruhatUnitTranslate
                (adelicPrincipalValueLocalUnit v (π * (u : (v.val.adicCompletion F)ˣ))) f) x
            ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val) := by
  let d := (Units.map ((adeleProjection F S).comp
    (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  let U : Set (v.val.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v.val).units : Set (v.val.adicCompletion F)ˣ)
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
  let ℓ : (v.val.adicCompletion F)ˣ → (SAdeleRing F S)ˣ :=
    fun u => (adelicPrincipalValueLocalUnit v (π * u))⁻¹ * x
  have hℓ : Continuous ℓ := (continuous_inv.comp ((sLocalAdelicTheta_sAdelePrincipalValue_singleton_unit_continuous v).comp
    (continuous_const.mul continuous_id))).mul continuous_const
  have : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  have : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  have hK : IsCompact U :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v.val))
  have hUμ : μ U < ⊤ := hK.measure_lt_top
  -- the summands
  let G : _ → (v.val.adicCompletion F)ˣ → ℂ := fun ξ u =>
    f (Multiplicative.ofAdd (d ξ * ℓ u).val)
  have hGcont : ∀ ξ, Continuous (G ξ) := fun ξ =>
    (schwartzBruhat_continuous f).comp (continuous_ofAdd.comp
      (Units.continuous_val.comp (continuous_const.mul hℓ)))
  have hGint : ∀ ξ, Integrable (G ξ) (μ.restrict U) := fun ξ =>
    ContinuousOn.integrableOn_compact hK (hGcont ξ).continuousOn
  obtain ⟨b, hb, hbK⟩ := sLocalAdelicTheta_exists_summable_bound F S f (ℓ '' U) (hK.image hℓ)
  have hGb : ∀ ξ, ∫ u in U, ‖G ξ u‖ ∂μ ≤ b ξ * μ.real U := fun ξ => by
    refine (Real.le_norm_self _).trans ?_
    refine norm_setIntegral_le_of_norm_le_const hUμ fun u hu => ?_
    rw [norm_norm]
    exact hbK ξ (ℓ u) ⟨u, hu, rfl⟩
  have hsum : Summable fun ξ => ∫ u in U, ‖G ξ u‖ ∂μ :=
    Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun _ => norm_nonneg _) hGb
      (hb.mul_right _)
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (Set.integer (S : Set V) F)ˣ :=
    (Subtype.val_injective.comp Units.val_injective).countable
  have hswap := integral_tsum_of_summable_integral_norm hGint hsum
  have hsumI : Summable fun ξ => ∫ u in U, G ξ u ∂μ :=
    Summable.of_norm_bounded hsum fun ξ => norm_integral_le_integral_norm _
  have hs1 : Summable fun ξ => f (Multiplicative.ofAdd (d ξ * x).val) :=
    ((sLocalAdelicTheta_hasSumUniformlyOn F S f {x} isCompact_singleton).hasSum rfl).summable
  -- left side
  have hL : sLocalAdelicTheta F S
      (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f) x =
        ∑' ξ, (f (Multiplicative.ofAdd (d ξ * x).val) -
          ((μ.real U : ℝ) : ℂ)⁻¹ * ∫ u in U, G ξ u ∂μ) := by
    refine (sLocalAdelicTheta_apply F S _ x).trans (tsum_congr fun ξ => ?_)
    refine (sLocalAdelicTheta_sAdelePrincipalValue_singleton_apply v π hπ f (d ξ * x).val).trans ?_
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    change f (Multiplicative.ofAdd (((adelicPrincipalValueLocalUnit v (π * u))⁻¹).val *
      (d ξ * x).val)) = f (Multiplicative.ofAdd (d ξ * ((adelicPrincipalValueLocalUnit v (π * u))⁻¹ * x)).val)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, mul_left_comm]
  have hR : ∫ u in U, sLocalAdelicTheta F S
      (schwartzBruhatUnitTranslate (adelicPrincipalValueLocalUnit v (π * u)) f) x ∂μ =
        ∑' ξ, ∫ u in U, G ξ u ∂μ := by
    refine Eq.trans ?_ hswap.symm
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact (sAdelePrincipalValue_preserves_thetaKernel_translate _ x f).trans (sLocalAdelicTheta_apply F S f _)
  have hθ : sLocalAdelicTheta F S f x = ∑' ξ, f (Multiplicative.ofAdd (d ξ * x).val) :=
    sLocalAdelicTheta_apply F S f x
  rw [hL, hR, hθ, hs1.tsum_sub (hsumI.mul_left _), tsum_mul_left]

/-- Paper: (5.3.1.9), p. 242.
The single-place principal value at `v` maps the theta kernel into itself: theta of the average
of the translates vanishes because theta of every translate is theta of the test at another
idele, and theta of the test is zero. -/
private theorem sAdelePrincipalValue_preserves_thetaKernel_singleton {S : Finset V} (v : S)
    (f : ℬₛ(S)) (hf : sLocalAdelicTheta F S f = 0) :
    sLocalAdelicTheta F S
      (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f) = 0 := by
  let hunif := (Valued.v :
    Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ :=
    Units.mk0 (hunif.choose : v.val.adicCompletion F) hunif.choose_spec.ne_zero
  have hπ : (Valued.v :
      Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
        (π : v.val.adicCompletion F) := hunif.choose_spec
  refine ContinuousMap.ext fun y => ?_
  refine (sLocalAdelicTheta_sAdelePrincipalValue_singleton v π hπ f y).trans ?_
  have hzero : ∀ (u : (v.val.adicCompletion F)ˣ) (z : (SAdeleRing F S)ˣ), sLocalAdelicTheta F S
        (schwartzBruhatUnitTranslate (R := SAdeleRing F S)
          (adelicPrincipalValueLocalUnit v (π * u)) f) z = 0 := by
    intro u z
    rw [sAdelePrincipalValue_preserves_thetaKernel_translate]
    exact DFunLike.congr_fun hf _
  have hfun : (fun u : (v.val.adicCompletion F)ˣ => sLocalAdelicTheta F S
        (schwartzBruhatUnitTranslate (R := SAdeleRing F S)
          (adelicPrincipalValueLocalUnit v (π * u)) f) y) = fun _ => 0 :=
    funext fun u => hzero u y
  have hf0 : sLocalAdelicTheta F S f y = 0 := DFunLike.congr_fun hf y
  rw [hfun, integral_zero, mul_zero, sub_zero]
  exact hf0

open Classical in
/-- Paper: (5.3.1.9), p. 242.
The S-local principal value is the composition, over the selected places, of its single-place
versions: each factor acts in its own coordinate of the tensor decomposition of the S-local test
space, so the operators commute and compose to the operator attached to the whole set. The
composite is written as a product over a list so that it can be peeled one place at a time. -/
private theorem sAdelePrincipalValue_preserves_thetaKernel_list {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬₛ(S)) :
    sAdelePrincipalValue F h₀ f =
      (S₀.val.toList.map fun v => if h : v ∈ S then
        sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1).prod f := by sorry

/-- Paper: (5.3.1.9), p. 242.
The S-local principal value preserves the kernel of theta averaging. -/
theorem sAdelePrincipalValue_preserves_thetaKernel {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    Kₛ(S) ≤ (Kₛ(S)).comap (sAdelePrincipalValue F h₀) := by
  classical
  have key : ∀ (l : List V), (∀ v ∈ l, v ∈ S) → ∀ g : ℬₛ(S), sLocalAdelicTheta F S g = 0 →
      sLocalAdelicTheta F S ((l.map fun v => if h : v ∈ S then
        sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1).prod g) = 0 := by
    intro l
    induction l with
    | nil =>
      intro _ g hg
      simpa using hg
    | cons a l ih =>
      intro hmem g hg
      have ha : a ∈ S := hmem a List.mem_cons_self
      have hta : ∀ v ∈ l, v ∈ S := fun v hv => hmem v (List.mem_cons_of_mem a hv)
      have htail := ih hta g hg
      have hQa : (if h : a ∈ S then
          sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1) =
          sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr ha) := dif_pos ha
      rw [List.map_cons, List.prod_cons, hQa]
      exact sAdelePrincipalValue_preserves_thetaKernel_singleton ⟨a, ha⟩ _ htail
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_comap]
  rw [sAdelePrincipalValue_preserves_thetaKernel_list h₀]
  exact key S₀.val.toList (fun v hv => h₀ (Multiset.mem_toList.mp hv)) f hf

/-- Paper: (5.3.1.10), p. 242.
The global principal value preserves the kernel of theta averaging. -/
theorem adelePrincipalValue_preserves_thetaKernel (S₀ : Finset V) :
    K𝔽 ≤ (K𝔽).comap (adelePrincipalValue F S₀) := by sorry

variable (F) in
/-- Paper: (5.3.1.9), p. 242.
The S-local principal value acts on the S-local theta quotient by descent. -/
def sLocalThetaPrincipalValue {S S₀ : Finset V} (h₀ : S₀ ⊆ S) : Θₛ(S) →ₗ[ℂ] Θₛ(S) :=
  (Kₛ(S)).mapQ (Kₛ(S)) (sAdelePrincipalValue F h₀)
    (sAdelePrincipalValue_preserves_thetaKernel h₀)

variable (F) in
/-- Paper: (5.3.1.10), p. 242.
The global principal value acts on the global theta quotient by descent. -/
def globalThetaPrincipalValue (S₀ : Finset V) : Θ𝔽 →ₗ[ℂ] Θ𝔽 :=
  (K𝔽).mapQ K𝔽 (adelePrincipalValue F S₀) (adelePrincipalValue_preserves_thetaKernel S₀)

/-- Paper: (5.3.1.9), p. 242.
On a class represented by a test function the S-local operator gives the class of its image. -/
theorem sLocalThetaPrincipalValue_mk {S S₀ : Finset V} (h₀ : S₀ ⊆ S) (f : ℬₛ(S)) :
    sLocalThetaPrincipalValue F h₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F h₀ f) := by
  rfl

/-- Paper: (5.3.1.10), p. 242.
On a class represented by a test function the global operator gives the class of its image. -/
theorem globalThetaPrincipalValue_mk (S₀ : Finset V) (f : ℬ(𝔸[F])) :
    globalThetaPrincipalValue F S₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (adelePrincipalValue F S₀ f) := by
  rfl

/-- Paper: (5.3.1.9), p. 242.
The S-local operator descends continuously for every set of selected places. -/
theorem sLocalThetaPrincipalValue_continuous {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    Continuous (sLocalThetaPrincipalValue F h₀) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (Kₛ(S)).isQuotientMap_mkQ.continuous.comp
    (sAdelePrincipalValue_isClosedEmbedding h₀).continuous

/-- Paper: (5.3.1.10), p. 242.
The global operator descends continuously for every set of selected places. -/
theorem globalThetaPrincipalValue_continuous (S₀ : Finset V) :
    Continuous (globalThetaPrincipalValue F S₀) := by
  apply (K𝔽).isQuotientMap_mkQ.continuous_iff.mpr
  exact (K𝔽).isQuotientMap_mkQ.continuous.comp
    (adelePrincipalValue_isClosedEmbedding S₀).continuous

-- TODO(paper-gap): Let K be the theta kernel and P the operator on tests.
-- On the quotient the preimage of the range is range P + K. Closedness of
-- range P and injectivity after descent do not establish closedness of this
-- sum or continuity of the inverse on its image. This affects both quotients.

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value on theta classes is a closed topological embedding. -/
theorem sLocalThetaPrincipalValue_isClosedEmbedding {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (hn : S₀.Nonempty) :
    IsClosedEmbedding (sLocalThetaPrincipalValue F h₀) := by sorry

-- TODO(paper-gap): The proof of global closed range claims that the image is contained in
-- any fixed S-stage. This does not follow from stage compatibility and fails at larger stages.

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value on theta classes is a closed topological embedding. -/
theorem globalThetaPrincipalValue_isClosedEmbedding {S₀ : Finset V} (hn : S₀.Nonempty) :
    IsClosedEmbedding (globalThetaPrincipalValue F S₀) := by sorry

private theorem sLocalThetaPrincipalValue_transition_ext {ι A X Y : Type*} {M : ι → Type*}
    [TopologicalSpace A] [AddCommGroup A] [Module ℂ A] [TopologicalSpace X]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] X)
    (i : X →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X) (q : Y →ₗ[ℂ] Y)
    (h : ∀ (a : A) (g : ∀ i, M i),
      i (p (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)))) = q (i (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))) :
    i.comp p = q.comp i := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top (h a)

private theorem sLocalThetaPrincipalValue_transition_tmul {ι A X : Type*} {M : ι → Type*}
    [TopologicalSpace A] [AddCommGroup A] [Module ℂ A] [TopologicalSpace X]
    [AddCommGroup X] [Module ℂ X] [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] X)
    (P : ∀ i, M i →ₗ[ℂ] M i) (a : A) (b : ∀ i, M i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, M i)
    let Q : W →ₗ[ℂ] W := PiTensorProduct.map P
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A)
      Q).comp e.symm.toLinearMap)) (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, b i))) =
        e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, P i (b i))) := by
  change e ((TensorProduct.map _ (PiTensorProduct.map P)) (e.symm (e _))) = _
  erw [e.symm_apply_apply]
  apply congrArg e
  exact (TensorProduct.map_tmul LinearMap.id (PiTensorProduct.map P) a _).trans
    (congrArg (TensorProduct.tmul ℂ a) (PiTensorProduct.map_tprod P b))

open Classical in
private theorem sLocalThetaPrincipalValue_transition_factors {ι : Type*} {M : ι → Type*}
    [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)]
    {S₀ S T : Finset ι} (h₀ : S₀ ⊆ S) (P : ∀ v, M v →ₗ[ℂ] M v) (c : ∀ v, M v)
    (g : ∀ w : S, M w.val) :
    let extend := fun (b : ∀ w : S, M w.val) (w : T) ↦
      if hw : w.val ∈ S then b ⟨w.val, hw⟩ else c w.val
    let op := fun (R : Finset ι) (b : ∀ w : R, M w.val) (w : R) ↦
      (if w.val ∈ S₀ then P w.val else LinearMap.id) (b w)
    extend (op S g) = op T (extend g) := by
  funext w
  by_cases hw : w.val ∈ S
  · simp [hw]
  · simp [hw, show w.val ∉ S₀ from fun h ↦ hw (h₀ h)]

open Classical in
private theorem sLocalThetaPrincipalValue_transition_tests {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) :
    (sAdeleSchwartzTransition F hST).comp (sAdelePrincipalValue F h₀) =
      (sAdelePrincipalValue F (h₀.trans hST)).comp (sAdeleSchwartzTransition F hST) := by
  let e (R : Finset V) := (sAdeleSchwartz_inductiveTensor_equiv F R).choose
  apply sLocalThetaPrincipalValue_transition_ext (e S)
  intro a g
  let pureTest (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) : ℬₛ(R) :=
    e R (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
  let P (v : V) : ℬ(v.adicCompletion F) →ₗ[ℂ] ℬ(v.adicCompletion F) :=
    if v ∈ S₀ then (finitePlacePrincipalValue v).toLinearMap else LinearMap.id
  let op (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) (w : R) :=
    P w.val (b w)
  have pv (R : Finset V) (hR : S₀ ⊆ R) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) :
      sAdelePrincipalValue F hR (pureTest R b) = pureTest R (op R b) := by
    unfold sAdelePrincipalValue
    with_reducible exact sLocalThetaPrincipalValue_transition_tmul (e R) (fun w : R ↦ P w.val) a b
  let extend (b : ∀ w : S, ℬ(w.val.adicCompletion F)) (w : T) :=
    if hw : w.val ∈ S then b ⟨w.val, hw⟩ else finiteStandardGaussian w.val 1
  have insertTest (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      sAdeleSchwartzTransition F hST (pureTest S b) = pureTest T (extend b) := by
    apply Subtype.ext
    funext x
    have hg (w : T) (hw : w.val ∉ S) (y : w.val.adicCompletion F) :
        extend b w (Multiplicative.ofAdd y) =
          (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F)).indicator
            (fun _ ↦ (1 : ℂ)) y := by
      rw [show extend b w = finiteStandardGaussian w.val 1 by simp [extend, hw]]
      change finiteStandardGaussianValue w.val 1 y = _
      unfold finiteStandardGaussianValue
      exact ite_eq_left fun u _ ↦ rfl
    have hr (w : S) : extend b ⟨w.val, hST w.property⟩ = b w := by
      simp only [extend, dite_eq_left w.property]
    have spec (R : Finset V) (d : ∀ w : R, ℬ(w.val.adicCompletion F)) (y : SAdeleRing F R) :
        pureTest R d (Multiplicative.ofAdd y) = a (Multiplicative.ofAdd y.1) *
          ∏ w : R, d w (Multiplicative.ofAdd (y.2 w)) := by
      with_reducible exact (sAdeleSchwartz_inductiveTensor_equiv F R).choose_spec a d y
    with_reducible refine Eq.trans ?_ (spec T (extend b) x.toAdd).symm
    change sAdeleSchwartzTransition F hST (pureTest S b) (Multiplicative.ofAdd x.toAdd) = _
    with_reducible
      refine sAdeleSchwartzTransition_pure F hST a (extend b) hg (pureTest S b) ?_ x.toAdd
    intro y
    simp only [hr]
    with_reducible exact spec S b y
  with_reducible change sAdeleSchwartzTransition F hST (sAdelePrincipalValue F h₀ (pureTest S g)) =
    sAdelePrincipalValue F (h₀.trans hST) (sAdeleSchwartzTransition F hST (pureTest S g))
  have hcomm : extend (op S g) = op T (extend g) := by
    with_reducible
      exact sLocalThetaPrincipalValue_transition_factors (M := fun v : V ↦ ℬ(v.adicCompletion F))
        (T := T) h₀ (fun v ↦ (finitePlacePrincipalValue v).toLinearMap)
        (fun v ↦ finiteStandardGaussian v 1) g
  with_reducible
    exact (congrArg (sAdeleSchwartzTransition F hST) (pv S h₀ g)).trans
      ((insertTest (op S g)).trans ((congrArg (pureTest T) hcomm).trans
        ((pv T (h₀.trans hST) (extend g)).symm.trans
          (congrArg (sAdelePrincipalValue F (h₀.trans hST)) (insertTest g).symm))))

private theorem sLocalThetaPrincipalValue_transition_mapQ {X Y : Type*} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (K : Submodule ℂ X) (L : Submodule ℂ Y)
    (i : X →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X) (q : Y →ₗ[ℂ] Y) (hi : K ≤ L.comap i)
    (hp : K ≤ K.comap p) (hq : L ≤ L.comap q) (h : i.comp p = q.comp i) :
    (K.mapQ L i hi).comp (K.mapQ K p hp) = (L.mapQ L q hq).comp (K.mapQ L i hi) := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  exact congrArg L.mkQ (DFunLike.congr_fun h f)

/-- Paper: Lemma 5.3.1.5, p. 242.
The principal value commutes with passage from an S-local theta stage to a larger stage. -/
theorem sLocalThetaPrincipalValue_transition {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) (hn : S₀.Nonempty) :
    (sLocalThetaTransition (F := F) hST).comp (sLocalThetaPrincipalValue F h₀) =
      (sLocalThetaPrincipalValue F (h₀.trans hST)).comp (sLocalThetaTransition hST) := by
  unfold sLocalThetaTransition sLocalThetaPrincipalValue
  apply sLocalThetaPrincipalValue_transition_mapQ
  exact sLocalThetaPrincipalValue_transition_tests h₀ hST

open Classical in
/-- Through a stage containing the selected places, the global principal value of an
inserted test is the insertion of the S-local principal value. The integer tail indicator
is obtained by slicing the inserted test `k₀` at a point `p` where its value is one. -/
private theorem sLocalThetaPrincipalValue_toGlobal_slice {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (k₀ : ℬₛ(S)) (p : SAdeleRing F S)
    (hk₀ : k₀ (Multiplicative.ofAdd p) = 1) (k : ℬₛ(S)) :
    adelePrincipalValue F S₀ (sAdeleSchwartzToGlobal F S k) =
      sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F h₀ k) := by
  let Tl := ℬ(FiniteAdeleTail F S)
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose_spec
  let ev : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun a ↦ a (Multiplicative.ofAdd p)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : ℬₛ(S) ⊗[ℂ] Tl →ₗ[ℂ] Tl := TensorProduct.lift ((LinearMap.lsmul ℂ Tl).comp ev)
  let c : Tl := L (e.symm (sAdeleSchwartzToGlobal F S k₀))
  have hc (y : FiniteAdeleTail F S) : c (Multiplicative.ofAdd y) =
      if ∀ w, y w ∈ w.val.adicCompletionIntegers F then 1 else 0 := by
    let f : ∀ w : V, w.adicCompletion F := fun w ↦ if h : w ∈ S then p.2 ⟨w, h⟩ else y ⟨w, h⟩
    have hf : ∀ᶠ w in Filter.cofinite, f w ∈ w.adicCompletionIntegers F := by
      filter_upwards [S.eventually_cofinite_notMem, Filter.eventually_comap.mp
        (y.2.filter_mono (Filter.comap_cofinite_le Subtype.val))] with w hw h
      simp only [f, dite_eq_right hw]
      exact h ⟨w, hw⟩ rfl
    let z : FiniteAdeleRing (𝓞 F) F := ⟨f, hf⟩
    let x : AdeleRing (𝓞 F) F := (p.1, z)
    have hx (w : V) (hw : w ∉ S) : x.2 w = y ⟨w, hw⟩ := dite_eq_right hw
    have hp : adeleProjection F S x = p :=
      Prod.ext rfl (funext fun w ↦ (dite_eq_left w.2 : f w.val = p.2 w))
    have ht : finiteAdeleTailProjection F S x.2 = y := by
      apply RestrictedProduct.ext
      intro w
      exact dite_eq_right w.2
    let evy : Tl →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd y)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let evx : ℬ(AdeleRing (𝓞 F) F) →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd x)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have key : evy ∘ₗ L = evx ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S) Tl →ₗ[ℂ] _) := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change (a (Multiplicative.ofAdd p) • b) (Multiplicative.ofAdd y) =
        e (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x)
      rw [he a b x, hp, ht]
      rfl
    have h2 : c (Multiplicative.ofAdd y) =
        sAdeleSchwartzToGlobal F S k₀ (Multiplicative.ofAdd x) :=
      (LinearMap.congr_fun key (e.symm (sAdeleSchwartzToGlobal F S k₀))).trans
        (congrArg (fun φ : ℬ(AdeleRing (𝓞 F) F) ↦
          φ (Multiplicative.ofAdd x)) (e.apply_symm_apply _))
    rw [h2, sAdeleSchwartzToGlobal_apply, hp, hk₀]
    by_cases hy : ∀ w, y w ∈ w.val.adicCompletionIntegers F
    · rw [ite_eq_left hy, ite_eq_left fun w hw ↦ by rw [hx w hw]; exact hy ⟨w, hw⟩]
    · rw [ite_eq_right hy, ite_eq_right fun h ↦ hy fun w ↦ by rw [← hx w.val w.2]; exact h w.val w.2]
  have hslice (a : ℬₛ(S)) : e (a ⊗ₜ[ℂ] c) = sAdeleSchwartzToGlobal F S a := by
    apply Subtype.ext
    funext x
    change e (a ⊗ₜ[ℂ] c) (Multiplicative.ofAdd x.toAdd) =
      sAdeleSchwartzToGlobal F S a (Multiplicative.ofAdd x.toAdd)
    rw [he a c x.toAdd, hc, sAdeleSchwartzToGlobal_apply]
    by_cases hx : ∀ w : V, w ∉ S → x.toAdd.2 w ∈ w.adicCompletionIntegers F
    · rw [ite_eq_left hx, ite_eq_left (show ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun w ↦ hx w.val w.2), mul_one]
    · rw [ite_eq_right hx, ite_eq_right (show ¬ ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun h ↦ hx fun w hw ↦ h ⟨w, hw⟩), mul_zero]
  rw [← hslice k, ← hslice (sAdelePrincipalValue F h₀ k)]
  exact adelePrincipalValue_tmul h₀ k c

/-- On test functions, insertion of an S-local stage intertwines the S-local and the
global principal values. A nonzero test, normalized at a point where it does not vanish,
supplies the slice that identifies the integer tail indicator. -/
private theorem sLocalThetaPrincipalValue_toGlobal_tests {S₀ S : Finset V} (h₀ : S₀ ⊆ S) :
    (sAdeleSchwartzToGlobal F S).comp (sAdelePrincipalValue F h₀) =
      (adelePrincipalValue F S₀).comp (sAdeleSchwartzToGlobal F S) := by
  apply LinearMap.ext
  intro k
  by_cases hk : k = 0
  · rw [hk, map_zero, map_zero]
  · obtain ⟨x, hx⟩ : ∃ x : Multiplicative (SAdeleRing F S), k x ≠ 0 := by
      by_contra h
      apply hk
      apply Subtype.ext
      funext x
      exact not_not.mp fun hx ↦ h ⟨x, hx⟩
    have hk₀ : ((k x)⁻¹ • k) (Multiplicative.ofAdd x.toAdd) = 1 := inv_mul_cancel₀ hx
    exact (sLocalThetaPrincipalValue_toGlobal_slice h₀ _ x.toAdd hk₀ k).symm

/-- Paper: Lemma 5.3.1.5, p. 242.
The local and global principal value operators commute with insertion of an S-local theta stage. -/
theorem sLocalThetaPrincipalValue_toGlobal {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) :
    (sLocalThetaToGlobal F S).comp (sLocalThetaPrincipalValue F h₀) =
      (globalThetaPrincipalValue F S₀).comp (sLocalThetaToGlobal F S) := by
  unfold sLocalThetaToGlobal sLocalThetaPrincipalValue globalThetaPrincipalValue
  apply sLocalThetaPrincipalValue_transition_mapQ
  exact sLocalThetaPrincipalValue_toGlobal_tests h₀

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value commutes with each S-idele translation on theta classes. -/
theorem sLocalThetaPrincipalValue_equivariant {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    Submodule.Quotient.mk
        (sAdelePrincipalValue F h₀ (schwartzBruhatUnitTranslate g f)) =
      (Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (sAdelePrincipalValue F h₀ f)) : Θₛ(S)) := by sorry

/-- Weil's local principal value commutes with multiplicative translation, since both only
rescale the argument. -/
private theorem globalThetaPrincipalValue_equivariant_local (v : V) (c : (v.adicCompletion F)ˣ)
    (h : ℬ(v.adicCompletion F)) :
    finitePlacePrincipalValue v (schwartzBruhatUnitTranslate c h) =
      schwartzBruhatUnitTranslate c (finitePlacePrincipalValue v h) := by
  let hπ0 := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (hπ0.choose : v.adicCompletion F) hπ0.choose_spec.ne_zero
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  apply Subtype.ext
  funext x
  change finitePlacePrincipalValue v (schwartzBruhatUnitTranslate c h)
      (Multiplicative.ofAdd x.toAdd) =
    schwartzBruhatUnitTranslate c (finitePlacePrincipalValue v h) (Multiplicative.ofAdd x.toAdd)
  rw [schwartzBruhatUnitTranslate_apply, finitePlacePrincipalValue_spec v π hπ0.choose_spec,
    finitePlacePrincipalValue_spec v π hπ0.choose_spec]
  unfold finitePlacePrincipalValueFun
  simp only [schwartzBruhatUnitTranslate_apply, toAdd_ofAdd]
  congr 2
  refine setIntegral_congr_fun ?_ fun u _ ↦ ?_
  · exact (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  · exact congrArg (fun y ↦ h (Multiplicative.ofAdd y)) (by ring)

/-- Two linear maps agree once they agree on the pure tensors of an inductive tensor product
with a projective tensor power. -/
private theorem globalThetaPrincipalValue_equivariant_ext {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (L₁ L₂ : B →ₗ[ℂ] B)
    (h : ∀ (a : A) (g : ∀ i, D i), L₁ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) =
      L₂ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (x : B) :
    L₁ x = L₂ x := by
  obtain ⟨t, rfl⟩ := e.surjective x
  let W := FinestLocallyConvex (⨂[ℂ] i, D i)
  let M₁ : A ⊗[ℂ] W →ₗ[ℂ] B := L₁ ∘ₗ (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B)
  let M₂ : A ⊗[ℂ] W →ₗ[ℂ] B := L₂ ∘ₗ (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B)
  have hM : M₁ = M₂ := by
    refine TensorProduct.ext' fun a z ↦ ?_
    refine PiTensorProduct.induction_on (motive := fun z : ⨂[ℂ] i, D i ↦
      M₁ (a ⊗ₜ[ℂ] (z : W)) = M₂ (a ⊗ₜ[ℂ] (z : W))) z ?_ ?_
    · intro r g
      have ht : (a ⊗ₜ[ℂ] (((r • (⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
          r • (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) :=
        (TensorProduct.mk ℂ A W a).map_smul r (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)
      have hp : M₁ (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) =
          M₂ (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) := h a g
      exact (congrArg M₁ ht).trans ((map_smul M₁ r _).trans ((congrArg (r • ·) hp).trans
        ((map_smul M₂ r _).symm.trans (congrArg M₂ ht.symm))))
    · intro z₁ z₂ h₁ h₂
      have ht : (a ⊗ₜ[ℂ] (((z₁ + z₂ : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
          a ⊗ₜ[ℂ] (z₁ : W) + a ⊗ₜ[ℂ] (z₂ : W) :=
        (TensorProduct.mk ℂ A W a).map_add (z₁ : W) (z₂ : W)
      exact (congrArg M₁ ht).trans ((map_add M₁ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans
        ((map_add M₂ _ _).symm.trans (congrArg M₂ ht.symm))))
  exact LinearMap.congr_fun hM t

open Classical in
/-- The S-local principal value commutes with translation by an S-idele. -/
private theorem globalThetaPrincipalValue_equivariant_stage {S₀ : Finset V}
    (gS : (SAdeleRing F S₀)ˣ) (k : ℬₛ(S₀)) :
    sAdelePrincipalValue F (Finset.Subset.refl S₀) (schwartzBruhatUnitTranslate gS k) =
      schwartzBruhatUnitTranslate gS (sAdelePrincipalValue F (Finset.Subset.refl S₀) k) := by
  let e' := (sAdeleSchwartz_inductiveTensor_equiv F S₀).choose
  have he' := (sAdeleSchwartz_inductiveTensor_equiv F S₀).choose_spec
  let P := sAdelePrincipalValue F (Finset.Subset.refl S₀)
  let T : ℬₛ(S₀) →ₗ[ℂ] ℬₛ(S₀) :=
    { toFun := schwartzBruhatUnitTranslate gS
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let gInf : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom gS
  let gw (w : S₀) : (w.val.adicCompletion F)ˣ :=
    Units.map ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).toMonoidHom gS
  have hT (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S₀, ℬ(w.val.adicCompletion F)) :
      T (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = e' (schwartzBruhatUnitTranslate gInf a ⊗ₜ[ℂ]
        (⨂ₜ[ℂ] w, schwartzBruhatUnitTranslate (gw w) (g w))) := by
    apply Subtype.ext
    funext x
    refine (he' a g ((↑gS⁻¹ : SAdeleRing F S₀) * x.toAdd)).trans (Eq.trans ?_
      (he' (schwartzBruhatUnitTranslate gInf a)
        (fun w ↦ schwartzBruhatUnitTranslate (gw w) (g w)) x.toAdd).symm)
    rfl
  have hyp : ∀ (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S₀, ℬ(w.val.adicCompletion F)),
      (P ∘ₗ T) (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = (T ∘ₗ P) (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := by
    intro a g
    have h1 := sAdelePrincipalValue_tmul (Finset.Subset.refl S₀) (schwartzBruhatUnitTranslate gInf a)
      (fun w ↦ schwartzBruhatUnitTranslate (gw w) (g w))
    have h2 := sAdelePrincipalValue_tmul (Finset.Subset.refl S₀) a g
    refine (congrArg P (hT a g)).trans (h1.trans ?_)
    refine Eq.trans ?_ (congrArg T h2).symm
    refine Eq.trans ?_ (hT a _).symm
    have hfun : (fun w : S₀ ↦ if w.val ∈ S₀ then
          finitePlacePrincipalValue w.val (schwartzBruhatUnitTranslate (gw w) (g w))
        else schwartzBruhatUnitTranslate (gw w) (g w)) =
        fun w ↦ schwartzBruhatUnitTranslate (gw w)
          (if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w) := by
      funext w
      simp only [w.property, ite_true]
      exact globalThetaPrincipalValue_equivariant_local w.val (gw w) (g w)
    exact congrArg (fun φ : ∀ w : S₀, ℬ(w.val.adicCompletion F) ↦
      e' (schwartzBruhatUnitTranslate gInf a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, φ w))) hfun
  exact globalThetaPrincipalValue_equivariant_ext
    (D := fun w : S₀ ↦ ℬ(w.val.adicCompletion F)) e' (P ∘ₗ T) (T ∘ₗ P)
    (by with_reducible exact hyp) k

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value commutes with each idele translation on theta classes. -/
theorem globalThetaPrincipalValue_equivariant {S₀ : Finset V}
    (hn : S₀.Nonempty) (g : IdeleGroup (𝓞 F) F) (f : ℬ(𝔸[F])) :
    Submodule.Quotient.mk (adelePrincipalValue F S₀ (schwartzBruhatUnitTranslate g f)) =
      (Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (adelePrincipalValue F S₀ f)) : Θ𝔽) := by
  apply congrArg
  have : Fact (∀ w : {w : V // w ∉ S₀},
      IsOpen (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))) :=
    ⟨fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F)⟩
  let : IsTopologicalRing (FiniteAdeleTail F S₀) :=
    RestrictedProduct.isTopologicalRing (fun w : {w : V // w ∉ S₀} ↦ w.val.adicCompletion F)
  let Tl := ℬ(FiniteAdeleTail F S₀)
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose
  have he := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose_spec
  let P := adelePrincipalValue F S₀
  let T : ℬ(𝔸[F]) →ₗ[ℂ] ℬ(𝔸[F]) :=
    { toFun := schwartzBruhatUnitTranslate g
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let gS : (SAdeleRing F S₀)ˣ := Units.map (adeleProjection F S₀).toMonoidHom g
  have hval : finiteAdeleTailProjection F S₀ g.val.2 * finiteAdeleTailProjection F S₀ g.inv.2 = 1 := by
    apply RestrictedProduct.ext
    intro w
    exact congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 w.val) g.val_inv
  have hinv : finiteAdeleTailProjection F S₀ g.inv.2 * finiteAdeleTailProjection F S₀ g.val.2 = 1 := by
    apply RestrictedProduct.ext
    intro w
    exact congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 w.val) g.inv_val
  let gt : (FiniteAdeleTail F S₀)ˣ := ⟨_, _, hval, hinv⟩
  have hT (k : ℬₛ(S₀)) (b : Tl) : T (e (k ⊗ₜ[ℂ] b)) =
      e (schwartzBruhatUnitTranslate gS k ⊗ₜ[ℂ] schwartzBruhatUnitTranslate gt b) := by
    apply Subtype.ext
    funext x
    refine (he k b ((↑g⁻¹ : AdeleRing (𝓞 F) F) * x.toAdd)).trans (Eq.trans ?_
      (he (schwartzBruhatUnitTranslate gS k) (schwartzBruhatUnitTranslate gt b) x.toAdd).symm)
    rfl
  obtain ⟨t, rfl⟩ := e.surjective f
  suffices h : P ∘ₗ T ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S₀) Tl →ₗ[ℂ] _) =
      T ∘ₗ P ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S₀) Tl →ₗ[ℂ] _) from
    LinearMap.congr_fun h t
  refine TensorProduct.ext' fun k b ↦ ?_
  have h1 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl S₀)
    (schwartzBruhatUnitTranslate gS k) (schwartzBruhatUnitTranslate gt b)
  have h2 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl S₀) k b
  change P (T (e (k ⊗ₜ[ℂ] b))) = T (P (e (k ⊗ₜ[ℂ] b)))
  refine (congrArg P (hT k b)).trans (h1.trans ?_)
  refine Eq.trans ?_ (congrArg T h2).symm
  refine Eq.trans ?_ (hT _ b).symm
  exact congrArg (fun z ↦ e (z ⊗ₜ[ℂ] schwartzBruhatUnitTranslate gt b))
    (globalThetaPrincipalValue_equivariant_stage gS k)

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value commutes with the norm-one character average of §5.2.3. -/
theorem sLocalThetaPrincipalValue_isotypicAverage {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) (x : Θₛ(S)) :
    let A := (existsUnique_sLocalThetaIsotypicAverage (F := F) χ).exists.choose
    sLocalThetaPrincipalValue F h₀ (A x) = A (sLocalThetaPrincipalValue F h₀ x) := by sorry

private theorem globalThetaPrincipalValue_isotypicAverage_tensor
    {M N Y : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (e : InductiveTensor M N ≃L[ℂ] Y)
    (f : M →ₗ[ℂ] M) (g : N →ₗ[ℂ] N) (hf : f = LinearMap.id) (hg : g = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map f g).comp e.symm.toLinearMap) = LinearMap.id := by
  subst f g
  have H : TensorProduct.map (LinearMap.id (R := ℂ) (M := M)) (LinearMap.id (R := ℂ) (M := N)) =
      LinearMap.id := TensorProduct.map_id
  rw [H]
  apply LinearMap.ext
  exact e.apply_symm_apply

private theorem globalThetaPrincipalValue_isotypicAverage_emptyTensor
    {ι M Y : Type*} {N : ι → Type*} [IsEmpty ι]
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (e : InductiveTensor M (FinestLocallyConvex (⨂[ℂ] i, N i)) ≃L[ℂ] Y)
    (L : ∀ i, N i →ₗ[ℂ] N i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, N i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map L
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id (R := ℂ) (M := M)) P).comp
      e.symm.toLinearMap) = LinearMap.id := by
  intro W P
  have hp : P = LinearMap.id := (congrArg (PiTensorProduct.map (R := ℂ))
    (Subsingleton.elim L (fun i ↦ (LinearMap.id : N i →ₗ[ℂ] N i)))).trans PiTensorProduct.map_id
  exact globalThetaPrincipalValue_isotypicAverage_tensor e LinearMap.id P rfl hp

private theorem globalThetaPrincipalValue_isotypicAverage_emptyTest :
    adelePrincipalValue F ∅ = LinearMap.id := by
  unfold adelePrincipalValue
  with_reducible_and_instances
    refine globalThetaPrincipalValue_isotypicAverage_tensor _ _ _ ?_ rfl
  unfold sAdelePrincipalValue
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_emptyTensor (ι := ↥(∅ : Finset V)) _ _

private theorem globalThetaPrincipalValue_isotypicAverage_mapQ_id {E : Type*}
    [AddCommGroup E] [Module ℂ E] (K : Submodule ℂ E) (P : E →ₗ[ℂ] E)
    (hK : K ≤ K.comap P) (h : P = LinearMap.id) (x : E ⧸ K) : K.mapQ K P hK x = x := by
  subst P
  exact Submodule.Quotient.induction_on K x fun _ ↦ rfl

private theorem globalThetaPrincipalValue_isotypicAverage_empty (x : Θ𝔽) :
    globalThetaPrincipalValue F ∅ x = x := by
  unfold globalThetaPrincipalValue
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_mapQ_id _ _ _
      (globalThetaPrincipalValue_isotypicAverage_emptyTest (F := F)) x

private theorem globalThetaPrincipalValue_isotypicAverage_onReps {G C E X : Type*}
    (π : G → C) (m : E → X) (hπ : Surjective π) (hm : Surjective m)
    (p : E → E) (t : G → E → E) (P : X → X) (ρ : C → X → X)
    (hp : ∀ f, P (m f) = m (p f)) (ht : ∀ g f, ρ (π g) (m f) = m (t g f))
    (h : ∀ g f, m (p (t g f)) = m (t g (p f))) (q : C) (y : X) :
    P (ρ q y) = ρ q (P y) := by
  obtain ⟨g, rfl⟩ := hπ q
  obtain ⟨f, rfl⟩ := hm y
  rw [ht, hp, hp, ht, h]

private theorem globalThetaPrincipalValue_isotypicAverage_action {S₀ : Finset V} (hn : S₀.Nonempty)
    (q : IdeleClassGroup (𝓞 F) F) (y : Θ𝔽) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    globalThetaPrincipalValue F S₀ (ρ q y) = ρ q (globalThetaPrincipalValue F S₀ y) := by
  intro ρ
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_onReps
      (QuotientGroup.mk : IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F)
      (Submodule.Quotient.mk (p := K𝔽)) QuotientGroup.mk_surjective
      (Submodule.Quotient.mk_surjective _)
      (adelePrincipalValue F S₀) schwartzBruhatUnitTranslate (globalThetaPrincipalValue F S₀)
      (fun g y ↦ ρ g y) (globalThetaPrincipalValue_mk S₀)
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
      (globalThetaPrincipalValue_equivariant hn) q y

private theorem globalThetaPrincipalValue_isotypicAverage_commutes
    {G E : Type*} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    {μ : Measure G} {ρ : G →* (E →L[ℂ] E)} {χ : PontryaginDual G} {A : E →L[ℂ] E}
    (hA : IsPettisIsotypicAverageOn μ univ ρ χ A) (P : E →L[ℂ] E)
    (hP : ∀ g y, P (ρ g y) = ρ g (P y)) (x : E) : P (A x) = A (P x) := by
  have h : HasPettisIntegral (.positive (μ.restrict univ))
      (fun g ↦ P (star (χ g : ℂ) • ρ g x)) (P (A x)) := by
    obtain ⟨hi, he⟩ := hA x
    refine ⟨fun φ ↦ hi (φ.comp P), LinearMap.ext fun φ ↦ ?_⟩
    exact LinearMap.congr_fun he (φ.comp P)
  simp only [map_smul, hP] at h
  exact h.unique (hA (P x))

private theorem globalThetaPrincipalValue_isotypicAverage_nonempty (S₀ : Finset V) (hn : S₀.Nonempty)
    (χ : PontryaginDual (ideleClassNorm F).ker) (x : Θ𝔽) :
    let A := (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose
    globalThetaPrincipalValue F S₀ (A x) = A (globalThetaPrincipalValue F S₀ x) := by
  intro A
  let P : Θ𝔽 →L[ℂ] Θ𝔽 := ⟨globalThetaPrincipalValue F S₀, globalThetaPrincipalValue_continuous S₀⟩
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup Θ𝔽 := PolynormableSpace.isTopologicalAddGroup ℂ Θ𝔽
  let : ContinuousSMul ℂ Θ𝔽 := (PolynormableSpace.withSeminorms ℂ Θ𝔽).continuousSMul
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  refine globalThetaPrincipalValue_isotypicAverage_commutes
    (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose_spec P ?_ x
  intro g y
  exact globalThetaPrincipalValue_isotypicAverage_action (F := F) hn g.val y

private theorem globalThetaPrincipalValue_isotypicAverage_cases {ι E : Type*}
    (P : Finset ι → E → E) (A : E → E) (he : ∀ y, P ∅ y = y)
    (hn : ∀ t : Finset ι, t.Nonempty → ∀ y, P t (A y) = A (P t y))
    (s : Finset ι) (x : E) : P s (A x) = A (P s x) := by
  rcases s.eq_empty_or_nonempty with rfl | h
  · rw [he, he]
  · exact hn s h x

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value commutes with the norm-one character average of §5.2.3. -/
theorem globalThetaPrincipalValue_isotypicAverage (S₀ : Finset V)
    (χ : PontryaginDual (ideleClassNorm F).ker) (x : Θ𝔽) :
    let A := (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose
    globalThetaPrincipalValue F S₀ (A x) = A (globalThetaPrincipalValue F S₀ x) := by
  intro A
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_cases
      (fun S y ↦ globalThetaPrincipalValue F S y) A
      (globalThetaPrincipalValue_isotypicAverage_empty (F := F))
      (fun S hn y ↦ globalThetaPrincipalValue_isotypicAverage_nonempty (F := F) S hn χ y) S₀ x

end AdelicPrincipalValue


section DistributionOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "𝒟(" E ")" => 𝓓((⊤ : TopologicalSpace.Opens E), ℂ)

/-- Paper: Theorem 5.3.2.3, p. 245.
A distribution has order at most N if on each compact support it is bounded by the sup norms
of derivatives of orders zero through N. The same predicate applies to a tempered distribution
by restricting it to compactly supported test functions. -/
def DistributionOrderLE (T : 𝒟(E) → ℂ) (N : ℕ) : Prop :=
  ∀ K : Compacts E, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : 𝒟(E)), tsupport (f : E → ℂ) ⊆ (K : Set E) →
      ∀ B : ℝ, 0 ≤ B →
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ B) →
        ‖T f‖ ≤ C * B

/-- Paper: Theorem 5.3.2.1, p. 243.
Point evaluation on compactly supported tests has order at most zero. -/
theorem distributionOrderLE_eval (x : E) :
    DistributionOrderLE (fun f : 𝒟(E) ↦ f x) 0 := by
  intro K
  refine ⟨1, zero_le_one, fun f _ B _ h ↦ ?_⟩
  have hx := h 0 le_rfl x
  rw [norm_iteratedFDeriv_zero] at hx
  rw [one_mul]
  exact hx

/-- Paper: Theorem 5.3.2.1, p. 243.
The distributional support of a tempered distribution is contained in the origin. -/
abbrev TemperedSupportedAtOrigin (T : StrongDual ℂ 𝓢(E, ℂ)) : Prop :=
  Distribution.dsupport (⇑T) ⊆ {(0 : E)}

/-- Paper: Theorem 5.3.2.1, p. 243.
The Dirac distribution at zero is supported at zero. -/
theorem temperedSupportedAtOrigin_delta :
    TemperedSupportedAtOrigin (TemperedDistribution.delta (0 : E)) := by
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx {0}
    (TemperedDistribution.isVanishingOn_delta 0) isClosed_singleton

/-- Paper: Theorem 5.3.2.1, p. 243 and Definition D.1.8.2, p. 779.
A pointwise identification with additive Schwartz–Bruhat functions transports
the support of Appendix D to the distributional support of the classical test space. -/
theorem temperedSupport_eq_bruhatSupport_preimage
    (e : 𝓢(E, ℂ) ≃L[ℂ] SchwartzBruhat (Multiplicative E))
    (he : ∀ (f : 𝓢(E, ℂ)) (x : E), e f (Multiplicative.ofAdd x) = f x)
    (T : StrongDual ℂ 𝓢(E, ℂ)) :
    Distribution.dsupport (⇑T) = Multiplicative.ofAdd ⁻¹'
      schwartzBruhatDistributionSupport (T.comp e.symm.toContinuousLinearMap) := by
  let a : E ≃ₜ Multiplicative E := Homeomorph.refl E
  have hs (f : 𝓢(E, ℂ)) :
      tsupport (f : E → ℂ) = a ⁻¹' tsupport (e f : Multiplicative E → ℂ) := by
    have h : (e f : Multiplicative E → ℂ) ∘ a = (f : E → ℂ) := funext (he f)
    rw [← tsupport_comp_eq_preimage _ a, h]
  ext x
  change x ∈ Distribution.dsupport (⇑T) ↔ a x ∈ schwartzBruhatDistributionSupport _
  apply not_iff_not.mp
  refine (Distribution.notMem_dsupport_iff (f := (T : 𝓢(E, ℂ) → ℂ)) x).trans ?_
  simp only [schwartzBruhatDistributionSupport, Set.mem_compl_iff, not_not,
    schwartzBruhatVanishingLocus, Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨U, hU, ho, hx⟩
    refine ⟨a '' U, ⟨a.isOpenMap U ho, ?_⟩, ⟨x, hx, rfl⟩⟩
    intro g hg
    change T (e.symm g) = 0
    apply hU
    rw [hs, e.apply_symm_apply]
    exact (Set.preimage_mono hg).trans (by rw [Set.preimage_image_eq _ a.injective])
  · rintro ⟨U, ⟨ho, hU⟩, hx⟩
    refine ⟨a ⁻¹' U, ?_, ho.preimage a.continuous, hx⟩
    intro f hf
    have h := hU (e f) (fun y hy ↦ by
      obtain ⟨z, rfl⟩ := a.surjective y
      exact hf (by rwa [hs]))
    change T (e.symm (e f)) = 0 at h
    simpa only [e.symm_apply_apply] using h

end DistributionOrder

section RealOrigin

open scoped PowerSeries.WithPiTopology

local notation "𝒟ℝ" => 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)

/-- Paper: Theorem 5.3.2.1, p. 243.
The kth derivative of the real Dirac distribution uses the negative transpose of
differentiation on real Schwartz functions. -/
def realDiracDerivative (k : ℕ) : StrongDual ℂ 𝓢(ℝ, ℂ) :=
  (-1 : ℂ)^k •
    (TemperedDistribution.delta (0 : ℝ)).comp ((SchwartzMap.derivCLM ℂ ℂ)^k)

/-- The kth Dirac derivative is `(-1)^k` times the kth derivative at zero. -/
private theorem realSchwartzFlatQuotient_strongDual_dirac (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    realDiracDerivative k f = (-1 : ℂ) ^ k * iteratedDeriv k (f : ℝ → ℂ) 0 := by
  have hd : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f)) = _
      rw [ih]
  change (-1 : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ ^ k) f) 0 = _
  rw [congrFun hd 0]

/-- The Dirac derivatives of `x ↦ xⁿ χ(x / ε)`, which agrees with `xⁿ` near zero. -/
private theorem realSchwartzFlatQuotient_strongDual_scaled_dirac (χ : ContDiffBump (0 : ℝ))
    (n : ℕ) (G ψ : 𝓢(ℝ, ℂ)) (hG : ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) (ε : ℝ)
    (hε : 0 < ε) (hψ : ∀ x, ψ x = (ε : ℂ) ^ n * G (ε⁻¹ * x)) (j : ℕ) :
    realDiracDerivative j ψ = (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0 := by
  rw [realSchwartzFlatQuotient_strongDual_dirac, ← realSchwartzFlatQuotient_strongDual_pow]
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hball : Metric.ball (0 : ℝ) (ε * χ.rIn) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (mul_pos hε χ.rIn_pos)
  filter_upwards [hball] with x hx
  have hx' : ε⁻¹ * x ∈ Metric.closedBall (0 : ℝ) χ.rIn := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
      inv_mul_le_iff₀ hε]
    exact hx.le
  rw [hψ, hG, χ.one_of_mem_closedBall hx', Complex.ofReal_one, mul_one, Complex.ofReal_mul,
    mul_pow, ← mul_assoc, ← mul_pow, Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hε.ne'),
    one_pow, one_mul]

/-- Borel's lemma with uniform bounds: for every bound on the derivatives at zero, one bounded
set of Schwartz functions realizes every sequence of Dirac derivatives within that bound. -/
private theorem realSchwartzFlatQuotient_strongDual_borel (M : ℕ → ℝ) :
    ∃ S : Set 𝓢(ℝ, ℂ), Bornology.IsVonNBounded ℂ S ∧ ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ M n) →
      ∃ f ∈ S, ∀ n, realDiracDerivative n f = c n := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hχ : χ.rOut ≤ 1 := le_rfl
  choose G hG using realSchwartzFlatQuotient_strongDual_exists_bump χ
  have hGc (n : ℕ) : HasCompactSupport (G n : ℝ → ℂ) :=
    (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (realSchwartzFlatQuotient_strongDual_bump_tsupport χ hχ n (G n) (hG n))
  let C (n m : ℕ) : ℝ := SchwartzMap.seminorm ℂ 0 m (G n)
  have hC (n m : ℕ) : 0 ≤ C n m := apply_nonneg _ _
  let δ (n : ℕ) : ℝ := (1 / 2) ^ n / (|M n| + 1)
  have hδ (n : ℕ) : 0 < δ n := by positivity
  have hsC (n : ℕ) : 0 < ∑ m ∈ Finset.range n, C n m + 1 := by
    have : 0 ≤ ∑ m ∈ Finset.range n, C n m := Finset.sum_nonneg fun m _ ↦ hC n m
    linarith
  let ε (n : ℕ) : ℝ := min 1 (δ n / (∑ m ∈ Finset.range n, C n m + 1))
  have hε (n : ℕ) : 0 < ε n := lt_min one_pos (div_pos (hδ n) (hsC n))
  choose φ hφe using fun n ↦
    realSchwartzFlatQuotient_strongDual_exists_scaled (G n) (hGc n) n (ε n) (hε n).ne'
  have hφ (n m k : ℕ) (hmn : m < n) : SchwartzMap.seminorm ℂ k m (φ n) ≤ δ n := by
    have hS : C n m ≤ ∑ m ∈ Finset.range n, C n m + 1 := by
      have := Finset.single_le_sum (fun m _ ↦ hC n m) (Finset.mem_range.mpr hmn)
      linarith
    calc SchwartzMap.seminorm ℂ k m (φ n) ≤ ε n * C n m :=
          realSchwartzFlatQuotient_strongDual_scaled_seminorm χ hχ n m k hmn (G n) (φ n) (hG n)
            (ε n) (hε n) (min_le_left _ _) (hφe n)
      _ ≤ δ n / (∑ m ∈ Finset.range n, C n m + 1) * (∑ m ∈ Finset.range n, C n m + 1) := by
          gcongr
          · exact min_le_right _ _
      _ = δ n := div_mul_cancel₀ _ (hsC n).ne'
  let u (i : ℕ × ℕ) (n : ℕ) : ℝ :=
    (1 / 2) ^ n + if n ≤ i.2 then |M n| * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0
  have hu (i : ℕ × ℕ) : Summable (u i) := by
    refine (summable_geometric_of_lt_one (by norm_num) (by norm_num)).add ?_
    refine summable_of_ne_finset_zero (s := Finset.range (i.2 + 1)) fun n hn ↦ ?_
    rw [Finset.mem_range, not_lt] at hn
    simp [show ¬ n ≤ i.2 by omega]
  let b (c : ℕ → ℂ) (n : ℕ) : ℂ := c n * (-1 : ℂ) ^ n / (n.factorial : ℂ)
  have hb (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M n) (n : ℕ) : ‖b c n‖ ≤ |M n| := by
    have hf : (1 : ℝ) ≤ n.factorial := mod_cast n.factorial_pos
    simp only [b, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      Complex.norm_natCast]
    calc ‖c n‖ / (n.factorial : ℝ) ≤ ‖c n‖ / 1 := by gcongr
      _ = ‖c n‖ := div_one _
      _ ≤ |M n| := (hc n).trans (le_abs_self _)
  have hx (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M n) (i : ℕ × ℕ) (n : ℕ) :
      schwartzSeminormFamily ℂ ℝ ℂ i (b c n • φ n) ≤ u i n := by
    rw [SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul]
    have h0 : 0 ≤ SchwartzMap.seminorm ℂ i.1 i.2 (φ n) := apply_nonneg _ _
    have hg : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    by_cases hn : n ≤ i.2
    · simp only [u, hn, ↓reduceIte]
      have := mul_le_mul_of_nonneg_right (hb c hc n) h0
      linarith
    · simp only [u, hn, ↓reduceIte, add_zero]
      calc ‖b c n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) ≤ |M n| * δ n :=
            mul_le_mul (hb c hc n) (hφ n i.2 i.1 (by omega)) h0 (abs_nonneg _)
        _ = (1 / 2) ^ n * (|M n| / (|M n| + 1)) := by simp only [δ]; ring
        _ ≤ (1 / 2) ^ n * 1 := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ = (1 / 2) ^ n := mul_one _
  have hsum (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M n) :=
    realSchwartzFlatQuotient_strongDual_summable (schwartz_withSeminorms ℂ ℝ ℂ)
      (fun n ↦ b c n • φ n) u hu (hx c hc)
  refine ⟨{f | ∃ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ M n) ∧ f = ∑' n, b c n • φ n}, ?_, fun c hc ↦ ?_⟩
  · rw [(schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded]
    intro i
    have h0 : 0 ≤ ∑' n, u i n := tsum_nonneg fun n ↦ by
      have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      have : 0 ≤ if n ≤ i.2 then |M n| * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0 := by
        split_ifs
        · exact mul_nonneg (abs_nonneg _) (apply_nonneg _ _)
        · exact le_rfl
      simp only [u]
      linarith
    refine ⟨∑' n, u i n + 1, by linarith, ?_⟩
    rintro f ⟨c, hc, rfl⟩
    exact ((hsum c hc).2 i).trans_lt (by linarith)
  · refine ⟨∑' n, b c n • φ n, ⟨c, hc, rfl⟩, fun j ↦ ?_⟩
    rw [ContinuousLinearMap.map_tsum _ (hsum c hc).1]
    have hd (n : ℕ) : realDiracDerivative j (φ n) =
        (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0 :=
      realSchwartzFlatQuotient_strongDual_scaled_dirac χ n (G n) (φ n) (hG n) (ε n) (hε n)
        (hφe n) j
    simp only [map_smul, smul_eq_mul, hd]
    rw [tsum_eq_single j fun n hn ↦ by simp [Ne.symm hn]]
    simp only [↓reduceIte]
    have hf : (j.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero j
    simp only [b]
    field_simp
    rw [← pow_mul, mul_comm j 2, pow_mul, neg_one_sq, one_pow, mul_one]

/-- Paper: Theorem 5.3.2.1, p. 243.
The first derivative of the real Dirac distribution evaluates to minus the derivative at zero. -/
theorem realDiracDerivative_one (f : 𝓢(ℝ, ℂ)) :
    realDiracDerivative 1 f = -deriv (f : ℝ → ℂ) 0 := by
  change (-1 : ℂ) ^ 1 • (((SchwartzMap.derivCLM ℂ ℂ) ^ 1) f) 0 = _
  rw [pow_one, pow_one, SchwartzMap.derivCLM_apply, neg_one_smul]

/-- Paper: Theorem 5.3.2.1, p. 243.
Every real tempered distribution supported at zero is a finite linear combination of
derivatives of the Dirac distribution at zero. -/
theorem realTemperedDistribution_eq_sum_diracDerivative (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : TemperedSupportedAtOrigin T) :
    ∃ (N : ℕ) (c : Fin (N + 1) → ℂ),
      T = ∑ k : Fin (N + 1), c k • realDiracDerivative k.val := by sorry

/-- Paper: Theorem 5.3.2.1(1), p. 243.
The flat real Schwartz subspace is the intersection of the kernels of all Dirac derivatives. -/
def realSchwartzFlatAtOrigin : Submodule ℂ 𝓢(ℝ, ℂ) :=
  ⨅ k : ℕ, LinearMap.ker (realDiracDerivative k).toLinearMap

/-- Paper: Theorem 5.3.2.1(1), p. 243.
A real Schwartz function lies in the flat subspace exactly when every derivative at zero
vanishes. -/
theorem mem_realSchwartzFlatAtOrigin_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ realSchwartzFlatAtOrigin ↔
      ∀ k : ℕ, iteratedDeriv k (f : ℝ → ℂ) 0 = 0 := by
  have hd (k : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f)) = _
      rw [ih]
  rw [realSchwartzFlatAtOrigin, Submodule.mem_iInf]
  apply forall_congr'
  intro k
  change (-1 : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ ^ k) f) 0 = 0 ↔ _
  rw [congrFun (hd k) 0, mul_eq_zero]
  simp

/-- Paper: Theorem 5.3.2.1(1), p. 243.
The flat real Schwartz subspace is closed. -/
theorem realSchwartzFlatAtOrigin_isClosed :
    IsClosed (realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)) := by
  rw [realSchwartzFlatAtOrigin, Submodule.coe_iInf]
  exact isClosed_iInter fun k ↦ (realDiracDerivative k).isClosed_ker

/-- Every bounded set of the flat quotient is the image of a bounded set of Schwartz
functions. -/
private theorem realSchwartzFlatQuotient_strongDual_lift
    (B : Set (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ S : Set 𝓢(ℝ, ℂ), Bornology.IsVonNBounded ℂ S ∧ B ⊆ realSchwartzFlatAtOrigin.mkQ '' S := by
  have hle (n : ℕ) : realSchwartzFlatAtOrigin ≤ (realDiracDerivative n).ker := fun f hf ↦
    (Submodule.mem_iInf _).mp hf n
  have hM (n : ℕ) : ∃ M : ℝ, ∀ y ∈ B,
      ‖realSchwartzFlatAtOrigin.liftQL (realDiracDerivative n) (hle n) y‖ ≤ M := by
    have := hB.image (realSchwartzFlatAtOrigin.liftQL (realDiracDerivative n) (hle n))
    rw [NormedSpace.isVonNBounded_iff] at this
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp this
    exact ⟨M, fun y hy ↦ hM _ ⟨y, hy, rfl⟩⟩
  choose M hM using hM
  obtain ⟨S, hS, hlift⟩ := realSchwartzFlatQuotient_strongDual_borel M
  refine ⟨S, hS, fun y hy ↦ ?_⟩
  obtain ⟨g, rfl⟩ := realSchwartzFlatAtOrigin.mkQ_surjective y
  obtain ⟨f, hf, hfd⟩ := hlift (fun n ↦ realDiracDerivative n g) (fun n ↦ hM n _ hy)
  refine ⟨f, hf, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
  rw [LinearMap.mem_ker, map_sub]
  change realDiracDerivative n f - realDiracDerivative n g = 0
  rw [hfd n, sub_self]

/-- A Borel series `∑ bₙ φₙ` whose terms past `m` are dominated by a summable sequence converges
in the Schwartz space. Its Dirac derivatives are those of the coefficients, and its seminorms of
order at most `m` are bounded by the first `m + 1` terms plus the dominating sum. -/
private theorem realSchwartzTaylor_equiv_series (m : ℕ) (φ : ℕ → 𝓢(ℝ, ℂ)) (b : ℕ → ℂ)
    (w : ℕ → ℝ) (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n)
    (hφ : ∀ n k j, j < n → m < n → ‖b n‖ * SchwartzMap.seminorm ℂ k j (φ n) ≤ w n)
    (hd : ∀ n j, realDiracDerivative j (φ n) =
      (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ j, realDiracDerivative j f = b j * (-1 : ℂ) ^ j * (j.factorial : ℂ)) ∧
      ∀ k j, j ≤ m → SchwartzMap.seminorm ℂ k j f ≤
        ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ k j (φ n) + ∑' n, w n := by
  let v (i : ℕ × ℕ) (n : ℕ) : ℝ :=
    if n ≤ max i.2 m then ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0
  have hv (i : ℕ × ℕ) : Summable (v i) := by
    refine summable_of_ne_finset_zero (s := Finset.range (max i.2 m + 1)) fun n hn ↦ ?_
    rw [Finset.mem_range, not_lt] at hn
    simp only [v, show ¬ n ≤ max i.2 m by omega, ↓reduceIte]
  let u (i : ℕ × ℕ) (n : ℕ) : ℝ := w n + v i n
  have hx (i : ℕ × ℕ) (n : ℕ) : schwartzSeminormFamily ℂ ℝ ℂ i (b n • φ n) ≤ u i n := by
    rw [SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul]
    by_cases hn : n ≤ max i.2 m
    · simp only [u, v, hn, ↓reduceIte]
      linarith [hw0 n]
    · simp only [u, v, hn, ↓reduceIte, add_zero]
      exact hφ n i.1 i.2 (by omega) (by omega)
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  obtain ⟨hsum, hbound⟩ := realSchwartzFlatQuotient_strongDual_summable
    (schwartz_withSeminorms ℂ ℝ ℂ) (fun n ↦ b n • φ n) u (fun i ↦ hw.add (hv i)) hx
  refine ⟨∑' n, b n • φ n, fun j ↦ ?_, fun k j hj ↦ ?_⟩
  · rw [ContinuousLinearMap.map_tsum _ hsum]
    simp only [map_smul, smul_eq_mul, hd]
    rw [tsum_eq_single j fun n hn ↦ by simp [Ne.symm hn]]
    simp only [↓reduceIte]
    ring
  · have h := hbound (k, j)
    rw [SchwartzMap.schwartzSeminormFamily_apply] at h
    refine h.trans (le_of_eq ?_)
    rw [Summable.tsum_add hw (hv (k, j)), add_comm]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (m + 1)) fun n hn ↦ ?_]
    · refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [Finset.mem_range] at hn
      simp only [v, show n ≤ max j m by omega, ↓reduceIte]
    · rw [Finset.mem_range, not_lt] at hn
      simp only [v, show ¬ n ≤ max j m by omega, ↓reduceIte]

/-- A small Borel lemma: for finitely many Schwartz seminorms and `r > 0`, every sequence whose
first `N` terms are below `δ` is the sequence of Taylor coefficients of a Schwartz function whose
seminorms in the family are below `r`. -/
private theorem realSchwartzTaylor_equiv_small (s : Finset (ℕ × ℕ)) (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∃ δ > 0, ∀ b : ℕ → ℂ, (∀ n ≤ N, ‖b n‖ < δ) → ∃ f : 𝓢(ℝ, ℂ),
      (∀ n, realDiracDerivative n f = b n * (-1 : ℂ) ^ n * (n.factorial : ℂ)) ∧
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f < r := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hχ : χ.rOut ≤ 1 := le_rfl
  choose G hG using realSchwartzFlatQuotient_strongDual_exists_bump χ
  have hGc (n : ℕ) : HasCompactSupport (G n : ℝ → ℂ) :=
    (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (realSchwartzFlatQuotient_strongDual_bump_tsupport χ hχ n (G n) (hG n))
  let m := s.sup Prod.snd
  let K : ℝ := ∑ i ∈ s, ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ i.1 i.2 (G n)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun n _ ↦ apply_nonneg _ _
  refine ⟨m, r / (2 * (K + 1)), by positivity, fun b hb ↦ ?_⟩
  let C (n j : ℕ) : ℝ := SchwartzMap.seminorm ℂ 0 j (G n)
  have hC (n j : ℕ) : 0 ≤ C n j := apply_nonneg _ _
  let w (n : ℕ) : ℝ := r / 4 * (1 / 2) ^ n
  have hw0 (n : ℕ) : 0 ≤ w n := by positivity
  have hwsum : HasSum w (r / 2) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (r / 4)
    convert this using 1
    norm_num
    ring
  have hsC (n : ℕ) : 0 < ∑ j ∈ Finset.range n, C n j + 1 := by
    have : 0 ≤ ∑ j ∈ Finset.range n, C n j := Finset.sum_nonneg fun j _ ↦ hC n j
    linarith
  let ε (n : ℕ) : ℝ := min 1 (w n / (‖b n‖ + 1) / (∑ j ∈ Finset.range n, C n j + 1))
  have hε (n : ℕ) : 0 < ε n := lt_min one_pos (by have := hsC n; positivity)
  choose ψ hψ using fun n ↦
    realSchwartzFlatQuotient_strongDual_exists_scaled (G n) (hGc n) n (ε n) (hε n).ne'
  let φ (n : ℕ) : 𝓢(ℝ, ℂ) := if n ≤ m then G n else ψ n
  have hd (n j : ℕ) : realDiracDerivative j (φ n) =
      (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0 := by
    by_cases hn : n ≤ m
    · simp only [φ, hn, ↓reduceIte]
      exact realSchwartzFlatQuotient_strongDual_scaled_dirac χ n (G n) (G n) (hG n) 1 one_pos
        (fun x ↦ by simp) j
    · simp only [φ, hn, ↓reduceIte]
      exact realSchwartzFlatQuotient_strongDual_scaled_dirac χ n (G n) (ψ n) (hG n) (ε n) (hε n)
        (hψ n) j
  have hφ (n k j : ℕ) (hjn : j < n) (hmn : m < n) :
      ‖b n‖ * SchwartzMap.seminorm ℂ k j (φ n) ≤ w n := by
    simp only [φ, show ¬ n ≤ m by omega, ↓reduceIte]
    have hS : C n j ≤ ∑ j ∈ Finset.range n, C n j + 1 := by
      have := Finset.single_le_sum (fun j _ ↦ hC n j) (Finset.mem_range.mpr hjn)
      linarith
    have h1 : SchwartzMap.seminorm ℂ k j (ψ n) ≤ w n / (‖b n‖ + 1) :=
      calc SchwartzMap.seminorm ℂ k j (ψ n) ≤ ε n * C n j :=
            realSchwartzFlatQuotient_strongDual_scaled_seminorm χ hχ n j k hjn (G n) (ψ n) (hG n)
              (ε n) (hε n) (min_le_left _ _) (hψ n)
        _ ≤ w n / (‖b n‖ + 1) / (∑ j ∈ Finset.range n, C n j + 1) *
              (∑ j ∈ Finset.range n, C n j + 1) := by
            gcongr
            · exact min_le_right _ _
        _ = w n / (‖b n‖ + 1) := div_mul_cancel₀ _ (hsC n).ne'
    calc ‖b n‖ * SchwartzMap.seminorm ℂ k j (ψ n) ≤ ‖b n‖ * (w n / (‖b n‖ + 1)) := by gcongr
      _ = w n * (‖b n‖ / (‖b n‖ + 1)) := by ring
      _ ≤ w n * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = w n := mul_one _
  obtain ⟨f, hfd, hfb⟩ :=
    realSchwartzTaylor_equiv_series m φ b w hwsum.summable hw0 hφ hd
  refine ⟨f, hfd, Seminorm.finset_sup_apply_lt hr fun i hi ↦ ?_⟩
  have him : i.2 ≤ m := Finset.le_sup (f := Prod.snd) hi
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  have hlow : ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) ≤
      r / (2 * (K + 1)) * K := by
    calc ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n)
        ≤ ∑ n ∈ Finset.range (m + 1), r / (2 * (K + 1)) * SchwartzMap.seminorm ℂ i.1 i.2 (G n) := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          rw [Finset.mem_range] at hn
          simp only [φ, show n ≤ m by omega, ↓reduceIte]
          exact mul_le_mul_of_nonneg_right (hb n (by omega)).le (apply_nonneg _ _)
      _ = r / (2 * (K + 1)) *
            ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ i.1 i.2 (G n) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ r / (2 * (K + 1)) * K := by
          gcongr
          exact Finset.single_le_sum (f := fun i : ℕ × ℕ ↦
            ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ i.1 i.2 (G n))
            (fun i _ ↦ Finset.sum_nonneg fun n _ ↦ apply_nonneg _ _) hi
  have hrK : r / (2 * (K + 1)) * K < r / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc SchwartzMap.seminorm ℂ i.1 i.2 f
      ≤ ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) + ∑' n, w n :=
        hfb i.1 i.2 him
    _ < r / 2 + r / 2 := by rw [hwsum.tsum_eq]; linarith
    _ = r := add_halves r

/-- Paper: Theorem 5.3.2.1(2), p. 243.
The real Schwartz quotient by flat functions is identified with formal power series by the
Taylor map. The topology of coefficientwise convergence is generated by (5.3.2.3).
Deviation: The Taylor formula is applied to test functions, as required by the quotient domain. -/
theorem realSchwartzTaylor_equiv :
    ∃ e : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃L[ℂ] PowerSeries ℂ,
      ∀ (f : 𝓢(ℝ, ℂ)) (k : ℕ),
        PowerSeries.coeff k (e (realSchwartzFlatAtOrigin.mkQ f)) =
          iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ) := by
  let a (k : ℕ) : StrongDual ℂ 𝓢(ℝ, ℂ) :=
    ((-1 : ℂ) ^ k / (k.factorial : ℂ)) • realDiracDerivative k
  have hfact (k : ℕ) : (k.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero k
  have hsq (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have ha (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
      a k f = iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ) := by
    simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      realSchwartzFlatQuotient_strongDual_dirac]
    rw [div_mul_eq_mul_div, div_left_inj₀ (hfact k), ← mul_assoc, hsq, one_mul]
  have hinv (k : ℕ) (z : ℂ) :
      (-1 : ℂ) ^ k / (k.factorial : ℂ) * (z * (-1 : ℂ) ^ k * (k.factorial : ℂ)) = z := by
    rw [div_mul_eq_mul_div, div_eq_iff (hfact k)]
    linear_combination (z * (k.factorial : ℂ)) * hsq k
  let T : 𝓢(ℝ, ℂ) →ₗ[ℂ] PowerSeries ℂ :=
    { toFun := fun f ↦ PowerSeries.mk fun k ↦ a k f
      map_add' := fun f g ↦ by ext k; simp
      map_smul' := fun c f ↦ by ext k; simp }
  have hT (f : 𝓢(ℝ, ℂ)) (k : ℕ) : PowerSeries.coeff k (T f) = a k f := by
    change PowerSeries.coeff k (PowerSeries.mk fun k ↦ a k f) = _
    exact PowerSeries.coeff_mk _ _
  have hTc : Continuous T := by
    refine continuous_iff_continuousAt.mpr fun f ↦ ?_
    rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    simp only [hT]
    exact (a d).continuous.tendsto f
  let TL : 𝓢(ℝ, ℂ) →L[ℂ] PowerSeries ℂ := ⟨T, hTc⟩
  have hTL (f : 𝓢(ℝ, ℂ)) (k : ℕ) : PowerSeries.coeff k (TL f) = a k f := hT f k
  have hmem (f : 𝓢(ℝ, ℂ)) : f ∈ realSchwartzFlatAtOrigin ↔ TL f = 0 := by
    rw [realSchwartzFlatAtOrigin, Submodule.mem_iInf, PowerSeries.ext_iff]
    refine forall_congr' fun k ↦ ?_
    rw [LinearMap.mem_ker, hTL, map_zero]
    simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
    have : (-1 : ℂ) ^ k / (k.factorial : ℂ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num)) (hfact k)
    rw [mul_eq_zero, or_iff_right this]
  have hle : realSchwartzFlatAtOrigin ≤ TL.ker := fun f hf ↦ (hmem f).mp hf
  let E := realSchwartzFlatAtOrigin.liftQL TL hle
  have hE (f : 𝓢(ℝ, ℂ)) : E (realSchwartzFlatAtOrigin.mkQ f) = TL f := rfl
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).mpr fun y hy ↦ ?_
    obtain ⟨f, rfl⟩ := realSchwartzFlatAtOrigin.mkQ_surjective y
    rw [hE] at hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((hmem f).mpr hy)
  have hsurj : Function.Surjective E := by
    intro p
    let c (n : ℕ) : ℂ := PowerSeries.coeff n p * (-1 : ℂ) ^ n * (n.factorial : ℂ)
    obtain ⟨S, -, hS⟩ := realSchwartzFlatQuotient_strongDual_borel (fun n ↦ ‖c n‖)
    obtain ⟨f, -, hf⟩ := hS c fun n ↦ le_rfl
    refine ⟨realSchwartzFlatAtOrigin.mkQ f, ?_⟩
    rw [hE]
    ext k
    rw [hTL]
    simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hf, c]
    exact hinv k _
  let e : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃ₗ[ℂ] PowerSeries ℂ :=
    LinearEquiv.ofBijective (E : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) →ₗ[ℂ] PowerSeries ℂ)
      ⟨hinj, hsurj⟩
  have he (y : 𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) : e y = E y := rfl
  have hsymm : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro V hV
    have hq : realSchwartzFlatAtOrigin.mkQ ⁻¹' V ∈ 𝓝 (0 : 𝓢(ℝ, ℂ)) :=
      realSchwartzFlatAtOrigin.mkQL.continuous.continuousAt.preimage_mem_nhds
        (by simpa using hV)
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).hasBasis_zero_ball.mem_iff.mp hq
    obtain ⟨N, δ, hδ, hsmall⟩ := realSchwartzTaylor_equiv_small s r hr
    have hW : ∀ᶠ p in 𝓝 (0 : PowerSeries ℂ),
        ∀ n ∈ Finset.range (N + 1), ‖PowerSeries.coeff n p‖ < δ := by
      rw [Filter.eventually_all_finset]
      intro n _
      have h := (PowerSeries.WithPiTopology.continuous_coeff ℂ n).tendsto 0
      rw [map_zero] at h
      exact (h.eventually (Metric.ball_mem_nhds 0 hδ)).mono fun p hp ↦ by simpa using hp
    rw [Filter.mem_map]
    filter_upwards [hW] with p hp
    obtain ⟨f, hfd, hf⟩ := hsmall (fun n ↦ PowerSeries.coeff n p)
      fun n hn ↦ hp n (Finset.mem_range.mpr (by omega))
    have hp' : e.symm p = realSchwartzFlatAtOrigin.mkQ f := by
      rw [LinearEquiv.symm_apply_eq, he, hE]
      ext k
      rw [hTL]
      simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hfd]
      exact (hinv k _).symm
    rw [Set.mem_preimage, hp']
    exact hsub ((Seminorm.mem_ball_zero _).mpr hf)
  let eL : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃L[ℂ] PowerSeries ℂ :=
    { e with
      continuous_toFun := E.continuous
      continuous_invFun := hsymm }
  refine ⟨eL, fun f k ↦ ?_⟩
  change PowerSeries.coeff k (TL f) = _
  rw [hTL, ha]

/-- Paper: Remark 5.3.2.2, p. 243.
Pullback from the strong dual of the real flat quotient embeds it in the strong dual of the
real Schwartz space with image the annihilator of the flat subspace. -/
theorem realSchwartzFlatQuotient_strongDual :
    let pull := fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
      T.comp realSchwartzFlatAtOrigin.mkQL
    IsEmbedding pull ∧ Set.range pull =
      {T : StrongDual ℂ 𝓢(ℝ, ℂ) | ∀ f ∈ realSchwartzFlatAtOrigin, T f = 0} := by
  intro pull
  refine ⟨realSchwartzFlatQuotient_strongDual_isEmbedding _
    realSchwartzFlatQuotient_strongDual_lift, ?_⟩
  change Set.range (fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
    T.comp realSchwartzFlatAtOrigin.mkQL) = _
  rw [range_transpose_mkQL]
  ext T
  simp [Set.mem_iInter]

/-- A continuous functional on formal power series vanishes on every series whose coefficients
up to some fixed order are zero. -/
private theorem realDiracDerivatives_polynomialEquiv_finite (L : PowerSeries ℂ →L[ℂ] ℂ) :
    ∃ N : ℕ, ∀ s : PowerSeries ℂ, (∀ n ≤ N, PowerSeries.coeff n s = 0) → L s = 0 := by
  by_contra h
  push Not at h
  choose s hs0 hs using h
  let t (N : ℕ) : PowerSeries ℂ := (L (s N))⁻¹ • s N
  have ht : Tendsto t atTop (𝓝 0) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    rw [map_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop d] with N hN
    simp [t, hs0 N d hN]
  have h1 := (L.continuous.tendsto 0).comp ht
  rw [map_zero] at h1
  have h2 : ⇑L ∘ t = fun _ ↦ 1 := by
    funext N
    simp [t, inv_mul_cancel₀ (hs N)]
  rw [h2] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

-- TODO(paper-gap): The coefficient seminorms in (5.3.2.2) give the coefficientwise
-- topology on the whole polynomial space and do not give its finest locally convex topology.

/-- Paper: Theorem 5.3.2.1(1), p. 243.
Polynomials with the finest locally convex topology identify with the strong dual of the
real Schwartz quotient by flat functions through the factorial-normalized Dirac derivatives.
The least order bound of the distribution is the polynomial's natural degree.
Deviation: Uses the finest locally convex topology and omits the false equivalence in (5.3.2.2). -/
theorem realDiracDerivatives_polynomialEquiv :
    ∃ e : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ]
        StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin),
      (∀ k : ℕ, ∀ f : 𝓢(ℝ, ℂ),
        e (Polynomial.monomial k 1) (realSchwartzFlatAtOrigin.mkQ f) =
          realDiracDerivative k f / (k.factorial : ℂ)) ∧
      ∀ (p : Polynomial ℂ) (N : ℕ),
        DistributionOrderLE
          (fun f : 𝒟ℝ ↦ e p (realSchwartzFlatAtOrigin.mkQ
            (f.hasCompactSupport.toSchwartzMap f.contDiff))) N ↔ p.natDegree ≤ N := by
  obtain ⟨τ, hτ⟩ := realSchwartzTaylor_equiv
  have hfact (k : ℕ) : (k.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero k
  let cf (k : ℕ) : PowerSeries ℂ →L[ℂ] ℂ :=
    ⟨PowerSeries.coeff k, PowerSeries.WithPiTopology.continuous_coeff ℂ k⟩
  let c (k : ℕ) : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    ((-1 : ℂ) ^ k) • (cf k).comp τ.toContinuousLinearMap
  have hc (k : ℕ) (y : 𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :
      c k y = (-1 : ℂ) ^ k * PowerSeries.coeff k (τ y) := rfl
  have hcf (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
      c k (realSchwartzFlatAtOrigin.mkQ f) = realDiracDerivative k f / (k.factorial : ℂ) := by
    rw [hc, hτ, realSchwartzFlatQuotient_strongDual_dirac]
    ring
  let Φ : Polynomial ℂ →ₗ[ℂ] StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    Polynomial.lsum fun k ↦ LinearMap.smulRight LinearMap.id (c k)
  have hΦ (p : Polynomial ℂ) (y : 𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :
      Φ p y = ∑ k ∈ p.support, p.coeff k * c k y := by
    simp [Φ, Polynomial.lsum_apply, Polynomial.sum_def, sum_apply]
  have hΦm (k : ℕ) (a : ℂ) : Φ (Polynomial.monomial k a) = a • c k := by
    simp [Φ, Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).mpr fun p hp ↦ ?_
    ext n
    have h := congrArg (fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
      T (τ.symm (PowerSeries.X ^ n))) hp
    simp only [hΦ, hc, ContinuousLinearEquiv.apply_symm_apply, PowerSeries.coeff_X_pow,
      zero_apply] at h
    rw [Finset.sum_eq_single n (fun k _ hk ↦ by simp [hk])
      (fun hn ↦ by simp [Polynomial.notMem_support_iff.mp hn])] at h
    simpa using h
  have hsurj : Function.Surjective Φ := by
    intro T
    let L : PowerSeries ℂ →L[ℂ] ℂ := T.comp τ.symm.toContinuousLinearMap
    obtain ⟨N, hN⟩ := realDiracDerivatives_polynomialEquiv_finite L
    refine ⟨∑ n ∈ Finset.range (N + 1),
      Polynomial.monomial n ((-1 : ℂ) ^ n * L (PowerSeries.X ^ n)), ?_⟩
    ext y
    rw [map_sum]
    simp only [hΦm, sum_apply, smul_apply, hc,
      smul_eq_mul]
    have hy : T y = L (τ y) := by simp [L]
    have hs : L (τ y - ∑ n ∈ Finset.range (N + 1),
        PowerSeries.coeff n (τ y) • PowerSeries.X ^ n) = 0 := by
      apply hN
      intro m hm
      rw [map_sub, map_sum]
      simp [PowerSeries.coeff_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_of_le hm]
    rw [map_sub, map_sum, sub_eq_zero] at hs
    rw [hy, hs]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [map_smul, smul_eq_mul]
    have : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (L (PowerSeries.X ^ n) * PowerSeries.coeff n (τ y)) * this
  let e₀ : Polynomial ℂ ≃ₗ[ℂ] StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let e₁ : FinestLocallyConvex (Polynomial ℂ) ≃ₗ[ℂ]
      StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) := e₀
  have he₁ (p : Polynomial ℂ) : e₁ p = Φ p := rfl
  have : IsClosed (realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)) := realSchwartzFlatAtOrigin_isClosed
  let : UniformSpace (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    isUniformAddGroup_of_addCommGroup
  let : PolynormableSpace ℂ (StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin)) :=
    uniformConvergenceCLM_polynormable (F := ℂ)
      {B : Set (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) | Bornology.IsVonNBounded ℂ B}
      (fun _ h ↦ by exact h)
      (by rw [Bornology.sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  have hcont : Continuous e₁ :=
    continuous_of_finestLocallyConvex (Polynomial ℂ) e₁.toLinearMap
  have hsymm : Continuous e₁.symm := by
    refine (finestLocallyConvex_withSeminorms (Polynomial ℂ)).continuous_of_continuous_comp
      e₁.symm.toLinearMap fun p ↦ ?_
    refine Seminorm.continuous (r := 1) ?_
    let w (n : ℕ) : ℝ := p (Polynomial.monomial n 1)
    obtain ⟨S, hS, hSc⟩ :=
      realSchwartzFlatQuotient_strongDual_borel fun n ↦ (n.factorial : ℝ) * w n
    have hB : Bornology.IsVonNBounded ℂ (realSchwartzFlatAtOrigin.mkQ '' S) :=
      hS.image realSchwartzFlatAtOrigin.mkQL
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo hB
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with T hT
    rw [Seminorm.mem_ball_zero]
    change p (e₁.symm T) < 1
    obtain ⟨q, hq⟩ : ∃ q : Polynomial ℂ, e₁.symm T = q := ⟨_, rfl⟩
    have hTq : T = Φ q := by rw [← he₁, ← hq, LinearEquiv.apply_symm_apply]
    rw [hq]
    let d (n : ℕ) : ℂ :=
      (n.factorial : ℂ) * (w n : ℂ) * (star (q.coeff n) / (‖q.coeff n‖ : ℂ))
    have hd (n : ℕ) : ‖d n‖ ≤ (n.factorial : ℝ) * w n := by
      have hw : 0 ≤ w n := apply_nonneg _ _
      have hu : ‖star (q.coeff n) / (‖q.coeff n‖ : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
        exact div_self_le_one _
      calc ‖d n‖ = (n.factorial : ℝ) * w n * ‖star (q.coeff n) / (‖q.coeff n‖ : ℂ)‖ := by
            simp only [d, norm_mul, Complex.norm_natCast, Complex.norm_real,
              Real.norm_of_nonneg hw]
        _ ≤ (n.factorial : ℝ) * w n * 1 := by gcongr
        _ = (n.factorial : ℝ) * w n := mul_one _
    obtain ⟨f, hfS, hf⟩ := hSc d hd
    have hval : T (realSchwartzFlatAtOrigin.mkQ f) =
        ((∑ k ∈ q.support, w k * ‖q.coeff k‖ : ℝ) : ℂ) := by
      rw [hTq, hΦ]
      push_cast
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hq0 : q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
      have hn0 : (‖q.coeff k‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq0
      rw [hcf, hf k]
      simp only [d]
      field_simp
      rw [Complex.star_def, show q.coeff k * (k.factorial : ℂ) * (w k : ℂ) *
          (starRingEnd ℂ) (q.coeff k) = (q.coeff k * (starRingEnd ℂ) (q.coeff k)) *
          ((k.factorial : ℂ) * (w k : ℂ)) by ring, Complex.mul_conj']
      field_simp
      exact mul_div_cancel_left₀ _ (hfact k)
    have hle : p q ≤ ∑ k ∈ q.support, w k * ‖q.coeff k‖ := by
      conv_lhs => rw [q.as_sum_support]
      refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
        (Finset.sum_le_sum fun k _ ↦ ?_)
      rw [show Polynomial.monomial k (q.coeff k) = q.coeff k • Polynomial.monomial k 1 by
        rw [Polynomial.smul_monomial, smul_eq_mul, mul_one], map_smul_eq_mul, mul_comm]
    have hlt := hT ⟨f, hfS, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, hval, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦
        mul_nonneg (apply_nonneg _ _) (norm_nonneg _))] at hlt
    exact hle.trans_lt hlt
  let e : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ]
      StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    { e₁ with
      continuous_toFun := hcont
      continuous_invFun := hsymm }
  have he (p : Polynomial ℂ) : e p = Φ p := rfl
  have hev (p : Polynomial ℂ) (g : 𝓢(ℝ, ℂ)) : e p (realSchwartzFlatAtOrigin.mkQ g) =
      ∑ k ∈ p.support, p.coeff k * (realDiracDerivative k g / (k.factorial : ℂ)) := by
    rw [he, hΦ]
    simp only [hcf]
  refine ⟨e, fun k f ↦ ?_, fun p N ↦ ⟨fun hord ↦ ?_, fun hdeg K ↦ ?_⟩⟩
  · rw [he, hΦm, one_smul, hcf]
  · by_contra hlt
    push Not at hlt
    have hpd : p.coeff p.natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hlt)
    have hpd' : 0 < ‖p.coeff p.natDegree‖ := norm_pos_iff.mpr hpd
    let K0 : Compacts ℝ := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
    obtain ⟨C, hC0, hC⟩ := hord K0
    let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
    obtain ⟨G, hG⟩ := realSchwartzFlatQuotient_strongDual_exists_bump χ p.natDegree
    have hGc : HasCompactSupport (G : ℝ → ℂ) :=
      (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
        (realSchwartzFlatQuotient_strongDual_bump_tsupport χ le_rfl _ G hG)
    let A : ℝ := ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j G
    have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
    let ε : ℝ := min 1 (‖p.coeff p.natDegree‖ / (2 * (C * A + 1)))
    have hε : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hε2 : ε * (2 * (C * A + 1)) ≤ ‖p.coeff p.natDegree‖ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    obtain ⟨ψ, hψ⟩ := realSchwartzFlatQuotient_strongDual_exists_scaled G hGc p.natDegree ε hε.ne'
    have hψsupp : tsupport (ψ : ℝ → ℂ) ⊆ Metric.closedBall 0 1 := by
      refine closure_minimal (fun x hx ↦ ?_) Metric.isClosed_closedBall
      rw [mem_support, hψ] at hx
      have hGx : ε⁻¹ * x ∈ tsupport (G : ℝ → ℂ) := subset_tsupport _ (right_ne_zero_of_mul hx)
      have h := realSchwartzFlatQuotient_strongDual_bump_tsupport χ le_rfl _ G hG hGx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
        inv_mul_le_iff₀ hε] at h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      nlinarith
    have hψc : HasCompactSupport (ψ : ℝ → ℂ) :=
      (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _) hψsupp
    let φ : 𝒟ℝ := ⟨ψ, ψ.smooth ⊤, hψc, by simp⟩
    have hφ : φ.hasCompactSupport.toSchwartzMap φ.contDiff = ψ := by ext x; rfl
    have hbound := hC φ hψsupp (ε * A) (by positivity) fun j hj x ↦ by
      change ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) x‖ ≤ ε * A
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 := SchwartzMap.le_seminorm' ℂ 0 j ψ x
      rw [pow_zero, one_mul] at h1
      have h2 := realSchwartzFlatQuotient_strongDual_scaled_seminorm χ le_rfl p.natDegree j 0
        (by omega) G ψ hG ε hε hε1 hψ
      have h3 : SchwartzMap.seminorm ℂ 0 j G ≤ A :=
        Finset.single_le_sum (f := fun j ↦ SchwartzMap.seminorm ℂ 0 j G)
          (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
      calc ‖iteratedDeriv j (ψ : ℝ → ℂ) x‖ ≤ SchwartzMap.seminorm ℂ 0 j ψ := h1
        _ ≤ ε * SchwartzMap.seminorm ℂ 0 j G := h2
        _ ≤ ε * A := by gcongr
    simp only at hbound
    rw [hφ, hev] at hbound
    have hsum : ∑ k ∈ p.support, p.coeff k * (realDiracDerivative k ψ / (k.factorial : ℂ)) =
        p.coeff p.natDegree * (-1 : ℂ) ^ p.natDegree := by
      rw [Finset.sum_eq_single p.natDegree]
      · rw [realSchwartzFlatQuotient_strongDual_scaled_dirac χ _ G ψ hG ε hε hψ]
        simp only [↓reduceIte]
        rw [mul_div_assoc, div_self (hfact _), mul_one]
      · intro k _ hk
        rw [realSchwartzFlatQuotient_strongDual_scaled_dirac χ _ G ψ hG ε hε hψ]
        simp [hk]
      · intro h
        exact absurd (Polynomial.mem_support_iff.mpr hpd) h
    rw [hsum, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one] at hbound
    have hCA : 0 ≤ C * (ε * A) := by positivity
    nlinarith
  · refine ⟨∑ k ∈ p.support, ‖p.coeff k‖, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _,
      fun f _ B _ hf ↦ ?_⟩
    beta_reduce
    rw [hev, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
    have hkN : k ≤ N := (Polynomial.le_natDegree_of_mem_supp k hk).trans hdeg
    have hB := hf k hkN 0
    change ‖iteratedFDeriv ℝ k (f.hasCompactSupport.toSchwartzMap f.contDiff : ℝ → ℂ) 0‖ ≤ B
      at hB
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hB
    have hf1 : (1 : ℝ) ≤ k.factorial := mod_cast k.factorial_pos
    rw [norm_mul, norm_div, realSchwartzFlatQuotient_strongDual_dirac, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    gcongr
    exact (div_le_self (norm_nonneg _) hf1).trans hB

end RealOrigin

section CoordinatePlane

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "Eᵣ(" ι ")" => EuclideanSpace ℝ ι
local notation "𝒟(" ι ")" => 𝓓((⊤ : TopologicalSpace.Opens Eᵣ(ι)), ℂ)
local notation "𝒮(" ι ")" => 𝓢(Eᵣ(ι), ℂ)
local notation "𝒟'(" ι ")" => StrongDual ℂ 𝒟(ι)
local notation "𝒮'(" ι ")" => StrongDual ℂ 𝒮(ι)

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
The coordinate derivative for a multi-index acts by the indicated number of derivatives
in each coordinate. The factors can be ordered arbitrarily on smooth tests. -/
def coordinateDerivative {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (α : ι → ℕ) : A :=
  ((Finset.univ.toList : List ι).map (fun i ↦ derivative i ^ α i)).prod

/-- The coordinate derivative of the zero multi-index is the identity. -/
theorem coordinateDerivative_zero {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A) :
    coordinateDerivative derivative (0 : ι → ℕ) = 1 := by
  simp [coordinateDerivative]

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
A multi-index supported in one coordinate acts by the corresponding power
of that coordinate's derivative. -/
theorem coordinateDerivative_single {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (i : ι) (k : ℕ) :
    coordinateDerivative derivative (Pi.single i k) = derivative i ^ k := by
  have key : ∀ l : List ι, l.Nodup →
      (l.map fun j ↦ derivative j ^ (Pi.single i k : ι → ℕ) j).prod =
        if i ∈ l then derivative i ^ k else 1 := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.nodup_cons] at hl
      by_cases h : a = i
      · subst h
        simp [hl.1, ih hl.2]
      · rw [List.map_cons, List.prod_cons, ih hl.2, Pi.single_apply, if_neg h,
          pow_zero, one_mul]
        simp [Ne.symm h]
  unfold coordinateDerivative
  rw [key _ (Finset.nodup_toList _)]
  simp

open Classical in
local notation "eᵣ" i => WithLp.toLp 2 (Pi.single i (1 : ℝ))

local notation "∂𝒟[" I ", " α "]" =>
  coordinateDerivative
    (fun i : I ↦ (LineDeriv.lineDerivOpCLM ℂ 𝒟(I) (eᵣ i : Eᵣ(I)) : 𝒟(I) →L[ℂ] 𝒟(I))) α
local notation "∂𝒮[" I ", " α "]" =>
  coordinateDerivative
    (fun i : I ↦ (LineDeriv.lineDerivOpCLM ℂ 𝒮(I) (eᵣ i : Eᵣ(I)) : 𝒮(I) →L[ℂ] 𝒮(I))) α

local notation "insertPlane" y =>
  WithLp.toLp 2 (Sum.elim (fun _ ↦ (0 : ℝ)) (fun j ↦ y j))

/-- Precomposition with a closed-embedding continuous linear map of norm at most one is a
continuous linear map between spaces of test functions. -/
private theorem exists_testFunction_coordinatePlaneRestriction_comp {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : E' →L[ℝ] E) (hg : IsClosedEmbedding g) (hn : ‖g‖ ≤ 1) :
    ∃ R : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ) →L[ℂ] 𝓓((⊤ : TopologicalSpace.Opens E'), ℂ),
      ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ)) (y : E'), R f y = f (g y) := by
  have hloc (K : TopologicalSpace.Compacts E) :
      ∃ M : ContDiffMapSupportedIn E ℂ ⊤ K →L[ℂ]
          ContDiffMapSupportedIn E' ℂ ⊤ ⟨g ⁻¹' K, hg.isCompact_preimage K.isCompact⟩,
        ∀ f y, M f y = f (g y) := by
    let M : ContDiffMapSupportedIn E ℂ ⊤ K →ₗ[ℂ]
        ContDiffMapSupportedIn E' ℂ ⊤ ⟨g ⁻¹' K, hg.isCompact_preimage K.isCompact⟩ :=
      { toFun := fun f ↦ ContDiffMapSupportedIn.of_support_subset
          (f.contDiff.comp g.contDiff) (fun _ hy ↦ f.support_subset hy)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine ⟨⟨M, WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ _ _)
      (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ _ _) _
      (Seminorm.IsBounded.of_real fun i ↦ ⟨{i}, 1, fun f ↦ ?_⟩)⟩, fun _ _ ↦ rfl⟩
    rw [Finset.sup_singleton, one_mul]
    refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg _ _) i _).mpr
      fun y _ ↦ ?_
    change ‖iteratedFDeriv ℝ i (⇑f ∘ g) y‖ ≤ _
    rw [g.iteratedFDeriv_comp_right f.contDiff y (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i f (g y)‖ * 1 := by
          gcongr
          exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hn
      _ ≤ _ := by
          rw [mul_one]
          exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
  let L : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ) →ₗ[ℂ] 𝓓((⊤ : TopologicalSpace.Opens E'), ℂ) :=
    { toFun := fun f ↦ ⟨f ∘ g, f.contDiff.comp g.contDiff,
        f.hasCompactSupport.comp_isClosedEmbedding hg, fun _ _ ↦ trivial⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL : Continuous L := by
    refine (TestFunction.continuous_iff_continuous_comp L).mpr fun K hK ↦ ?_
    obtain ⟨M, hM⟩ := hloc K
    have h : L ∘ TestFunction.ofSupportedIn hK =
        TestFunction.ofSupportedIn (fun _ _ ↦ trivial) ∘ M :=
      funext fun f ↦ TestFunction.ext fun y ↦ (hM f y).symm
    rw [h]
    exact (TestFunction.continuous_ofSupportedIn _).comp M.continuous
  exact ⟨⟨L, hL⟩, fun _ _ ↦ rfl⟩

/-- Inserting zeros into the normal coordinates is a continuous linear map of norm at most one
whose norm is preserved, hence a closed embedding. -/
private theorem exists_coordinatePlaneRestriction_inclusion :
    ∃ g : Eᵣ(κ) →L[ℝ] Eᵣ(ι ⊕ κ), (∀ y : Eᵣ(κ), g y = insertPlane y) ∧
      IsClosedEmbedding g ∧ ‖g‖ ≤ 1 ∧ ∀ y, ‖g y‖ = ‖y‖ := by
  let g : Eᵣ(κ) →L[ℝ] Eᵣ(ι ⊕ κ) := LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ insertPlane y
      map_add' := fun y y' ↦ by ext i; cases i <;> simp
      map_smul' := fun c y ↦ by ext i; cases i <;> simp }
  have hnorm (y : Eᵣ(κ)) : ‖g y‖ = ‖y‖ := by
    simp [g, EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  exact ⟨g, fun _ ↦ rfl, (AddMonoidHomClass.isometry_of_norm _ hnorm).isClosedEmbedding,
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by rw [hnorm, one_mul], hnorm⟩

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on compactly supported smooth functions. -/
theorem exists_testFunction_coordinatePlaneRestriction :
    ∃ R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ), ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by
  obtain ⟨g, hg, hce, hn, -⟩ := exists_coordinatePlaneRestriction_inclusion (ι := ι) (κ := κ)
  obtain ⟨R, hR⟩ := exists_testFunction_coordinatePlaneRestriction_comp g hce hn
  exact ⟨R, fun f y ↦ (hR f y).trans (congrArg f (hg y))⟩

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on Schwartz functions. -/
theorem exists_schwartz_coordinatePlaneRestriction :
    ∃ R : 𝒮(ι ⊕ κ) →L[ℂ] 𝒮(κ), ∀ (f : 𝒮(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by
  obtain ⟨g, hg, -, -, hnorm⟩ := exists_coordinatePlaneRestriction_inclusion (ι := ι) (κ := κ)
  have hA : AntilipschitzWith 1 g := AntilipschitzWith.of_le_mul_dist fun y y' ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, NNReal.coe_one, one_mul]
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ g.hasTemperateGrowth hA,
    fun f y ↦ congrArg f (hg y)⟩

local notation "R𝒟" => (exists_testFunction_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose
local notation "R𝒮" => (exists_schwartz_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose
local notation "weight(" α ")" => (∑ i, α i)
local notation "index(" N ")" =>
  {α : (ι ⊕ κ) → Fin (N + 1) // (∑ i, (α i : ℕ)) ≤ N}
local notation "multi(" α ")" => (fun i ↦ ((((α).val) i).val : ℕ))
local notation "normal(" α ")" => (fun i : ι ↦ multi(α) (Sum.inl i))
local notation "tangent(" α ")" => (fun i : κ ↦ multi(α) (Sum.inr i))
local notation "factors(" f ", " g ", " x ")" =>
  f (WithLp.toLp 2 (fun i : ι ↦ x (.inl i))) * g (WithLp.toLp 2 (fun j : κ ↦ x (.inr j)))

-- TODO(paper-gap): The count N^m in (2) disagrees with the sum in (5.3.2.4).
-- In (2)–(5) the coefficient orders must be upper bounds. The distributional transpose
-- also introduces the factor (-1)^|α| in (5.3.2.5) and (5.3.2.6).

open Classical in
/-- Paper: Theorem 5.3.2.3(2), p. 245.
A compactly supported distribution of order at most N supported on a coordinate plane is a sum
of transposed restrictions of derivatives. Each coefficient has compact support and its order
is bounded by N minus the derivative degree.
Deviation: The finite indices are exactly those in (5.3.2.4). Orders are upper bounds. -/
theorem distribution_coordinatePlane_decomposition [Nonempty ι] (T : 𝒟'(ι ⊕ κ)) (N : ℕ)
    (hT : DistributionOrderLE T N)
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hplane : Distribution.dsupport (⇑T) ⊆
      Set.range (fun y : Eᵣ(κ) ↦ (insertPlane y : Eᵣ(ι ⊕ κ)))) :
    ∃ A : index(N) → 𝒟'(κ),
      (∀ α, DistributionOrderLE (A α) (N - weight(multi(α))) ∧
        IsCompact (Distribution.dsupport (⇑(A α)))) ∧
      ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f)) := by sorry

open Classical in
/-- Paper: Theorem 5.3.2.3(3), p. 245.
On a pure tensor, the summand factors as the normal derivative evaluated at zero and the
tangential coefficient applied to the derivative of the tangential test.
Deviation: This is the test-function derivative form of (5.3.2.5), with the transpose signs
canceled. Using distributional derivatives in both factors requires a sign of (-1)^|α|. -/
theorem distribution_coordinatePlane_decomposition_apply_tmul {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f)))
    (f : 𝒟(ι ⊕ κ)) (g : 𝒟(ι)) (h : 𝒟(κ))
    (hf : ∀ x : Eᵣ(ι ⊕ κ), f x = factors(g, h, x)) :
    T f = ∑ α : index(N), (∂𝒟[ι, normal(α)] g) 0 * A α (∂𝒟[κ, tangent(α)] h) := by sorry

private theorem coordinateDerivative_split_sum {M : Type*} [Monoid M] (D : (ι ⊕ κ) → M)
    (hc : ∀ i j, Commute (D i) (D j)) (a : (ι ⊕ κ) → ℕ) :
    coordinateDerivative D a =
      coordinateDerivative (D ∘ Sum.inr) (a ∘ Sum.inr) *
        coordinateDerivative (D ∘ Sum.inl) (a ∘ Sum.inl) := by
  classical
  let l := (Finset.univ : Finset (ι ⊕ κ)).toList
  let r := (Finset.univ : Finset κ).toList
  let s := (Finset.univ : Finset ι).toList
  have hp : l.Perm (r.map Sum.inr ++ s.map Sum.inl) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) _).2
    · intro i; cases i <;> simp [r, s]
    · apply List.nodup_append'.2
      refine ⟨(Finset.nodup_toList _).map Sum.inr_injective,
        (Finset.nodup_toList _).map Sum.inl_injective, ?_⟩
      apply List.disjoint_left.mpr
      rintro _ h₁ h₂
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp h₁
      simp at h₂
  have h := (hp.map (fun i ↦ D i ^ a i)).prod_eq' (List.pairwise_map.mpr
    (List.pairwise_of_forall_mem_list (fun i _ j _ ↦ (hc i j).pow_pow _ _)))
  simpa [coordinateDerivative, l, r, s, List.map_append, List.map_map, Function.comp_def] using h

private theorem coordinateDerivative_line_commute (v w : Eᵣ(ι)) :
    Commute (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) v : 𝒟(ι) →L[ℂ] 𝒟(ι))
      (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) w) := by
  have hd (u : Eᵣ(ι)) (g : 𝒟(ι)) :
      ⇑((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) u : 𝒟(ι) →L[ℂ] 𝒟(ι)) g) =
        fun y ↦ fderiv ℝ (⇑g) y u := by
    ext y
    rw [TestFunction.lineDerivOpCLM_eq_lineDerivCLM, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le g le_top]
  apply ContinuousLinearMap.ext
  intro f
  apply TestFunction.ext
  intro x
  simp only [mul_apply_eq_comp, hd]
  have hf : DifferentiableAt ℝ (fderiv ℝ ⇑f) x :=
    ((f.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero).differentiableAt
  simp only [fderiv_clm_apply hf (differentiableAt_const _), fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact f.contDiff.contDiffAt.isSymmSndFDerivAt (by simp) v w

open Classical in
private theorem coordinateDerivative_plane_line (R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ))
    (hR : ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)), R f y = f (insertPlane y))
    (j : κ) (f : 𝒟(ι ⊕ κ)) :
    R ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ (Sum.inr j) : Eᵣ(ι ⊕ κ)) :
        𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ)) f) =
      (LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) (eᵣ j : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ)) (R f) := by
  classical
  apply TestFunction.ext
  intro y
  simp only [hR, TestFunction.lineDerivOpCLM_eq_lineDerivCLM,
    TestFunction.lineDerivCLM_apply_of_le le_top, lineDeriv]
  congr 1
  funext t
  congr 1
  ext i
  cases i <;> simp

open Classical in
private theorem coordinateDerivative_plane_restrict (R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ))
    (hR : ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)), R f y = f (insertPlane y))
    (a : (ι ⊕ κ) → ℕ) (f : 𝒟(ι ⊕ κ)) :
    R (∂𝒟[ι ⊕ κ, a] f) = ∂𝒟[κ, a ∘ Sum.inr]
      (R (∂𝒟[ι ⊕ κ, Sum.elim (a ∘ Sum.inl) (0 : κ → ℕ)] f)) := by
  let D (i : ι ⊕ κ) := (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) :
    𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ))
  let d (j : κ) := (LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) (eᵣ j : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ))
  have hD (i j : ι ⊕ κ) : Commute (D i) (D j) := coordinateDerivative_line_commute _ _
  have hd (j : κ) : Semiconj R (D (.inr j)) (d j) := coordinateDerivative_plane_line R hR j
  have hprod (l : List κ) : Semiconj R
      ((l.map fun j ↦ D (.inr j) ^ a (.inr j)).prod : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ))
      ((l.map fun j ↦ d j ^ a (.inr j)).prod : 𝒟(κ) →L[ℂ] 𝒟(κ)) := by
    induction l with
    | nil => exact fun _ ↦ rfl
    | cons j l ih =>
      simpa only [List.map_cons, List.prod_cons, FunLike.coe_mul_eq_comp,
        FunLike.coe_pow_eq_iterate] using ((hd j).iterate_right (a (.inr j))).comp_right ih
  let b := Sum.elim (a ∘ Sum.inl) (0 : κ → ℕ)
  change R (coordinateDerivative D a f) = coordinateDerivative d _ (R (coordinateDerivative D b f))
  rw [coordinateDerivative_split_sum D hD a, coordinateDerivative_split_sum D hD b]
  rw [show b ∘ Sum.inr = 0 from rfl, coordinateDerivative_zero, one_mul, mul_apply_eq_comp]
  exact hprod _ _

open Classical in
/-- Paper: Theorem 5.3.2.3(4), p. 245.
Tensoring a normal Dirac derivative with a tangential distribution is the transposed normal
derivative of the restriction to the coordinate plane. -/
def coordinatePlaneDiracTensor (β : ι → ℕ) (U : 𝒟'(κ)) : 𝒟'(ι ⊕ κ) :=
  (-1 : ℂ)^weight(β) • U.comp ((R𝒟).comp ∂𝒟[ι ⊕ κ, Sum.elim β (0 : κ → ℕ)])

/-- Paper: Theorem 5.3.2.3(4), p. 245.
At derivative order zero the tensor restricts the test to the coordinate plane and applies
the tangential distribution. -/
theorem coordinatePlaneDiracTensor_zero (U : 𝒟'(κ)) (f : 𝒟(ι ⊕ κ)) :
    coordinatePlaneDiracTensor (0 : ι → ℕ) U f = U (R𝒟 f) := by
  have h0 : Sum.elim (0 : ι → ℕ) (0 : κ → ℕ) = 0 := by
    ext i; cases i <;> rfl
  simp [coordinatePlaneDiracTensor, h0, coordinateDerivative_zero]

open Classical in
/-- Paper: Theorem 5.3.2.3(4), p. 245.
The decomposition is a finite sum of tensor products of normal Dirac derivatives with
tangential distributional derivatives.
Deviation: Each tensor in (5.3.2.6) has the factor (-1)^|α| required by (5.3.2.4). -/
theorem distribution_coordinatePlane_decomposition_eq_sum {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f))) :
    T = ∑ α : index(N), (-1 : ℂ)^weight(multi(α)) •
      coordinatePlaneDiracTensor (normal(α))
        ((-1 : ℂ)^weight(tangent(α)) • (A α).comp ∂𝒟[κ, tangent(α)]) := by
  ext f
  rw [hA, sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  simp only [coordinatePlaneDiracTensor, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  rw [coordinateDerivative_plane_restrict R𝒟
    exists_testFunction_coordinatePlaneRestriction.choose_spec (multi(α)) f]
  rw [← mul_assoc ((-1 : ℂ)^weight(normal(α))) _ _, ← pow_add,
    ← Fintype.sum_sum_type (multi(α)), ← mul_assoc, ← mul_pow]
  simp [Function.comp_def]

open Classical in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
Passing from a compactly supported test to its Schwartz function commutes with all
coordinate derivatives. This also identifies derivatives of the tempered extensions. -/
theorem coordinateDerivative_testFunction_toSchwartz {ι : Type*} [Fintype ι]
    (β : ι → ℕ) (f : 𝒟(ι)) :
    let g := ∂𝒟[ι, β] f
    g.hasCompactSupport.toSchwartzMap g.contDiff =
      ∂𝒮[ι, β] (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
  intro g
  have hpow : ∀ i (k : ℕ) (f : 𝒟(ι)),
      ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) ^ k) f).hasCompactSupport.toSchwartzMap
          ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) ^ k) f).contDiff =
        (LineDeriv.lineDerivOpCLM ℂ 𝒮(ι) (eᵣ i : Eᵣ(ι)) ^ k)
          (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
    intro i k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      congr 1
  show (∂𝒟[ι, β] f).hasCompactSupport.toSchwartzMap (∂𝒟[ι, β] f).contDiff = _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l generalizing f with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [← ih, ← hpow]

/-- Paper: Theorem 5.3.2.3(5), p. 245.
A compactly supported distribution has a tempered extension. Cutting a Schwartz test off by a
test function that equals one on a neighbourhood of the distribution's support does not change
the value of the distribution, and the resulting functional is continuous on the Schwartz space. -/
private theorem distribution_coordinatePlane_decomposition_tempered_extension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : StrongDual ℂ 𝓓((⊤ : Opens E), ℂ))
    (hA : IsCompact (Distribution.dsupport (⇑A))) :
    ∃ B : StrongDual ℂ 𝓢(E, ℂ),
      ∀ g : 𝓓((⊤ : Opens E), ℂ), B (g.hasCompactSupport.toSchwartzMap g.contDiff) = A g := by
  sorry

/-- Restriction to the coordinate plane commutes with passing a compactly supported test to
its Schwartz function: both restrictions are given by inserting zeros in the normal
coordinates. -/
private theorem distribution_coordinatePlane_decomposition_tempered_restriction_toSchwartz
    (f : 𝒟(ι ⊕ κ)) :
    let g := R𝒟 f
    R𝒮 (f.hasCompactSupport.toSchwartzMap f.contDiff) =
      g.hasCompactSupport.toSchwartzMap g.contDiff := by
  intro g
  ext y
  rw [(exists_schwartz_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose_spec _ y]
  simp only [HasCompactSupport.toSchwartzMap_toFun]
  exact ((exists_testFunction_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose_spec f y).symm

open Classical in
/-- Passing from a compactly supported test on the product to its Schwartz function commutes
with coordinate derivatives, at the product type itself. -/
private theorem distribution_coordinatePlane_decomposition_tempered_toSchwartz
    (β : (ι ⊕ κ) → ℕ) (f : 𝒟(ι ⊕ κ)) :
    let g := ∂𝒟[ι ⊕ κ, β] f
    g.hasCompactSupport.toSchwartzMap g.contDiff =
      ∂𝒮[ι ⊕ κ, β] (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
  intro g
  have hpow : ∀ i (k : ℕ) (f : 𝒟(ι ⊕ κ)),
      ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) ^ k)
          f).hasCompactSupport.toSchwartzMap
          ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) ^ k) f).contDiff =
        (LineDeriv.lineDerivOpCLM ℂ 𝒮(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) ^ k)
          (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
    intro i k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      congr 1
  show (∂𝒟[ι ⊕ κ, β] f).hasCompactSupport.toSchwartzMap (∂𝒟[ι ⊕ κ, β] f).contDiff = _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List (ι ⊕ κ)) = l
  induction l generalizing f with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [← ih, ← hpow]

open Classical in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
The coefficient distributions and the ambient distribution have tempered extensions.
The identity holds for every Schwartz test after extension.
Deviation: The tempered identity uses the test-function derivative convention of (5.3.2.4),
equivalent to the signed tensor identity with distributional derivatives. -/
theorem distribution_coordinatePlane_decomposition_tempered {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hK : ∀ α, IsCompact (Distribution.dsupport (⇑(A α))))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f))) :
    ∃ (U : 𝒮'(ι ⊕ κ)) (B : index(N) → 𝒮'(κ)),
      (∀ f : 𝒟(ι ⊕ κ), U (f.hasCompactSupport.toSchwartzMap f.contDiff) = T f) ∧
      (∀ α, ∀ g : 𝒟(κ), B α (g.hasCompactSupport.toSchwartzMap g.contDiff) = A α g) ∧
      ∀ f : 𝒮(ι ⊕ κ), U f = ∑ α : index(N), B α (R𝒮 (∂𝒮[ι ⊕ κ, multi(α)] f)) := by
  choose B hB using fun α : index(N) =>
    distribution_coordinatePlane_decomposition_tempered_extension (A α) (hK α)
  refine ⟨∑ α : index(N), (B α).comp ((R𝒮).comp ∂𝒮[ι ⊕ κ, multi(α)]), B, ?_, fun α => hB α, ?_⟩
  · intro f
    simp only [sum_apply, ContinuousLinearMap.comp_apply]
    rw [hA f]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hder : ∂𝒮[ι ⊕ κ, multi(α)] (f.hasCompactSupport.toSchwartzMap f.contDiff) =
        (∂𝒟[ι ⊕ κ, multi(α)] f).hasCompactSupport.toSchwartzMap
          (∂𝒟[ι ⊕ κ, multi(α)] f).contDiff :=
      (distribution_coordinatePlane_decomposition_tempered_toSchwartz (multi(α)) f).symm
    rw [← hB α, ← distribution_coordinatePlane_decomposition_tempered_restriction_toSchwartz
      (∂𝒟[ι ⊕ κ, multi(α)] f), hder]
  · intro f
    simp only [sum_apply, ContinuousLinearMap.comp_apply]

/-- Paper: Remark 5.3.2.4, p. 246.
Products of test functions define a map from the inductive tensor product with
sequentially dense range. The completed inductive tensor product is isomorphic
to the test space on the product by the same pure tensor formula.
Deviation: The isomorphism uses the completion, as required for the full test space. -/
theorem testFunction_inductiveTensor_equiv :
    let W := InductiveTensor 𝒟(ι) 𝒟(κ)
    letI : ContinuousSMul ℂ W := WithSeminorms.continuousSMul (E := W)
      (withGeneratingSeminorms_spec _ _)
    letI : UniformContinuousConstSMul ℂ W := uniformContinuousConstSMul_of_continuousConstSMul ℂ W
    ∃ e : UniformSpace.Completion W ≃L[ℂ] 𝒟(ι ⊕ κ),
      (∀ (f : 𝒟(ι)) (g : 𝒟(κ)) (x : Eᵣ(ι ⊕ κ)),
        e (UniformSpace.Completion.coe' (α := W) (f ⊗ₜ[ℂ] g)) x = factors(f, g, x)) ∧
      ∀ h : 𝒟(ι ⊕ κ), ∃ s : ℕ → W,
        Tendsto (fun n ↦ e (s n : UniformSpace.Completion W))
          atTop (𝓝 h) := by sorry

/-- Iterated line derivatives are iterated derivatives along the line. -/
private theorem lineDerivPow_apply_eq_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℂ)) (y : E) (s : ℝ) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
        →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) φ) (y + s • v) =
      iteratedDeriv k (fun t : ℝ ↦ φ (y + t • v)) s := by
  induction k generalizing φ s with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, iteratedDeriv_succ', ih]
    congr 1
    funext t
    rw [TestFunction.lineDerivOpCLM_eq_lineDerivCLM]
    rw [TestFunction.lineDerivCLM_apply_of_le (𝕜 := ℂ) (n := ⊤) (k := ⊤) le_rfl, lineDeriv]
    have h : (fun u : ℝ ↦ φ (y + t • v + u • v)) = fun u ↦ (fun w : ℝ ↦ φ (y + w • v)) (u + t) := by
      funext u; congr 1; rw [add_smul, add_assoc, add_comm (u • v)]
    rw [h]
    exact (deriv_comp_add_const (f := fun w : ℝ ↦ φ (y + w • v)) (a := t)
        (x := 0)).trans (by rw [zero_add])

private theorem lineDerivPow_apply_eq_iteratedDeriv_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℂ)) (y : E) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
        →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) φ) y =
      iteratedDeriv k (fun t : ℝ ↦ φ (y + t • v)) 0 := by
  have h := lineDerivPow_apply_eq_iteratedDeriv v k φ y 0
  rwa [zero_smul, add_zero] at h

/-- `𝓓_K` is not normable: a zero neighbourhood of test functions only controls finitely many
derivatives on the unit ball, so some `∂ₑⁿ δ₀` is unbounded on it. -/
private theorem exists_lineDeriv_unbounded_on_nhds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e : E) (he : e ≠ 0)
    (U : Set 𝓓((⊤ : Opens E), ℂ)) (hU : U ∈ 𝓝 (0 : 𝓓((⊤ : Opens E), ℂ))) :
    ∃ n : ℕ, ∀ M : ℝ, ∃ g ∈ U,
      M ≤ ‖(((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) e : 𝓓((⊤ : Opens E), ℂ)
          →L[ℂ] 𝓓((⊤ : Opens E), ℂ))) ^ n) g 0‖ := by
  classical
  let K : Compacts E := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
  have hK : (K : Set E) ⊆ ((⊤ : Opens E) : Set E) := fun _ _ ↦ trivial
  let ιK : 𝓓_{K}(E, ℂ) →L[ℝ] 𝓓((⊤ : Opens E), ℂ) := TestFunction.ofSupportedInCLM ℝ hK
  have hU' : ιK ⁻¹' U ∈ 𝓝 (0 : 𝓓_{K}(E, ℂ)) := by
    apply ιK.continuous.continuousAt.preimage_mem_nhds
    rw [map_zero]; exact hU
  obtain ⟨s, r, hr, hsub⟩ :=
    ((ContDiffMapSupportedIn.withSeminorms' ℝ E ℂ ⊤ K).mem_nhds_iff 0 _).mp hU'
  set N := s.sup id
  have hmem : ∀ g : 𝓓_{K}(E, ℂ),
      (∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ r / 2) → ιK g ∈ U := by
    intro g hg
    apply hsub
    rw [Seminorm.mem_ball, sub_zero]
    refine lt_of_le_of_lt (Seminorm.finset_sup_apply_le (a := r / 2) (by positivity) fun j hj ↦ ?_)
      (by linarith)
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦ ?_
    rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (by positivity)]
    intro x _
    exact hg i ((Finset.mem_Iic.mp hi).trans (Finset.le_sup (f := id) hj)) x
  -- the profile `g₀ y = χ y * ⟪e, y⟫ ^ (N + 1)`
  let χ : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let ψ : E → ℂ := fun y ↦ ((χ y * (inner ℝ e y) ^ (N + 1) : ℝ) : ℂ)
  have hψ : ContDiff ℝ (∞) ψ :=
    Complex.ofRealCLM.contDiff.comp (χ.contDiff.mul ((contDiff_const.inner ℝ contDiff_id).pow _))
  have hψ0 : ∀ y : E, 1 ≤ ‖y‖ → ψ y = 0 := fun y hy ↦ by
    have : χ y = 0 := χ.zero_of_le_dist (by simpa using hy)
    simp [ψ, this]
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) 1) fun y hy ↦ by
      have h1 : ¬ ‖y‖ ≤ 1 := by simpa using hy
      exact hψ0 y (le_of_lt (not_le.mp h1))
  have hb : ∀ i : ℕ, ∃ C, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ C := fun i ↦
    Continuous.bounded_above_of_compact_support
      (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)) (hψc.iteratedFDeriv i)
  choose C hC using hb
  set B : ℝ := 1 + ∑ i ∈ Finset.range (N + 1), |C i| with hB
  have hB0 : 0 < B := by positivity
  have hCB : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ B := fun i hi y ↦ by
    refine (hC i y).trans ((le_abs_self _).trans ?_)
    have := Finset.single_le_sum (f := fun i ↦ |C i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    linarith
  -- its `(N+1)`-th derivative along `e` at `0`
  set d : ℂ := iteratedDeriv (N + 1) (fun t : ℝ ↦ ψ (t • e)) 0 with hd
  have hd0 : d ≠ 0 := by
    have hev : (fun t : ℝ ↦ ψ (t • e)) =ᶠ[𝓝 0]
        fun t : ℝ ↦ t ^ (N + 1) • ((‖e‖ ^ 2) ^ (N + 1) : ℂ) := by
      have hc : Tendsto (fun t : ℝ ↦ t • e) (𝓝 0) (𝓝 0) := by
        have := (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const e
        rwa [zero_smul] at this
      filter_upwards [hc.eventually (χ.eventuallyEq_one)] with t ht
      simp only [Pi.one_apply] at ht
      simp only [ψ, ht, one_mul, real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hd, hev.iteratedDeriv_eq, iteratedDeriv_smul_const (by fun_prop),
      iteratedDeriv_fun_pow_zero]
    have : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
    simp [this, Nat.factorial_ne_zero]
  refine ⟨N + 1, fun M ↦ ?_⟩
  -- scaled copies `a • g₀ (λ • y)`
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  set lam : ℝ := max 1 (M * B / (r / 2 * ‖d‖)) with hlam
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlam0 : 0 < lam := by linarith
  set a : ℝ := r / 2 / (B * lam ^ N) with ha
  have ha0 : 0 < a := by positivity
  let G : E → ℂ := fun y ↦ a • ψ (lam • y)
  have hψl : ContDiff ℝ (∞) (fun y : E ↦ ψ (lam • y)) := hψ.comp (contDiff_const_smul lam)
  have hG : ContDiff ℝ (∞) G := hψl.const_smul a
  have hGs : support G ⊆ (K : Set E) := by
    intro y hy
    by_contra hyK
    apply hy
    have h1 : 1 < ‖y‖ := by simpa [K] using hyK
    have : 1 ≤ ‖lam • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hlam0.le]; nlinarith
    simp [G, hψ0 _ this]
  let gK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hG hGs
  refine ⟨ιK gK, hmem gK fun i hi y ↦ ?_, ?_⟩
  · change ‖iteratedFDeriv ℝ i G y‖ ≤ r / 2
    rw [iteratedFDeriv_const_smul_apply' (f := fun y : E ↦ ψ (lam • y)) (hψl.contDiffAt.of_le
      (by exact_mod_cast le_top)), iteratedFDeriv_comp_const_smul lam (hψ.of_le
      (by exact_mod_cast le_top)), norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg ha0.le,
      Real.norm_of_nonneg hlam0.le]
    calc a * (lam ^ i * ‖iteratedFDeriv ℝ i ψ (lam • y)‖) ≤ a * (lam ^ N * B) := by
          gcongr
          exact hCB i hi _
      _ = r / 2 := by rw [ha]; field_simp
  · have hl : ContDiff ℝ (N + 1 : ℕ) (fun t : ℝ ↦ ψ (t • e)) :=
      (hψ.comp (contDiff_id.smul contDiff_const)).of_le (by exact_mod_cast le_top)
    have hfun : (fun t : ℝ ↦ (ιK gK) (0 + t • e)) =
        fun t : ℝ ↦ a • (fun s : ℝ ↦ ψ (s • e)) (lam * t) := by
      funext t
      change a • ψ (lam • (0 + t • e)) = a • ψ ((lam * t) • e)
      rw [zero_add, smul_smul]
    rw [lineDerivPow_apply_eq_iteratedDeriv_zero, hfun, iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_comp_const_smul hl lam]
    beta_reduce
    rw [mul_zero, ← hd, norm_smul, norm_smul, norm_pow,
      Real.norm_of_nonneg ha0.le, Real.norm_of_nonneg hlam0.le]
    have h1 : M * B / (r / 2 * ‖d‖) ≤ lam := le_max_right _ _
    have h2 : M * B ≤ lam * (r / 2 * ‖d‖) := (div_le_iff₀ (by positivity)).mp h1
    have h3 : a * (lam ^ (N + 1) * ‖d‖) = lam * (r / 2 * ‖d‖) / B := by
      rw [ha]; field_simp; ring
    rw [h3, le_div_iff₀ hB0]
    linarith


/-- Line derivatives preserve vanishing on an open set. -/
private theorem lineDerivPow_apply_eq_zero_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (O : Set E) (hO : IsOpen O) (φ : 𝓓((⊤ : Opens E), ℂ))
    (hφ : ∀ z ∈ O, φ z = 0) (k : ℕ) (z : E) (hz : z ∈ O) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
        →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) φ) z = 0 := by
  rw [lineDerivPow_apply_eq_iteratedDeriv_zero]
  have hc : Tendsto (fun t : ℝ ↦ z + t • v) (𝓝 0) (𝓝 z) := by
    have := ((tendsto_id (x := 𝓝 (0 : ℝ))).smul_const v).const_add z
    rwa [zero_smul, add_zero] at this
  have hev : (fun t : ℝ ↦ φ (z + t • v)) =ᶠ[𝓝 0] fun _ ↦ 0 :=
    (hc.eventually (hO.mem_nhds hz)).mono fun t ht ↦ hφ _ ht
  rw [hev.iteratedDeriv_eq]
  simp


/-- `h ↦ ∑ₖ (∂ᵥᵏ h)(pₖ)` is a continuous functional when `‖pₖ‖ ≥ k` (locally finite sum). -/
private theorem exists_finsum_lineDerivPow_CLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (p : ℕ → E) (hp : ∀ k : ℕ, (k : ℝ) ≤ ‖p k‖) :
    ∃ T : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] ℂ, ∀ h : 𝓓((⊤ : Opens E), ℂ),
      T h = ∑ᶠ k, (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
          →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) h) (p k) := by
  set D : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] 𝓓((⊤ : Opens E), ℂ) :=
    LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v with hD
  let Tk : ℕ → 𝓓((⊤ : Opens E), ℂ) →L[ℂ] ℂ := fun k ↦
    ((BoundedContinuousFunction.evalCLM ℂ (p k)).comp
      (TestFunction.toBoundedContinuousFunctionCLM ℂ)).comp (D ^ k)
  have hTk : ∀ k h, Tk k h = ((D ^ k) h) (p k) := fun _ _ ↦ rfl
  have hvan : ∀ (h : 𝓓((⊤ : Opens E), ℂ)) (R : ℝ), (∀ z, R < ‖z‖ → h z = 0) → ∀ k : ℕ, R < k →
      Tk k h = 0 := by
    intro h R hR k hk
    rw [hTk]
    exact lineDerivPow_apply_eq_zero_of_isOpen v {z | R < ‖z‖}
      (isOpen_lt continuous_const continuous_norm) h hR k (p k) (hk.trans_le (hp k))
  have hsum : ∀ (h : 𝓓((⊤ : Opens E), ℂ)) (R : ℝ), (∀ z, R < ‖z‖ → h z = 0) → ∀ m : ℕ, R < m →
      ∑ᶠ k, Tk k h = ∑ k ∈ Finset.range m, Tk k h := by
    intro h R hR m hm
    apply finsum_eq_sum_of_support_subset
    intro k hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hkm
    push Not at hkm
    exact hk (hvan h R hR k (hm.trans_le (by exact_mod_cast hkm)))
  have hbd : ∀ h : 𝓓((⊤ : Opens E), ℂ), ∃ R : ℝ, ∀ z, R < ‖z‖ → h z = 0 := by
    intro h
    obtain ⟨R, hR⟩ := h.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz ↦ image_eq_zero_of_notMem_tsupport fun hz' ↦ ?_⟩
    have := hR hz'
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hmax : ∀ (h : 𝓓((⊤ : Opens E), ℂ)) (R R' : ℝ), (∀ z, R < ‖z‖ → h z = 0) → R ≤ R' →
      ∀ z, R' < ‖z‖ → h z = 0 := fun h R R' hR hle z hz ↦ hR z (hle.trans_lt hz)
  let Tl : 𝓓((⊤ : Opens E), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ ∑ᶠ k, Tk k h
      map_add' := fun h₁ h₂ ↦ by
        obtain ⟨R₁, h1⟩ := hbd h₁
        obtain ⟨R₂, h2⟩ := hbd h₂
        obtain ⟨m, hm⟩ := exists_nat_gt (max R₁ R₂)
        have h1' := hmax h₁ R₁ (max R₁ R₂) h1 (le_max_left _ _)
        have h2' := hmax h₂ R₂ (max R₁ R₂) h2 (le_max_right _ _)
        have h12 : ∀ z, max R₁ R₂ < ‖z‖ → (h₁ + h₂) z = 0 := fun z hz ↦ by
          rw [IsAddApply.add_apply, h1' z hz, h2' z hz, add_zero]
        rw [hsum _ _ h12 m hm, hsum _ _ h1' m hm, hsum _ _ h2' m hm, ← Finset.sum_add_distrib]
        simp only [map_add]
      map_smul' := fun a h ↦ by
        obtain ⟨R, hR⟩ := hbd h
        obtain ⟨m, hm⟩ := exists_nat_gt R
        have haR : ∀ z, R < ‖z‖ → (a • h) z = 0 := fun z hz ↦ by
          rw [IsSMulApply.smul_apply, hR z hz, smul_zero]
        rw [hsum _ _ haR m hm, hsum h R hR m hm, RingHom.id_apply, Finset.smul_sum]
        simp only [map_smul] }
  have hcont : Continuous Tl := by
    refine (TestFunction.continuous_iff_continuous_comp Tl).mpr fun K hK ↦ ?_
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨m, hm⟩ := exists_nat_gt R
    have hK' : ∀ φ : 𝓓_{K}(E, ℂ), ∀ z, R < ‖z‖ → (TestFunction.ofSupportedIn hK φ) z = 0 := by
      intro φ z hz
      have hzK : z ∉ (K : Set E) := fun hzK ↦ by
        have := hR hzK
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      exact φ.zero_on_compl hzK
    have heq : (Tl ∘ TestFunction.ofSupportedIn hK) =
        fun φ ↦ ∑ k ∈ Finset.range m, Tk k (TestFunction.ofSupportedIn hK φ) :=
      funext fun φ ↦ hsum _ R (hK' φ) m hm
    rw [heq]
    exact continuous_finsetSum _ fun k _ ↦
      (Tk k).continuous.comp (TestFunction.continuous_ofSupportedIn hK)
  exact ⟨⟨Tl, hcont⟩, fun h ↦ rfl⟩

/-- A smooth bump equal to `1` at `x` and vanishing off the ball of radius `1/2`. -/
private theorem exists_bump_testFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) :
    ∃ f : 𝓓((⊤ : Opens E), ℂ), f x = 1 ∧ ∀ y, 1 / 2 ≤ dist y x → f y = 0 := by
  let b : ContDiffBump x := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨⟨fun y ↦ ((b y : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, by simp⟩, ?_, fun y hy ↦ ?_⟩
  · change ((b x : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num)), Complex.ofReal_one]
  · change ((b y : ℝ) : ℂ) = 0
    rw [b.zero_of_le_dist hy, Complex.ofReal_zero]

/-- Pure tensors are jointly continuous at zero for the projective topology (copy of the private
`continuousAt_projectiveTensor_tmul_zero` of AppC Sec2a_part2). -/
private theorem continuousAt_projectiveTensor_tmul_zero' (X Y : Type*)
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] :
    @ContinuousAt (X × Y) (ProjectiveTensor X Y) _ _ (fun v ↦ v.1 ⊗ₜ[ℂ] v.2) 0 := by
  let tmul : X × Y → ProjectiveTensor X Y := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
  have hzero : tmul 0 = 0 := TensorProduct.zero_tmul _ _
  have hws : WithSeminorms (E := ProjectiveTensor X Y) (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val) := ⟨rfl⟩
  change Tendsto tmul (𝓝 0) (𝓝 (tmul 0))
  rw [hzero, (SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp hws, tendsto_iInf]
  intro p
  rw [tendsto_comap_iff]
  have hp := p.property.tendsto
  change Tendsto (p.val ∘ tmul) (𝓝 0) (𝓝 (p.val (tmul 0))) at hp
  rwa [hzero, show p.val (0 : ProjectiveTensor X Y) = 0 from map_zero p.val] at hp

/-- Soft part: a continuous `L` out of the projective tensor product, a functional `T` and
"coefficient" maps `lam n` with `T (L ((c • fₙ) ⊗ g)) = c * lam n g` cannot coexist if every zero
neighbourhood of `Y` leaves some `lam n` unbounded. -/
private theorem false_of_projectiveTensor_unbounded {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [Module ℝ X] [ContinuousSMul ℝ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (L : ProjectiveTensor X Y →L[ℂ] Z) (T : Z →L[ℂ] ℂ) (lam : ℕ → Y → ℂ)
    (hT : ∀ n : ℕ, ∃ f : X, ∀ (c : ℝ) (g : Y), T (L ((c • f) ⊗ₜ[ℂ] g)) = c * lam n g)
    (hY : ∀ U ∈ 𝓝 (0 : Y), ∃ n : ℕ, ∀ M : ℝ, ∃ g ∈ U, M ≤ ‖lam n g‖) : False := by
  have hβ : ContinuousAt (fun v : X × Y ↦ T (L (v.1 ⊗ₜ[ℂ] v.2))) 0 :=
    (T.continuous.comp L.continuous).continuousAt.comp
      (continuousAt_projectiveTensor_tmul_zero' X Y)
  have hmem : {v : X × Y | ‖T (L (v.1 ⊗ₜ[ℂ] v.2))‖ < 1} ∈ 𝓝 ((0 : X), (0 : Y)) := by
    refine hβ.preimage_mem_nhds (t := {w : ℂ | ‖w‖ < 1}) ?_
    have hz : ((0 : X) ⊗ₜ[ℂ] (0 : Y) : ProjectiveTensor X Y) = (0 : ProjectiveTensor X Y) :=
      TensorProduct.zero_tmul _ _
    have hL0 : L (0 : ProjectiveTensor X Y) = 0 := map_zero L
    have h0 : T (L ((0 : X × Y).1 ⊗ₜ[ℂ] (0 : X × Y).2)) = 0 := by
      change T (L ((0 : X) ⊗ₜ[ℂ] (0 : Y))) = 0
      rw [hz, hL0, map_zero]
    rw [h0]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨n, hn⟩ := hY U₂ hU₂
  obtain ⟨f, hf⟩ := hT n
  have hcont : Continuous (fun c : ℝ ↦ c • f) := continuous_id.smul continuous_const
  have hsmul : Tendsto (fun c : ℝ ↦ c • f) (𝓝 0) (𝓝 0) := by
    have h := hcont.tendsto 0
    rwa [zero_smul] at h
  obtain ⟨c, hcU, hc⟩ := ((hsmul.eventually hU₁).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hc0 : (0 : ℝ) < c := hc
  obtain ⟨g, hgU, hg⟩ := hn (1 / c)
  have hlt : ‖T (L ((c • f) ⊗ₜ[ℂ] g))‖ < 1 := hsub (Set.mk_mem_prod hcU hgU)
  rw [hf c g, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at hlt
  have := (div_le_iff₀' hc0).mp hg
  linarith

/-- Normal-direction-free product rule: differentiating a product in a tangential direction. -/
private theorem lineDerivPow_factors [DecidableEq ι] [DecidableEq κ] (j₀ : κ) (f : 𝒟(ι)) (g : 𝒟(κ))
    (h : 𝒟(ι ⊕ κ))
    (hh : ∀ z, h z = factors(f, g, z)) (k : ℕ) (z : Eᵣ(ι ⊕ κ)) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (EuclideanSpace.single (Sum.inr j₀ : ι ⊕ κ) (1 : ℝ)) :
      𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ)) ^ k) h) z =
      factors(f, ((LineDeriv.lineDerivOpCLM ℂ 𝒟(κ)
          (EuclideanSpace.single j₀ (1 : ℝ) : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ)) ^ k) g, z) := by
  rw [lineDerivPow_apply_eq_iteratedDeriv_zero, lineDerivPow_apply_eq_iteratedDeriv_zero]
  have hfun : (fun t : ℝ ↦ h (z + t • EuclideanSpace.single (Sum.inr j₀ : ι ⊕ κ) (1 : ℝ))) =
      fun t : ℝ ↦ f (WithLp.toLp 2 (fun i : ι ↦ z (Sum.inl i))) *
        g (WithLp.toLp 2 (fun j : κ ↦ z (Sum.inr j)) + t • EuclideanSpace.single j₀ (1 : ℝ)) := by
    funext t
    rw [hh]
    congr 2
    · ext i; simp
    · ext j; simp [PiLp.single_apply]
  rw [hfun, iteratedDeriv_const_mul_field]


/-- An infinite-order distribution `T = ∑ₙ δ_{(xₙ, 0)} ∘ ∂_{(0,e)}ⁿ` (locally finite, `xₙ → ∞`), and
bumps `fₙ` with `fₙ (x_k) = δ_{kn}`: on products `(c • fₙ) ⊗ g` it gives `c * (∂ₑⁿ g) 0`. -/
private theorem exists_infiniteOrder_functional [Nonempty ι] [Nonempty κ] :
    ∃ (T : 𝒟(ι ⊕ κ) →L[ℂ] ℂ) (e : Eᵣ(κ)), e ≠ 0 ∧ ∀ n : ℕ, ∃ f : 𝒟(ι),
      ∀ (c : ℝ) (g : 𝒟(κ)) (h : 𝒟(ι ⊕ κ)), (∀ z, h z = factors(c • f, g, z)) →
        T h = c * ((LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) (e : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ)) ^ n) g 0 := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  let p : ℕ → Eᵣ(ι ⊕ κ) := fun k ↦ EuclideanSpace.single (Sum.inl i₀) (k : ℝ)
  obtain ⟨T, hT⟩ := exists_finsum_lineDerivPow_CLM
    (EuclideanSpace.single (Sum.inr j₀ : ι ⊕ κ) (1 : ℝ)) p (fun k ↦ by simp [p])
  refine ⟨T, EuclideanSpace.single j₀ 1, by simp, fun n ↦ ?_⟩
  obtain ⟨f, hf1, hf0⟩ := exists_bump_testFunction (EuclideanSpace.single i₀ (n : ℝ) : Eᵣ(ι))
  refine ⟨f, fun c g h hh ↦ ?_⟩
  have e1 : ∀ k : ℕ, (WithLp.toLp 2 (fun i : ι ↦ p k (Sum.inl i)) : Eᵣ(ι)) =
      EuclideanSpace.single i₀ (k : ℝ) := fun k ↦ by
    ext i; simp [p, PiLp.single_apply]
  have e2 : ∀ k : ℕ, (WithLp.toLp 2 (fun j : κ ↦ p k (Sum.inr j)) : Eᵣ(κ)) = 0 := fun k ↦ by
    ext j; simp [p]
  rw [hT h, finsum_eq_single _ n]
  · rw [lineDerivPow_factors j₀ (c • f) g h hh n (p n), e1, e2, IsSMulApply.smul_apply, hf1]
    simp
  · intro k hk
    rw [lineDerivPow_factors j₀ (c • f) g h hh k (p k), e1, e2, IsSMulApply.smul_apply,
      hf0 _ ?_]
    · simp
    rw [EuclideanSpace.single, EuclideanSpace.single, PiLp.dist_single_same, Real.dist_eq]
    have : (1 : ℤ) ≤ |(k : ℤ) - n| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hk))
    have h' : (1 : ℝ) ≤ |(k : ℝ) - n| := by exact_mod_cast this
    linarith

-- TODO(paper-gap): If the tangential dimension is zero, its test space is ℂ
-- and the projective and inductive tensor products agree.

/-- Paper: Remark 5.3.2.4, p. 246.
In positive dimensions the product of test functions is not represented by a
continuous linear map out of the projective tensor product.
Deviation: The exception of a zero-dimensional factor is excluded explicitly. -/
theorem testFunction_no_projectiveTensor_product [Nonempty ι] [Nonempty κ] :
    ¬ ∃ L : ProjectiveTensor 𝒟(ι) 𝒟(κ) →L[ℂ] 𝒟(ι ⊕ κ),
      ∀ (f : 𝒟(ι)) (g : 𝒟(κ)) (x : Eᵣ(ι ⊕ κ)),
        L (f ⊗ₜ[ℂ] g) x = factors(f, g, x) := by
  rintro ⟨L, hL⟩
  obtain ⟨T, e, he, hT⟩ := exists_infiniteOrder_functional (ι := ι) (κ := κ)
  exact false_of_projectiveTensor_unbounded L T
    (fun n g ↦ (((LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) e : 𝒟(κ) →L[ℂ] 𝒟(κ)) ^ n) g) 0)
    (fun n ↦ (hT n).imp fun f hf c g ↦ hf c g _ (hL (c • f) g))
    (fun U hU ↦ exists_lineDeriv_unbounded_on_nhds e he U hU)

end CoordinatePlane

section ComplexOrigin

open scoped MvPowerSeries.WithPiTopology

local notation "𝒟ℂ" => 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)
local notation "∂x" => LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) (1 : ℂ)
local notation "∂y" => LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) Complex.I

/-- Paper: Theorem 5.3.2.5, p. 246.
The holomorphic Wirtinger operator on Schwartz functions is half of the real
directional derivative minus i times the imaginary directional derivative. -/
def schwartzWirtingerZ : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂x - Complex.I • ∂y)

/-- Paper: Theorem 5.3.2.5, p. 246.
The antiholomorphic Wirtinger operator on Schwartz functions is half of the real
directional derivative plus i times the imaginary directional derivative. -/
def schwartzWirtingerZBar : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂x + Complex.I • ∂y)

/-- Paper: Theorem 5.3.2.5, pp. 246–247.
The bundled Schwartz derivatives have the pointwise Wirtinger conventions of §3.3.2. -/
theorem schwartzWirtinger_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZ f z = wirtingerDeriv f z ∧
    schwartzWirtingerZBar f z = wirtingerConjDeriv f z := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a - b) = (a - b) / 2 ∧ (2 : ℂ)⁻¹ * (a + b) = (a + b) / 2
  constructor <;> ring

/-- Paper: Theorem 5.3.2.5, p. 246.
The sum of the Wirtinger derivatives recovers the real directional derivative. -/
theorem schwartzWirtingerZ_add_zBar (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZ f z + schwartzWirtingerZBar f z = fderiv ℝ (f : ℂ → ℂ) z 1 := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a - b) + (2 : ℂ)⁻¹ * (a + b) = a
  ring

/-- Paper: Theorem 5.3.2.5, p. 246.
The difference of the Wirtinger derivatives recovers the imaginary directional derivative
times i. -/
theorem schwartzWirtingerZBar_sub_z (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZBar f z - schwartzWirtingerZ f z =
      Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a + b) - (2 : ℂ)⁻¹ * (a - b) = b
  ring

/-- Paper: Theorem 5.3.2.5, p. 246.
A mixed Wirtinger derivative of the Dirac distribution at zero uses the negative transpose
of each Wirtinger differentiation on the test space. -/
def complexDiracDerivative (k l : ℕ) : StrongDual ℂ 𝓢(ℂ, ℂ) :=
  (-1 : ℂ)^(k + l) •
    (TemperedDistribution.delta (0 : ℂ)).comp
      ((schwartzWirtingerZ^k).comp (schwartzWirtingerZBar^l))

/-- Paper: Theorem 5.3.2.5, p. 246.
The first holomorphic derivative of the Dirac distribution is minus the test function's
holomorphic Wirtinger derivative at zero. -/
theorem complexDiracDerivative_one_zero (f : 𝓢(ℂ, ℂ)) :
    complexDiracDerivative 1 0 f = -schwartzWirtingerZ f 0 := by
  change (-1 : ℂ) ^ (1 + 0) • ((schwartzWirtingerZ ^ 1) ((schwartzWirtingerZBar ^ 0) f)) 0 = _
  simp

-- TODO(paper-gap): In (5.3.2.15)–(16) only the sum of tangential
-- derivatives for each normal index is determined. For a point support,
-- take both real coordinates normal in Theorem 5.3.2.3, then change basis.

section ComplexPointSupportHelpers


/-- The LF topology makes inclusion of smooth compactly supported tests into Schwartz space continuous. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_test_schwartz_map
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ J : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ →L[ℂ] SchwartzMap E ℂ,
      ∀ f x, J f x = f x := by
  let J : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ →ₗ[ℂ] SchwartzMap E ℂ :=
    { toFun := fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  have hc : Continuous J := by
    refine (TestFunction.continuous_iff_continuous_comp J).mpr fun K hK ↦ ?_
    have he : J ∘ TestFunction.ofSupportedIn hK = (supportedToSchwartzCLM ℂ K) := by
      funext f
      ext x
      rfl
    rw [he]
    exact (supportedToSchwartzCLM ℂ K).continuous
  exact ⟨⟨J, hc⟩, fun _ _ ↦ rfl⟩

private theorem complexTemperedDistribution_eq_sum_diracDerivative_complex_coordinates :
    Nonempty (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0) ≃L[ℝ] ℂ) := by
  let : Unique (EuclideanSpace ℝ (Fin 0)) := uniqueOfSubsingleton 0
  exact ⟨EuclideanSpace.sumEquivProd.trans
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 0))).trans
      Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv)⟩

private theorem complexTemperedDistribution_eq_sum_diracDerivative_support_schwartz_pull
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E ≃L[ℝ] ℂ) (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) :
    Distribution.dsupport (fun f : SchwartzMap E ℂ ↦ T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm f)) ⊆
      D ⁻¹' Distribution.dsupport (⇑T) := by
  intro x hx
  by_contra hn
  obtain ⟨U, hU, hOpen, hxU⟩ := (Distribution.notMem_dsupport_iff _).mp hn
  apply ((Distribution.notMem_dsupport_iff _).mpr ⟨D ⁻¹' U, ?_, hOpen.preimage D.continuous, hxU⟩) hx
  intro f hf
  apply hU
  intro y hy
  change y ∈ tsupport ((f : E → ℂ) ∘ D.symm.toHomeomorph) at hy
  rw [tsupport_comp_eq_preimage _ D.symm.toHomeomorph] at hy
  have hh := hf hy
  change D (D.symm y) ∈ U at hh
  simpa only [D.apply_symm_apply] using hh

private theorem complexTemperedDistribution_eq_sum_diracDerivative_support_test_restrict
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ →L[ℂ] SchwartzMap E ℂ)
    (hJ : ∀ f x, J f x = f x) (T : StrongDual ℂ (SchwartzMap E ℂ)) :
    Distribution.dsupport (fun f ↦ T (J f)) ⊆ Distribution.dsupport (⇑T) := by
  intro x hx
  by_contra hn
  obtain ⟨U, hU, hOpen, hxU⟩ := (Distribution.notMem_dsupport_iff _).mp hn
  apply ((Distribution.notMem_dsupport_iff _).mpr ⟨U, ?_, hOpen, hxU⟩) hx
  intro f hf
  apply hU
  have he : (J f : E → ℂ) = f := funext (hJ f)
  simpa only [he] using hf

/-- A finite Schwartz seminorm bound gives finite derivative order on each compact support. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_tempered_order_finite
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : StrongDual ℂ (SchwartzMap E ℂ)) :
    ∃ N : ℕ, DistributionOrderLE
      (fun f : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ ↦ T (f.hasCompactSupport.toSchwartzMap f.contDiff)) N := by
  let q : Seminorm ℂ (SchwartzMap E ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  let N := s.sup Prod.snd
  refine ⟨N, fun K ↦ ?_⟩
  obtain ⟨R, hR0, hR⟩ := K.isCompact.isBounded.exists_pos_norm_le
  refine ⟨(C : ℝ) * ∑ i ∈ s, R ^ i.1, by positivity, fun f hf B hB hderiv ↦ ?_⟩
  let φ := f.hasCompactSupport.toSchwartzMap f.contDiff
  have hsemi (i : ℕ × ℕ) (hi : i ∈ s) : SchwartzMap.seminorm ℂ i.1 i.2 φ ≤ R ^ i.1 * B := by
    apply SchwartzMap.seminorm_le_bound ℂ i.1 i.2 φ (by positivity)
    intro x
    change ‖x‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (f : E → ℂ) x‖ ≤ R ^ i.1 * B
    by_cases hx : x ∈ (K : Set E)
    · have hn : i.2 ≤ N := Finset.le_sup hi
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hR x hx) _) (hderiv i.2 hn x)
        (norm_nonneg _) (pow_nonneg hR0.le _)
    · have hx' : x ∉ tsupport (iteratedFDeriv ℝ i.2 (f : E → ℂ)) :=
        fun h ↦ hx (hf ((tsupport_iteratedFDeriv_subset i.2) h))
      rw [image_eq_zero_of_notMem_tsupport hx', norm_zero, mul_zero]
      positivity
  have ht := hb φ
  simp only [smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul] at ht
  change ‖T φ‖ ≤ (C : ℝ) * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 φ at ht
  calc
    ‖T φ‖ ≤ (C : ℝ) * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 φ := ht
    _ ≤ (C : ℝ) * ∑ i ∈ s, R ^ i.1 * B := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsemi) C.coe_nonneg
    _ = ((C : ℝ) * ∑ i ∈ s, R ^ i.1) * B := by rw [← Finset.sum_mul]; ring


private theorem complexTemperedDistribution_eq_sum_diracDerivative_point_coordinate_distribution
    (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) (hT : TemperedSupportedAtOrigin T) :
    ∃ (D : EuclideanSpace ℝ (Fin 2 ⊕ Fin 0) ≃L[ℝ] ℂ)
      (V : TestFunction (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0))) ℂ ⊤ →L[ℂ] ℂ)
      (N : ℕ), DistributionOrderLE V N ∧ Distribution.dsupport (⇑V) ⊆ {0} ∧
      ∀ f, V f = T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm (f.hasCompactSupport.toSchwartzMap f.contDiff)) := by
  let E := EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)
  obtain ⟨D⟩ := complexTemperedDistribution_eq_sum_diracDerivative_complex_coordinates
  obtain ⟨J, hJ⟩ := complexTemperedDistribution_eq_sum_diracDerivative_test_schwartz_map E
  let U : StrongDual ℂ (SchwartzMap E ℂ) := T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm)
  let V := U.comp J
  have hsU : Distribution.dsupport (⇑U) ⊆ {0} := by
    intro x hx
    have he := hT (complexTemperedDistribution_eq_sum_diracDerivative_support_schwartz_pull E D T hx)
    have hx0 : x = 0 := D.injective ((show D x = 0 from he).trans (map_zero D).symm)
    exact hx0
  have hsV : Distribution.dsupport (⇑V) ⊆ {0} :=
    (complexTemperedDistribution_eq_sum_diracDerivative_support_test_restrict E J hJ U).trans hsU
  have heJ (f) : J f = f.hasCompactSupport.toSchwartzMap f.contDiff := SchwartzMap.ext (hJ f)
  obtain ⟨N, hN⟩ := complexTemperedDistribution_eq_sum_diracDerivative_tempered_order_finite E U
  have hVN : DistributionOrderLE V N := by
    have he : (fun f ↦ V f) = (fun f ↦ U (f.hasCompactSupport.toSchwartzMap f.contDiff)) :=
      funext fun f ↦ congrArg U (heJ f)
    change DistributionOrderLE (fun f ↦ V f) N
    rw [he]
    exact hN
  refine ⟨D, V, N, hVN, hsV, fun f ↦ ?_⟩
  change U (J f) = _
  rw [heJ]
  rfl

private theorem complexTemperedDistribution_eq_sum_diracDerivative_zero_dim_dual
    (T : StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 0)) ℂ)) :
    ∃ c : ℂ, ∀ f, T f = c * f 0 := by
  let E := EuclideanSpace ℝ (Fin 0)
  let one : SchwartzMap E ℂ := (show HasCompactSupport (fun _ : E ↦ (1 : ℂ)) from
    (isClosed_tsupport _).isCompact).toSchwartzMap contDiff_const
  refine ⟨T one, fun f ↦ ?_⟩
  have he : f = (f 0) • one := by
    ext x
    change f x = f 0 * (1 : ℂ)
    rw [Subsingleton.elim x 0, mul_one]
  calc T f = T ((f 0) • one) := congrArg T he
       _ = f 0 * T one := T.map_smul _ _
       _ = T one * f 0 := mul_comm _ _

private theorem complexTemperedDistribution_eq_sum_diracDerivative_single_independent
    (d₁ d₂ : DecidableEq (Fin 2 ⊕ Fin 0)) (i : Fin 2 ⊕ Fin 0) (a : ℝ) :
    @Pi.single (Fin 2 ⊕ Fin 0) (fun _ ↦ ℝ) (fun _ ↦ inferInstance) d₁ i a =
      @Pi.single (Fin 2 ⊕ Fin 0) (fun _ ↦ ℝ) (fun _ ↦ inferInstance) d₂ i a :=
  congrArg (fun d ↦ @Pi.single (Fin 2 ⊕ Fin 0) (fun _ ↦ ℝ) (fun _ ↦ inferInstance) d i a) (Subsingleton.elim d₁ d₂)
open Classical in

/-- Take both real coordinates normal in the coordinate-plane decomposition, then use density. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_point_real_decomposition
    (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) (hT : TemperedSupportedAtOrigin T) :
    ∃ (D : EuclideanSpace ℝ (Fin 2 ⊕ Fin 0) ≃L[ℝ] ℂ) (N : ℕ)
      (c : {α : (Fin 2 ⊕ Fin 0) → Fin (N + 1) // (∑ i, (α i).val) ≤ N} → ℂ),
      ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)) ℂ,
        T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm f) =
          ∑ α, c α * (coordinateDerivative
            (fun i : Fin 2 ⊕ Fin 0 ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)) ℂ)
              (WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)) : _ →L[ℂ] _)) (fun i ↦ (α.val i).val) f) 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)
  obtain ⟨D, V, N, hVN, hsV, hVS⟩ := complexTemperedDistribution_eq_sum_diracDerivative_point_coordinate_distribution T hT
  have hK : IsCompact (Distribution.dsupport (⇑V)) :=
    isCompact_singleton.of_isClosed_subset Distribution.isClosed_dsupport hsV
  have hp : Distribution.dsupport (⇑V) ⊆ Set.range (fun y : EuclideanSpace ℝ (Fin 0) ↦
      (WithLp.toLp 2 (Sum.elim (fun _ : Fin 2 ↦ (0 : ℝ)) (fun j : Fin 0 ↦ y j)) : E)) := by
    intro x hx
    have he : x = 0 := hsV hx
    refine ⟨0, ?_⟩
    rw [he]
    ext i
    cases i <;> rfl
  obtain ⟨A, hA, heA⟩ := distribution_coordinatePlane_decomposition (ι := Fin 2) (κ := Fin 0) V N hVN hK hp
  obtain ⟨U, B, hU, hB, hrep⟩ := distribution_coordinatePlane_decomposition_tempered V A (fun α ↦ (hA α).2) heA
  let W : StrongDual ℂ (SchwartzMap E ℂ) := T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm)
  have heUW : U = W := by
    apply DFunLike.ext'
    apply Continuous.ext_on (SchwartzMap.dense_hasCompactSupport (E := E) (F := ℂ)) U.continuous W.continuous
    intro f hf
    let φ : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ := ⟨f, f.smooth ⊤, hf, by simp⟩
    have he : φ.hasCompactSupport.toSchwartzMap φ.contDiff = f := by ext; rfl
    have hu := hU φ
    rw [he] at hu
    exact hu.trans (hVS φ)
  have hz : (WithLp.toLp 2 (Sum.elim (fun _ : Fin 2 ↦ (0 : ℝ)) (fun j : Fin 0 ↦ (0 : EuclideanSpace ℝ (Fin 0)) j)) : E) = 0 := by
    ext i
    cases i <;> rfl
  have hr0 (φ : SchwartzMap E ℂ) :
      (exists_schwartz_coordinatePlaneRestriction (ι := Fin 2) (κ := Fin 0)).choose φ 0 = φ 0 := by
    have hr := (exists_schwartz_coordinatePlaneRestriction (ι := Fin 2) (κ := Fin 0)).choose_spec φ 0
    simpa only [hz] using hr
  choose c hc using fun α ↦ complexTemperedDistribution_eq_sum_diracDerivative_zero_dim_dual (B α)
  refine ⟨D, N, c, fun f ↦ ?_⟩
  change W f = _
  rw [← heUW]
  rw [hrep]
  refine Finset.sum_congr ?_ ?_
  · ext α
    simp
  · intro α hα
    rw [hc, hr0]
    congr 2
    apply congrArg (fun op : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ ↦ op f)
    apply congrArg (fun d ↦ coordinateDerivative d (fun i ↦ (α.val i).val))
    funext i
    apply congrArg (fun v : E ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap E ℂ) v : _ →L[ℂ] _))
    apply congrArg (WithLp.toLp 2)
    exact complexTemperedDistribution_eq_sum_diracDerivative_single_independent _ _ i (1 : ℝ)


private theorem complexTemperedDistribution_eq_sum_diracDerivative_partials_commute
    (v w : ℂ) :
    Commute (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _)
      (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) w : _ →L[ℂ] _) := by
  ext f x
  have hs : IsSymmSndFDerivAt ℝ (f : ℂ → ℂ) x :=
    (f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)
  calc
    _ = iteratedFDeriv ℝ 2 (f : ℂ → ℂ) x ![v, w] :=
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
    _ = iteratedFDeriv ℝ 2 (f : ℂ → ℂ) x ![w, v] := hs.iteratedFDeriv_cons
    _ = _ := SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm

private theorem complexTemperedDistribution_eq_sum_diracDerivative_wirtingers_commute : Commute schwartzWirtingerZ schwartzWirtingerZBar := by
  let X := (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (1 : ℂ) : _ →L[ℂ] _)
  let Y := (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) Complex.I : _ →L[ℂ] _)
  have hXY : Commute X (Complex.I • Y) := (complexTemperedDistribution_eq_sum_diracDerivative_partials_commute 1 Complex.I).smul_right Complex.I
  have hleft : Commute (X - Complex.I • Y) X := (Commute.refl X).sub_left hXY.symm
  have hright : Commute (X - Complex.I • Y) (Complex.I • Y) := hXY.sub_left (Commute.refl _)
  exact ((hleft.add_right hright).smul_left ((2 : ℂ)⁻¹)).smul_right ((2 : ℂ)⁻¹)

private theorem complexTemperedDistribution_eq_sum_diracDerivative_direction_wirtingers
    (v : ℂ) :
    (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _) =
      v • schwartzWirtingerZ + (star v) • schwartzWirtingerZBar := by
  ext f x
  change fderiv ℝ (f : ℂ → ℂ) x v = v * schwartzWirtingerZ f x + star v * schwartzWirtingerZBar f x
  rw [(schwartzWirtinger_apply f x).1, (schwartzWirtinger_apply f x).2]
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by simp [Complex.real_smul, Complex.re_add_im]
  have hm : fderiv ℝ (f : ℂ → ℂ) x v =
      (v.re : ℂ) * fderiv ℝ (f : ℂ → ℂ) x 1 + (v.im : ℂ) * fderiv ℝ (f : ℂ → ℂ) x Complex.I := by
    conv_lhs => rw [hv, map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  rw [hm]
  unfold wirtingerDeriv wirtingerConjDeriv
  conv_rhs => rw [← Complex.re_add_im v]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

/-- Commuting Wirtinger powers span every finite word of real directional derivatives. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_coordinate_operator_span
    (ι : Type*) [Fintype ι] (d : ι → ℂ) (α : ι → ℕ) :
    coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (d i) : _ →L[ℂ] _)) α ∈
      Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ schwartzWirtingerZ ^ p.1 * schwartzWirtingerZBar ^ p.2)) := by
  classical
  let A := schwartzWirtingerZ
  let B := schwartzWirtingerZBar
  let W := Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ A ^ p.1 * B ^ p.2))
  have hAB : Commute A B := complexTemperedDistribution_eq_sum_diracDerivative_wirtingers_commute
  have hA (q) (hq : q ∈ W) : A * q ∈ W := by
    refine Submodule.span_induction (p := fun q _ ↦ A * q ∈ W) ?_ ?_ ?_ ?_ hq
    · rintro q ⟨⟨k, l⟩, rfl⟩
      have he : A * (A ^ k * B ^ l) = A ^ (k + 1) * B ^ l := by rw [pow_succ']; simp only [mul_assoc]
      rw [he]
      exact Submodule.subset_span ⟨(k + 1, l), rfl⟩
    · simpa only [mul_zero] using W.zero_mem
    · intro q r _ _ hq hr
      simpa only [mul_add] using W.add_mem hq hr
    · intro c q _ hq
      simpa only [mul_smul_comm] using W.smul_mem c hq
  have hB (q) (hq : q ∈ W) : B * q ∈ W := by
    refine Submodule.span_induction (p := fun q _ ↦ B * q ∈ W) ?_ ?_ ?_ ?_ hq
    · rintro q ⟨⟨k, l⟩, rfl⟩
      have he : B * (A ^ k * B ^ l) = A ^ k * B ^ (l + 1) := by
        rw [← mul_assoc, (hAB.symm.pow_right k).eq, mul_assoc, ← pow_succ']
      rw [he]
      exact Submodule.subset_span ⟨(k, l + 1), rfl⟩
    · simpa only [mul_zero] using W.zero_mem
    · intro q r _ _ hq hr
      simpa only [mul_add] using W.add_mem hq hr
    · intro c q _ hq
      simpa only [mul_smul_comm] using W.smul_mem c hq
  have hv (v : ℂ) (q) (hq : q ∈ W) :
      (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _) * q ∈ W := by
    rw [complexTemperedDistribution_eq_sum_diracDerivative_direction_wirtingers, add_mul, smul_mul_assoc, smul_mul_assoc]
    exact W.add_mem (W.smul_mem v (hA q hq)) (W.smul_mem (star v) (hB q hq))
  have hpow (v : ℂ) (n : ℕ) (q) (hq : q ∈ W) :
      (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _) ^ n * q ∈ W := by
    induction n with
    | zero => simpa only [pow_zero, one_mul] using hq
    | succ n ih => rw [pow_succ', mul_assoc]; exact hv v _ ih
  have h1 : (1 : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ) ∈ W := by
    change A ^ 0 * B ^ 0 ∈ W
    exact Submodule.subset_span ⟨(0, 0), rfl⟩
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l with
  | nil => exact h1
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact hpow (d i) (α i) _ ih

private theorem complexTemperedDistribution_eq_sum_diracDerivative_coordinate_functional_span
    (ι : Type*) [Fintype ι] (d : ι → ℂ) (α : ι → ℕ) :
    (TemperedDistribution.delta (0 : ℂ)).comp
      (coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (d i) : _ →L[ℂ] _)) α) ∈
      Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ complexDiracDerivative p.1 p.2)) := by
  let A := schwartzWirtingerZ
  let B := schwartzWirtingerZBar
  let W := Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ A ^ p.1 * B ^ p.2))
  let S := Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ complexDiracDerivative p.1 p.2))
  let Φ : (SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ) →ₗ[ℂ] StrongDual ℂ (SchwartzMap ℂ ℂ) :=
    { toFun := fun op ↦ (TemperedDistribution.delta (0 : ℂ)).comp op
      map_add' := fun op op' ↦ by
        ext f
        change (TemperedDistribution.delta (0 : ℂ)) (op f + op' f) = _
        exact map_add (TemperedDistribution.delta (0 : ℂ)) _ _
      map_smul' := fun c op ↦ by
        ext f
        change (TemperedDistribution.delta (0 : ℂ)) (c • op f) = c • (TemperedDistribution.delta (0 : ℂ)) (op f)
        exact map_smul (TemperedDistribution.delta (0 : ℂ)) _ _ }
  have hgen (k l : ℕ) : Φ (A ^ k * B ^ l) = (-1 : ℂ) ^ (k + l) • complexDiracDerivative k l := by
    ext f
    change ((A ^ k) ((B ^ l) f)) 0 = (-1 : ℂ) ^ (k + l) * ((-1 : ℂ) ^ (k + l) * ((A ^ k) ((B ^ l) f)) 0)
    have hs : (-1 : ℂ) ^ (k + l) * (-1) ^ (k + l) = 1 := by rw [← mul_pow]; norm_num
    rw [← mul_assoc, hs, one_mul]
  have hmap (op) (hop : op ∈ W) : Φ op ∈ S := by
    refine Submodule.span_induction (p := fun op _ ↦ Φ op ∈ S) ?_ ?_ ?_ ?_ hop
    · rintro op ⟨⟨k, l⟩, rfl⟩
      rw [hgen]
      exact S.smul_mem _ (Submodule.subset_span ⟨(k, l), rfl⟩)
    · simpa only [map_zero] using S.zero_mem
    · intro q r _ _ hq hr
      simpa only [map_add] using S.add_mem hq hr
    · intro c q _ hq
      simpa only [map_smul] using S.smul_mem c hq
  exact hmap _ (complexTemperedDistribution_eq_sum_diracDerivative_coordinate_operator_span ι d α)

private theorem complexTemperedDistribution_eq_sum_diracDerivative_coordinate_pull
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ι : Type*) [Fintype ι] (D : E ≃L[ℝ] ℂ) (d : ι → E) (α : ι → ℕ)
    (f : SchwartzMap ℂ ℂ) :
    coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap E ℂ) (d i) : _ →L[ℂ] _)) α
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f) =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D
      (coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (D (d i)) : _ →L[ℂ] _)) α f) := by
  have hp (i : ι) (k : ℕ) (f : SchwartzMap ℂ ℂ) :
      ((LineDeriv.lineDerivOpCLM ℂ (SchwartzMap E ℂ) (d i) : _ →L[ℂ] _) ^ k)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D
        (((LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (D (d i)) : _ →L[ℂ] _) ^ k) f) := by
    induction k generalizing f with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih]
      exact SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℂ _ D _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [ih, hp]


private theorem complexTemperedDistribution_eq_sum_diracDerivative_point_complex_span
    (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) (hT : TemperedSupportedAtOrigin T) :
    T ∈ Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ complexDiracDerivative p.1 p.2)) := by
  classical
  obtain ⟨D, N, c, hrep⟩ := complexTemperedDistribution_eq_sum_diracDerivative_point_real_decomposition T hT
  let E := EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)
  let I := {α : (Fin 2 ⊕ Fin 0) → Fin (N + 1) // (∑ i, (α i).val) ≤ N}
  let d : Fin 2 ⊕ Fin 0 → E := fun i ↦ WithLp.toLp 2 (Pi.single i (1 : ℝ))
  let Q (α : I) := coordinateDerivative (fun i ↦
    (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (D (d i)) : _ →L[ℂ] _)) (fun i ↦ (α.val i).val)
  let V (α : I) := (TemperedDistribution.delta (0 : ℂ)).comp (Q α)
  have he : T = ∑ α : I, c α • V α := by
    ext f
    have hh := hrep (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f)
    have hi : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f) = f := by
      ext z
      change f (D (D.symm z)) = f z
      rw [D.apply_symm_apply]
    rw [hi] at hh
    rw [hh]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro α hα
    change c α * _ = c α * (Q α f) 0
    congr 1
    have hp := congrArg (fun φ : SchwartzMap E ℂ ↦ φ 0)
      (complexTemperedDistribution_eq_sum_diracDerivative_coordinate_pull E (Fin 2 ⊕ Fin 0) D d (fun i ↦ (α.val i).val) f)
    change _ = (Q α f) (D 0) at hp
    simpa only [map_zero] using hp
  rw [he]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  exact complexTemperedDistribution_eq_sum_diracDerivative_coordinate_functional_span (Fin 2 ⊕ Fin 0) (fun i ↦ D (d i)) (fun i ↦ (α.val i).val)
end ComplexPointSupportHelpers

/-- Paper: Theorem 5.3.2.5, p. 246.
Every complex tempered distribution supported at zero is a finite linear combination of
mixed Wirtinger derivatives of the Dirac distribution. -/
theorem complexTemperedDistribution_eq_sum_diracDerivative (T : StrongDual ℂ 𝓢(ℂ, ℂ))
    (hT : TemperedSupportedAtOrigin T) :
    ∃ (N : ℕ) (c : (k : Fin (N + 1)) → Fin (N + 1 - k.val) → ℂ),
      T = ∑ k : Fin (N + 1), ∑ l : Fin (N + 1 - k.val),
        c k l • complexDiracDerivative k.val l.val := by
  classical
  obtain ⟨a,ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (complexTemperedDistribution_eq_sum_diracDerivative_point_complex_span T hT)
  let N := a.support.sup (fun p ↦ p.1+p.2)
  let I := (k : Fin (N+1)) × Fin (N+1-k.val)
  let e : I ↪ ℕ × ℕ :=
    { toFun := fun u ↦ (u.1.val, u.2.val)
      inj' := by
        rintro ⟨k,l⟩ ⟨k',l'⟩ h
        have hk : k = k' := Fin.ext (congrArg Prod.fst h)
        subst k'
        congr
        exact Fin.ext (congrArg Prod.snd h) }
  have hs : a.support ⊆ Finset.univ.map e := by
    rintro ⟨k,l⟩ hp
    have hb : k+l ≤ N := Finset.le_sup (f := fun p : ℕ × ℕ ↦ p.1+p.2) hp
    let u : I := ⟨⟨k, by omega⟩, ⟨l, by change l < N+1-k; omega⟩⟩
    exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, rfl⟩
  refine ⟨N, fun k l ↦ a (k.val,l.val), ?_⟩
  rw [← ha, a.sum_of_support_subset hs _ (by intro p hp; simp), Finset.sum_map]
  exact Fintype.sum_sigma' (fun (k : Fin (N+1)) (l : Fin (N+1-k.val)) ↦ a (k.val,l.val) • complexDiracDerivative k.val l.val)

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The flat complex Schwartz subspace is the common kernel of the mixed Dirac derivatives. -/
def complexSchwartzFlatAtOrigin : Submodule ℂ 𝓢(ℂ, ℂ) :=
  ⨅ k : ℕ, ⨅ l : ℕ, LinearMap.ker (complexDiracDerivative k l).toLinearMap

/-- Paper: Theorem 5.3.2.5(1), p. 246.
Membership in the flat complex subspace means all mixed Wirtinger derivatives vanish at zero. -/
theorem mem_complexSchwartzFlatAtOrigin_iff (f : 𝓢(ℂ, ℂ)) :
    f ∈ complexSchwartzFlatAtOrigin ↔
      ∀ k l : ℕ, (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) f) 0 = 0 := by
  simp only [complexSchwartzFlatAtOrigin, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall₂_congr fun k l ↦ ?_
  change (-1 : ℂ) ^ (k + l) • ((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) 0 = 0 ↔ _
  rw [smul_eq_zero]
  exact or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The flat complex Schwartz subspace is closed. -/
theorem complexSchwartzFlatAtOrigin_isClosed :
    IsClosed (complexSchwartzFlatAtOrigin : Set 𝓢(ℂ, ℂ)) := by
  simp only [complexSchwartzFlatAtOrigin, Submodule.coe_iInf]
  exact isClosed_iInter fun k ↦ isClosed_iInter fun l ↦ (complexDiracDerivative k l).isClosed_ker

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The quotient adjoint identifies the strong dual of the complex flat quotient with
the annihilator in the strong dual of the complex Schwartz space. -/
theorem complexSchwartzFlatQuotient_strongDual :
    let pull := fun T : StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ↦
      T.comp complexSchwartzFlatAtOrigin.mkQL
    IsEmbedding pull ∧ Set.range pull =
      {T : StrongDual ℂ 𝓢(ℂ, ℂ) | ∀ f ∈ complexSchwartzFlatAtOrigin, T f = 0} := by sorry

-- TODO(paper-gap): Under ordinary coefficient pairing the adjoint on p. 249
-- has a sign for each odd total degree and includes all degrees. The positive
-- Taylor map below differs from that adjoint by (X,Y) ↦ (-X,-Y).

/-- the first Wirtinger derivatives of a mixed monomial. -/
private theorem complexSchwartzTaylor_equiv_monomial_deriv (c : ℂ) (k l : ℕ) (z : ℂ) :
    wirtingerDeriv (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z =
      c * (k : ℂ) * z ^ (k - 1) * (star z) ^ l ∧
    wirtingerConjDeriv (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z =
      c * (l : ℂ) * z ^ k * (star z) ^ (l - 1) := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) z).pow k
  have hb := (Complex.conjCLE.hasFDerivAt (x := z)).pow l
  have h := (hi.mul hb).const_mul c
  simp only [Pi.mul_apply, id_eq, Complex.conjCLE_apply, ← Complex.star_def] at h
  change (fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z 1 -
    Complex.I * fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z Complex.I) / 2 = _ ∧
    (fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z 1 +
    Complex.I * fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z Complex.I) / 2 = _
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, Complex.conjCLE_apply, smul_eq_mul, map_one,
    Complex.star_def, Complex.conj_I, nsmul_eq_mul,
    ContinuousLinearEquiv.coe_coe]
  constructor
  · linear_combination (c * (l : ℂ) * z ^ k * ((starRingEnd ℂ) z) ^ (l - 1) -
      c * (k : ℂ) * z ^ (k - 1) * ((starRingEnd ℂ) z) ^ l) * Complex.I_sq / 2
  · linear_combination (c * (k : ℂ) * z ^ (k - 1) * ((starRingEnd ℂ) z) ^ l -
      c * (l : ℂ) * z ^ k * ((starRingEnd ℂ) z) ^ (l - 1)) * Complex.I_sq / 2

/-- Wirtinger differentiation preserves equality with a monomial near zero. -/
private theorem complexSchwartzTaylor_equiv_germ (f : 𝓢(ℂ, ℂ))
    (c : ℂ) (k l : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * (z ^ k * (star z) ^ l)) :
    (schwartzWirtingerZ f : ℂ → ℂ) =ᶠ[𝓝 0]
      (fun z ↦ (c * k) * (z ^ (k - 1) * (star z) ^ l)) ∧
    (schwartzWirtingerZBar f : ℂ → ℂ) =ᶠ[𝓝 0]
      (fun z ↦ (c * l) * (z ^ k * (star z) ^ (l - 1))) := by
  have hd := hf.fderiv (𝕜 := ℝ)
  constructor
  · filter_upwards [hd] with z hz
    rw [(schwartzWirtinger_apply f z).1, wirtingerDeriv, hz]
    have h := (complexSchwartzTaylor_equiv_monomial_deriv c k l z).1
    dsimp only [wirtingerDeriv] at h
    rw [h]
    ring
  · filter_upwards [hd] with z hz
    rw [(schwartzWirtinger_apply f z).2, wirtingerConjDeriv, hz]
    have h := (complexSchwartzTaylor_equiv_monomial_deriv c k l z).2
    dsimp only [wirtingerConjDeriv] at h
    rw [h]
    ring

/-- iterated mixed derivatives of a monomial germ have descending-factorial coefficients. -/
private theorem complexSchwartzTaylor_equiv_germ_pow (f : 𝓢(ℂ, ℂ))
    (c : ℂ) (k l : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * (z ^ k * (star z) ^ l)) (u v : ℕ) :
    ((schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) f) : ℂ → ℂ) =ᶠ[𝓝 0]
      fun z ↦ (c * (l.descFactorial v : ℂ) * (k.descFactorial u : ℂ)) *
        (z ^ (k - u) * (star z) ^ (l - v)) := by
  have hb (v : ℕ) : ((schwartzWirtingerZBar ^ v) f : ℂ → ℂ) =ᶠ[𝓝 0]
      fun z ↦ (c * (l.descFactorial v : ℂ)) * (z ^ k * (star z) ^ (l - v)) := by
    induction v with
    | zero => simpa using hf
    | succ v ih =>
      have h := (complexSchwartzTaylor_equiv_germ _ _ _ _ ih).2
      rw [pow_succ']
      filter_upwards [h] with z hz
      change schwartzWirtingerZBar ((schwartzWirtingerZBar ^ v) f) z = _
      rw [hz, Nat.descFactorial_succ, Nat.sub_sub]
      push_cast
      ring
  induction u with
  | zero => simpa using hb v
  | succ u ih =>
    have h := (complexSchwartzTaylor_equiv_germ _ _ _ _ ih).1
    rw [pow_succ']
    filter_upwards [h] with z hz
    change schwartzWirtingerZ ((schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) f)) z = _
    rw [hz, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/-- a mixed monomial germ has exactly one nonzero mixed derivative at zero. -/
private theorem complexSchwartzTaylor_equiv_germ_zero (f : 𝓢(ℂ, ℂ)) (k l : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ z ^ k * (star z) ^ l) (u v : ℕ) :
    (schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) f) 0 =
      if u = k ∧ v = l then (k.factorial * l.factorial : ℂ) else 0 := by
  have h := (complexSchwartzTaylor_equiv_germ_pow f 1 k l (by simpa using hf) u v).eq_of_nhds
  rw [h]
  rcases lt_trichotomy u k with hu | rfl | hu
  · simp [hu.ne, Nat.sub_ne_zero_of_lt hu]
  · rcases lt_trichotomy v l with hv | rfl | hv
    · simp [hv.ne, Nat.sub_ne_zero_of_lt hv]
    · simp [Nat.descFactorial_self, mul_comm]
    · simp [hv.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hv]
  · simp [hu.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hu]

/-- dilation makes every seminorm below the homogeneous degree arbitrarily small. -/
private theorem complexSchwartzTaylor_equiv_scaled (G ψ : 𝓢(ℂ, ℂ)) (n m k : ℕ)
    (hG : tsupport (G : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hmn : m < n)
    (hψ : ∀ z, ψ z = (ε : ℂ) ^ n * G (ε⁻¹ • z)) :
    SchwartzMap.seminorm ℂ k m ψ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by
  have hd (z : ℂ) : iteratedFDeriv ℝ m (ψ : ℂ → ℂ) z =
      (ε : ℂ) ^ n • ((ε⁻¹) ^ m • iteratedFDeriv ℝ m (G : ℂ → ℂ) (ε⁻¹ • z)) := by
    rw [show (ψ : ℂ → ℂ) = fun z ↦ (ε : ℂ) ^ n • G (ε⁻¹ • z) from funext hψ,
      iteratedFDeriv_const_smul_apply']
    · rw [iteratedFDeriv_comp_const_smul ε⁻¹ (G.smooth m)]
    · exact ((G.smooth m).comp (contDiff_id.const_smul ε⁻¹)).contDiffAt
  have hGb (z : ℂ) : ‖iteratedFDeriv ℝ m (G : ℂ → ℂ) z‖ ≤ SchwartzMap.seminorm ℂ 0 m G := by
    simpa using SchwartzMap.le_seminorm ℂ 0 m G z
  have hpow : ε ^ n * (ε⁻¹) ^ m ≤ ε := by
    rw [← pow_sub_mul_pow ε hmn.le, mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow,
      mul_one]
    calc ε ^ (n - m) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by omega)
      _ = ε := pow_one ε
  refine SchwartzMap.seminorm_le_bound ℂ k m _ (by positivity) fun z ↦ ?_
  rw [hd, norm_smul, norm_smul, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos (inv_pos.mpr hε)]
  by_cases hz : ‖z‖ ≤ 1
  · calc ‖z‖ ^ k * (ε ^ n * ((ε⁻¹) ^ m * ‖iteratedFDeriv ℝ m (G : ℂ → ℂ) (ε⁻¹ • z)‖))
        ≤ 1 * ((ε ^ n * (ε⁻¹) ^ m) * SchwartzMap.seminorm ℂ 0 m G) := by
          rw [← mul_assoc (ε ^ n)]
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hz
          · exact hGb _
      _ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by rw [one_mul]; gcongr
  · have hout : ε⁻¹ • z ∉ tsupport (G : ℂ → ℂ) := by
      intro h
      have hh := hG h
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hε, inv_mul_le_iff₀ hε] at hh
      exact hz ((by simpa using hh : ‖z‖ ≤ ε).trans hε1)
    have h0 : iteratedFDeriv ℝ m (G : ℂ → ℂ) (ε⁻¹ • z) = 0 := by
      by_contra hne
      exact hout (support_iteratedFDeriv_subset m hne)
    rw [h0, norm_zero, mul_zero, mul_zero, mul_zero]
    positivity

/-- a compactly supported mixed monomial and its dilations realize the same jet. -/
private theorem complexSchwartzTaylor_equiv_bump (k l : ℕ) :
    ∃ G : 𝓢(ℂ, ℂ), tsupport (G : ℂ → ℂ) ⊆ Metric.closedBall 0 1 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ψ : 𝓢(ℂ, ℂ),
        (∀ z, ψ z = (ε : ℂ) ^ (k + l) * G (ε⁻¹ • z)) ∧
        (∀ u v, (schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) ψ) 0 =
          if u = k ∧ v = l then (k.factorial * l.factorial : ℂ) else 0) := by
  let χ : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let g : ℂ → ℂ := fun z ↦ (χ z : ℂ) * (z ^ k * (star z) ^ l)
  have hc : HasCompactSupport g :=
    (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hd : ContDiff (ℝ) (∞) g := (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
    ((contDiff_id.pow k).mul (Complex.conjLIE.contDiff.pow l))
  let G := hc.toSchwartzMap hd
  have hG : tsupport (G : ℂ → ℂ) ⊆ Metric.closedBall 0 1 := by
    change tsupport g ⊆ _
    exact tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero _).trans
      (by rw [χ.tsupport_eq]))
  refine ⟨G, hG, fun ε hε ↦ ?_⟩
  have hsc : HasCompactSupport (fun z : ℂ ↦ (ε : ℂ) ^ (k + l) * G (ε⁻¹ • z)) :=
    (hc.comp_smul (inv_ne_zero hε.ne')).mul_left
  have hsd : ContDiff (ℝ) (∞) (fun z : ℂ ↦ (ε : ℂ) ^ (k + l) * G (ε⁻¹ • z)) :=
    contDiff_const.mul ((G.smooth ⊤).comp (contDiff_id.const_smul ε⁻¹))
  let ψ := hsc.toSchwartzMap hsd
  refine ⟨ψ, fun _ ↦ rfl, fun u v ↦ complexSchwartzTaylor_equiv_germ_zero ψ k l ?_ u v⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (mul_pos hε χ.rIn_pos)] with z hz
  have hb : ε⁻¹ • z ∈ Metric.closedBall (0 : ℂ) χ.rIn := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hε, inv_mul_le_iff₀ hε]
    exact hz.le
  change (ε : ℂ) ^ (k + l) * ((χ (ε⁻¹ • z) : ℂ) * ((ε⁻¹ • z) ^ k * (star (ε⁻¹ • z)) ^ l)) = _
  rw [χ.one_of_mem_closedBall hb]
  simp only [Complex.ofReal_one, one_mul, Complex.real_smul, star_mul',
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, map_inv₀, mul_pow, pow_add]
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hk : (ε : ℂ) ^ k * ((ε : ℂ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ he, one_pow]
  have hl : (ε : ℂ) ^ l * ((ε : ℂ)⁻¹) ^ l = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ he, one_pow]
  calc _ = ((ε : ℂ) ^ k * ((ε : ℂ)⁻¹) ^ k) *
      ((ε : ℂ) ^ l * ((ε : ℂ)⁻¹) ^ l) * (z ^ k * ((starRingEnd ℂ) z) ^ l) := by ring
    _ = _ := by rw [hk, hl]; simp

/-- a normalized jet basis element can be made small in every lower-order seminorm. -/
private theorem complexSchwartzTaylor_equiv_basis (d : Fin 2 →₀ ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : 𝓢(ℂ, ℂ),
      (∀ q : Fin 2 →₀ ℕ,
        (schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) φ) 0 /
          ((q 0).factorial * (q 1).factorial : ℂ) = if q = d then 1 else 0) ∧
      ∀ k m : ℕ, m < d 0 + d 1 → SchwartzMap.seminorm ℂ k m φ ≤ δ := by
  classical
  obtain ⟨G, hG, hψ⟩ := complexSchwartzTaylor_equiv_bump (d 0) (d 1)
  let C : ℝ := ∑ m ∈ Finset.range (d 0 + d 1), SchwartzMap.seminorm ℂ 0 m G + 1
  have hC : 0 < C := by
    have : 0 ≤ ∑ m ∈ Finset.range (d 0 + d 1), SchwartzMap.seminorm ℂ 0 m G :=
      Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
    dsimp [C]; linarith
  let ε := min 1 (δ / C)
  have hε : 0 < ε := lt_min one_pos (div_pos hδ hC)
  obtain ⟨φ, hφ, hj⟩ := hψ ε hε
  refine ⟨φ, fun q ↦ ?_, fun k m hm ↦ ?_⟩
  · rw [hj]
    have he : q 0 = d 0 ∧ q 1 = d 1 ↔ q = d := by
      constructor
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> assumption
      · rintro rfl; exact ⟨rfl, rfl⟩
    simp only [he]
    split_ifs with h
    · subst q
      exact div_self (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d 0))
        (by exact_mod_cast Nat.factorial_ne_zero (d 1)))
    · exact zero_div _
  · have hmc : SchwartzMap.seminorm ℂ 0 m G ≤ C := by
      have h := Finset.single_le_sum (fun j _ ↦ apply_nonneg (SchwartzMap.seminorm ℂ 0 j) G)
        (Finset.mem_range.mpr hm)
      dsimp [C]; linarith
    calc SchwartzMap.seminorm ℂ k m φ ≤ ε * SchwartzMap.seminorm ℂ 0 m G :=
          complexSchwartzTaylor_equiv_scaled G φ (d 0 + d 1) m k hG ε hε (min_le_left _ _) hm hφ
      _ ≤ (δ / C) * C := by
          gcongr
          exact min_le_right _ _
      _ = δ := div_mul_cancel₀ _ hC.ne'

/-- Paper: Theorem 5.3.2.5(2), p. 246.
Finite mixed Wirtinger jets can be realized by Schwartz functions, with a linear bound
on any prescribed finite family of Schwartz seminorms. -/
private theorem complexSchwartzTaylor_equiv_finite
    (s : Finset (ℕ × ℕ)) (t : Finset (Fin 2 →₀ ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : (Fin 2 →₀ ℕ) → ℂ, ∃ f : 𝓢(ℂ, ℂ),
      (∀ d : Fin 2 →₀ ℕ,
        (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
          ((d 0).factorial * (d 1).factorial : ℂ) = if d ∈ t then b d else 0) ∧
      (s.sup (schwartzSeminormFamily ℂ ℂ ℂ)) f ≤ C * ∑ d ∈ t, ‖b d‖ := by
  classical
  choose φ hφ using fun d ↦ complexSchwartzTaylor_equiv_basis d 1 one_pos
  let p := s.sup (schwartzSeminormFamily ℂ ℂ ℂ)
  let C := ∑ d ∈ t, p (φ d) + 1
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun d (_ : d ∈ t) ↦ apply_nonneg p (φ d))
    dsimp [C]; linarith
  refine ⟨C, hC, fun b ↦ ⟨∑ d ∈ t, b d • φ d, fun q ↦ ?_, ?_⟩⟩
  · let a : StrongDual ℂ 𝓢(ℂ, ℂ) :=
      (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ •
        (TemperedDistribution.delta (0 : ℂ)).comp
          ((schwartzWirtingerZ ^ (q 0)).comp (schwartzWirtingerZBar ^ (q 1)))
    have ha (f : 𝓢(ℂ, ℂ)) : a f =
        (schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) f) 0 /
          ((q 0).factorial * (q 1).factorial : ℂ) := by
      change (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ * _ = _; rw [div_eq_mul_inv, mul_comm]; rfl
    have hap (d : Fin 2 →₀ ℕ) : a (φ d) = if q = d then 1 else 0 :=
      (ha _).trans ((hφ d).1 q)
    rw [← ha, map_sum]
    simp [map_smul, hap]
  · calc p (∑ d ∈ t, b d • φ d) ≤ ∑ d ∈ t, p (b d • φ d) :=
          Finset.le_sum_of_subadditive p (map_zero _).le (map_add_le_add _) _ _
      _ ≤ ∑ d ∈ t, C * ‖b d‖ := by
          apply Finset.sum_le_sum
          intro d hd
          rw [map_smul_eq_mul, mul_comm]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have h := Finset.single_le_sum (fun d _ ↦ apply_nonneg p (φ d)) hd
          dsimp [C]; linarith
      _ = C * ∑ d ∈ t, ‖b d‖ := (Finset.mul_sum _ _ _).symm


/-- Paper: Theorem 5.3.2.5(2), p. 246.
For any finite family of Schwartz seminorms, jets vanishing on a sufficiently large
finite set of indices admit realizations arbitrarily small in those seminorms.
This is the tail part of the two-variable Borel construction. -/
private theorem complexSchwartzTaylor_equiv_tail (s : Finset (ℕ × ℕ)) :
    ∃ t : Finset (Fin 2 →₀ ℕ), ∀ b : (Fin 2 →₀ ℕ) → ℂ,
      (∀ d ∈ t, b d = 0) → ∀ r : ℝ, 0 < r → ∃ f : 𝓢(ℂ, ℂ),
        (∀ d : Fin 2 →₀ ℕ,
          (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
            ((d 0).factorial * (d 1).factorial : ℂ) = b d) ∧
        (s.sup (schwartzSeminormFamily ℂ ℂ ℂ)) f < r := by
  classical
  let e : ℕ ≃ (Fin 2 →₀ ℕ) :=
    (Finsupp.equivFunOnFinite.trans ((finTwoArrowEquiv ℕ).trans Nat.pairEquiv)).symm
  have he (n : ℕ) : (e n) 0 = (Nat.unpair n).1 ∧ (e n) 1 = (Nat.unpair n).2 := by
    simp [e, finTwoArrowEquiv, Nat.pairEquiv]
    exact ⟨rfl, rfl⟩
  have hdeg (j n : ℕ) (hn : (j + 1) ^ 2 ≤ n) : j < (e n) 0 + (e n) 1 := by
    by_contra h
    have h0 : (Nat.unpair n).1 ≤ j := by rw [← (he n).1]; omega
    have h1 : (Nat.unpair n).2 ≤ j := by rw [← (he n).2]; omega
    have hp := Nat.pair_lt_max_add_one_sq (Nat.unpair n).1 (Nat.unpair n).2
    rw [Nat.pair_unpair] at hp
    have hmax : max (Nat.unpair n).1 (Nat.unpair n).2 ≤ j := max_le h0 h1
    have hs : (max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 ≤ (j + 1) ^ 2 := by gcongr
    omega
  let m := s.sup Prod.snd
  let t := (Finset.range ((m + 1) ^ 2)).image e
  refine ⟨t, fun b hb r hr ↦ ?_⟩
  let w (n : ℕ) : ℝ := r / 4 * (1 / 2) ^ n
  have hw (n : ℕ) : 0 < w n := by positivity
  have hwsum : HasSum w (r / 2) := by
    have h := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (r / 4)
    convert h using 1
    norm_num
    ring
  choose φ hφ using fun n ↦ complexSchwartzTaylor_equiv_basis (e n)
    (w n / (‖b (e n)‖ + 1)) (by have := hw n; positivity)
  have hsmall (n k j : ℕ) (hn : (j + 1) ^ 2 ≤ n) :
      ‖b (e n)‖ * SchwartzMap.seminorm ℂ k j (φ n) ≤ w n := by
    calc ‖b (e n)‖ * SchwartzMap.seminorm ℂ k j (φ n)
        ≤ ‖b (e n)‖ * (w n / (‖b (e n)‖ + 1)) := by
          gcongr
          exact (hφ n).2 k j (hdeg j n hn)
      _ = w n * (‖b (e n)‖ / (‖b (e n)‖ + 1)) := by ring
      _ ≤ w n * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = w n := mul_one _
  let v (i : ℕ × ℕ) (n : ℕ) : ℝ :=
    if n < (i.2 + 1) ^ 2 then ‖b (e n)‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0
  have hv (i : ℕ × ℕ) : Summable (v i) := by
    refine summable_of_ne_finset_zero (s := Finset.range ((i.2 + 1) ^ 2)) fun n hn ↦ ?_
    simp only [Finset.mem_range] at hn
    simp only [v, hn, ↓reduceIte]
  have hx (i : ℕ × ℕ) (n : ℕ) :
      schwartzSeminormFamily ℂ ℂ ℂ i (b (e n) • φ n) ≤ w n + v i n := by
    rw [SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul]
    by_cases hn : n < (i.2 + 1) ^ 2
    · simp only [v, hn, ↓reduceIte]
      linarith [hw n]
    · simp only [v, hn, ↓reduceIte, add_zero]
      exact hsmall n i.1 i.2 (by omega)
  have : CompleteSpace 𝓢(ℂ, ℂ) := completeSpace_schwartzMap
  obtain ⟨hsum, hbound⟩ := realSchwartzFlatQuotient_strongDual_summable
    (schwartz_withSeminorms ℂ ℂ ℂ) (fun n ↦ b (e n) • φ n)
    (fun i n ↦ w n + v i n) (fun i ↦ hwsum.summable.add (hv i)) hx
  refine ⟨∑' n, b (e n) • φ n, fun q ↦ ?_, ?_⟩
  · let a : StrongDual ℂ 𝓢(ℂ, ℂ) :=
      (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ •
        (TemperedDistribution.delta (0 : ℂ)).comp
          ((schwartzWirtingerZ ^ (q 0)).comp (schwartzWirtingerZBar ^ (q 1)))
    have ha (f : 𝓢(ℂ, ℂ)) : a f =
        (schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) f) 0 /
          ((q 0).factorial * (q 1).factorial : ℂ) := by
      change (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ * _ = _
      rw [div_eq_mul_inv, mul_comm]; rfl
    have hap (n : ℕ) : a (φ n) = if q = e n then 1 else 0 := (ha _).trans ((hφ n).1 q)
    rw [← ha, ContinuousLinearMap.map_tsum _ hsum]
    simp only [map_smul, hap, smul_eq_mul]
    rw [tsum_eq_single (e.symm q) fun n hn ↦ ?_]
    · simp
    · have hne : q ≠ e n := fun h ↦ hn (by rw [h, e.symm_apply_apply])
      simp [hne]
  · apply Seminorm.finset_sup_apply_lt hr
    intro i hi
    have him : i.2 ≤ m := Finset.le_sup (f := Prod.snd) hi
    have hv0 : v i = 0 := by
      funext n
      dsimp only [v]
      split_ifs with hn
      · have hnm : n < (m + 1) ^ 2 := hn.trans_le (by gcongr)
        have hb0 := hb (e n) (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hnm, rfl⟩)
        simp [hb0]
      · rfl
    have h := hbound i
    rw [hv0] at h
    simp only [Pi.zero_apply, add_zero, hwsum.tsum_eq] at h
    exact h.trans_lt (by linarith)

/-- A finite jet and an arbitrarily small tail give a quantitative Borel realization. -/
private theorem complexSchwartzTaylor_equiv_bound (s : Finset (ℕ × ℕ)) :
    ∃ t : Finset (Fin 2 →₀ ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ b : (Fin 2 →₀ ℕ) → ℂ, ∀ r : ℝ, 0 < r → ∃ f : 𝓢(ℂ, ℂ),
        (∀ d : Fin 2 →₀ ℕ,
          (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
            ((d 0).factorial * (d 1).factorial : ℂ) = b d) ∧
        (s.sup (schwartzSeminormFamily ℂ ℂ ℂ)) f < C * ∑ d ∈ t, ‖b d‖ + r := by
  classical
  obtain ⟨t, ht⟩ := complexSchwartzTaylor_equiv_tail s
  obtain ⟨C, hC, hfinite⟩ := complexSchwartzTaylor_equiv_finite s t
  refine ⟨t, C, hC, fun b r hr ↦ ?_⟩
  obtain ⟨f, hf, hfb⟩ := hfinite b
  obtain ⟨g, hg, hgb⟩ := ht (fun d ↦ if d ∈ t then 0 else b d)
    (fun d hd ↦ by simp [hd]) r hr
  refine ⟨f + g, fun d ↦ ?_, (map_add_le_add _ f g).trans_lt (add_lt_add_of_le_of_lt hfb hgb)⟩
  simp only [map_add, add_apply, add_div, hf, hg]
  split_ifs <;> simp

/-- Paper: Theorem 5.3.2.5(2), p. 246.
The complex flat quotient is identified with formal power series in two variables by the
mixed Wirtinger Taylor coefficients, with the coefficientwise topology of (5.3.2.13).
Deviation: The Taylor formula takes a Schwartz test as input, as required by the domain. -/
theorem complexSchwartzTaylor_equiv :
    ∃ e : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ,
      ∀ (f : 𝓢(ℂ, ℂ)) (s : Fin 2 →₀ ℕ),
        MvPowerSeries.coeff s (e (complexSchwartzFlatAtOrigin.mkQ f)) =
          (schwartzWirtingerZ^(s 0)) ((schwartzWirtingerZBar^(s 1)) f) 0 /
            ((s 0).factorial * (s 1).factorial : ℂ) := by
  classical
  let a (d : Fin 2 →₀ ℕ) : StrongDual ℂ 𝓢(ℂ, ℂ) :=
    (((d 0).factorial * (d 1).factorial : ℂ))⁻¹ •
      (TemperedDistribution.delta (0 : ℂ)).comp
        ((schwartzWirtingerZ ^ (d 0)).comp (schwartzWirtingerZBar ^ (d 1)))
  have ha (d : Fin 2 →₀ ℕ) (f : 𝓢(ℂ, ℂ)) :
      a d f = (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
        ((d 0).factorial * (d 1).factorial : ℂ) := by
    change (((d 0).factorial * (d 1).factorial : ℂ))⁻¹ * _ = _
    rw [div_eq_mul_inv, mul_comm]
    rfl
  have hfact (d : Fin 2 →₀ ℕ) : ((d 0).factorial * (d 1).factorial : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d 0))
      (by exact_mod_cast Nat.factorial_ne_zero (d 1))
  let T : 𝓢(ℂ, ℂ) →ₗ[ℂ] MvPowerSeries (Fin 2) ℂ :=
    { toFun := fun f d ↦ a d f
      map_add' := fun f g ↦ by ext d; exact map_add (a d) f g
      map_smul' := fun c f ↦ by ext d; exact map_smul (a d) c f }
  have hT (f : 𝓢(ℂ, ℂ)) (d : Fin 2 →₀ ℕ) : MvPowerSeries.coeff d (T f) = a d f := rfl
  have hTc : Continuous T := by
    refine continuous_iff_continuousAt.mpr fun f ↦ ?_
    rw [ContinuousAt, MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    simp only [hT]
    exact (a d).continuous.tendsto f
  let TL : 𝓢(ℂ, ℂ) →L[ℂ] MvPowerSeries (Fin 2) ℂ := ⟨T, hTc⟩
  have hTL (f : 𝓢(ℂ, ℂ)) (d : Fin 2 →₀ ℕ) : MvPowerSeries.coeff d (TL f) = a d f := rfl
  have hmem (f : 𝓢(ℂ, ℂ)) : f ∈ complexSchwartzFlatAtOrigin ↔ TL f = 0 := by
    rw [mem_complexSchwartzFlatAtOrigin_iff, MvPowerSeries.ext_iff]
    simp only [hTL, ha, map_zero, div_eq_zero_iff, hfact, or_false]
    constructor
    · intro h d
      exact h (d 0) (d 1)
    · intro h k l
      let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![k, l]
      simpa [d] using h d
  have hle : complexSchwartzFlatAtOrigin ≤ TL.ker := fun f hf ↦ (hmem f).mp hf
  let E := complexSchwartzFlatAtOrigin.liftQL TL hle
  have hE (f : 𝓢(ℂ, ℂ)) : E (complexSchwartzFlatAtOrigin.mkQ f) = TL f := rfl
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).mpr fun y hy ↦ ?_
    obtain ⟨f, rfl⟩ := complexSchwartzFlatAtOrigin.mkQ_surjective y
    rw [hE] at hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((hmem f).mpr hy)
  have hsurj : Function.Surjective E := by
    intro p
    obtain ⟨t, C, hC, hb⟩ := complexSchwartzTaylor_equiv_bound ∅
    obtain ⟨f, hf, -⟩ := hb (fun d ↦ MvPowerSeries.coeff d p) 1 one_pos
    refine ⟨complexSchwartzFlatAtOrigin.mkQ f, ?_⟩
    ext d
    rw [hE, hTL, ha, hf]
  let e : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃ₗ[ℂ] MvPowerSeries (Fin 2) ℂ :=
    LinearEquiv.ofBijective E.toLinearMap ⟨hinj, hsurj⟩
  have he (y : 𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) : e y = E y := rfl
  have hsymm : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro V hV
    have hq : complexSchwartzFlatAtOrigin.mkQ ⁻¹' V ∈ 𝓝 (0 : 𝓢(ℂ, ℂ)) :=
      complexSchwartzFlatAtOrigin.mkQL.continuous.continuousAt.preimage_mem_nhds
        (by simpa using hV)
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ ℂ ℂ).hasBasis_zero_ball.mem_iff.mp hq
    obtain ⟨t, C, hC, hb⟩ := complexSchwartzTaylor_equiv_bound s
    have hcont : Continuous (fun p : MvPowerSeries (Fin 2) ℂ ↦
        C * ∑ d ∈ t, ‖MvPowerSeries.coeff d p‖) := by
      fun_prop
    have hW : ∀ᶠ p in 𝓝 (0 : MvPowerSeries (Fin 2) ℂ),
        C * ∑ d ∈ t, ‖MvPowerSeries.coeff d p‖ < r / 2 := by
      have h := hcont.tendsto 0
      have hz : C * ∑ d ∈ t, ‖MvPowerSeries.coeff d (0 : MvPowerSeries (Fin 2) ℂ)‖ = 0 := by simp
      rw [hz] at h
      exact h.eventually (gt_mem_nhds (by linarith))
    rw [Filter.mem_map]
    filter_upwards [hW] with p hp
    obtain ⟨f, hf, hfb⟩ := hb (fun d ↦ MvPowerSeries.coeff d p) (r / 2) (by linarith)
    have hp' : e.symm p = complexSchwartzFlatAtOrigin.mkQ f := by
      rw [LinearEquiv.symm_apply_eq, he, hE]
      ext d
      rw [hTL, ha, hf]
    rw [Set.mem_preimage, hp']
    apply hsub
    apply (Seminorm.mem_ball_zero _).mpr
    linarith
  let eL : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ :=
    { e with
      continuous_toFun := E.continuous
      continuous_invFun := hsymm }
  refine ⟨eL, fun f d ↦ ?_⟩
  change MvPowerSeries.coeff d (TL f) = _
  rw [hTL, ha]


section ComplexPolynomialDualHelpers


/-- A continuous functional on coefficientwise formal power series has finite coefficient support. -/
private theorem complexDiracDerivatives_polynomialEquiv_poly_finite
    (L : MvPowerSeries (Fin 2) ℂ →L[ℂ] ℂ) :
    ∃ N : ℕ, ∀ s : MvPowerSeries (Fin 2) ℂ,
      (∀ d : Fin 2 →₀ ℕ, d 0 + d 1 ≤ N → MvPowerSeries.coeff d s = 0) → L s = 0 := by
  by_contra h
  push Not at h
  choose s hs0 hs using h
  let t (N : ℕ) : MvPowerSeries (Fin 2) ℂ := (L (s N))⁻¹ • s N
  have ht : Tendsto t atTop (𝓝 0) := by
    rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    rw [map_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (d 0 + d 1)] with N hN
    simp [t, hs0 N d hN]
  have h1 := (L.continuous.tendsto 0).comp ht
  rw [map_zero] at h1
  have h2 : ⇑L ∘ t = fun _ ↦ 1 := by
    funext N
    simp [t, inv_mul_cancel₀ (hs N)]
  rw [h2] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

private theorem complexDiracDerivatives_polynomialEquiv_poly_box
    (N : ℕ) :
    ∃ t : Finset (Fin 2 →₀ ℕ), ∀ d : Fin 2 →₀ ℕ, d 0 + d 1 ≤ N → d ∈ t := by
  classical
  refine ⟨((Finset.range (N + 1)).product (Finset.range (N + 1))).image
    (fun p ↦ Finsupp.equivFunOnFinite.symm ![p.1, p.2]), fun d hd ↦ ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(d 0, d 1), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

private theorem complexDiracDerivatives_polynomialEquiv_poly_bounded
    (w : (Fin 2 →₀ ℕ) → ℝ) :
    Bornology.IsVonNBounded ℂ {b : MvPowerSeries (Fin 2) ℂ | ∀ d, ‖MvPowerSeries.coeff d b‖ ≤ w d} := by
  change Bornology.IsVonNBounded ℂ {b : (Fin 2 →₀ ℕ) → ℂ | ∀ d, ‖b d‖ ≤ w d}
  rw [Bornology.isVonNBounded_pi_iff]
  intro d
  apply (NormedSpace.isVonNBounded_iff ℂ).mpr
  apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := w d)).subset
  rintro z ⟨b, hb, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb d

private theorem complexDiracDerivatives_polynomialEquiv_poly_algebra :
    ∃ e : MvPolynomial (Fin 2) ℂ ≃ₗ[ℂ] StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
      ∀ (p : MvPolynomial (Fin 2) ℂ) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
        e p y = ∑ d ∈ p.support, p.coeff d * (-1 : ℂ) ^ (d 0 + d 1) *
          MvPowerSeries.coeff d (complexSchwartzTaylor_equiv.choose y) := by
  classical
  let τ := complexSchwartzTaylor_equiv.choose
  let cf (d : Fin 2 →₀ ℕ) : MvPowerSeries (Fin 2) ℂ →L[ℂ] ℂ :=
    ⟨MvPowerSeries.coeff d, MvPowerSeries.WithPiTopology.continuous_coeff ℂ d⟩
  let c (d : Fin 2 →₀ ℕ) : StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    (-1 : ℂ) ^ (d 0 + d 1) • (cf d).comp τ.toContinuousLinearMap
  have hc (d) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :
      c d y = (-1 : ℂ) ^ (d 0 + d 1) * MvPowerSeries.coeff d (τ y) := rfl
  let Φ : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    (Finsupp.linearCombination ℂ c).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  have hΦ (p : MvPolynomial (Fin 2) ℂ) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :
      Φ p y = ∑ d ∈ p.support, p.coeff d * c d y := by
    simp [Φ, Finsupp.linearCombination_apply, Finsupp.sum, sum_apply]
    rfl
  have hΦm (d : Fin 2 →₀ ℕ) (a : ℂ) : Φ (MvPolynomial.monomial d a) = a • c d := by
    simp [Φ, MvPolynomial.monomial, Finsupp.linearCombination_apply]
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).mpr fun p hp ↦ ?_
    ext n
    have h := congrArg (fun T : StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) ↦
      T (τ.symm (MvPowerSeries.monomial n 1))) hp
    simp only [hΦ, hc, ContinuousLinearEquiv.apply_symm_apply, MvPowerSeries.coeff_monomial,
      zero_apply] at h
    rw [Finset.sum_eq_single n (fun d _ hd ↦ by simp [hd])
      (fun hn ↦ by simp [MvPolynomial.notMem_support_iff.mp hn])] at h
    simpa using h
  have hsurj : Function.Surjective Φ := by
    intro T
    let L : MvPowerSeries (Fin 2) ℂ →L[ℂ] ℂ := T.comp τ.symm.toContinuousLinearMap
    obtain ⟨N, hN⟩ := complexDiracDerivatives_polynomialEquiv_poly_finite L
    obtain ⟨t, ht⟩ := complexDiracDerivatives_polynomialEquiv_poly_box N
    refine ⟨∑ d ∈ t, MvPolynomial.monomial d ((-1 : ℂ) ^ (d 0 + d 1) * L (MvPowerSeries.monomial d 1)), ?_⟩
    ext y
    rw [map_sum]
    simp only [hΦm, sum_apply, smul_apply, hc, smul_eq_mul]
    have hy : T y = L (τ y) := by simp [L]
    have hs : L (τ y - ∑ d ∈ t, MvPowerSeries.coeff d (τ y) • MvPowerSeries.monomial d 1) = 0 := by
      apply hN
      intro m hm
      rw [map_sub, map_sum]
      simp [MvPowerSeries.coeff_monomial, ht m hm, Finset.sum_ite_eq]
    rw [map_sub, map_sum, sub_eq_zero] at hs
    rw [hy, hs]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [map_smul, smul_eq_mul]
    have he : (-1 : ℂ) ^ (d 0 + d 1) * (-1) ^ (d 0 + d 1) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (L (MvPowerSeries.monomial d 1) * MvPowerSeries.coeff d (τ y)) * he
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun p y ↦ ?_⟩
  change Φ p y = _
  rw [hΦ]
  simp only [hc, mul_assoc]
  rfl

/-- Bounded coefficient polydiscs control every seminorm of the inverse strong-dual map. -/
private theorem complexDiracDerivatives_polynomialEquiv_poly_topology :
    ∃ e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
        StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
      ∀ (p : MvPolynomial (Fin 2) ℂ) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
        e p y = ∑ d ∈ p.support, p.coeff d * (-1 : ℂ) ^ (d 0 + d 1) *
          MvPowerSeries.coeff d (complexSchwartzTaylor_equiv.choose y) := by
  classical
  obtain ⟨e₀, he₀⟩ := complexDiracDerivatives_polynomialEquiv_poly_algebra
  let τ := complexSchwartzTaylor_equiv.choose
  let e₁ : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃ₗ[ℂ]
      StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) := e₀
  have : IsClosed (complexSchwartzFlatAtOrigin : Set (SchwartzMap ℂ ℂ)) := complexSchwartzFlatAtOrigin_isClosed
  let : UniformSpace (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    isUniformAddGroup_of_addCommGroup
  let : PolynormableSpace ℂ (StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin)) :=
    uniformConvergenceCLM_polynormable (F := ℂ)
      {B : Set (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) | Bornology.IsVonNBounded ℂ B}
      (fun _ h ↦ h)
      (by rw [Bornology.sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  have hcont : Continuous e₁ := continuous_of_finestLocallyConvex _ e₁.toLinearMap
  have hsymm : Continuous e₁.symm := by
    refine (finestLocallyConvex_withSeminorms (MvPolynomial (Fin 2) ℂ)).continuous_of_continuous_comp
      e₁.symm.toLinearMap fun p ↦ ?_
    refine Seminorm.continuous (r := 1) ?_
    let w (d : Fin 2 →₀ ℕ) : ℝ := p (MvPolynomial.monomial d 1)
    let B : Set (MvPowerSeries (Fin 2) ℂ) := {b | ∀ d, ‖MvPowerSeries.coeff d b‖ ≤ w d}
    have hB := (complexDiracDerivatives_polynomialEquiv_poly_bounded w).image τ.symm.toContinuousLinearMap
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo hB
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with T hT
    rw [Seminorm.mem_ball_zero]
    change p (e₁.symm T) < 1
    let q : MvPolynomial (Fin 2) ℂ := e₁.symm T
    have hTq : T = e₀ q := by exact (e₁.apply_symm_apply T).symm
    let b : MvPowerSeries (Fin 2) ℂ := fun d ↦
      (-1 : ℂ) ^ (d 0 + d 1) * (w d : ℂ) * (star (q.coeff d) / (‖q.coeff d‖ : ℂ))
    have hb : b ∈ B := by
      intro d
      have hw : 0 ≤ w d := apply_nonneg _ _
      have hu : ‖star (q.coeff d) / (‖q.coeff d‖ : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
        exact div_self_le_one _
      change ‖(-1 : ℂ) ^ (d 0 + d 1) * (w d : ℂ) * _‖ ≤ w d
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_of_nonneg hw, mul_one] using mul_le_mul_of_nonneg_left hu hw
    have hval : T (τ.symm b) = ((∑ d ∈ q.support, w d * ‖q.coeff d‖ : ℝ) : ℂ) := by
      rw [hTq, he₀]
      simp only [τ, ContinuousLinearEquiv.apply_symm_apply]
      push_cast
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hz : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hn : (‖q.coeff d‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      have hs : (-1 : ℂ) ^ (d 0 + d 1) * (-1) ^ (d 0 + d 1) = 1 := by rw [← mul_pow]; norm_num
      change q.coeff d * (-1 : ℂ) ^ (d 0 + d 1) *
        ((-1 : ℂ) ^ (d 0 + d 1) * (w d : ℂ) * (star (q.coeff d) / (‖q.coeff d‖ : ℂ))) = _
      calc
        _ = ((-1 : ℂ) ^ (d 0 + d 1) * (-1) ^ (d 0 + d 1)) * (w d : ℂ) *
            (q.coeff d * star (q.coeff d)) / (‖q.coeff d‖ : ℂ) := by ring
        _ = _ := by rw [hs, Complex.star_def, Complex.mul_conj']; field_simp
    have hle : p q ≤ ∑ d ∈ q.support, w d * ‖q.coeff d‖ := by
      conv_lhs => rw [q.as_sum]
      refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
        (Finset.sum_le_sum fun d _ ↦ ?_)
      rw [show MvPolynomial.monomial d (q.coeff d) = q.coeff d • MvPolynomial.monomial d 1 by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul_eq_mul, mul_comm]
    have hlt := hT ⟨b, hb, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hlt
    change ‖T (τ.symm b)‖ < 1 at hlt
    rw [hval, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun d _ ↦ mul_nonneg (apply_nonneg _ _) (norm_nonneg _))] at hlt
    exact hle.trans_lt hlt
  refine ⟨{e₁ with continuous_toFun := hcont, continuous_invFun := hsymm}, ?_⟩
  exact he₀

private theorem complexDiracDerivatives_polynomialEquiv_dir_norm
    (v x : ℂ) (f : SchwartzMap ℂ ℂ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (LineDeriv.lineDerivOp v f : ℂ → ℂ) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖ := by
  have hf : ContDiff ℝ (n : ℕ∞ω) (fderiv ℝ (f : ℂ → ℂ)) :=
    (f.smooth (n + 1)).fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) hf.contDiffAt le_rfl
  have he : (LineDeriv.lineDerivOp v f : ℂ → ℂ) = fun y ↦ fderiv ℝ (f : ℂ → ℂ) y v :=
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv v f)
  rw [he]
  simpa only [norm_iteratedFDeriv_fderiv] using h

private theorem complexDiracDerivatives_polynomialEquiv_wirt_norm
    (f : SchwartzMap ℂ ℂ) (n : ℕ) (x : ℂ) :
    ‖iteratedFDeriv ℝ n (schwartzWirtingerZ f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖ ∧
    ‖iteratedFDeriv ℝ n (schwartzWirtingerZBar f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖ := by
  have h1 := complexDiracDerivatives_polynomialEquiv_dir_norm 1 x f n
  have hI := complexDiracDerivatives_polynomialEquiv_dir_norm Complex.I x f n
  simp only [norm_one, Complex.norm_I, one_mul] at h1 hI
  have hd (g : SchwartzMap ℂ ℂ) (c : ℂ) :
      iteratedFDeriv ℝ n (c • g : SchwartzMap ℂ ℂ) x = c • iteratedFDeriv ℝ n (g : ℂ → ℂ) x :=
    by
      change iteratedFDeriv ℝ n (fun z ↦ c • g z) x = _
      exact iteratedFDeriv_const_smul_apply' (a := c) (g.smooth n).contDiffAt
  have hsub (g h : SchwartzMap ℂ ℂ) :
      iteratedFDeriv ℝ n (g - h : SchwartzMap ℂ ℂ) x =
        iteratedFDeriv ℝ n (g : ℂ → ℂ) x - iteratedFDeriv ℝ n (h : ℂ → ℂ) x := by
    change iteratedFDeriv ℝ n ((g : ℂ → ℂ) - (h : ℂ → ℂ)) x = _
    exact iteratedFDeriv_sub_apply (g.smooth n).contDiffAt (h.smooth n).contDiffAt
  have hadd (g h : SchwartzMap ℂ ℂ) :
      iteratedFDeriv ℝ n (g + h : SchwartzMap ℂ ℂ) x =
        iteratedFDeriv ℝ n (g : ℂ → ℂ) x + iteratedFDeriv ℝ n (h : ℂ → ℂ) x := by
    change iteratedFDeriv ℝ n ((g : ℂ → ℂ) + (h : ℂ → ℂ)) x = _
    exact iteratedFDeriv_add_apply (g.smooth n).contDiffAt (h.smooth n).contDiffAt
  constructor
  · change ‖iteratedFDeriv ℝ n (((2 : ℂ)⁻¹ • (LineDeriv.lineDerivOp (1 : ℂ) f -
      Complex.I • LineDeriv.lineDerivOp Complex.I f)) : SchwartzMap ℂ ℂ) x‖ ≤ _
    rw [hd, hsub, hd, norm_smul, show ‖(2 : ℂ)⁻¹‖ = (1/2 : ℝ) by norm_num]
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith
  · change ‖iteratedFDeriv ℝ n (((2 : ℂ)⁻¹ • (LineDeriv.lineDerivOp (1 : ℂ) f +
      Complex.I • LineDeriv.lineDerivOp Complex.I f)) : SchwartzMap ℂ ℂ) x‖ ≤ _
    rw [hd, hadd, hd, norm_smul, show ‖(2 : ℂ)⁻¹‖ = (1/2 : ℝ) by norm_num]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith

private theorem complexDiracDerivatives_polynomialEquiv_mixed_norm
    (f : SchwartzMap ℂ ℂ) (k l : ℕ) (x : ℂ) :
    ‖((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) x‖ ≤
      ‖iteratedFDeriv ℝ (k + l) (f : ℂ → ℂ) x‖ := by
  have hp (op : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ)
      (ho : ∀ (f : SchwartzMap ℂ ℂ) (n : ℕ), ‖iteratedFDeriv ℝ n (op f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖)
      (m n : ℕ) (f : SchwartzMap ℂ ℂ) :
      ‖iteratedFDeriv ℝ n ((op ^ m) f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + m) (f : ℂ → ℂ) x‖ := by
    induction m generalizing n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have h := (ho ((op ^ m) f) n).trans (ih (n + 1))
      rw [show n + 1 + m = n + (m + 1) by omega] at h
      exact h
  have hz := hp schwartzWirtingerZ (fun f n ↦ (complexDiracDerivatives_polynomialEquiv_wirt_norm f n x).1) k 0 ((schwartzWirtingerZBar ^ l) f)
  have hb := hp schwartzWirtingerZBar (fun f n ↦ (complexDiracDerivatives_polynomialEquiv_wirt_norm f n x).2) l k f
  rw [zero_add, norm_iteratedFDeriv_zero] at hz
  exact hz.trans hb

private theorem complexDiracDerivatives_polynomialEquiv_dirac_bound
    (f : SchwartzMap ℂ ℂ) (k l : ℕ) :
    ‖complexDiracDerivative k l f / ((k.factorial * l.factorial : ℂ))‖ ≤
      ‖iteratedFDeriv ℝ (k + l) (f : ℂ → ℂ) 0‖ := by
  change ‖((-1 : ℂ) ^ (k + l) * ((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) 0) /
    ((k.factorial * l.factorial : ℂ))‖ ≤ _
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hf : (1 : ℝ) ≤ (k.factorial : ℝ) * (l.factorial : ℝ) := by
    have hk : (1 : ℝ) ≤ k.factorial := mod_cast k.factorial_pos
    have hl : (1 : ℝ) ≤ l.factorial := mod_cast l.factorial_pos
    nlinarith
  exact (div_le_self (norm_nonneg _) hf).trans (complexDiracDerivatives_polynomialEquiv_mixed_norm f k l 0)

private theorem complexDiracDerivatives_polynomialEquiv_poly_weight
    (d : Fin 2 →₀ ℕ) : d.sum (fun _ n ↦ n) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl), Fin.sum_univ_two]

private theorem complexDiracDerivatives_polynomialEquiv_poly_upper
    (e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
      StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin))
    (hev : ∀ (p : MvPolynomial (Fin 2) ℂ) (g : SchwartzMap ℂ ℂ), e p (complexSchwartzFlatAtOrigin.mkQ g) =
      ∑ d ∈ p.support, p.coeff d * (complexDiracDerivative (d 0) (d 1) g /
        ((d 0).factorial * (d 1).factorial : ℂ)))
    (p : MvPolynomial (Fin 2) ℂ) (N : ℕ) (hdeg : p.totalDegree ≤ N) :
    DistributionOrderLE (fun f : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ ↦
      e p (complexSchwartzFlatAtOrigin.mkQ (f.hasCompactSupport.toSchwartzMap f.contDiff))) N := by
  intro K
  refine ⟨∑ d ∈ p.support, ‖p.coeff d‖, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, fun f _ B _ hf ↦ ?_⟩
  beta_reduce
  rw [hev, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hdN : d 0 + d 1 ≤ N := by
    have h := (MvPolynomial.le_totalDegree hd).trans hdeg
    simpa only [complexDiracDerivatives_polynomialEquiv_poly_weight] using h
  exact (complexDiracDerivatives_polynomialEquiv_dirac_bound _ _ _).trans (hf _ hdN 0)

/-- Shrinking mixed-monomial bumps isolate a coefficient while all lower-order derivatives vanish in norm. -/
private theorem complexDiracDerivatives_polynomialEquiv_poly_lower
    (e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
      StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin))
    (hev : ∀ (p : MvPolynomial (Fin 2) ℂ) (g : SchwartzMap ℂ ℂ), e p (complexSchwartzFlatAtOrigin.mkQ g) =
      ∑ d ∈ p.support, p.coeff d * (complexDiracDerivative (d 0) (d 1) g /
        ((d 0).factorial * (d 1).factorial : ℂ)))
    (p : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hord : DistributionOrderLE (fun f : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ ↦
      e p (complexSchwartzFlatAtOrigin.mkQ (f.hasCompactSupport.toSchwartzMap f.contDiff))) N) :
    p.totalDegree ≤ N := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro d hd
  rw [complexDiracDerivatives_polynomialEquiv_poly_weight]
  by_contra hdn
  have hn : N < d 0 + d 1 := by omega
  have hpd : p.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hpd' : 0 < ‖p.coeff d‖ := norm_pos_iff.mpr hpd
  let K0 : Compacts ℂ := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
  obtain ⟨C, hC0, hC⟩ := hord K0
  obtain ⟨G, hG, hscale⟩ := complexSchwartzTaylor_equiv_bump (d 0) (d 1)
  let A : ℝ := ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j G
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  let ε : ℝ := min 1 (‖p.coeff d‖ / (2 * (C * A + 1)))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (2 * (C * A + 1)) ≤ ‖p.coeff d‖ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨ψ, hψ, hjets⟩ := hscale ε hε
  have hψsupp : tsupport (ψ : ℂ → ℂ) ⊆ Metric.closedBall 0 1 := by
    refine closure_minimal (fun z hz ↦ ?_) Metric.isClosed_closedBall
    rw [mem_support, hψ] at hz
    have hzG : ε⁻¹ • z ∈ tsupport (G : ℂ → ℂ) := subset_tsupport _ (right_ne_zero_of_mul hz)
    have hb := hG hzG
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hε, inv_mul_le_iff₀ hε, mul_one] at hb
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hb.trans hε1
  have hψc : HasCompactSupport (ψ : ℂ → ℂ) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _) hψsupp
  let φ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ := ⟨ψ, ψ.smooth ⊤, hψc, by simp⟩
  have hφ : φ.hasCompactSupport.toSchwartzMap φ.contDiff = ψ := by ext; rfl
  have hbound := hC φ hψsupp (ε * A) (by positivity) fun j hj z ↦ by
    change ‖iteratedFDeriv ℝ j (ψ : ℂ → ℂ) z‖ ≤ ε * A
    have h1 : ‖iteratedFDeriv ℝ j (ψ : ℂ → ℂ) z‖ ≤ SchwartzMap.seminorm ℂ 0 j ψ := by
      simpa using SchwartzMap.le_seminorm ℂ 0 j ψ z
    have h2 := complexSchwartzTaylor_equiv_scaled G ψ (d 0 + d 1) j 0 hG ε hε hε1 (by omega) hψ
    have h3 : SchwartzMap.seminorm ℂ 0 j G ≤ A :=
      Finset.single_le_sum (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hε.le))
  beta_reduce at hbound
  rw [hφ, hev] at hbound
  have hjet (q : Fin 2 →₀ ℕ) : complexDiracDerivative (q 0) (q 1) ψ /
      ((q 0).factorial * (q 1).factorial : ℂ) = if q = d then (-1 : ℂ) ^ (d 0 + d 1) else 0 := by
    change ((-1 : ℂ) ^ (q 0 + q 1) * ((schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) ψ)) 0) / _ = _
    rw [hjets]
    by_cases h : q = d
    · subst q
      simp only [↓reduceIte, and_self]
      rw [mul_div_assoc, div_self (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d 0))
        (by exact_mod_cast Nat.factorial_ne_zero (d 1))), mul_one]
    · have he : ¬ (q 0 = d 0 ∧ q 1 = d 1) := by
        rintro ⟨h0, h1⟩
        apply h
        ext i
        fin_cases i <;> assumption
      simp [he, h]
  have hsum : ∑ q ∈ p.support, p.coeff q * (complexDiracDerivative (q 0) (q 1) ψ /
      ((q 0).factorial * (q 1).factorial : ℂ)) = p.coeff d * (-1 : ℂ) ^ (d 0 + d 1) := by
    simp_rw [hjet]
    rw [Finset.sum_eq_single d]
    · simp
    · intro q hq hqd
      simp [hqd]
    · exact fun h ↦ False.elim (h hd)
  rw [hsum, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one] at hbound
  have hCA : 0 ≤ C * (ε * A) := by positivity
  nlinarith
end ComplexPolynomialDualHelpers

-- TODO(paper-gap): The coefficient seminorms in (5.3.2.12) give the coefficientwise
-- topology on the whole polynomial space and do not give its finest locally convex topology.

/-- Paper: Theorem 5.3.2.5(1), p. 246.
Polynomials in two variables with the finest locally convex topology identify with the strong
dual of the complex flat quotient through factorial-normalized mixed Dirac derivatives.
The least order bound of the distribution is the polynomial's total degree.
Deviation: Uses the finest locally convex topology and omits the false equivalence in
(5.3.2.12). -/
theorem complexDiracDerivatives_polynomialEquiv :
    ∃ e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
        StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin),
      (∀ s : Fin 2 →₀ ℕ, ∀ f : 𝓢(ℂ, ℂ),
        e (MvPolynomial.monomial s 1) (complexSchwartzFlatAtOrigin.mkQ f) =
          complexDiracDerivative (s 0) (s 1) f /
            ((s 0).factorial * (s 1).factorial : ℂ)) ∧
      ∀ (p : MvPolynomial (Fin 2) ℂ) (N : ℕ),
        DistributionOrderLE
          (fun f : 𝒟ℂ ↦ e p (complexSchwartzFlatAtOrigin.mkQ
            (f.hasCompactSupport.toSchwartzMap f.contDiff))) N ↔ p.totalDegree ≤ N := by
  obtain ⟨e,he⟩ := complexDiracDerivatives_polynomialEquiv_poly_topology
  have hcf (d : Fin 2 →₀ ℕ) (f : SchwartzMap ℂ ℂ) :
      (-1 : ℂ)^(d 0+d 1) * MvPowerSeries.coeff d
        (complexSchwartzTaylor_equiv.choose (complexSchwartzFlatAtOrigin.mkQ f)) =
      complexDiracDerivative (d 0) (d 1) f / ((d 0).factorial * (d 1).factorial : ℂ) := by
    rw [complexSchwartzTaylor_equiv.choose_spec]
    change (-1 : ℂ)^(d 0+d 1) *
      (((schwartzWirtingerZ^(d 0)) ((schwartzWirtingerZBar^(d 1)) f)) 0 /
        ((d 0).factorial * (d 1).factorial : ℂ)) =
      ((-1 : ℂ)^(d 0+d 1) * ((schwartzWirtingerZ^(d 0)) ((schwartzWirtingerZBar^(d 1)) f)) 0) /
        ((d 0).factorial * (d 1).factorial : ℂ)
    ring
  have hev (p : MvPolynomial (Fin 2) ℂ) (f : SchwartzMap ℂ ℂ) :
      e p (complexSchwartzFlatAtOrigin.mkQ f) =
      ∑ d ∈ p.support, p.coeff d * (complexDiracDerivative (d 0) (d 1) f /
        ((d 0).factorial * (d 1).factorial : ℂ)) := by
    rw [he]
    exact Finset.sum_congr rfl fun d _ ↦ by rw [mul_assoc, hcf]
  refine ⟨e, ?_, fun p N ↦ ⟨complexDiracDerivatives_polynomialEquiv_poly_lower e hev p N, complexDiracDerivatives_polynomialEquiv_poly_upper e hev p N⟩⟩
  intro s f
  rw [hev]
  simp [MvPolynomial.support_monomial, MvPolynomial.coeff_monomial]

end ComplexOrigin

end RiemannMasullo
