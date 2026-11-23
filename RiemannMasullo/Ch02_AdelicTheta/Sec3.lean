module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1

import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# S-local adelic theta functions

Masullo, §2.3, pp. 98–106. As in §A.1.5, the place set is represented by
its finite part from Notation 2.3.1.1. All archimedean places are included
in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Uₛ" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)
local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "normℝ" => fun (g : Iₛ) ↦ valueℝ (sIdeleNorm F S g)
local notation "thetaTerm" => fun (f : ℬₛ) (ξ : Uₛ) (g : Iₛ) ↦
  f (Multiplicative.ofAdd (Units.val (unitAtS ξ * g)))
local notation "thetaSum" => fun (f : ℬₛ) (g : Iₛ) ↦ ∑' ξ : Uₛ, thetaTerm f ξ g

/-! ## S-local theta operators -/

section Summability

open scoped Classical

local notation "A∞" => mixedEmbedding.mixedSpace F
set_option quotPrecheck false in
local notation "Aᶠₛ" => (∀ v : S, HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "arch" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "sDiagonal" =>
  RingHom.comp (RingHom.comp (adeleProjection F S) (Subring.subtype (integralAdelesOutside F S)))
    (integralAdeleDiagonal F S)

omit [NumberField F] in
/-- The real and complex coordinates give a topological embedding of the infinite adeles. -/
private theorem isEmbedding_thetaArch : IsEmbedding (arch : InfiniteAdeleRing F → A∞) := by
  let e : InfiniteAdeleRing F ≃ₜ A∞ :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans <|
      Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex)))
  exact e.isEmbedding

/-- A compact set of finite S-adeles fits in a compact additive subgroup. -/
private theorem finiteSAdele_exists_compact_addSubgroup (C : Set Aᶠₛ) (hC : IsCompact C) :
    ∃ H : AddSubgroup Aᶠₛ, IsCompact (H : Set Aᶠₛ) ∧ C ⊆ H := by
  classical
  have hBound (v : S) : ∃ r : ℝ, ∀ x ∈ C, ‖x v‖ ≤ r :=
    hC.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  choose r hr using hBound
  let H : AddSubgroup Aᶠₛ :=
    { carrier := {x | ∀ v, ‖x v‖ ≤ max (r v) 0}
      zero_mem' := fun v ↦ by simp
      add_mem' := fun hx hy v ↦
        (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx v) (hy v))
      neg_mem' := fun hx v ↦ by simpa only [Pi.neg_apply, norm_neg] using hx v }
  refine ⟨H, ?_, fun x hx v ↦ (hr v x hx).trans (le_max_left _ _)⟩
  change IsCompact {x : Aᶠₛ | ∀ v, ‖x v‖ ≤ max (r v) 0}
  let balls (v : S) := Metric.closedBall (0 : v.val.adicCompletion F) (max (r v) 0)
  have heq : {x : Aᶠₛ | ∀ v, ‖x v‖ ≤ max (r v) 0} = Set.univ.pi balls := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, balls,
      Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact isCompact_univ_pi fun v ↦ by
    let := properSpace_adicCompletion v.val (K := F)
    exact isCompact_closedBall _ _

/-- Restricting the finite coordinates of diagonal S-integers to a compact additive
subgroup puts their archimedean images in a discrete integral lattice. -/
private theorem sInteger_arch_discrete_lattice (H : AddSubgroup Aᶠₛ)
    (hH : IsCompact (H : Set Aᶠₛ)) :
    ∃ L : Submodule ℤ A∞, DiscreteTopology L ∧
      ∀ x : (S : Set (HeightOneSpectrum (𝓞 F))).integer F,
        (sDiagonal x).2 ∈ H → arch (sDiagonal x).1 ∈ L := by
  let d := sDiagonal
  let D := d.toAddMonoidHom.range
  obtain ⟨_, hClosed, hDiscrete, _⟩ := sAdele_additive_quotient F S
  let l : InfiniteAdeleRing F × H → Aₛ := fun x ↦ (x.1, x.2.val)
  have hl : Continuous l := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hli : Injective l := fun _ _ h ↦
    Prod.ext (congrArg (Prod.fst : Aₛ → _) h) (Subtype.ext (congrArg (Prod.snd : Aₛ → _) h))
  let D' : Set (InfiniteAdeleRing F × H) := l ⁻¹' (D : Set Aₛ)
  have hD' : IsClosed D' := hClosed.preimage hl
  have : DiscreteTopology D' := isDiscrete_iff_discreteTopology.mp
    (hDiscrete.preimage hl.continuousOn hli)
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  -- Projection away from the compact finite factor is closed.
  let p : D' → InfiniteAdeleRing F := fun x ↦ x.val.1
  have hp : IsClosedEmbedding p := .of_continuous_injective_isClosedMap
    (continuous_fst.comp continuous_subtype_val) (by
      intro x y hxy
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have hab : a = b := Subtype.ext ((algebraMap F w.Completion).injective
        (show algebraMap F w.Completion a.val = algebraMap F w.Completion b.val from
          ((congrArg (fun z : Aₛ ↦ z.1 w) ha).trans
            ((congrFun hxy w).trans (congrArg (fun z : Aₛ ↦ z.1 w) hb).symm))))
      exact Subtype.ext (hli (ha.symm.trans (hab ▸ hb))))
    (isClosedMap_fst_of_compactSpace.comp hD'.isClosedMap_subtype_val)
  let L := ((D ⊓ H.comap (AddMonoidHom.snd _ _)).map
    ((arch).toAddMonoidHom.comp (AddMonoidHom.fst _ _))).toIntSubmodule
  refine ⟨L, ?_, fun x hx ↦ ⟨d x, ⟨⟨x, rfl⟩, hx⟩, rfl⟩⟩
  have hRange : Set.range (arch ∘ p) = (L : Set A∞) := by
    ext z
    constructor
    · rintro ⟨⟨⟨a, b⟩, h⟩, rfl⟩
      exact ⟨(a, b.val), ⟨h, b.property⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨h, hb⟩, rfl⟩
      exact ⟨⟨(a, ⟨b, hb⟩), h⟩, rfl⟩
  exact SetLike.isDiscrete_iff_discreteTopology.mp
    (hRange ▸ ((isEmbedding_thetaArch F).comp hp.isEmbedding).isInducing.isDiscrete_range)

local notation "Gₛ" => Multiplicative (SAdeleRing F S)

/-- The finite coordinates of an S-adelic stage lie in a compact additive subgroup. -/
private theorem sAdeleStage_exists_compact_finite (a : BruhatStructuralPair Gₛ) :
    ∃ C : Set Aᶠₛ, IsCompact C ∧ ∀ x ∈ a.val.1, (Multiplicative.toAdd x).2 ∈ C := by
  obtain ⟨V, _, hV, hgen⟩ := a.property.2.1
  let p : a.val.1 →* Multiplicative Aᶠₛ :=
    (AddMonoidHom.snd (InfiniteAdeleRing F) Aᶠₛ).toMultiplicative.comp a.val.1.subtype
  have hp : Continuous p := continuous_snd.comp continuous_subtype_val
  obtain ⟨H, hH, hVH⟩ :=
    finiteSAdele_exists_compact_addSubgroup F S (Multiplicative.toAdd '' (p '' V))
      ((hV.image hp).image continuous_toAdd)
  have hle : Subgroup.closure V ≤ H.toSubgroup.comap p :=
    (Subgroup.closure_le _).2 fun x hx ↦ hVH ⟨p x, ⟨x, hx, rfl⟩, rfl⟩
  rw [hgen] at hle
  exact ⟨H, hH, fun x hx ↦ hle (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1)))⟩

/-- The compact subgroup of an S-adelic structural pair has zero archimedean projection. -/
private theorem sAdeleStage_arch_eq_zero (a : BruhatStructuralPair Gₛ) :
    ∀ x ∈ OrderDual.ofDual a.val.2, arch (Multiplicative.toAdd x).1 = 0 := by
  let (v : S) : LocallyCompactSpace (v.val.adicCompletion F) :=
    locallyCompactSpace_adicCompletion v.val
  let : LocallyCompactSpace Gₛ := inferInstanceAs (LocallyCompactSpace
    (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Gₛ := inferInstanceAs (T2Space
    (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F)))
  let k := OrderDual.ofDual a.val.2
  have hk := isCompact_lcaDualAnnihilator (lcaAnnihilator k) a.property.2.2.1.2.1
  rw [lcaDualAnnihilator_annihilator k a.property.2.2.1.1] at hk
  let m : Aₛ →+ A∞ := (arch).toAddMonoidHom.comp (AddMonoidHom.fst _ _)
  have hm : Continuous m := (isEmbedding_thetaArch F).continuous.comp continuous_fst
  obtain ⟨B, hB⟩ := hk.exists_bound_of_continuousOn
    (hm.comp continuous_toAdd).continuousOn
  intro x hx
  change m x.toAdd = 0
  by_contra h
  have hy : 0 < ‖m x.toAdd‖ := norm_pos_iff.mpr h
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ‖m x.toAdd‖)
  have hn' := hB (x ^ n) (k.pow_mem hx n)
  change ‖m (n • x.toAdd)‖ ≤ B at hn'
  rw [map_nsmul, RCLike.norm_nsmul ℝ, nsmul_eq_mul] at hn'
  exact (not_lt_of_ge hn') ((div_lt_iff₀ hy).mp hn)

/-- A descended continuous additive coordinate has the decay of a Schwartz stage. -/
private theorem stage_exists_decay {G V : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (N : ℕ) (m : G →* Multiplicative V) (hm : Continuous m)
    (hk : OrderDual.ofDual a.val.2 ≤ m.ker) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : G, ‖schwartzBruhatStageRealization a e s x‖ *
      ‖(m x).toAdd‖ ^ N ≤ B := by
  classical
  let l := m.comp a.val.1.subtype
  have hker : (OrderDual.ofDual a.val.2).comap a.val.1.subtype ≤ l.ker :=
    fun x hx ↦ hk hx
  let p : a.quotient →* Multiplicative V := QuotientGroup.lift _ l hker
  have hp : Continuous p := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (hm.comp continuous_subtype_val)
  let P : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor →+ V :=
    (p.comp e.equiv.symm.toMonoidHom).toAdditive
  have hP : Continuous P :=
    continuous_toAdd.comp (hp.comp (e.equiv.symm.continuous.comp continuous_ofAdd))
  obtain ⟨A, B, hA, hAB⟩ := elementary_additive_norm_le P hP P.map_add
  obtain ⟨C, hC⟩ := elementarySchwartz_decay s.property N
  have hB : 0 ≤ (1 + A + max B 0) ^ N * max C 0 := by positivity
  refine ⟨_, hB, fun x ↦ ?_⟩
  by_cases hx : x ∈ a.val.1
  · rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    let q : a.quotient := QuotientGroup.mk ⟨x, hx⟩
    let w := Multiplicative.toAdd (e.equiv q)
    have hw : P w = (m x).toAdd := by
      change (p (e.equiv.symm (e.equiv q))).toAdd = _
      rw [e.equiv.symm_apply_apply]
      rfl
    change ‖s w‖ * ‖(m x).toAdd‖ ^ N ≤ _
    have hbound := hAB w
    rw [hw] at hbound
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (le_add_of_nonneg_left zero_le_one) _) (norm_nonneg (s w))).trans ?_
    exact real_decay_aux (norm_nonneg _)
      (add_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)) hA (norm_nonneg _) hbound (hC w)
  · simpa only [schwartzBruhatStageRealization_apply, dite_eq_right hx, norm_zero, zero_mul] using hB

/-- The elementary Schwartz bounds control every archimedean norm power on an S-adelic stage. -/
private theorem sAdeleStage_exists_arch_decay (a : BruhatStructuralPair Gₛ)
    (e : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage e) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Aₛ,
      ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd x)‖ * ‖arch x.1‖ ^ N ≤ B := by
  let m : Gₛ →* Multiplicative A∞ :=
    ((arch).toAddMonoidHom.comp (AddMonoidHom.fst _ _)).toMultiplicative
  have hm : Continuous m := (isEmbedding_thetaArch F).continuous.comp continuous_fst
  exact stage_exists_decay a e s N m hm (sAdeleStage_arch_eq_zero F S a)


/-- Compact support in one coordinate and polynomial bounds persist under the sums of
stage realizations that generate the Schwartz–Bruhat submodule. -/
private theorem schwartzBruhat_exists_coordinate_bounds {G T : Type*} [CommGroup G]
    [TopologicalSpace G] [TopologicalSpace T] (pr : G → T) (size : G → ℝ)
    (hsize : ∀ x, 0 ≤ size x)
    (hsupp : ∀ a : BruhatStructuralPair G, ∃ C : Set T, IsCompact C ∧
      ∀ x ∈ a.val.1, pr x ∈ C)
    (hdecay : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (s : SchwartzBruhatStage e) (N : ℕ), ∃ B : ℝ, 0 ≤ B ∧
        ∀ x, ‖schwartzBruhatStageRealization a e s x‖ * size x ^ N ≤ B)
    (f : SchwartzBruhat G) :
    ∃ C : Set T, IsCompact C ∧ (∀ x, pr x ∉ C → f x = 0) ∧
      ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ * size x ^ N ≤ B := by
  classical
  let P (g : G → ℂ) : Prop :=
    ∃ C : Set T, IsCompact C ∧ (∀ x, pr x ∉ C → g x = 0) ∧
      ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖g x‖ * size x ^ N ≤ B
  have hzero : P 0 := ⟨∅, isCompact_empty, fun _ _ ↦ rfl, fun _ ↦ ⟨0, le_rfl, by simp⟩⟩
  have hadd : ∀ g h, P g → P h → P (g + h) := by
    rintro g h ⟨C, hC, hg, hCg⟩ ⟨D, hD, hh, hDh⟩
    refine ⟨C ∪ D, hC.union hD, fun x hx ↦ ?_, fun N ↦ ?_⟩
    · simp [hg x (fun h ↦ hx (Or.inl h)), hh x (fun h ↦ hx (Or.inr h))]
    · obtain ⟨B, hB, hBg⟩ := hCg N
      obtain ⟨E, hE, hEh⟩ := hDh N
      refine ⟨B + E, add_nonneg hB hE, fun x ↦ ?_⟩
      change ‖g x + h x‖ * size x ^ N ≤ B + E
      refine (mul_le_mul_of_nonneg_right (norm_add_le (g x) (h x)) (pow_nonneg (hsize x) N)).trans ?_
      rw [add_mul]
      exact add_le_add (hBg x) (hEh x)
  let fs : schwartzBruhatSubmodule G := f
  change P fs.val
  refine Submodule.iSup_induction (motive := P) _ fs.property ?_ hzero hadd
  intro a g hg
  refine Submodule.iSup_induction (motive := P) _ hg ?_ hzero hadd
  intro e g hg
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hg
  obtain ⟨C, hC, hCa⟩ := hsupp a
  refine ⟨C, hC, fun x hx ↦ ?_, hdecay a e s⟩
  rw [schwartzBruhatStageRealization_apply, dite_eq_right (fun hy ↦ hx (hCa x hy))]

/-- Paper: Proof of Proposition 2.3.1.2(1), pp. 100–102. This bound for the
S-unit series applies to an individual S-adelic Schwartz–Bruhat function. The function vanishes
outside a compact set of finite coordinates, and its absolute value times any nonnegative
integer power of the archimedean norm is bounded on the whole S-adele ring. -/
theorem sAdeleSchwartz_exists_decay_bound (f : ℬₛ) :
    ∃ C : Set Aᶠₛ, IsCompact C ∧
      (∀ x : Aₛ, x.2 ∉ C → f (Multiplicative.ofAdd x) = 0) ∧
      ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ x : Aₛ, ‖f (Multiplicative.ofAdd x)‖ * ‖arch x.1‖ ^ N ≤ B :=
  schwartzBruhat_exists_coordinate_bounds (fun x : Gₛ ↦ x.toAdd.2)
    (fun x ↦ ‖arch x.toAdd.1‖) (fun _ ↦ norm_nonneg _)
    (sAdeleStage_exists_compact_finite F S) (sAdeleStage_exists_arch_decay F S) f

/-- On a compact set of S-ideles, archimedean dilation preserving the finite
coordinates admits a single summable majorant even after weighting by a power of the dilation. -/
private theorem sLocalAdelicTheta_exists_dilation_bound (f : ℬₛ) (p : ℕ)
    (K : Set Iₛ) (hK : IsCompact K) :
    ∃ u : Uₛ → ℝ, Summable u ∧
      ∀ (ξ : Uₛ) (g : Iₛ), g ∈ K → ∀ (r : ℝ), 1 ≤ r → ∀ (y : Aₛ),
        y.2 = (unitAtS ξ * g).val.2 →
        ‖arch y.1‖ = r * ‖arch (unitAtS ξ * g).val.1‖ →
        ‖f (Multiplicative.ofAdd y)‖ * r ^ p ≤ u ξ := by
  classical
  obtain ⟨C, hC, hsupport, hdecay⟩ := sAdeleSchwartz_exists_decay_bound F S f
  -- Undo the idele translates on the finite support simultaneously.
  let T : Aᶠₛ × Iₛ → Aᶠₛ := fun p ↦ p.1 * (p.2⁻¹).val.2
  have hT : Continuous T := continuous_fst.mul
    (continuous_snd.comp (Units.continuous_val.comp (continuous_inv.comp continuous_snd)))
  obtain ⟨H, hH, hTH⟩ :=
    finiteSAdele_exists_compact_addSubgroup F S (T '' (C ×ˢ K)) ((hC.prod hK).image hT)
  obtain ⟨L, hL, hmemL⟩ := sInteger_arch_discrete_lattice F S H hH
  let N := Module.finrank ℤ L + 1 + p
  have hN : Module.finrank ℤ L < N := by dsimp [N]; omega
  obtain ⟨B, _, hB⟩ := hdecay N
  let d (ξ : Uₛ) : Aₛ := sDiagonal ξ.val
  let P : Set Uₛ := {ξ | (d ξ).2 ∈ H}
  let toL (ξ : P) : L := ⟨arch (d ξ.val).1, hmemL ξ.val.val ξ.property⟩
  have hToL : Injective toL := by
    intro ξ η h
    have heq := (arch).injective (congrArg Subtype.val h)
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact Subtype.ext (Units.ext (Subtype.ext ((algebraMap F w.Completion).injective
      (congrFun heq w))))
  have hs : Summable (P.indicator (fun ξ ↦ ‖arch (d ξ).1‖⁻¹ ^ N)) := by
    apply summable_subtype_iff_indicator.mp
    change Summable ((fun z : L ↦ ‖z‖⁻¹ ^ N) ∘ toL)
    exact (ZLattice.summable_norm_pow_inv L N hN).comp_injective hToL
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (((isEmbedding_thetaArch F).continuous.comp
      (continuous_fst.comp (Units.continuous_val.comp continuous_inv))).continuousOn :
      ContinuousOn (fun g : Iₛ ↦ arch (g⁻¹).val.1) K)
  let R := max M 1
  have hR : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
  refine ⟨_, hs.mul_left (B * R ^ N), fun ξ g hg r hr y hyfin hyarch ↦ ?_⟩
  let z : Aₛ := (unitAtS ξ * g).val
  have hd : d ξ = z * (g⁻¹).val := by
    change (unitAtS ξ).val = ((unitAtS ξ * g) * g⁻¹).val
    rw [mul_assoc, mul_inv_cancel, mul_one]
  change ‖f (Multiplicative.ofAdd y)‖ * r ^ p ≤
    (B * R ^ N) * P.indicator (fun ξ ↦ ‖arch (d ξ).1‖⁻¹ ^ N) ξ
  by_cases hξ : ξ ∈ P
  · rw [Set.indicator_of_mem hξ, inv_pow, ← div_eq_mul_inv]
    have hpos : 0 < ‖arch (d ξ).1‖ := by
      apply norm_pos_iff.mpr
      exact (Units.map ((arch).toMonoidHom.comp (RingHom.fst _ _).toMonoidHom)
        (unitAtS ξ)).ne_zero
    apply (le_div_iff₀ (pow_pos hpos _)).mpr
    have hnorm : ‖arch (d ξ).1‖ ≤ ‖arch z.1‖ * R := by
      rw [hd, Prod.fst_mul, map_mul]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ((hM g hg).trans (le_max_left _ _)) (norm_nonneg _))
    have hpN : p ≤ N := Nat.le_add_left _ _
    have hdilation : r ^ p * ‖arch (d ξ).1‖ ^ N ≤ ‖arch y.1‖ ^ N * R ^ N := by
      rw [hyarch, mul_pow, mul_assoc, ← mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ hr hpN)
        (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (pow_nonneg (norm_nonneg _) _)
        (pow_nonneg (zero_le_one.trans hr) _)
    calc
      (‖f (Multiplicative.ofAdd y)‖ * r ^ p) * ‖arch (d ξ).1‖ ^ N
          = ‖f (Multiplicative.ofAdd y)‖ * (r ^ p * ‖arch (d ξ).1‖ ^ N) := mul_assoc _ _ _
      _ ≤ ‖f (Multiplicative.ofAdd y)‖ * (‖arch y.1‖ ^ N * R ^ N) :=
        mul_le_mul_of_nonneg_left hdilation (norm_nonneg _)
      _ ≤ B * R ^ N := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hB y) (pow_nonneg hR _)
  · have hyC : y.2 ∉ C := by
      intro h
      apply hξ
      change (d ξ).2 ∈ H
      rw [hd]
      refine hTH ⟨(y.2, g), ⟨h, hg⟩, ?_⟩
      change y.2 * (g⁻¹).val.2 = z.2 * (g⁻¹).val.2
      rw [hyfin]
    rw [hsupport y hyC, norm_zero, zero_mul, Set.indicator_of_notMem hξ, mul_zero]

/-- Paper: Proposition 2.3.1.2(1), p. 100. On a compact set of S-ideles, the
norms of the S-unit summands are bounded by a common summable family. -/
theorem sLocalAdelicTheta_exists_summable_bound (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    ∃ u : Uₛ → ℝ, Summable u ∧ ∀ ξ g, g ∈ K → ‖thetaTerm f ξ g‖ ≤ u ξ := by
  obtain ⟨u, hu, hle⟩ := sLocalAdelicTheta_exists_dilation_bound F S f 0 K hK
  exact ⟨u, hu, fun ξ g hg ↦ by
    simpa only [pow_zero, mul_one] using hle ξ g hg 1 le_rfl (unitAtS ξ * g).val rfl
      (one_mul _).symm⟩

/-- Paper: Proposition 2.3.1.2(1), p. 100. The series of norms of the
S-unit translates is summable uniformly on each compact set of S-ideles. -/
theorem sLocalAdelicTheta_summableUniformlyOn_norm (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    SummableUniformlyOn (fun (ξ : Uₛ) (g : Iₛ) ↦ ‖thetaTerm f ξ g‖) K := by
  obtain ⟨u, hu, hle⟩ := sLocalAdelicTheta_exists_summable_bound F S f K hK
  exact summableUniformlyOn_of_ge hu fun ξ g hg ↦ by simpa only [norm_norm] using hle ξ g hg

end Summability

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit series converges
uniformly to its sum on each compact set of S-ideles. -/
theorem sLocalAdelicTheta_hasSumUniformlyOn (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    HasSumUniformlyOn (thetaTerm f) (thetaSum f) K := by
  obtain ⟨u, hu, hle⟩ := sLocalAdelicTheta_exists_summable_bound F S f K hK
  exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr (tendstoUniformlyOn_tsum hu hle)

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit sum is a continuous
function of the S-idele. -/
theorem sLocalAdelicTheta_continuous (f : ℬₛ) : Continuous (thetaSum f) := by
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have hsum : HasSumLocallyUniformly (thetaTerm f) (thetaSum f) :=
    hasSumLocallyUniformly_of_forall_compact (sLocalAdelicTheta_hasSumUniformlyOn F S f)
  have hterm (ξ : Uₛ) : Continuous (thetaTerm f ξ) :=
    (continuous_schwartzBruhat_apply f).comp (continuous_ofAdd.comp
      (Units.continuous_val.comp (continuous_const (y := unitAtS ξ) |>.mul continuous_id)))
  exact hsum.continuous
    (Eventually.of_forall fun t ↦ continuous_finsetSum t fun ξ _ ↦ hterm ξ).frequently

/-- Paper: Definition 2.3.1.1, p. 99. Forming the continuous S-unit sum
is complex linear in the test function. -/
theorem sLocalAdelicTheta_isLinear :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨thetaSum f, sLocalAdelicTheta_continuous F S f⟩ : C(Iₛ, ℂ))) :=
  by
  have hs : ∀ (f : ℬₛ) (x : Iₛ), Summable fun ξ : Uₛ ↦ thetaTerm f ξ x := fun f x ↦
    ((sLocalAdelicTheta_hasSumUniformlyOn F S f {x} isCompact_singleton).hasSum rfl).summable
  refine ⟨fun f g ↦ ContinuousMap.ext fun x ↦ ?_, fun c f ↦ ContinuousMap.ext fun x ↦ ?_⟩
  · exact (tsum_congr fun ξ ↦ rfl).trans ((hs f x).tsum_add (hs g x))
  · exact (tsum_congr fun ξ ↦ rfl).trans (tsum_mul_left (a := c) (f := fun ξ ↦ thetaTerm f ξ x))

/-- Paper: Definition 2.3.1.1, p. 99. The S-local theta operator sums the
test function over the diagonal S-unit multiples of each S-idele. -/
def sLocalAdelicTheta : ℬₛ →ₗ[ℂ] C(Iₛ, ℂ) :=
  IsLinearMap.mk' _ (sLocalAdelicTheta_isLinear F S)

/-- Paper: Equation (2.3.1.2), p. 99. Evaluating S-local theta at an idele
gives the sum of the evaluations at its S-unit multiples. -/
theorem sLocalAdelicTheta_apply (f : ℬₛ) (g : Iₛ) :
    sLocalAdelicTheta F S f g = thetaSum f g := rfl

/-- Paper: Proposition 2.3.1.2(1), p. 100. S-local theta is invariant under
left translation by S-units, expressed as constancy on each class fiber. -/
theorem sLocalAdelicTheta_factorsThrough (f : ℬₛ) :
    FactorsThrough (sLocalAdelicTheta F S f) classOf := by
  intro a b hab
  have h := QuotientGroup.eq.mp hab
  rw [MonoidHom.map_range, MonoidHom.mem_range] at h
  obtain ⟨u, hu⟩ := h
  refine Eq.trans ?_ (congrArg (sLocalAdelicTheta F S f) (inv_mul_eq_iff_eq_mul.mp hu.symm)).symm
  change ∑' ξ : Uₛ, thetaTerm f ξ a = ∑' ξ : Uₛ, thetaTerm f ξ (a * unitAtS u)
  refine ((Equiv.mulRight u).tsum_eq (fun ξ ↦ thetaTerm f ξ a)).symm.trans (tsum_congr fun ξ ↦ ?_)
  change f (Multiplicative.ofAdd (Units.val (unitAtS (ξ * u) * a))) =
    f (Multiplicative.ofAdd (Units.val (unitAtS ξ * (a * unitAtS u))))
  rw [map_mul, mul_assoc, mul_comm (unitAtS u) a]

/-- Paper: Proposition 2.3.1.2(1), p. 100. The S-unit invariant theta
function descends to a continuous function on the S-idele classes. -/
def sLocalAdelicThetaOnClasses (f : ℬₛ) : C(Jₛ, ℂ) :=
  IsQuotientMap.lift (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk _) (sLocalAdelicTheta F S f)
    (sLocalAdelicTheta_factorsThrough F S f)

/-- Paper: Proposition 2.3.1.2(1), p. 100. The descended function at the
class of an S-idele agrees with theta at that S-idele. -/
theorem sLocalAdelicThetaOnClasses_mk (f : ℬₛ) (g : Iₛ) :
    sLocalAdelicThetaOnClasses F S f (classOf g) = sLocalAdelicTheta F S f g :=
  DFunLike.congr_fun (IsQuotientMap.lift_comp (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk _) (sLocalAdelicTheta F S f)
    (sLocalAdelicTheta_factorsThrough F S f)) g

-- TODO(paper-gap): The support argument before (2.3.1.5) bounds only the finite
-- coordinates. On p. 104 the argument also switches to test functions on the
-- finite unit groups, where restrictions of additive test functions need not
-- have compact support.
-- TODO(paper-gap): The equality in (2.3.1.9) assumes that a section of the
-- idelic norm scales the Euclidean sup norm by t. Even at a single complex
-- place a positive-real section scales it by √t.

section LargeNorm

open scoped Classical

local notation "A∞" => mixedEmbedding.mixedSpace F
local notation "arch" => InfiniteAdeleRing.ringEquiv_mixedSpace F
set_option quotPrecheck false in
local notation "τ" => (Units.map (adeleProjection F S).toMonoidHom).comp
  (canonicalIdeleNormSection F)
local notation "degree" => Module.finrank ℚ F
local notation "root" => fun t : ℝ≥0ˣ ↦ (valueℝ t) ^ (degree : ℝ)⁻¹

/-- The projected canonical section has S-idelic norm equal to its input. -/
private theorem thetaSection_rightInverse (t : ℝ≥0ˣ) : sIdeleNorm F S (τ t) = t := by
  let A := integralAdelesOutside F S
  let s := canonicalIdeleNormSection F
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    change (canonicalIdeleNormSection F u).val.2 v ∈ v.adicCompletionIntegers F
    rw [canonicalIdeleNormSection_finite F u]
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units := by
    refine ⟨hmem t, ?_⟩
    change ((s t)⁻¹).val ∈ A
    rw [← map_inv]
    exact hmem t⁻¹
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (canonicalIdeleNormSection_rightInverse F t)

/-- The canonical section acts by the same positive scalar at every infinite place. -/
private theorem thetaSection_arch (t : ℝ≥0ˣ) (x : InfiniteAdeleRing F) :
    arch (x * (τ t).val.1) = root t • arch x := by
  have h : arch (τ t).val.1 = root t • (1 : A∞) := by
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    apply Prod.ext <;> funext v
    · apply Complex.ofReal_injective
      rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      change InfinitePlace.Completion.extensionEmbedding v.val
        ((canonicalIdeleNormSection F t).val.1 v) = ((root t * 1 : ℝ) : ℂ)
      rw [mul_one]
      exact canonicalIdeleNormSection_infinite F t v
    · change InfinitePlace.Completion.extensionEmbedding v.val
        ((canonicalIdeleNormSection F t).val.1 v) = (root t : ℂ) * 1
      rw [mul_one]
      exact canonicalIdeleNormSection_infinite F t v
  rw [map_mul, h, mul_smul_comm, mul_one]

/-- The norm-one S-idele classes are covered by the image of a compact set of S-ideles. -/
private theorem exists_compact_lifts_normOne :
    ∃ K : Set Iₛ, IsCompact K ∧
      ∀ c : Jₛ, sIdeleQuotientNorm F S c = 1 → ∃ k ∈ K, classOf k = c := by
  let q : Iₛ → Jₛ := classOf
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  choose K hK hKi using (fun k : Iₛ ↦ exists_compact_mem_nhds k)
  have hc : IsCompact (sIdeleQuotientNorm F S ⁻¹' {1}) :=
    (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton
  have hcover : (sIdeleQuotientNorm F S ⁻¹' {1}) ⊆ ⋃ k, q '' interior (K k) := by
    intro c _
    obtain ⟨k, rfl⟩ := hq.surjective c
    exact Set.mem_iUnion.mpr ⟨k, k, mem_interior_iff_mem_nhds.mpr (hKi k), rfl⟩
  obtain ⟨E, hE⟩ := hc.elim_finite_subcover _ (fun _ ↦ hq.isOpenMap _ isOpen_interior) hcover
  refine ⟨⋃ k ∈ E, K k, E.isCompact_biUnion fun k _ ↦ hK k, fun c hc ↦ ?_⟩
  obtain ⟨k, hk, x, hx, rfl⟩ := Set.mem_iUnion₂.mp (hE hc)
  exact ⟨x, Set.mem_iUnion₂.mpr ⟨k, hk, interior_subset hx⟩, rfl⟩

/-- The weighted summable majorant applies to the field-degree root dilation. -/
private theorem sLocalAdelicTheta_exists_scaled_bound (f : ℬₛ) (N : ℕ)
    (K : Set Iₛ) (hK : IsCompact K) :
    ∃ u : Uₛ → ℝ, Summable u ∧ ∀ ξ k, k ∈ K → ∀ t : ℝ≥0ˣ, 1 ≤ valueℝ t →
      ‖thetaTerm f ξ (k * τ t)‖ * (valueℝ t) ^ N ≤ u ξ := by
  obtain ⟨u, hu, hle⟩ := sLocalAdelicTheta_exists_dilation_bound F S f (degree * N) K hK
  refine ⟨u, hu, fun ξ k hk t ht ↦ ?_⟩
  have hr : 1 ≤ root t := Real.one_le_rpow ht (by positivity)
  have hpow : root t ^ (degree * N) = valueℝ t ^ N := by
    rw [pow_mul, Real.rpow_inv_natCast_pow (zero_le_one.trans ht)
      (Module.finrank_pos (R := ℚ) (M := F)).ne']
  let y : Aₛ := (unitAtS ξ * (k * τ t)).val
  let z : Aₛ := (unitAtS ξ * k).val
  have hy : y = z * (τ t).val := by
    change (unitAtS ξ * (k * τ t)).val = ((unitAtS ξ * k) * τ t).val
    rw [mul_assoc]
  have hfin : (τ t).val.2 = 1 := by
    funext v
    change (canonicalIdeleNormSection F t).val.2 v = 1
    rw [canonicalIdeleNormSection_finite]
    rfl
  have hyfin : y.2 = z.2 := by rw [hy, Prod.snd_mul, hfin, mul_one]
  have hyarch : ‖arch y.1‖ = root t * ‖arch z.1‖ := by
    rw [hy, Prod.fst_mul, thetaSection_arch, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hr)]
  rw [← hpow]
  exact hle ξ k hk (root t) hr y hyfin hyarch

/-- Paper: Proposition 2.3.1.2(2), p. 100. As the S-idelic norm tends
to infinity, S-local theta decays at every positive inverse power. -/
theorem sLocalAdelicTheta_decay_large (f : ℬₛ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : Iₛ, T < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  clear hN
  refine Exists.elim (exists_compact_lifts_normOne F S) ?_
  intro K hK
  refine Exists.elim (sLocalAdelicTheta_exists_scaled_bound F S f N K hK.1) ?_
  intro u hu
  refine ⟨max (∑' ξ, u ξ) 1, 1, zero_lt_one.trans_le (le_max_right _ _), zero_lt_one, ?_⟩
  intro g hg
  let t := sIdeleNorm F S g
  let s := τ t
  let a := g / s
  have ha : sIdeleQuotientNorm F S (classOf a) = 1 := by
    rw [sIdeleQuotientNorm_mk]
    change sIdeleNorm F S (g / s) = 1
    rw [map_div, thetaSection_rightInverse, div_self']
  refine Exists.elim (hK.2 (classOf a) ha) ?_
  intro k hk
  have hclass : classOf (k * s) = classOf g := by
    rw [QuotientGroup.mk_mul, hk.2, ← QuotientGroup.mk_mul, div_mul_cancel]
  have htheta : sLocalAdelicTheta F S f g = thetaSum f (k * s) :=
    (sLocalAdelicTheta_factorsThrough F S f hclass).symm.trans
      (sLocalAdelicTheta_apply F S f (k * s))
  have hp : 0 < valueℝ t ^ N := pow_pos (zero_lt_one.trans hg) _
  have hle (ξ : Uₛ) : ‖thetaTerm f ξ (k * s)‖ ≤ u ξ * (valueℝ t ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    exact hu.2 ξ k hk.1 t hg.le
  have hb := hu.1.mul_right (valueℝ t ^ N)⁻¹
  have hs := hb.of_nonneg_of_le (fun ξ ↦ norm_nonneg (thetaTerm f ξ (k * s))) hle
  calc
    ‖sLocalAdelicTheta F S f g‖ = ‖thetaSum f (k * s)‖ := congrArg norm htheta
    _ ≤ ∑' ξ, ‖thetaTerm f ξ (k * s)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ξ, u ξ * (valueℝ t ^ N)⁻¹ := hs.tsum_le_tsum hle hb
    _ = (∑' ξ, u ξ) * (valueℝ t ^ N)⁻¹ := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hp.le)

end LargeNorm

section UniformDecay

open scoped Classical

local notation "A∞" => mixedEmbedding.mixedSpace F
set_option quotPrecheck false in
local notation "Aᶠₛ" => (∀ v : S, HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "arch" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "sDiagonal" =>
  RingHom.comp (RingHom.comp (adeleProjection F S) (Subring.subtype (integralAdelesOutside F S)))
    (integralAdeleDiagonal F S)
local notation "Gₛ" => Multiplicative (SAdeleRing F S)

set_option quotPrecheck false in
local notation "radial" => fun t : ℝ≥0ˣ ↦
  Units.map (adeleProjection F S).toMonoidHom (canonicalIdeleNormSection F t)

/-- The norm-one S-idele classes have representatives in one compact set of S-ideles. -/
private theorem sLocalTheta_exists_compact_representatives :
    ∃ K : Set Iₛ, IsCompact K ∧ ∀ c : Jₛ, sIdeleQuotientNorm F S c = 1 →
      ∃ k ∈ K, classOf k = c := by
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have hCompact : IsCompact ((sIdeleQuotientNorm F S) ⁻¹' {1}) :=
    (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton
  choose U hUc hU using fun k : Iₛ ↦ exists_compact_mem_nhds k
  let V (k : Iₛ) := classOf '' interior (U k)
  have hVo (k : Iₛ) : IsOpen (V k) := QuotientGroup.isOpenMap_coe _ isOpen_interior
  have hCover : (sIdeleQuotientNorm F S) ⁻¹' {1} ⊆ ⋃ k, V k := by
    intro c _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective c
    exact mem_iUnion.mpr ⟨k, mem_image_of_mem _ (mem_interior_iff_mem_nhds.mpr (hU k))⟩
  obtain ⟨s, hs⟩ := hCompact.elim_finite_subcover V hVo hCover
  refine ⟨⋃ k : s, U k, isCompact_iUnion (fun k ↦ hUc k), fun c hc ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (show c ∈ (sIdeleQuotientNorm F S) ⁻¹' {1} from hc))
  obtain ⟨hi', k, hk, rfl⟩ := mem_iUnion.mp hi
  exact ⟨k, mem_iUnion.mpr ⟨⟨i, hi'⟩, interior_subset hk⟩, rfl⟩

/-- The projected canonical section has S-idelic norm equal to its parameter. -/
private theorem sLocalTheta_radial_norm (t : ℝ≥0ˣ) : sIdeleNorm F S (radial t) = t := by
  have hinsert : sIdeleInsertion F S (radial t) = canonicalIdeleNormSection F t := by
    obtain ⟨harch, hin, hout⟩ := sIdeleInsertion_apply F S (radial t)
    apply Units.ext
    refine Prod.ext harch (Subtype.ext (funext fun v ↦ ?_))
    by_cases hv : v ∈ S
    · exact hin ⟨v, hv⟩
    · exact (hout v hv).trans
        (congrArg (fun b : FiniteAdeleRing (𝓞 F) F ↦ b v)
          (canonicalIdeleNormSection_finite F t)).symm
  rw [← ideleNorm_sIdeleInsertion, hinsert]
  exact canonicalIdeleNormSection_rightInverse F t

/-- For functions with a fixed compact finite support, the norm-weighted theta estimate
is controlled by a single archimedean decay bound. -/
private theorem sLocalTheta_weighted_bound (C : Set Aᶠₛ) (hC : IsCompact C) (N : ℕ) :
    ∃ (M : ℕ) (D : ℝ), 0 ≤ D ∧
      ∀ (f : ℬₛ) (A : ℝ), 0 ≤ A →
        (∀ x : Aₛ, x.2 ∉ C → f (Multiplicative.ofAdd x) = 0) →
        (∀ x : Aₛ, ‖f (Multiplicative.ofAdd x)‖ * ‖arch x.1‖ ^ M ≤ A) →
          ∀ g : Iₛ, 1 ≤ normℝ g → ‖sLocalAdelicTheta F S f g‖ * (normℝ g) ^ N ≤ D * A := by
  refine (sLocalTheta_exists_compact_representatives F S).elim fun K h ↦ ?_
  have hK := h.1
  have hRep := h.2
  let T : Aᶠₛ × Iₛ → Aᶠₛ := fun p ↦ p.1 * (p.2⁻¹).val.2
  have hT : Continuous T := continuous_fst.mul
    (continuous_snd.comp (Units.continuous_val.comp (continuous_inv.comp continuous_snd)))
  refine (finiteSAdele_exists_compact_addSubgroup F S (T '' (C ×ˢ K))
    ((hC.prod hK).image hT)).elim fun H hH ↦ ?_
  refine (sInteger_arch_discrete_lattice F S H hH.1).elim fun L hL ↦ ?_
  let : DiscreteTopology L := hL.1
  let d := Module.finrank ℚ F
  let M := d * N + Module.finrank ℤ L + 1
  let diag (ξ : Uₛ) : Aₛ := sDiagonal ξ.val
  let P : Set Uₛ := {ξ | (diag ξ).2 ∈ H}
  let toL (ξ : P) : L := ⟨arch (diag ξ.val).1, hL.2 ξ.val.val ξ.property⟩
  have hToL : Injective toL := by
    intro ξ η h
    have heq := (arch).injective (congrArg Subtype.val h)
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact Subtype.ext (Units.ext (Subtype.ext ((algebraMap F w.Completion).injective
      (congrFun heq w))))
  let u := P.indicator (fun ξ ↦ (‖arch (diag ξ).1‖ ^ M)⁻¹)
  have hu : Summable u := by
    apply summable_subtype_iff_indicator.mp
    change Summable ((fun z : L ↦ (‖z‖ ^ M)⁻¹) ∘ toL)
    simpa only [inv_pow] using
      (ZLattice.summable_norm_pow_inv L M (by dsimp [M]; omega)).comp_injective hToL
  have hu₀ : ∀ ξ, 0 ≤ u ξ := indicator_nonneg (fun _ _ ↦ by positivity)
  refine (hK.exists_bound_of_continuousOn
    (((isEmbedding_thetaArch F).continuous.comp
      (continuous_fst.comp (Units.continuous_val.comp continuous_inv))).continuousOn :
      ContinuousOn (fun g : Iₛ ↦ arch (g⁻¹).val.1) K)).elim fun R₀ hR₀ ↦ ?_
  let R := max R₀ 1
  have hR : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
  refine ⟨M, R ^ M * ∑' ξ, u ξ, mul_nonneg (pow_nonneg hR _) (tsum_nonneg hu₀), ?_⟩
  intro f A hA hsupp hdecay g hg
  let t := sIdeleNorm F S g
  let a := radial t
  let q : Iₛ →* Jₛ := QuotientGroup.mk' _
  have haNorm : sIdeleNorm F S a = t := sLocalTheta_radial_norm F S t
  have hnorm : sIdeleQuotientNorm F S (classOf (a⁻¹ * g)) = 1 := by
    rw [sIdeleQuotientNorm_mk, map_mul, map_inv, haNorm]
    exact inv_mul_cancel t
  refine (hRep _ hnorm).elim fun k hk ↦ ?_
  have hq := hk.2
  have hclass : classOf (a * k) = classOf g := by
    change q (a * k) = q g
    rw [map_mul, show q k = q (a⁻¹ * g) from hq, ← map_mul, mul_inv_cancel_left]
  rw [← sLocalAdelicTheta_factorsThrough F S f hclass, sLocalAdelicTheta_apply]
  have hf : Summable (fun ξ : Uₛ ↦ ‖thetaTerm f ξ (a * k)‖) :=
    (sLocalAdelicTheta_summableUniformlyOn_norm F S f {a * k} isCompact_singleton).summable (by rfl)
  refine mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hf) (by positivity) |>.trans ?_
  rw [← tsum_mul_right]
  let r := (t.val : ℝ) ^ (d : ℝ)⁻¹
  have hr : 1 ≤ r := Real.one_le_rpow hg (by positivity)
  have hpow : r ^ (d * N) = (t.val : ℝ) ^ N := by
    have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
    dsimp [r]
    rw [← Real.rpow_mul_natCast t.val.coe_nonneg, ← Real.rpow_natCast,
      Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  have htPow : (t.val : ℝ) ^ N ≤ r ^ M :=
    hpow ▸ pow_le_pow_right₀ hr (by dsimp [M]; omega)
  have hterm (ξ : Uₛ) : ‖thetaTerm f ξ (a * k)‖ * (t.val : ℝ) ^ N ≤ (A * R ^ M) * u ξ := by
    let x : Aₛ := (unitAtS ξ * k).val
    let y : Aₛ := a.val * x
    have hy : (unitAtS ξ * (a * k)).val = y := by
      rw [mul_left_comm (unitAtS ξ) a k]
      rfl
    let fs : schwartzBruhatSubmodule Gₛ := f
    change ‖fs.val (Multiplicative.ofAdd ((unitAtS ξ * (a * k)).val))‖ * (t.val : ℝ) ^ N ≤ _
    rw [hy]
    have hfinite : y.2 = x.2 := by
      have ha : a.val.2 = 1 := by
        funext v
        change (canonicalIdeleNormSection F t).val.2 v.val = 1
        exact congrArg (fun b : FiniteAdeleRing (𝓞 F) F ↦ b v.val)
          (canonicalIdeleNormSection_finite F t)
      change a.val.2 * x.2 = x.2
      rw [ha, one_mul]
    have hdiag : diag ξ = x * (k⁻¹).val := by
      change (unitAtS ξ).val = x * (k⁻¹).val
      rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    by_cases hyC : y.2 ∈ C
    · have hξ : ξ ∈ P := by
        change (diag ξ).2 ∈ H
        rw [hdiag]
        exact hH.2 ⟨(y.2, k), ⟨hyC, hk.1⟩, by simp only [T, hfinite, Prod.snd_mul]⟩
      have hpos : 0 < ‖arch (diag ξ).1‖ := by
        apply norm_pos_iff.mpr
        exact (Units.map ((arch).toMonoidHom.comp (RingHom.fst _ _).toMonoidHom)
          (unitAtS ξ)).ne_zero
      have hnorm : ‖arch (diag ξ).1‖ ≤ ‖arch x.1‖ * R := by
        rw [hdiag, Prod.fst_mul, map_mul]
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left ((hR₀ k hk.1).trans (le_max_left _ _)) (norm_nonneg _))
      have hyNorm : ‖arch y.1‖ = r * ‖arch x.1‖ := by
        change ‖arch ((canonicalIdeleNormSection F t).val.1 * x.1)‖ = _
        rw [show arch ((canonicalIdeleNormSection F t).val.1 * x.1) = r • arch x.1
          from canonicalIdeleNormSection_smul_mixedSpace (F := F) t
            (x.1, (0 : FiniteAdeleRing (𝓞 F) F)), norm_smul,
          Real.norm_of_nonneg (zero_le_one.trans hr)]
      rw [show u ξ = _ from indicator_of_mem hξ _, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos M)]
      calc
        _ ≤ ‖fs.val (Multiplicative.ofAdd y)‖ * r ^ M * ‖arch (diag ξ).1‖ ^ M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htPow (norm_nonneg _)) (by positivity)
        _ = ‖fs.val (Multiplicative.ofAdd y)‖ * (r * ‖arch (diag ξ).1‖) ^ M := by
          rw [mul_pow, mul_assoc]
        _ ≤ ‖fs.val (Multiplicative.ofAdd y)‖ * (‖arch y.1‖ * R) ^ M := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply pow_le_pow_left₀ (by positivity)
          rw [hyNorm, mul_assoc]
          exact mul_le_mul_of_nonneg_left hnorm (zero_le_one.trans hr)
        _ = (‖fs.val (Multiplicative.ofAdd y)‖ * ‖arch y.1‖ ^ M) * R ^ M := by
          rw [mul_pow, mul_assoc]
        _ ≤ A * R ^ M := mul_le_mul_of_nonneg_right (hdecay y) (pow_nonneg hR _)
    · have hz : fs.val (Multiplicative.ofAdd y) = 0 := hsupp y hyC
      rw [hz, norm_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hA (pow_nonneg hR _)) (hu₀ ξ)
  calc
    _ ≤ ∑' ξ, (A * R ^ M) * u ξ :=
      Summable.tsum_le_tsum hterm (hf.mul_right _) (hu.mul_left _)
    _ = R ^ M * (∑' ξ, u ξ) * A := by rw [tsum_mul_left]; ring

/-- A continuous seminorm on an elementary Schwartz space controls the values weighted by the
sum of the absolute real and lattice coordinates. -/
private theorem elementarySchwartz_decay_seminorm {m n l : ℕ} {Fk : Type*}
    [AddCommGroup Fk] [TopologicalSpace Fk] [DiscreteTopology Fk] [Finite Fk] (N : ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n l Fk), Continuous q ∧
      ∀ (s : ElementarySchwartz m n l Fk) (w : ElementaryLieGroup m n l Fk),
        ‖s w‖ * (1 + (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|)) ^ N ≤ q s := by
  let I := Option (Fin m ⊕ Fin l)
  let idx : I → ElementarySchwartzIndex m n l
    | none => (0, 0, 0, 0)
    | some (Sum.inl j) => (Pi.single j N, 0, 0, 0)
    | some (Sum.inr k) => (0, 0, 0, Pi.single k N)
  let c : ℝ≥0 := Fintype.card I
  let q : Seminorm ℂ (ElementarySchwartz m n l Fk) :=
    c ^ N • ∑ i : I, elementarySchwartzSeminorm (idx i)
  have hq (s : ElementarySchwartz m n l Fk) :
      q s = (c : ℝ) ^ N * ∑ i : I, elementarySchwartzSeminorm (idx i) s := by
    change (↑(c ^ N) : ℝ) *
      FunLike.coeAddMonoidHom _ _ _ (∑ i : I, elementarySchwartzSeminorm (idx i)) s = _
    rw [NNReal.coe_pow, map_sum, Finset.sum_apply]
    rfl
  refine ⟨q, ?_, fun s w ↦ ?_⟩
  · simp_rw [show (q : ElementarySchwartz m n l Fk → ℝ) =
        (fun s ↦ (c : ℝ) ^ N * ∑ i : I, elementarySchwartzSeminorm (idx i) s) from funext hq]
    exact continuous_const.mul (continuous_finsetSum _ fun i _ ↦
      elementarySchwartz_withSeminorms.continuous_seminorm (idx i))
  let z : I → ℝ
    | none => 1
    | some (Sum.inl j) => |w.1 j|
    | some (Sum.inr k) => |(w.2.2.1 k : ℝ)|
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ z ⟨none, Finset.mem_univ _⟩
  have hsum : 1 + (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|) ≤ (c : ℝ) * z i := by
    calc
      _ = ∑ j : I, z j := by simp [I, z, Fintype.sum_option, Fintype.sum_sum_type]
      _ ≤ ∑ _ : I, z i := Finset.sum_le_sum hmax
      _ = _ := by simp [c, nsmul_eq_mul]
  have hmon (j : I) : ‖s w‖ * z j ^ N ≤ elementarySchwartzSeminorm (idx j) s := by
    change ‖s w‖ * z j ^ N ≤ (elementarySchwartzBound s.val (idx j)).toReal
    rcases j with _ | (_ | _)
    · simpa [idx, z] using elementarySchwartz_monomial_bound s.property 0 0 w
    · rename_i j
      have h := elementarySchwartz_monomial_bound s.property (Pi.single j N) 0 w
      rw [Finset.prod_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at h
      simpa [idx, z, mul_comm] using h
    · rename_i k
      have h := elementarySchwartz_monomial_bound s.property 0 (Pi.single k N) w
      rw [Finset.prod_eq_single k (fun j _ hj => by simp [hj]) (by simp)] at h
      simpa [idx, z, mul_comm] using h
  rw [hq]
  calc
    _ ≤ ‖s w‖ * ((c : ℝ) * z i) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) (norm_nonneg _)
    _ = (c : ℝ) ^ N * (‖s w‖ * z i ^ N) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((hmon i).trans (Finset.single_le_sum (f := fun j : I ↦ elementarySchwartzSeminorm (idx j) s)
        (fun _ _ ↦ apply_nonneg _ _) hi)) (by positivity)

/-- The archimedean polynomial weight on an S-adelic stage is controlled by a
continuous seminorm on that stage. -/
private theorem sAdeleStage_arch_decay_seminorm (a : BruhatStructuralPair Gₛ)
    (e : ElementaryLCAPresentation a.quotient) (M : ℕ) :
    ∃ q : Seminorm ℂ (SchwartzBruhatStage e), Continuous q ∧
      ∀ (s : SchwartzBruhatStage e) (x : Aₛ),
        ‖schwartzBruhatStageRealization a e s (Multiplicative.ofAdd x)‖ *
          ‖arch x.1‖ ^ M ≤ q s := by
  let m : Gₛ →* Multiplicative A∞ :=
    ((arch).toAddMonoidHom.comp (AddMonoidHom.fst _ _)).toMultiplicative
  have hm : Continuous m := (isEmbedding_thetaArch F).continuous.comp continuous_fst
  let l := m.comp a.val.1.subtype
  have hker : (OrderDual.ofDual a.val.2).comap a.val.1.subtype ≤ l.ker :=
    fun x hx ↦ sAdeleStage_arch_eq_zero F S a x hx
  let p : a.quotient →* Multiplicative A∞ := QuotientGroup.lift _ l hker
  have hp : Continuous p := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (hm.comp continuous_subtype_val)
  let P : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor →+ A∞ :=
    (p.comp e.equiv.symm.toMonoidHom).toAdditive
  have hP : Continuous P :=
    continuous_toAdd.comp (hp.comp (e.equiv.symm.continuous.comp continuous_ofAdd))
  refine (elementary_additive_norm_le P hP P.map_add).elim fun A hA ↦
    hA.elim fun B hAB ↦ ?_
  refine (elementarySchwartz_decay_seminorm
    (m := e.realDim) (n := e.torusDim) (l := e.latticeRank) (Fk := e.finiteFactor) M).elim
    fun q hq ↦ ?_
  let c : ℝ≥0 := ⟨(1 + A + max B 0) ^ M,
    pow_nonneg (add_nonneg (add_nonneg zero_le_one hAB.1) (le_max_right B 0)) _⟩
  have hqc : Continuous (c • q : Seminorm ℂ (SchwartzBruhatStage e)) :=
    continuous_const.mul hq.1
  refine ⟨c • q, hqc, fun s x ↦ ?_⟩
  by_cases hx : Multiplicative.ofAdd x ∈ a.val.1
  · let y : a.quotient := QuotientGroup.mk ⟨Multiplicative.ofAdd x, hx⟩
    let w := Multiplicative.toAdd (e.equiv y)
    have hw : P w = arch x.1 := by
      change (p (e.equiv.symm (e.equiv y))).toAdd = _
      rw [e.equiv.symm_apply_apply]
      rfl
    have hval : schwartzBruhatStageRealization a e s (Multiplicative.ofAdd x) = s w :=
      (schwartzBruhatStageRealization_apply a e s _).trans (dite_eq_left hx)
    have hnorm : ‖arch x.1‖ ≤ A * (∑ j, |w.1 j| + ∑ k, |(w.2.2.1 k : ℝ)|) + B :=
      (congrArg (fun z : A∞ ↦ ‖z‖) hw.symm).trans_le (hAB.2 w)
    have hbound := real_decay_aux (norm_nonneg (s w))
      (add_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)) hAB.1 (norm_nonneg _) hnorm (hq.2 s w)
    calc
      _ = ‖s w‖ * ‖arch x.1‖ ^ M := congrArg (fun z : ℂ ↦ ‖z‖ * ‖arch x.1‖ ^ M) hval
      _ ≤ ‖s w‖ * (1 + ‖arch x.1‖) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
          (le_add_of_nonneg_left zero_le_one) _) (norm_nonneg _)
      _ ≤ (c • q) s := hbound.trans_eq (congrArg ((c : ℝ) * ·) (max_eq_left (apply_nonneg q s)))
  · have hval : schwartzBruhatStageRealization a e s (Multiplicative.ofAdd x) = 0 :=
      (schwartzBruhatStageRealization_apply a e s _).trans (dite_eq_right hx)
    calc
      _ = ‖(0 : ℂ)‖ * ‖arch x.1‖ ^ M :=
        congrArg (fun z : ℂ ↦ ‖z‖ * ‖arch x.1‖ ^ M) hval
      _ ≤ (c • q) s := by simpa only [norm_zero, zero_mul] using apply_nonneg (c • q) s

/-- The uniform decay bound for a bounded set of test functions also holds at norm one. -/
private theorem sLocalAdelicTheta_decay_bounded_of_one_le
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 ≤ normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  let p (g : {g : Iₛ // 1 ≤ normℝ g}) : Seminorm ℂ ℬₛ :=
    let c : NNReal := ⟨(normℝ g.val) ^ N, pow_nonneg (NNReal.coe_nonneg _) _⟩
    c • (normSeminorm ℂ ℂ).comp ((ContinuousMap.evalCLM ℂ g.val).toLinearMap.comp
      (sLocalAdelicTheta F S))
  have hp (g) (f : ℬₛ) : p g f = ‖sLocalAdelicTheta F S f g.val‖ * (normℝ g.val) ^ N := by
    exact mul_comm _ _
  have hbounded : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.mpr fun f ↦ by
    refine (sAdeleSchwartz_exists_decay_bound F S f).elim fun C hC ↦ ?_
    refine (sLocalTheta_weighted_bound F S C hC.1 N).elim fun M hM ↦
      hM.elim fun D hD ↦ ?_
    refine (hC.2.2 M).elim fun A hA ↦ ?_
    exact ⟨D * A, Set.forall_mem_range.mpr fun g ↦ (hp g f).trans_le
      (hD.2 f A hA.1 hC.2.1 hA.2 g.val g.property)⟩
  let : Nonempty {g : Iₛ // 1 ≤ normℝ g} := ⟨⟨1, by simp⟩⟩
  let q : Seminorm ℂ (schwartzBruhatSubmodule Gₛ) := ⨆ g, p g
  have hq (g) : p g ≤ q := le_ciSup hbounded g
  have hstage (a : BruhatStructuralPair Gₛ) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (q ∘ schwartzBruhatStageInclusion a e) := by
    refine (sAdeleStage_exists_compact_finite F S a).elim fun C hC ↦ ?_
    refine (sLocalTheta_weighted_bound F S C hC.1 N).elim fun M hM ↦
      hM.elim fun D hD ↦ ?_
    refine (sAdeleStage_arch_decay_seminorm F S a e M).elim fun r hr ↦ ?_
    let c : ℝ≥0 := ⟨D, hD.1⟩
    have hcr : Continuous (c • r : Seminorm ℂ (SchwartzBruhatStage e)) :=
      continuous_const.mul hr.1
    apply Seminorm.continuous_of_le (p := q.comp (schwartzBruhatStageInclusion a e)) hcr
    intro s
    let f : ℬₛ := schwartzBruhatStageInclusion a e s
    change q f ≤ D * r s
    refine (Seminorm.iSup_apply (p := p) hbounded (x := f)).trans_le (ciSup_le fun g ↦ ?_)
    refine (hp g f).trans_le (hD.2 f (r s) (apply_nonneg r s) ?_ (hr.2 s) g.val g.property)
    intro x hx
    exact (schwartzBruhatStageRealization_apply a e s (Multiplicative.ofAdd x)).trans
      (dite_eq_right (fun h ↦ hx (hC.2 _ h)))
  let i : {p : Seminorm ℂ (schwartzBruhatSubmodule Gₛ) //
      ∀ (a : BruhatStructuralPair Gₛ) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} := ⟨q, hstage⟩
  refine (((withGeneratingSeminorms_spec _ _).isVonNBounded_iff_seminorm_bounded.mp hB) i).elim
    fun C hC ↦ ?_
  refine ⟨C, hC.1, fun f hf g hg ↦ ?_⟩
  have hweight := ((hp ⟨g, hg⟩ f).ge.trans (hq ⟨g, hg⟩ f)).trans (hC.2 f hf).le
  simpa only [div_eq_mul_inv] using
    (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hg) N)).mpr hweight

end UniformDecay

/-- Paper: Proposition 2.3.1.2(3), p. 100. The large-norm decay constant
and threshold can be chosen uniformly for a bounded set of test functions. -/
theorem sLocalAdelicTheta_decay_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, T < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  refine (sLocalAdelicTheta_decay_bounded_of_one_le F S B hB N).elim fun C hC ↦ ?_
  exact ⟨C, 1, hC.1, zero_lt_one, fun f hf g hg ↦ hC.2 f hf g hg.le⟩

/-- Paper: Proposition 2.3.1.2(4), p. 100. The bounded-set decay estimate
holds above S-idelic norm one with a uniform constant. -/
theorem sLocalAdelicTheta_decay_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 < normℝ g →
      ‖sLocalAdelicTheta F S f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  refine (sLocalAdelicTheta_decay_bounded_of_one_le F S B hB N).elim fun C hC ↦ ?_
  exact ⟨C, hC.1, fun f hf g hg ↦ hC.2 f hf g hg.le⟩

local instance normOneSIdeleQuotientMeasurableSpace (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

section HomogeneousTheta

-- TODO(paper-gap): Definition A.3.4.1(3)(3) names C_{F,S}^1 as the quotient
-- of the norm-one local S-ideles. The integral in (2.3.1.13) is over J_{F,S}^1.
-- The Haar measure on the latter is an explicit parameter pending its normalization.

variable (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm F S)))

local notation "classIntegrand" => fun (ω : PontryaginDual J₁) (f : ℬₛ) (g : Jₛ) (h : J₁) ↦
  sLocalAdelicThetaOnClasses F S f (g * Subtype.val h) * (ω h : ℂ)

/-- Paper: Proposition 2.3.1.4(1), p. 105. The character-weighted integral
is absolutely convergent at each S-idele class. -/
theorem sLocalHomogeneousAdelicTheta_integrable [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (g : Jₛ) :
    Integrable (classIntegrand ω f g) μ := by
  have hcompact : CompactSpace J₁ :=
    isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  have hopen : OpensMeasurableSpace J₁ := ⟨le_refl _⟩
  have hchar : Continuous (fun h : J₁ ↦ (ω h : ℂ)) :=
    continuous_subtype_val.comp ω.continuous_toFun
  have hcont : Continuous (classIntegrand ω f g) :=
    ((sLocalAdelicThetaOnClasses F S f).continuous_toFun.comp
      (continuous_const.mul continuous_subtype_val)).mul hchar
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  exact Integrable.of_bound (hcont.aestronglyMeasurable_of_compactSpace) C
    (Eventually.of_forall fun h ↦ hC h (Set.mem_univ h))

/-- Paper: Proposition 2.3.1.4(1), p. 105. On a compact set of S-ideles
the integrands have a common constant majorant on the compact norm-one classes.
Deviation: Uniform absolute convergence is expressed by this integrable majorant. -/
theorem sLocalHomogeneousAdelicTheta_integrand_bounded [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (K : Set Iₛ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun _ : J₁ ↦ C) μ ∧
      ∀ g ∈ K, ∀ h : J₁, ‖classIntegrand ω f (classOf g) h‖ ≤ C := by
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton :
      IsCompact (sIdeleQuotientNorm F S ⁻¹' {1}))
  have hclass : Continuous (fun p : Iₛ × J₁ ↦ classOf p.1) :=
    QuotientGroup.continuous_mk.comp continuous_fst
  have hval : Continuous (fun p : Iₛ × J₁ ↦ (p.2.val : Jₛ)) :=
    continuous_subtype_val.comp continuous_snd
  have hcont : Continuous (fun p : Iₛ × J₁ ↦
      sLocalAdelicThetaOnClasses F S f (classOf p.1 * p.2.val)) :=
    (sLocalAdelicThetaOnClasses F S f).continuous.comp (hclass.mul hval)
  obtain ⟨B, hB⟩ := (hK.prod isCompact_univ).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, integrable_const _, fun g hg h ↦ ?_⟩
  simp only [norm_mul, Circle.norm_coe, mul_one]
  exact (hB (g, h) ⟨hg, mem_univ h⟩).trans (le_max_left _ _)

/-- Uniform convergence on a set, together with integrability of the terms,
implies convergence of the integrals over that set for a finite measure. -/
private theorem tendsto_setIntegral_of_tendstoUniformlyOn {ι α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ι → α → E} {u : α → E} {s : Set α} {l : Filter ι}
    (hu : TendstoUniformlyOn F u l s) (hFi : ∀ i, IntegrableOn (F i) s μ)
    (hui : IntegrableOn u s μ) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, u x ∂μ)) := by
  have hμs : μ s < ⊤ :=
    lt_of_le_of_lt (measure_mono (subset_univ s)) (measure_lt_top μ univ)
  have key : ∀ d : ℝ, 0 < d → ∀ᶠ i in l,
      ‖∫ x in s, F i x ∂μ - ∫ x in s, u x ∂μ‖ ≤ d := by
    intro d hd
    have hc : (0 : ℝ) < max (μ.real s) 1 := by positivity
    have hle := (Metric.tendstoUniformlyOn_iff).mp hu (d / max (μ.real s) 1) (div_pos hd hc)
    filter_upwards [hle] with i hi
    have h1 : ‖∫ x in s, (F i - u) x ∂μ‖ ≤ d := by
      refine le_trans (norm_setIntegral_le_of_norm_le_const
        (C := d / max (μ.real s) 1) hμs fun x hx ↦ ?_) ?_
      · calc ‖(F i - u) x‖ = ‖u x - F i x‖ := norm_sub_rev _ _
          _ = dist (u x) (F i x) := (dist_eq_norm _ _).symm
          _ ≤ d / max (μ.real s) 1 := (hi x hx).le
      · refine le_trans (mul_le_mul_of_nonneg_left (le_max_left (μ.real s) 1)
          (by positivity)) (le_of_eq (div_mul_cancel₀ d hc.ne'))
    rw [show (∫ x in s, (F i - u) x ∂μ) =
      (∫ x in s, F i x ∂μ - ∫ x in s, u x ∂μ) from integral_sub (hFi i) hui] at h1
    exact h1
  refine tendsto_def.mpr fun U hU ↦ ?_
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp hU
  refine (key (r / 2) (by positivity)).mono fun i hi ↦ hrb ?_
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

/-- Paper: Proposition 2.3.1.4(1), p. 105. Integrating the character-weighted
theta function gives a continuous function on the S-idele classes. -/
theorem sLocalHomogeneousAdelicTheta_continuous [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) :
    Continuous (fun g : Jₛ ↦ ∫ h, classIntegrand ω f g h ∂μ) := by
  classical
  -- The norm-one classes form a compact group.
  haveI hcomp : CompactSpace J₁ := by
    have hker : (MonoidHom.ker (sIdeleQuotientNorm F S) : Set Jₛ) =
        (sIdeleQuotientNorm F S) ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    exact isCompact_iff_compactSpace.mp (by
      rw [hker]
      exact (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  haveI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  -- The uncurried integrand is continuous.
  have hΦ : Continuous fun p : Jₛ × J₁ ↦
      sLocalAdelicThetaOnClasses F S f (p.1 * p.2.val) * (ω p.2 : ℂ) :=
    Continuous.mul
      ((map_continuous (sLocalAdelicThetaOnClasses F S f)).comp
        (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
      (continuous_subtype_val.comp ((map_continuous ω).comp continuous_snd))
  -- Currying turns continuity on the product into a continuous curve in C(J₁, ℂ).
  have hΘ : Continuous
      ((ContinuousMap.curry (ContinuousMap.mk
        (fun p : Jₛ × J₁ ↦ sLocalAdelicThetaOnClasses F S f (p.1 * p.2.val) * (ω p.2 : ℂ)) hΦ :
        C(Jₛ × J₁, ℂ)) : Jₛ → C(J₁, ℂ))) :=
    map_continuous (ContinuousMap.curry (ContinuousMap.mk _ hΦ))
  refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
  -- Hence the integrands converge uniformly in the parameter.
  have htu : TendstoUniformlyOn
      (fun (g : Jₛ) (h : J₁) ↦ sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ))
      (fun h : J₁ ↦ sLocalAdelicThetaOnClasses F S f (g₀ * h.val) * (ω h : ℂ))
      (𝓝 g₀) univ := by
    have hlim := ContinuousMap.tendsto_iff_tendstoUniformly
      (F := ((ContinuousMap.curry (ContinuousMap.mk
        (fun p : Jₛ × J₁ ↦ sLocalAdelicThetaOnClasses F S f (p.1 * p.2.val) * (ω p.2 : ℂ)) hΦ :
        C(Jₛ × J₁, ℂ)) : Jₛ → C(J₁, ℂ))))
      (f := ContinuousMap.curry (ContinuousMap.mk
        (fun p : Jₛ × J₁ ↦ sLocalAdelicThetaOnClasses F S f (p.1 * p.2.val) * (ω p.2 : ℂ)) hΦ)
        g₀)
      (p := 𝓝 g₀)
    have hcont : Tendsto ((ContinuousMap.curry (ContinuousMap.mk
        (fun p : Jₛ × J₁ ↦ sLocalAdelicThetaOnClasses F S f (p.1 * p.2.val) * (ω p.2 : ℂ)) hΦ :
        C(Jₛ × J₁, ℂ)) : Jₛ → C(J₁, ℂ))) (𝓝 g₀)
        (𝓝 ((ContinuousMap.curry (ContinuousMap.mk
        (fun p : Jₛ × J₁ ↦ sLocalAdelicThetaOnClasses F S f (p.1 * p.2.val) * (ω p.2 : ℂ)) hΦ :
        C(Jₛ × J₁, ℂ)) : Jₛ → C(J₁, ℂ)) g₀)) :=
      hΘ.tendsto g₀
    exact (tendstoUniformlyOn_univ).mpr (hlim.mp hcont)
  -- Integrability of every integrand on the compact group.
  have hint (g : Jₛ) : Integrable
      (fun h : J₁ ↦ sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ)) μ := by
    haveI : BorelSpace J₁ := ⟨rfl⟩
    have hAt : Continuous fun h : J₁ ↦
        sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ) := by
      refine Continuous.mul
        ((map_continuous (sLocalAdelicThetaOnClasses F S f)).comp
          (continuous_const (y := g) |>.mul continuous_subtype_val)) ?_
      exact continuous_subtype_val.comp ((map_continuous ω).comp continuous_id)
    have hmeas : AEStronglyMeasurable
        (fun h : J₁ ↦ sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ)) μ :=
      hAt.measurable.aestronglyMeasurable
    obtain ⟨M, hM⟩ :=
      IsCompact.exists_bound_of_continuousOn isCompact_univ hAt.continuousOn
    exact (integrable_const M).mono' hmeas
      (Eventually.of_forall fun h ↦ hM h (Set.mem_univ h))
  refine ContinuousAt.congr_of_eventuallyEq
    (f := fun g : Jₛ ↦ ∫ x in univ, sLocalAdelicThetaOnClasses F S f (g * x.val) * (ω x : ℂ) ∂μ)
    ?_ ?_
  · exact tendsto_setIntegral_of_tendstoUniformlyOn (s := univ) htu
      (fun g ↦ (integrableOn_univ).mpr (hint g)) (integrableOn_univ.mpr (hint g₀))
  · filter_upwards with g
    simp [Measure.restrict_univ]

variable [Measure.IsHaarMeasure μ]

/-- Paper: Definition 2.3.1.3, p. 104. The character-weighted integral
defines a complex-linear map in the test function. -/
theorem sLocalHomogeneousAdelicTheta_isLinear (ω : PontryaginDual J₁) :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨fun g ↦ ∫ h, classIntegrand ω f g h ∂μ,
      sLocalHomogeneousAdelicTheta_continuous F S μ ω f⟩ : C(Jₛ, ℂ))) := by
  have linearIntegral {E X Y H : Type _} [AddCommMonoid E] [Module ℂ E]
      [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace H]
      (ν : Measure H) (p : X → Y) (hp : Surjective p) (θ : E →ₗ[ℂ] C(X, ℂ))
      (desc : E → C(Y, ℂ)) (hdesc : ∀ f x, desc f (p x) = θ f x)
      (shift : Y → H → Y) (weight : H → ℂ)
      (hint : ∀ f g, Integrable (fun h ↦ desc f (shift g h) * weight h) ν)
      (hcont : ∀ f, Continuous (fun g ↦ ∫ h, desc f (shift g h) * weight h ∂ν)) :
      IsLinearMap ℂ (fun f ↦ (⟨fun g ↦ ∫ h, desc f (shift g h) * weight h ∂ν,
        hcont f⟩ : C(Y, ℂ))) := by
    refine ⟨fun f₁ f₂ ↦ ContinuousMap.ext fun g ↦ ?_, fun c f ↦ ContinuousMap.ext fun g ↦ ?_⟩
    · refine (integral_congr_ae (Eventually.of_forall fun (h : H) ↦ ?_)).trans
        (integral_add (hint f₁ g) (hint f₂ g))
      obtain ⟨x, hx⟩ := hp (shift g h)
      simp only [← hx, hdesc, θ.map_add, ContinuousMap.add_apply, add_mul]
    · refine (integral_congr_ae (Eventually.of_forall fun (h : H) ↦ ?_)).trans
        (integral_smul c (fun h ↦ desc f (shift g h) * weight h))
      obtain ⟨x, hx⟩ := hp (shift g h)
      simp only [← hx, hdesc, θ.map_smul, ContinuousMap.smul_apply, smul_mul_assoc]
  exact linearIntegral (E := ℬₛ) (X := Iₛ) (Y := Jₛ) (H := J₁)
    μ classOf QuotientGroup.mk_surjective
    (sLocalAdelicTheta F S) (sLocalAdelicThetaOnClasses F S) (sLocalAdelicThetaOnClasses_mk F S)
    (fun g h ↦ g * h.val) (fun h ↦ (ω h : ℂ))
    (sLocalHomogeneousAdelicTheta_integrable F S μ ω)
    (sLocalHomogeneousAdelicTheta_continuous F S μ ω)

/-- Paper: Definition 2.3.1.3, p. 104. Homogeneous S-local theta integrates
theta at the class product `g * h` against the character on norm-one classes.
Deviation: The norm-one class Haar measure is an explicit parameter. In (2.3.1.13)
an idele argument is read through its class, as required by (2.3.1.12). -/
def sLocalHomogeneousAdelicTheta (ω : PontryaginDual J₁) : ℬₛ →ₗ[ℂ] C(Jₛ, ℂ) :=
  IsLinearMap.mk' _ (sLocalHomogeneousAdelicTheta_isLinear F S μ ω)

/-- Paper: Equation (2.3.1.13), p. 105. At the identity and for the trivial
character, homogeneous theta integrates unweighted theta on the norm-one classes. -/
theorem sLocalHomogeneousAdelicTheta_trivial_at_one (f : ℬₛ) :
    sLocalHomogeneousAdelicTheta F S μ (1 : PontryaginDual J₁) f 1 =
      ∫ h : J₁, sLocalAdelicThetaOnClasses F S f h.val ∂μ := by
  simp only [sLocalHomogeneousAdelicTheta, IsLinearMap.mk'_apply, ContinuousMap.coe_mk]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  exact (congrArg₂ (· * ·) (congrArg (sLocalAdelicThetaOnClasses F S f) (one_mul h.val))
    (congrArg Subtype.val (PontryaginDual.one_apply h))).trans (mul_one _)

/-- Paper: Proposition 2.3.1.4(1), p. 105. Inverse left translation by a
norm-one class multiplies homogeneous theta by the character at that class.
Its pullback to the S-ideles has the corresponding pulled-back character. -/
theorem sLocalHomogeneousAdelicTheta_homogeneous (ω : PontryaginDual J₁)
    (f : ℬₛ) (h : J₁) (g : Jₛ) :
    sLocalHomogeneousAdelicTheta F S μ ω f (h.val⁻¹ * g) =
      (ω h : ℂ) * sLocalHomogeneousAdelicTheta F S μ ω f g := by
  have : BorelSpace J₁ := ⟨rfl⟩
  simp only [sLocalHomogeneousAdelicTheta, IsLinearMap.mk'_apply, ContinuousMap.coe_mk]
  rw [← integral_mul_left_eq_self (μ := μ) (classIntegrand ω f (h.val⁻¹ * g)) h,
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun k ↦ ?_)
  have hproduct : (h.val⁻¹ * g) * (h * k).val = g * k.val := by
    change (h.val⁻¹ * g) * (h.val * k.val) = g * k.val
    rw [mul_comm h.val⁻¹ g, mul_assoc, inv_mul_cancel_left]
  change sLocalAdelicThetaOnClasses F S f ((h.val⁻¹ * g) * (h * k).val) * (ω (h * k) : ℂ) =
    (ω h : ℂ) * (sLocalAdelicThetaOnClasses F S f (g * k.val) * (ω k : ℂ))
  rw [hproduct, map_mul ω h k, Circle.coe_mul (ω h) (ω k), mul_left_comm]

/-- Paper: Proposition 2.3.1.4(2), p. 105. Homogeneous S-local theta decays
at every positive inverse power as the S-idelic norm tends to infinity. -/
theorem sLocalHomogeneousAdelicTheta_decay_large (ω : PontryaginDual J₁)
    (f : ℬₛ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : Iₛ, T < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  have integralDecay {X Y H : Type _} [Group Y] [MeasurableSpace H]
      (ν : Measure H) [IsFiniteMeasure ν] [NeZero ν]
      (q : X → Y) (hq : Surjective q)
      (m : Y →* ℝ≥0ˣ) (n : X → ℝ≥0ˣ) (hm : ∀ g, m (q g) = n g)
      (p : H → Y) (hp : ∀ h, m (p h) = 1) (χ : H → ℂ) (hχ : ∀ h, ‖χ h‖ = 1)
      (θ : X → ℂ) (φ : Y → ℂ) (hφ : ∀ g, φ (q g) = θ g)
      (ψ : X → ℂ) (hψ : ∀ g, ψ g = ∫ h, φ (q g * p h) * χ h ∂ν)
      (hθ : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ g, T < valueℝ (n g) →
        ‖θ g‖ ≤ A * (valueℝ (n g) ^ N)⁻¹) :
      ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g, T < valueℝ (n g) →
        ‖ψ g‖ ≤ C * (valueℝ (n g) ^ N)⁻¹ := by
    obtain ⟨A, T, hA, hT, hdecay⟩ := hθ
    refine ⟨A * ν.real univ, T, mul_pos hA measureReal_univ_pos, hT, fun g hg ↦ ?_⟩
    have hbound (h : H) : ‖φ (q g * p h) * χ h‖ ≤ A * (valueℝ (n g) ^ N)⁻¹ := by
      obtain ⟨k, hk⟩ := hq (q g * p h)
      have hnorm : n k = n g := by rw [← hm k, hk, map_mul, hp, mul_one, hm]
      simp only [norm_mul, hχ, mul_one, ← hk, hφ, ← hnorm]
      exact hdecay k (hnorm.symm ▸ hg)
    rw [hψ g]
    simpa only [mul_right_comm A (valueℝ (n g) ^ N)⁻¹ (ν.real univ)] using
      norm_integral_le_of_norm_le_const (μ := ν) (.of_forall hbound)
  have decay := @sLocalAdelicTheta_decay_large F ‹Field F› ‹NumberField F›
  have decayOnS := decay (by exact S)
  have decayForF := decayOnS (by exact f)
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  have : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure (μ := μ)
  exact integralDecay (X := Iₛ) (Y := Jₛ) (H := J₁) μ classOf QuotientGroup.mk_surjective
    (sIdeleQuotientNorm F S) (sIdeleNorm F S) (sIdeleQuotientNorm_mk F S)
    Subtype.val (fun h ↦ h.property) (fun h ↦ (ω h : ℂ)) (fun h ↦ Circle.norm_coe (ω h))
    (sLocalAdelicTheta F S f) (sLocalAdelicThetaOnClasses F S f)
    (sLocalAdelicThetaOnClasses_mk F S f)
    (fun g ↦ sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) (fun _ ↦ rfl) (decayForF N hN)

/-- Paper: Proposition 2.3.1.4(3), p. 105. The large-norm decay constants
for homogeneous S-local theta are uniform on a bounded set of test functions.
Deviation: Part (3) leaves the range of the exponent implicit. The nonnegative
range is supplied by part (4) and Proposition 2.3.1.2(3). -/
theorem sLocalHomogeneousAdelicTheta_decay_bounded (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, T < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  refine (sLocalAdelicTheta_decay_bounded F S B hB N).elim fun C hC ↦ ?_
  refine hC.elim fun T hbound ↦ ?_
  let : CompactSpace J₁ :=
    isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hμ : 0 < μ.real univ :=
    ENNReal.toReal_pos (isOpen_univ.measure_pos μ univ_nonempty).ne' (measure_ne_top μ _)
  refine ⟨C * μ.real univ, T, mul_pos hbound.1 hμ, hbound.2.1, fun f hf g hg ↦ ?_⟩
  have hpoint (h : J₁) : ‖classIntegrand ω f (classOf g) h‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (classOf g * h.val)
    have hh : sIdeleQuotientNorm F S h.val = 1 := h.property
    have hnorm : sIdeleNorm F S k = sIdeleNorm F S g := by
      rw [← sIdeleQuotientNorm_mk F S k, hk, map_mul, hh, mul_one, sIdeleQuotientNorm_mk]
    have hnormℝ : normℝ k = normℝ g := congrArg valueℝ hnorm
    have hkT : T < normℝ k := by rwa [hnormℝ]
    have hvalue : sLocalAdelicThetaOnClasses F S f (classOf g * h.val) =
        sLocalAdelicTheta F S f k :=
      (congrArg (fun c : Jₛ ↦ sLocalAdelicThetaOnClasses F S f c) hk.symm).trans
        (sLocalAdelicThetaOnClasses_mk F S f k)
    calc
      _ = ‖sLocalAdelicThetaOnClasses F S f (classOf g * h.val)‖ * ‖(ω h : ℂ)‖ :=
        norm_mul _ _
      _ = ‖sLocalAdelicTheta F S f k‖ :=
        (congrArg₂ (· * ·) (congrArg (fun z : ℂ ↦ ‖z‖) hvalue)
          (Circle.norm_coe (ω h))).trans (mul_one _)
      _ ≤ C * ((normℝ k) ^ N)⁻¹ := hbound.2.2 f hf k hkT
      _ = C * ((normℝ g) ^ N)⁻¹ := congrArg (fun r : ℝ ↦ C * (r ^ N)⁻¹) hnormℝ
  change ‖∫ h, classIntegrand ω f (classOf g) h ∂μ‖ ≤ _
  calc
    _ ≤ (C * ((normℝ g) ^ N)⁻¹) * μ.real univ :=
      norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)
    _ = (C * μ.real univ) * ((normℝ g) ^ N)⁻¹ := mul_right_comm _ _ _

/-- Paper: Proposition 2.3.1.4(4), p. 105. The uniform decay estimate
for homogeneous theta holds above S-idelic norm one. -/
theorem sLocalHomogeneousAdelicTheta_decay_bounded_threshold_one (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, 1 < normℝ g →
      ‖sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  refine (sLocalAdelicTheta_decay_bounded_threshold_one F S B hB N).elim fun C hbound ↦ ?_
  let : CompactSpace J₁ :=
    isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hμ : 0 < μ.real univ :=
    ENNReal.toReal_pos (isOpen_univ.measure_pos μ univ_nonempty).ne' (measure_ne_top μ _)
  refine ⟨C * μ.real univ, mul_pos hbound.1 hμ, fun f hf g hg ↦ ?_⟩
  have hpoint (h : J₁) : ‖classIntegrand ω f (classOf g) h‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (classOf g * h.val)
    have hh : sIdeleQuotientNorm F S h.val = 1 := h.property
    have hnorm : sIdeleNorm F S k = sIdeleNorm F S g := by
      rw [← sIdeleQuotientNorm_mk F S k, hk, map_mul, hh, mul_one, sIdeleQuotientNorm_mk]
    have hnormℝ : normℝ k = normℝ g := congrArg valueℝ hnorm
    have hkT : 1 < normℝ k := by rwa [hnormℝ]
    have hvalue : sLocalAdelicThetaOnClasses F S f (classOf g * h.val) =
        sLocalAdelicTheta F S f k :=
      (congrArg (fun c : Jₛ ↦ sLocalAdelicThetaOnClasses F S f c) hk.symm).trans
        (sLocalAdelicThetaOnClasses_mk F S f k)
    calc
      _ = ‖sLocalAdelicThetaOnClasses F S f (classOf g * h.val)‖ * ‖(ω h : ℂ)‖ :=
        norm_mul _ _
      _ = ‖sLocalAdelicTheta F S f k‖ :=
        (congrArg₂ (· * ·) (congrArg (fun z : ℂ ↦ ‖z‖) hvalue)
          (Circle.norm_coe (ω h))).trans (mul_one _)
      _ ≤ C * ((normℝ k) ^ N)⁻¹ := hbound.2 f hf k hkT
      _ = C * ((normℝ g) ^ N)⁻¹ := congrArg (fun r : ℝ ↦ C * (r ^ N)⁻¹) hnormℝ
  change ‖∫ h, classIntegrand ω f (classOf g) h ∂μ‖ ≤ _
  calc
    _ ≤ (C * ((normℝ g) ^ N)⁻¹) * μ.real univ :=
      norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)
    _ = (C * μ.real univ) * ((normℝ g) ^ N)⁻¹ := mul_right_comm _ _ _

end HomogeneousTheta

/-! ## Directional derivatives -/

section DirectionalDerivatives

variable (γ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ)

local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)
local notation "orbitDeriv" => fun (f : ℬₛ) (x : Multiplicative Aₛ) ↦
  deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd (Units.val (γ (expUnit s)) * Multiplicative.toAdd x))) 0

/-- A continuous linear equivalence from an inductive tensor product of Schwartz–Bruhat
spaces that multiplies the values of pure tensors has a slice map: contraction of the second
factor with the evaluation at a point `o` gives, for each `g`, a function `t` with
`t a = g b` at all points `a`, `b` where pure tensors evaluate to `f a * c o`. -/
private theorem sAdeleSchwartz_exists_zeroTailRestriction_aux {G H K : Type*}
    [CommGroup G] [TopologicalSpace G] [CommGroup H] [TopologicalSpace H]
    [CommGroup K] [TopologicalSpace K]
    (e : InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H) ≃L[ℂ] SchwartzBruhat K) (o : H)
    (g : SchwartzBruhat K) :
    ∃ t : SchwartzBruhat G, ∀ (a : G) (b : K),
      (∀ f c, e (TensorProduct.tmul ℂ f c) b = f a * c o) → t a = g b := by
  let φ : SchwartzBruhat H →ₗ[ℂ] ℂ := (LinearMap.proj o).comp (schwartzBruhatSubmodule H).subtype
  let L : InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H) →ₗ[ℂ] SchwartzBruhat G :=
    (TensorProduct.rid ℂ (SchwartzBruhat G)).toLinearMap.comp (TensorProduct.map LinearMap.id φ)
  refine ⟨L (e.symm g), fun a b h ↦ ?_⟩
  let p : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj a).comp (schwartzBruhatSubmodule G).subtype
  let q : SchwartzBruhat K →ₗ[ℂ] ℂ := (LinearMap.proj b).comp (schwartzBruhatSubmodule K).subtype
  have hL : p.comp L = q.comp e.toLinearEquiv.toLinearMap :=
    TensorProduct.ext' fun f c ↦ ((congrArg p (TensorProduct.rid_tmul f (φ c))).trans
      ((map_smul p (φ c) f).trans (mul_comm _ _))).trans (h f c).symm
  exact (LinearMap.congr_fun hL (e.symm g)).trans (congrArg q (e.apply_symm_apply g))

open scoped NumberField.AdeleRing in
/-- Paper: Corollary 2.1.4.2, p. 72. As a consequence of the first map in (2.1.4.7),
every global Schwartz–Bruhat function agrees with an S-local test function on the slice where
the omitted coordinates are zero. For a pure tensor this restriction evaluates the complementary
factor at zero and multiplies the S-local factor by that value. -/
theorem sAdeleSchwartz_exists_zeroTailRestriction
    (g : SchwartzBruhat (Multiplicative 𝔸[F])) :
    ∃ h : ℬₛ, ∀ x : 𝔸[F], finiteAdeleTailProjection F S x.2 = 0 →
      h (Multiplicative.ofAdd (adeleProjection F S x)) = g (Multiplicative.ofAdd x) := by
  obtain ⟨e, he⟩ := sAdeleTailSchwartz_inductiveTensor_equiv F S
  obtain ⟨t, ht⟩ := sAdeleSchwartz_exists_zeroTailRestriction_aux e (Multiplicative.ofAdd 0) g
  exact ⟨t, fun x hx ↦ ht _ _ fun f c ↦ (he f c x).trans (by rw [hx])⟩

open scoped NumberField.AdeleRing in
/-- Paper: Lemma 2.3.2.1, p. 105. Pointwise differentiation along the
one-parameter subgroup gives a Schwartz–Bruhat function. -/
theorem sAdeleDirectionalDeriv_mem (f : ℬₛ) :
    orbitDeriv f ∈ schwartzBruhatSubmodule (Multiplicative Aₛ) := by
  classical
  -- Lift the archimedean part of the subgroup, with finite component one.
  have hFinite (t : ℝ≥0ˣ) : (γ t).val.2 = 1 := by
    have : ConnectedSpace ℝ≥0ˣ :=
      (Nonneg.unitsHomeomorphPos ℝ).connectedSpace_iff.mpr
        (isConnected_iff_connectedSpace.mp (isConnected_Ioi (a := (0 : ℝ))))
    funext v
    have hCoord : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val.2 v) :=
      (continuous_apply v).comp
        (continuous_snd.comp (Units.continuous_val.comp γ.continuous))
    calc
      (γ t).val.2 v = (γ 1).val.2 v :=
        TotallyDisconnectedSpace.eq_of_continuous _ hCoord t 1
      _ = (1 : (v : S) → v.val.adicCompletion F) v := by rw [map_one]; rfl
  let liftArch : Aₛ →* 𝔸[F] := (MonoidHom.fst _ _).prod 1
  have hLiftArch : Continuous liftArch := continuous_fst.prodMk continuous_const
  let Γ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨(Units.map liftArch).comp γ.toMonoidHom, (hLiftArch.units_map _).comp γ.continuous⟩
  have hΓ (t : ℝ≥0ˣ) : adeleProjection F S (Γ t).val = (γ t).val :=
    Prod.ext rfl ((hFinite t).symm)
  -- Extend an S-adele by zero at the omitted places.
  obtain ⟨split, _, _, hsplit⟩ := integralAdelesOutside_factors F S
  let j (x : Aₛ) : integralAdelesOutside F S := split.symm (x, 0)
  have hj (x : Aₛ) : split (j x) = (x, 0) := split.apply_symm_apply _
  have hproj (x : Aₛ) : adeleProjection F S (j x).val = x :=
    ((hsplit (j x)).1).symm.trans (congrArg Prod.fst (hj x))
  have houtside (x : Aₛ) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ S) :
      (j x).val.2 w = 0 := by
    rw [← (hsplit (j x)).2 ⟨w, hw⟩, hj]
    rfl
  have htail (x : Aₛ) : finiteAdeleTailProjection F S (j x).val.2 = 0 := by
    apply RestrictedProduct.ext
    exact fun w ↦ houtside x w.val w.property
  let d := adeleDirectionalDeriv Γ (sAdeleSchwartzToGlobal F S f)
  obtain ⟨dₛ, hdₛ⟩ := sAdeleSchwartz_exists_zeroTailRestriction F S d
  have hcurve (x : Aₛ) (s : ℝ) :
      sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd ((Γ (expUnit s)).val * (j x).val)) =
        f (Multiplicative.ofAdd ((γ (expUnit s)).val * x)) := by
    have hIntegral (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ S) :
        ((Γ (expUnit s)).val * (j x).val).2 w ∈ w.adicCompletionIntegers F := by
      change 1 * (j x).val.2 w ∈ w.adicCompletionIntegers F
      rw [one_mul, houtside x w hw]
      exact Subring.zero_mem _
    have hp : adeleProjection F S ((Γ (expUnit s)).val * (j x).val) =
        (γ (expUnit s)).val * x :=
      ((adeleProjection F S).map_mul _ _).trans (congrArg₂ (· * ·) (hΓ _) (hproj x))
    exact (sAdeleSchwartzToGlobal_apply F S f _).trans
      ((ite_eq_left hIntegral).trans (congrArg (fun y : Aₛ ↦ f (Multiplicative.ofAdd y)) hp))
  have hd : (dₛ : Multiplicative Aₛ → ℂ) = orbitDeriv f := by
    funext y
    let x := y.toAdd
    have hs := hdₛ (j x).val (htail x)
    rw [hproj x] at hs
    exact hs.trans (congrArg (fun c : ℝ → ℂ ↦ deriv c 0) (funext (hcurve x)))
  rw [← hd]
  exact dₛ.property

/-- Inserting an S-idele and multiplying an adele integral outside S preserves integrality
outside S, so evaluating the global extension reduces to evaluating on the S-coordinates. -/
private theorem sAdeleSchwartzToGlobal_mul_sIdeleInsertion
    (f : ℬₛ) (g : Iₛ) (y : integralAdelesOutside F S) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd ((sIdeleInsertion F S g).val * y.val)) =
        f (Multiplicative.ofAdd (g.val * adeleProjection F S y.val)) := by
  classical
  have hInsertion := sIdeleInsertion_apply F S g
  have hy := y.property
  simp only [integralAdelesOutside, Subring.mem_iInf] at hy
  have hInt (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
      ((sIdeleInsertion F S g).val * y.val).2 v ∈ v.adicCompletionIntegers F := by
    change (sIdeleInsertion F S g).val.2 v * y.val.2 v ∈ v.adicCompletionIntegers F
    rw [hInsertion.2.2 v hv, one_mul]
    exact hy v hv
  have hProj : adeleProjection F S (sIdeleInsertion F S g).val = g.val := by
    apply Prod.ext
    · exact hInsertion.1
    · funext v
      exact hInsertion.2.1 v
  rw [sAdeleSchwartzToGlobal_apply F S f, ite_eq_left hInt, map_mul (adeleProjection F S), hProj]

/-- Paper: Lemma 2.3.2.1, p. 105. The orbit of an S-adelic test function
along the one-parameter subgroup is differentiable at zero in the logarithmic parameter. -/
private theorem sAdeleOrbit_differentiableAt (f : ℬₛ) (x : Multiplicative Aₛ) :
    DifferentiableAt ℝ (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * x.toAdd))) 0 := by
  have hLift (x : Multiplicative Aₛ) :
      ∃ y : integralAdelesOutside F S, Multiplicative.ofAdd (adeleProjection F S y.val) = x := by
    obtain ⟨e, -, -, he⟩ := integralAdelesOutside_factors F S
    refine ⟨e.symm (x.toAdd, 0), congrArg Multiplicative.ofAdd ?_⟩
    exact (he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _))
  obtain ⟨y, rfl⟩ := hLift x
  let Γ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨(sIdeleInsertion F S).comp γ.toMonoidHom,
      (isClosedEmbedding_sIdeleInsertion F S).continuous.comp γ.continuous⟩
  let u (s : ℝ) := sAdeleSchwartzToGlobal F S f
    (Multiplicative.ofAdd ((sIdeleInsertion F S (γ (expUnit s))).val * y.val))
  let v (s : ℝ) := f (Multiplicative.ofAdd ((γ (expUnit s)).val * adeleProjection F S y.val))
  have hp (s : ℝ) : u s = v s :=
    sAdeleSchwartzToGlobal_mul_sIdeleInsertion F S f (γ (expUnit s)) y
  have hu : DifferentiableAt ℝ u 0 :=
    adeleOrbit_differentiableAt Γ (sAdeleSchwartzToGlobal F S f) (Multiplicative.ofAdd y.val)
  change DifferentiableAt ℝ v 0
  exact (funext hp) ▸ hu

/-- Paper: Lemma 2.3.2.1, p. 106. Taking the directional derivative
is complex linear on the S-local test space. -/
theorem sAdeleDirectionalDeriv_isLinear :
    IsLinearMap ℂ (fun f : ℬₛ ↦ (⟨orbitDeriv f, sAdeleDirectionalDeriv_mem F S γ f⟩ : ℬₛ)) := by
  constructor
  · intro f g
    apply Subtype.ext
    funext x
    exact deriv_add (sAdeleOrbit_differentiableAt F S γ f x) (sAdeleOrbit_differentiableAt F S γ g x)
  · intro c f
    apply Subtype.ext
    funext x
    exact deriv_fun_const_smul_field c _

/-- Paper: Equation (2.3.2.1), p. 105. The directional derivative differentiates
the test function along the given one-parameter subgroup at the identity.
Deviation: As in the global definition, the derivative uses `t = exp s` at `s = 0`. -/
def sAdeleDirectionalDeriv : ℬₛ →ₗ[ℂ] ℬₛ :=
  IsLinearMap.mk' (fun f ↦ ⟨orbitDeriv f, sAdeleDirectionalDeriv_mem F S γ f⟩)
    (sAdeleDirectionalDeriv_isLinear F S γ)

/-- At the identity, a derivative in logarithmic coordinates gives the same slope
in the positive real parameter, since the derivative of the logarithm at one is one. -/
private theorem tendsto_unitSlope_of_hasDerivAt (u : ℝ≥0ˣ → ℂ) {d : ℂ}
    (hd : HasDerivAt (fun s : ℝ ↦ u (expUnit s)) d 0) :
    Tendsto (fun t : ℝ≥0ˣ ↦ (u t - u 1) / ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 d) := by
  have hLog := hd.scomp_of_eq (1 : ℝ) (Real.hasDerivAt_log one_ne_zero) Real.log_one.symm
  rw [inv_one, one_smul] at hLog
  have hVal : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.comp Units.continuous_val).continuousAt.continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  refine (hLog.tendsto_slope.comp hVal).congr' (.of_forall fun t ↦ ?_)
  have ht : expUnit (Real.log (valueℝ t)) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  have h0 : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  simp only [Function.comp_apply, slope_def_module, Real.log_one, ht, h0, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, div_eq_inv_mul]

/-- Paper: Lemma 2.3.2.1, p. 105. The difference quotient in the positive
real parameter converges to the S-adelic directional derivative. -/
theorem sAdeleDirectionalDeriv_tendsto (f : ℬₛ) (x : Aₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sAdeleDirectionalDeriv F S γ f (Multiplicative.ofAdd x))) := by
  change Tendsto _ _ (𝓝 (orbitDeriv f (Multiplicative.ofAdd x)))
  simpa only [map_one, Units.val_one, one_mul] using
    tendsto_unitSlope_of_hasDerivAt (fun t ↦ f (Multiplicative.ofAdd ((γ t).val * x)))
      (sAdeleOrbit_differentiableAt F S γ f (Multiplicative.ofAdd x)).hasDerivAt

/-- Paper: Lemma 2.3.2.1, p. 105. The directional derivative of a fixed
test function is continuous in the S-adele argument. -/
theorem sAdeleDirectionalDeriv_continuous_apply (f : ℬₛ) :
    Continuous (fun x : Aₛ ↦ sAdeleDirectionalDeriv F S γ f (Multiplicative.ofAdd x)) :=
  (schwartzBruhat_continuous (sAdeleDirectionalDeriv F S γ f)).comp continuous_ofAdd

/-- Paper: Lemma 2.3.2.1, p. 106. The directional derivative is continuous
as an endomorphism of the S-local Schwartz–Bruhat space. -/
theorem sAdeleDirectionalDeriv_continuous :
    Continuous (sAdeleDirectionalDeriv F S γ) := by
  classical
  let Γ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨(sIdeleInsertion F S).comp γ.toMonoidHom,
      (isClosedEmbedding_sIdeleInsertion F S).continuous.comp γ.continuous⟩
  have he := sAdeleSchwartzToGlobal_isEmbedding F S
  apply he.isInducing.continuous_iff.mpr
  refine ((adeleDirectionalDeriv_continuous Γ).comp he.continuous).congr fun f ↦ ?_
  apply Subtype.ext
  funext x
  change deriv (fun s : ℝ ↦ sAdeleSchwartzToGlobal F S f
    (Multiplicative.ofAdd ((sIdeleInsertion F S (γ (expUnit s))).val * x.toAdd))) 0 =
      sAdeleSchwartzToGlobal F S (sAdeleDirectionalDeriv F S γ f) (Multiplicative.ofAdd x.toAdd)
  refine Eq.trans ?_ (sAdeleSchwartzToGlobal_apply F S _ x.toAdd).symm
  by_cases hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x.toAdd.2 v ∈ v.adicCompletionIntegers F
  · refine Eq.trans ?_ (ite_eq_left hx).symm
    have hy : x.toAdd ∈ integralAdelesOutside F S := by
      simp only [integralAdelesOutside, Subring.mem_iInf]
      intro v hv
      exact hx v hv
    exact congrArg (fun u : ℝ → ℂ ↦ deriv u 0) (funext fun s ↦
      sAdeleSchwartzToGlobal_mul_sIdeleInsertion F S f (γ (expUnit s)) ⟨x.toAdd, hy⟩)
  · refine Eq.trans ?_ (ite_eq_right hx).symm
    have hz (s : ℝ) : sAdeleSchwartzToGlobal F S f
          (Multiplicative.ofAdd ((sIdeleInsertion F S (γ (expUnit s))).val * x.toAdd)) = 0 := by
      refine (sAdeleSchwartzToGlobal_apply F S f _).trans (ite_eq_right ?_)
      intro h
      apply hx
      intro v hv
      have hmem := h v hv
      change (sIdeleInsertion F S (γ (expUnit s))).val.2 v * x.toAdd.2 v ∈ _ at hmem
      rwa [(sIdeleInsertion_apply F S _).2.2 v hv, one_mul] at hmem
    exact (congrArg (fun u : ℝ → ℂ ↦ deriv u 0) (funext hz)).trans (deriv_const _ _)

/-- On a compact logarithmic orbit segment, the derivatives of the S-unit terms
have a common summable majorant. Thus theta can be differentiated term by term. -/
private theorem sLocalAdelicTheta_hasDerivAt (f : ℬₛ) (g : Iₛ) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ sLocalAdelicTheta F S f (γ (expUnit t) * g))
      (sLocalAdelicTheta F S (sAdeleDirectionalDeriv F S γ f) (γ (expUnit s) * g)) s := by
  let E : ℝ → ℝ≥0ˣ := expUnit
  let a (t : ℝ) := γ (E t) * g
  let d := sAdeleDirectionalDeriv F S γ f
  let term (φ : ℬₛ) (ξ : Uₛ) (t : ℝ) := thetaTerm φ ξ (a t)
  have hterm (ξ : Uₛ) (t : ℝ) : HasDerivAt (term f ξ) (term d ξ t) t := by
    let x := (unitAtS ξ * a t).val
    have h : HasDerivAt (fun r : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit r)).val * x)))
        (term d ξ t) (t - t) := by
      rw [sub_self]
      exact (sAdeleOrbit_differentiableAt F S γ f (Multiplicative.ofAdd x)).hasDerivAt
    refine (h.comp_sub_const t t).congr_of_eventuallyEq (.of_forall fun r ↦ ?_)
    have hAdd (v w : ℝ) : E (v + w) = E v * E w :=
      Units.ext (NNReal.coe_inj.mp (Real.exp_add v w))
    have hm : unitAtS ξ * a r = γ (E (r - t)) * (unitAtS ξ * a t) := by
      change unitAtS ξ * (γ (E r) * g) = γ (E (r - t)) * (unitAtS ξ * (γ (E t) * g))
      rw [mul_left_comm (γ (E (r - t))) (unitAtS ξ), ← mul_assoc (γ (E (r - t))) (γ (E t)) g,
        ← map_mul γ, ← hAdd, sub_add_cancel]
    exact congrArg (fun z : Iₛ ↦ f (Multiplicative.ofAdd z.val)) hm
  have hE : Continuous E :=
    (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous
  have ha : Continuous a := (γ.continuous.comp hE).mul_const g
  let K := a '' Icc (s - 1) (s + 1)
  have hK : IsCompact K := isCompact_Icc.image ha
  refine (sLocalAdelicTheta_exists_summable_bound F S d K hK).elim fun u hu ↦ ?_
  have hs : s ∈ Ioo (s - 1) (s + 1) :=
    ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩
  change HasDerivAt (fun t ↦ ∑' ξ, term f ξ t) (∑' ξ, term d ξ s) s
  have hsum : Summable (fun ξ ↦ term f ξ s) :=
    ((sLocalAdelicTheta_hasSumUniformlyOn F S f {a s} isCompact_singleton).hasSum rfl).summable
  have hle (ξ : Uₛ) (t : ℝ) (ht : t ∈ Ioo (s - 1) (s + 1)) : ‖term d ξ t‖ ≤ u ξ :=
    hu.2 ξ (a t) (mem_image_of_mem a (Ioo_subset_Icc_self ht))
  exact hasDerivAt_tsum_of_isPreconnected (g := term f) (g' := term d)
    (t := Ioo (s - 1) (s + 1)) hu.1 isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ ↦ hterm ξ t) hle hs hsum hs

/-- Convert a logarithmic derivative along an S-idele orbit to its difference
quotient at the base idele. -/
private theorem sIdeleOrbit_tendsto_of_hasDerivAt (u v : Iₛ → ℂ) (g : Iₛ)
    (h : HasDerivAt (fun s : ℝ ↦ u (γ (expUnit s) * g)) (v (γ (expUnit (0 : ℝ)) * g)) 0) :
    Tendsto (fun t : ℝ≥0ˣ ↦ (u (γ t * g) - u g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (v g)) := by
  let a (t : ℝ≥0ˣ) := γ t * g
  have hOne : a 1 = g := (congrArg (· * g) (map_one γ)).trans (one_mul g)
  have hZero : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hv : v (a (expUnit (0 : ℝ))) = v g := congrArg v ((congrArg a hZero).trans hOne)
  have hd : HasDerivAt (fun s : ℝ ↦ u (a (expUnit s))) (v g) 0 := hv ▸ h
  exact (tendsto_unitSlope_of_hasDerivAt (fun t ↦ u (a t)) hd).congr fun t ↦
    congrArg (fun z ↦ (u (a t) - u z) / ((valueℝ t : ℂ) - 1)) hOne

-- TODO(paper-gap): Equations (2.3.2.2)–(2.3.2.3) print τ(t) in both quotients.
-- For ℚ, S = {∞}, f(x) = exp(-x²), g = 1, and trivial γ, the τ derivative
-- of ordinary theta is -4/e, whereas the right side of (2.3.2.4) is zero.

/-- Paper: Proposition 2.3.2.2, p. 106. The directional difference quotient
of S-local theta converges to theta of the differentiated test function.
The limit is a continuous S-unit invariant function of the idele.
Deviation: Uses γ in (2.3.2.2), as specified by (2.3.2.4) and Lemma 2.3.2.1. -/
theorem sLocalAdelicTheta_directionalDeriv (f : ℬₛ) (g : Iₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (sLocalAdelicTheta F S f (γ t * g) - sLocalAdelicTheta F S f g) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sLocalAdelicTheta F S (sAdeleDirectionalDeriv F S γ f) g)) := by
  exact sIdeleOrbit_tendsto_of_hasDerivAt F S γ (sLocalAdelicTheta F S f)
    (sLocalAdelicTheta F S (sAdeleDirectionalDeriv F S γ f)) g
    (sLocalAdelicTheta_hasDerivAt F S γ f g 0)

/-- Paper: Proposition 2.3.2.2, p. 106. The directional difference quotient
of homogeneous theta converges to homogeneous theta of the differentiated test
function. The limit is continuous on the S-idele classes.
Deviation: Uses γ in (2.3.2.3), as specified by (2.3.2.4) and Lemma 2.3.2.1. -/
theorem sLocalHomogeneousAdelicTheta_directionalDeriv
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm F S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual J₁) (f : ℬₛ) (g : Iₛ) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (sLocalHomogeneousAdelicTheta F S μ ω f (classOf (γ t * g)) -
        sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1)
      (𝓝 (sLocalHomogeneousAdelicTheta F S μ ω (sAdeleDirectionalDeriv F S γ f) (classOf g))) := by
  let E : ℝ → ℝ≥0ˣ := expUnit
  let a (s : ℝ) := γ (E s) * g
  let d := sAdeleDirectionalDeriv F S γ f
  let term (φ : ℬₛ) (s : ℝ) (h : J₁) :=
    sLocalAdelicThetaOnClasses F S φ (classOf (a s) * h.val) * (ω h : ℂ)
  have hInt (φ : ℬₛ) (s : ℝ) : Integrable (term φ s) μ :=
    sLocalHomogeneousAdelicTheta_integrable F S μ ω φ (classOf (a s))
  have hTerm (h : J₁) (s : ℝ) : HasDerivAt (fun t ↦ term f t h) (term d s h) s := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective h.val
    have hEval (φ : ℬₛ) (t : ℝ) : term φ t h =
        sLocalAdelicTheta F S φ (γ (expUnit t) * (g * k)) * (ω h : ℂ) := by
      have hclass : classOf (a t) * h.val = classOf (γ (expUnit t) * (g * k)) := by
        rw [← hk, ← QuotientGroup.mk_mul, ← mul_assoc]
      exact congrArg (· * (ω h : ℂ)) ((congrArg (sLocalAdelicThetaOnClasses F S φ) hclass).trans
        (sLocalAdelicThetaOnClasses_mk F S φ _))
    rw [hEval d s]
    exact ((sLocalAdelicTheta_hasDerivAt F S γ f (g * k) s).mul_const (ω h : ℂ))
      |>.congr_of_eventuallyEq (.of_forall (hEval f))
  have hE : Continuous E :=
    (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous
  have ha : Continuous a := (γ.continuous.comp hE).mul_const g
  let K := a '' Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image ha
  refine (sLocalHomogeneousAdelicTheta_integrand_bounded F S μ ω d K hK).elim fun C hC ↦ ?_
  have hDiff := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := term f) (F' := term d)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) zero_lt_one)
    (.of_forall fun t ↦ (hInt f t).aestronglyMeasurable) (hInt f 0)
    (hInt d 0).aestronglyMeasurable
    (.of_forall fun h t ht ↦ hC.2.2 (a t) (mem_image_of_mem a ht) h) hC.2.1
    (.of_forall fun h t _ ↦ hTerm h t)).2
  change HasDerivAt (fun t ↦ sLocalHomogeneousAdelicTheta F S μ ω f (classOf (a t)))
    (sLocalHomogeneousAdelicTheta F S μ ω d (classOf (a 0))) 0 at hDiff
  exact sIdeleOrbit_tendsto_of_hasDerivAt F S γ
    (fun k ↦ sLocalHomogeneousAdelicTheta F S μ ω f (classOf k))
    (fun k ↦ sLocalHomogeneousAdelicTheta F S μ ω d (classOf k)) g hDiff

-- Remark 2.3.2.3, p. 106, defers the comparison with global theta to the
-- Mellin-transform constructions in Chapters 3–6.

end DirectionalDerivatives

end RiemannMasullo
