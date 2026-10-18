/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Module.Rat
import GeneralizationLinter

/-!
# Bridge rules

Every `GeneralizationLinter.bridgeRules` entry is a statement the linter trusts, so it must be
proved: this file proves each one, and `#check_bridge_rules` fails unless every rule elaborates here
and names a declaration of this file whose type is the rule's statement: a theorem for a rule
concluding a proposition, and a definition for one concluding a data-carrying class.
-/

namespace GeneralizationLinter.Test.BridgeRules

open Lean Meta Elab Command

universe u

theorem neZero_of_fintype_zmod : ∀ (n : ℕ) [Fintype (ZMod n)], NeZero n := by
  intro n _
  refine ⟨?_⟩
  rintro rfl
  have : Fintype ℤ := ‹Fintype (ZMod 0)›
  exact not_finite ℤ

noncomputable abbrev normedAddCommGroup_of_t0 :
    ∀ (E : Type u) [SeminormedAddCommGroup E] [T0Space E], NormedAddCommGroup E :=
  fun _ _ _ ↦ NormedAddCommGroup.ofSeparation fun _ h ↦ (inseparable_zero_iff_norm.mpr h).eq

noncomputable abbrev normedRing_of_t0 :
    ∀ (R : Type u) [SeminormedRing R] [T0Space R], NormedRing R :=
  fun R _ _ ↦ { ‹SeminormedRing R›, MetricSpace.ofT0PseudoMetricSpace R with }

noncomputable abbrev field_of_isSimpleRing :
    ∀ (R : Type u) [CommRing R] [IsSimpleRing R], Field R :=
  fun R _ _ ↦ ((isSimpleRing_iff_isField R).mp inferInstance).toField

theorem polishSpace_of_isCompletelyPseudoMetrizableSpace :
    ∀ (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] [T0Space X]
      [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X], PolishSpace X := by
  intro X _ _ _ _
  have := TopologicalSpace.IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace (X := X)
  infer_instance

theorem isTopologicalAddGroup_of_continuousSub :
    ∀ (G : Type u) [AddGroup G] [TopologicalSpace G] [ContinuousSub G],
      IsTopologicalAddGroup G := by
  intro G _ _ _
  have hneg : Continuous fun x : G => -x := by
    convert (continuous_const (y := (0 : G))).sub continuous_id using 1
    ext x
    simp
  refine { continuous_add := ?_, continuous_neg := hneg }
  convert continuous_fst.sub (hneg.comp continuous_snd) using 1
  ext p
  simp

theorem isTopologicalGroup_of_continuousDiv :
    ∀ (G : Type u) [Group G] [TopologicalSpace G] [ContinuousDiv G], IsTopologicalGroup G := by
  intro G _ _ _
  have hinv : Continuous fun x : G => x⁻¹ := by
    convert (continuous_const (y := (1 : G))).div' continuous_id using 1
    ext x
    simp
  refine { continuous_mul := ?_, continuous_inv := hinv }
  convert continuous_fst.div' (hinv.comp continuous_snd) using 1
  ext p
  simp

theorem isTopologicalRing_of_continuousSub :
    ∀ (R : Type u) [Ring R] [TopologicalSpace R] [ContinuousSub R] [ContinuousMul R],
      IsTopologicalRing R := by
  intro R _ _ _ _
  have := isTopologicalAddGroup_of_continuousSub R
  exact {}

theorem nonarchimedeanRing_of_nonarchimedeanAddGroup :
    ∀ (R : Type u) [Ring R] [TopologicalSpace R] [NonarchimedeanAddGroup R] [ContinuousMul R],
      NonarchimedeanRing R := by
  intro R _ _ _ _
  exact { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }

/-! ### Equivalent hypotheses from Tau Ceti rejections -/

noncomputable section

abbrev field_of_isAlgebraic (k E : Type*) [Field k] [CommRing E] [Nontrivial E]
    [NoZeroDivisors E] [Algebra k E] [Algebra.IsAlgebraic k E] : Field E := by
  letI : IsDomain E := NoZeroDivisors.to_isDomain E
  letI : Algebra.IsIntegral k E := Algebra.IsAlgebraic.isIntegral
  exact (isField_of_isIntegral_of_isField' (Field.toIsField k)).toField

abbrev field_of_finite (E : Type*) [CommRing E] [Nontrivial E] [NoZeroDivisors E]
    [Finite E] : Field E := by
  letI : IsDomain E := NoZeroDivisors.to_isDomain E
  letI := Fintype.ofFinite E
  letI := Classical.decEq E
  exact Fintype.fieldOfDomain E

abbrev commRing_of_algebra (R A : Type*) [CommRing R] [CommSemiring A] [Algebra R A] : CommRing A :=
  { Algebra.semiringToRing R with mul_comm := mul_comm }

abbrev addCancelCommMonoid_of_isLeftCancelAdd (M : Type*) [AddCommMonoid M] [IsLeftCancelAdd M] :
    AddCancelCommMonoid M :=
  { (inferInstance : AddCommMonoid M) with
    add_left_cancel := fun _ _ _ h => add_left_cancel h }

abbrev commGroup_of_isMulCommutative (G : Type*) [Group G] [IsMulCommutative G] : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }

abbrev commRing_of_isCentralScalar (R : Type*) [Ring R] [IsCentralScalar R R] : CommRing R :=
  { (inferInstance : Ring R) with mul_comm := fun a b => op_smul_eq_smul b a }

abbrev normedSpace_of_normSMulClass (K N : Type*) [NormedField K] [SeminormedAddCommGroup N]
    [Module K N] [NormSMulClass K N] : NormedSpace K N where
  norm_smul_le a b := (norm_smul a b).le

abbrev algebra_of_isScalarTower (A R : Type*) [CommSemiring A] [CommSemiring R]
    [Module A R] [IsScalarTower A R R] : Algebra A R :=
  Algebra.ofModule smul_mul_assoc fun a r s => by
    rw [mul_comm, smul_mul_assoc, mul_comm]

abbrev algebraRat_of_module (K : Type*) [Ring K] [Module ℚ K] : Algebra ℚ K :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem connectedSpace_of_preconnectedSpace (X : Type*) [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X] :
    ConnectedSpace X := { toNonempty := inferInstance }

theorem isGalois_of_normal_of_isSeparable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Normal K L] [Algebra.IsSeparable K L] : IsGalois K L :=
  { to_isSeparable := inferInstance, to_normal := inferInstance }

abbrev unique_of_subsingleton (X : Type*) [Inhabited X] [Subsingleton X] : Unique X :=
  { (inferInstance : Inhabited X) with uniq := fun _ => Subsingleton.elim _ _ }

theorem ringHomClass_of_addMonoidHomClass (F A B : Type*) [NonAssocSemiring A] [NonAssocSemiring B]
    [FunLike F A B] [MonoidHomClass F A B] [AddMonoidHomClass F A B] : RingHomClass F A B :=
  { (inferInstance : MonoidHomClass F A B), (inferInstance : AddMonoidHomClass F A B) with }

theorem isOrderedRing_of_posMulMono (R : Type*) [CommRing R] [LinearOrder R] [IsOrderedAddMonoid R]
    [PosMulMono R] : IsOrderedRing R := by
  have : ZeroLEOneClass R := ⟨by
    by_contra h
    have h1 : 1 < (0 : R) := lt_of_not_ge h
    have hm : 0 ≤ (-1 : R) := le_of_lt (neg_pos.mpr h1)
    have hh : 0 ≤ (-1 : R) * (-1) := mul_nonneg hm hm
    have hh1 : (0 : R) ≤ 1 := by simpa only [neg_mul_neg, one_mul] using hh
    exact (not_le_of_gt h1) hh1⟩
  exact IsOrderedRing.of_mul_nonneg fun _ _ ha hb => mul_nonneg ha hb

theorem isStrictOrderedRing_of_posMulMono (R : Type*) [Field R] [LinearOrder R]
    [IsOrderedAddMonoid R] [PosMulMono R] : IsStrictOrderedRing R := by
  let := isOrderedRing_of_posMulMono R
  infer_instance

theorem isStrictOrderedRing_of_mulPosMono (R : Type*) [Field R] [LinearOrder R]
    [IsOrderedAddMonoid R] [MulPosMono R] : IsStrictOrderedRing R := by
  have : PosMulMono R := posMulMono_iff_mulPosMono.mpr inferInstance
  exact isStrictOrderedRing_of_posMulMono R

abbrev addLeftCancelMonoid_of_isLeftCancelAdd (N : Type*) [AddMonoid N] [IsLeftCancelAdd N] :
    AddLeftCancelMonoid N :=
  { (inferInstance : AddMonoid N) with add_left_cancel := fun _ _ _ h => add_left_cancel h }

abbrev addRightCancelMonoid_of_isRightCancelAdd (N : Type*) [AddMonoid N] [IsRightCancelAdd N] :
    AddRightCancelMonoid N :=
  { (inferInstance : AddMonoid N) with add_right_cancel := fun _ _ _ h => add_right_cancel h }

abbrev rightCancelMonoid_of_isRightCancelMul (N : Type*) [Monoid N] [IsRightCancelMul N] :
    RightCancelMonoid N :=
  { (inferInstance : Monoid N) with mul_right_cancel := fun _ _ _ h => mul_right_cancel h }

theorem ringHomClass_of_addHomClass (F A B : Type*) [NonAssocRing A] [NonAssocRing B]
    [FunLike F A B] [MonoidHomClass F A B] [AddHomClass F A B] : RingHomClass F A B :=
  { (inferInstance : MonoidHomClass F A B), (inferInstance : AddHomClass F A B) with
    map_zero := fun f => add_left_cancel (show f 0 + f 0 = f 0 + 0 by
      simpa only [zero_add, add_zero] using (map_add f (0 : A) 0).symm) }

theorem subfieldClass_of_parts (S K : Type*) [DivisionRing K] [SetLike S K]
    [AddSubmonoidWithOneClass S K] [SubmonoidClass S K] [InvMemClass S K]
    [AddSubgroupClass S K] : SubfieldClass S K :=
  { (inferInstance : AddSubmonoidWithOneClass S K), (inferInstance : SubmonoidClass S K),
    (inferInstance : InvMemClass S K), (inferInstance : AddSubgroupClass S K) with }

theorem isTopologicalSemiring_of_continuousSMul (R : Type*) [Semiring R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousSMul R R] : IsTopologicalSemiring R where
  continuous_mul := continuous_smul

theorem isTopologicalRing_of_continuousSMul (R : Type*) [Ring R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousSMul R R] : IsTopologicalRing R := by
  have : ContinuousMul R := ⟨continuous_smul⟩
  exact IsTopologicalSemiring.toIsTopologicalRing (show IsTopologicalSemiring R from {})

theorem contMDiffMul_of_contMDiffSMul (𝕜 H E : Type*) [NontriviallyNormedField 𝕜]
    [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (G : Type*) [Mul G] [TopologicalSpace G] [ChartedSpace H G]
    [IsManifold I n G] [ContMDiffSMul I I n G G] : ContMDiffMul I n G where
  contMDiff_mul := contMDiff_smul

theorem isTopologicalRing_of_continuousMul (R : Type*) [NonAssocRing R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousMul R] : IsTopologicalRing R :=
  IsTopologicalSemiring.toIsTopologicalRing (show IsTopologicalSemiring R from {})

end

/-- Checks every bridge rule against the theorem it names. -/
elab "#check_bridge_rules" : command => liftTermElabM do
  for r in bridgeRules do
    let some abst ← r.elaborated? | throwError "the rule `{r.statement}` does not elaborate"
    let some c := (← getEnv).find? r.proof
      | throwError "the rule `{r.statement}` names `{r.proof}`, which does not exist"
    let (_, _, statement) ← openAbstractMVarsResult abst
    let proved ← instantiateTypeLevelParams c.toConstantVal (← mkFreshLevelMVars c.numLevelParams)
    unless ← isDefEq statement proved do
      throwError "`{r.proof}` proves `{proved}`, not the rule `{statement}`"
  logInfo m!"all {bridgeRules.size} bridge rules are proved"

/-- info: all 34 bridge rules are proved -/
#guard_msgs in
#check_bridge_rules

/-! ### The rule blocks the weakening it undoes -/

/--
warning: the `[NeZero n]` hypothesis of `GeneralizationLinter.Test.BridgeRules.mem_univ_zmod` can be weakened to `Fintype (ZMod n)`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.strictnessGuard false in
theorem mem_univ_zmod (n : ℕ) [NeZero n] (x : ZMod n) : x ∈ (Finset.univ : Finset (ZMod n)) :=
  Finset.mem_univ x

#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem mem_univ_zmod' (n : ℕ) [NeZero n] (x : ZMod n) : x ∈ (Finset.univ : Finset (ZMod n)) :=
  Finset.mem_univ x

/--
warning: the `[IsTopologicalAddGroup M]` hypothesis of `GeneralizationLinter.Test.BridgeRules.continuous_sub_add_neg` can be weakened to `ContinuousSub M`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.strictnessGuard false in
theorem continuous_sub_add_neg {M : Type*} [AddGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] : (Continuous fun p : M × M => p.1 - p.2) ∧ ∀ x : M, x + -x = 0 :=
  ⟨continuous_sub, add_neg_cancel⟩

#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem continuous_sub_add_neg' {M : Type*} [AddGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] : (Continuous fun p : M × M => p.1 - p.2) ∧ ∀ x : M, x + -x = 0 :=
  ⟨continuous_sub, add_neg_cancel⟩

#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem continuous_div_mul_inv' {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (Continuous fun p : G × G => p.1 / p.2) ∧ ∀ x : G, x * x⁻¹ = 1 :=
  ⟨continuous_div', mul_inv_cancel⟩

/--
warning: the `[Algebra ℚ K]` hypothesis of `GeneralizationLinter.Test.BridgeRules.add_smul_rat` can be weakened to `_root_.Module ℚ K`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.strictnessGuard false in
theorem add_smul_rat {K : Type*} [Ring K] [Algebra ℚ K] (q r : ℚ) (x y : K) :
    (q + r) • x = q • x + r • x ∧ x * y * x - 1 * y = x * (y * x) + -y :=
  ⟨add_smul q r x, by rw [mul_assoc, one_mul, sub_eq_add_neg]⟩

#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem add_smul_rat' {K : Type*} [Ring K] [Algebra ℚ K] (q r : ℚ) (x y : K) :
    (q + r) • x = q • x + r • x ∧ x * y * x - 1 * y = x * (y * x) + -y :=
  ⟨add_smul q r x, by rw [mul_assoc, one_mul, sub_eq_add_neg]⟩

end GeneralizationLinter.Test.BridgeRules
