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
    ∀ (G : Type u) [AddGroup G] [TopologicalSpace G] [ContinuousAdd G] [ContinuousSub G],
      IsTopologicalAddGroup G := by
  intro G _ _ _ _
  refine { continuous_neg := ?_ }
  convert (continuous_const (y := (0 : G))).sub continuous_id using 1
  ext x
  simp

theorem isTopologicalRing_of_continuousSub :
    ∀ (R : Type u) [Ring R] [TopologicalSpace R] [ContinuousSub R] [ContinuousNeg R]
      [ContinuousMul R], IsTopologicalRing R := by
  intro R _ _ _ _ _
  have : ContinuousAdd R := ⟨by
    convert continuous_fst.sub (continuous_snd.neg (G := R)) using 1
    ext p
    simp⟩
  exact {}

theorem nonarchimedeanRing_of_nonarchimedeanAddGroup :
    ∀ (R : Type u) [Ring R] [TopologicalSpace R] [NonarchimedeanAddGroup R] [ContinuousMul R],
      NonarchimedeanRing R := by
  intro R _ _ _ _
  exact { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }

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

/-- info: all 8 bridge rules are proved -/
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

end GeneralizationLinter.Test.BridgeRules
