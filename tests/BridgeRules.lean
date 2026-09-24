/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Fintype.Basic
import GeneralizationLinter

/-!
# Bridge rules

Every `GeneralizationLinter.bridgeRules` entry is a statement the linter trusts, so it must be
proved: this file proves each one, and `#check_bridge_rules` fails unless every rule elaborates here
and names a theorem of this file whose type is the rule's statement.
-/

namespace GeneralizationLinter.Test.BridgeRules

open Lean Meta Elab Command

theorem neZero_of_fintype_zmod : ∀ (n : ℕ) [Fintype (ZMod n)], NeZero n := by
  intro n _
  refine ⟨?_⟩
  rintro rfl
  have : Fintype ℤ := ‹Fintype (ZMod 0)›
  exact not_finite ℤ

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

/-- info: all 1 bridge rules are proved -/
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
