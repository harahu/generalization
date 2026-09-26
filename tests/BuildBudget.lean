/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter

/-!
# Verifying within the budget of a build

With `generalizeTypeclasses.buildHeartbeats` set, a proof, and the conclusion's source, are
re-elaborated against a weakened statement under that budget, the `maxHeartbeats` a build gives
each declaration. One that runs out of it would not compile as it stands, so the weakening is
reported as one whose proof or conclusion may have to be modified, rather than dropped as a
truncated analysis.
-/

namespace GeneralizationLinter.Test.BuildBudget

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

/-! ### A proof that fits the budget of a build -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.BuildBudget.fits` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.buildHeartbeats 200000 in
theorem fits {α : Type} [Rich α] : (Base.x : α) = Base.x ∧ (List.range 40).length = 40 :=
  ⟨rfl, by decide⟩

/-! ### A proof that does not fit the budget of a build -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.BuildBudget.exceeds` can be weakened to `Base α`, but its conclusion and its proof may have to be modified.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.buildHeartbeats 1 in
theorem exceeds {α : Type} [Rich α] : (Base.x : α) = Base.x ∧ (List.range 40).length = 40 :=
  ⟨rfl, by decide⟩

/-! ### Without a build budget, running out of the linter's own budget truncates -/

#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.perCandidateHeartbeats 1000 in
theorem truncated {α : Type} [Rich α] : (Base.x : α) = Base.x ∧ (List.range 40).length = 40 :=
  ⟨rfl, by decide⟩

end GeneralizationLinter.Test.BuildBudget
