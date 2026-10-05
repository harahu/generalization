/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.Algebra.Module.Defs
import GeneralizationLinter

/-!
# Keeping split replacements in their elaborated order

Splitting an additive cancellation monoid builds the additive monoid before its cancellation
property. A later fixpoint pass can weaken the monoid to `Add`, but must keep cancellation in the
reported split. Even without a later pass, the reported binders must be in a valid dependency order.
-/

namespace GeneralizationLinter.Test.SplitFixpointOrder

/--
warning: the `[Semiring R]` hypothesis of `GeneralizationLinter.Test.SplitFixpointOrder.cancelAction` can be weakened to `Monoid R`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[AddCancelCommMonoid N]` hypothesis of `GeneralizationLinter.Test.SplitFixpointOrder.cancelAction` can be split into `Add N`, `IsLeftCancelAdd N`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[Module R N]` hypothesis of `GeneralizationLinter.Test.SplitFixpointOrder.cancelAction` can be weakened to `MulAction R N`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "prefer" in
theorem cancelAction {R N : Type*} [Semiring R] [AddCancelCommMonoid N] [Module R N]
    (x y z : N) (h : x + y = x + z) : y = z ∧ (1 : R) • y = y :=
  ⟨add_left_cancel h, one_smul R y⟩

-- Applying the complete reported weakening leaves the proof unchanged.
theorem cancelActionApplied {R N : Type*} [Monoid R] [Add N] [IsLeftCancelAdd N] [MulAction R N]
    (x y z : N) (h : x + y = x + z) : y = z ∧ (1 : R) • y = y :=
  ⟨add_left_cancel h, one_smul R y⟩

/--
warning: the `[AddCancelCommMonoid N]` hypothesis of `GeneralizationLinter.Test.SplitFixpointOrder.needsModule` can be split into `AddCommMonoid N`, `IsLeftCancelAdd N`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "prefer" in
theorem needsModule {R N : Type*} [Semiring R] [AddCancelCommMonoid N] [Module R N]
    (x y z : N) (h : x + y = x + z) : y = z ∧ Nonempty (Module R N) :=
  ⟨add_left_cancel h, ⟨inferInstance⟩⟩

-- The first replacement supplies the operation used by the cancellation property.
theorem needsModuleApplied {R N : Type*} [Semiring R] [AddCommMonoid N] [IsLeftCancelAdd N]
    [Module R N] (x y z : N) (h : x + y = x + z) : y = z ∧ Nonempty (Module R N) :=
  ⟨add_left_cancel h, ⟨inferInstance⟩⟩

end GeneralizationLinter.Test.SplitFixpointOrder
