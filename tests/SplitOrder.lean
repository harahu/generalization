/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.FieldTheory.FinTrdeg
import GeneralizationLinter

/-!
# Replacements of a split that depend on each other

A split can replace a binder with classes that need data from one another: `NoZeroDivisors F` is
stated for the multiplication and zero of `CommRing F`. The replacement binders must be built from
each other, whatever the order of the split, and never from the binder they replace.
-/

namespace GeneralizationLinter.Test.SplitOrder

universe u v w

variable {k : Type u} {k' : Type v} {F : Type w} [Field k] [Field k'] [Field F]
variable [Algebra k k'] [Algebra k' F] [Algebra k F] [IsScalarTower k k' F]

/--
warning: the `[Field F]` hypothesis of `GeneralizationLinter.Test.SplitOrder.isAlgebraic_of_trdeg_eq` can be split into `Nontrivial F`, `NoZeroDivisors F`, `CommRing F`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "prefer" in
theorem isAlgebraic_of_trdeg_eq (h : Algebra.trdeg k' F = Algebra.trdeg k F)
    (hfin : Algebra.trdeg k F < Cardinal.aleph0) : Algebra.IsAlgebraic k k' := by
  rw [← trdeg_eq_zero_iff]
  have hadd := lift_trdeg_add_eq k k' F
  rw [h] at hadd
  rcases Cardinal.add_eq_right_iff.mp hadd with hle | hzero
  · exact absurd ((le_max_left _ _).trans hle) (not_le.2 (Cardinal.lift_lt_aleph0.2 hfin))
  · simpa using hzero

end GeneralizationLinter.Test.SplitOrder
