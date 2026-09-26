/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.NatInt
import GeneralizationLinter

/-!
# Vacuity bridges for families of instances

A bridge that undoes a weakening of `[AddCommGroup M]` also undoes the same weakening of a family
`[∀ i, AddCommGroup (N i)]`, taken pointwise. The strictness guard should apply its bridges to such
families, matching them against the families of instances in scope.
-/

namespace GeneralizationLinter.Test.PiBridges

/-! ### A family of modules over a ring is a family of additive groups -/

/--
warning: the `[(i : ι) → AddCommGroup (N i)]` hypothesis of `GeneralizationLinter.Test.PiBridges.sub_smul_eq` can be weakened to `(i : ι) → AddCommMonoid (N i)`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.strictnessGuard false in
theorem sub_smul_eq {ι R : Type} [Ring R] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (r s : R) (x : ∀ i, N i) : (r - s) • x = r • x + (-s) • x := by
  rw [sub_eq_add_neg, add_smul]

#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem sub_smul_eq' {ι R : Type} [Ring R] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (r s : R) (x : ∀ i, N i) : (r - s) • x = r • x + (-s) • x := by
  rw [sub_eq_add_neg, add_smul]

end GeneralizationLinter.Test.PiBridges
