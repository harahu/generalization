/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.Topology.Algebra.Group.Basic
import GeneralizationLinter

/-!
# Splits into a class's own parts

A class that only bundles its parent classes, such as `IsTopologicalGroup` bundling `ContinuousMul`
and `ContinuousInv`, is rebuilt from those parents, so splitting it into them restates the
hypothesis. The strictness guard should withhold such a split, and still allow one that leaves a
field out.
-/

namespace GeneralizationLinter.Test.PartsAssembly

/-! ### A split into the parents that make up the class -/

/--
warning: the `[IsTopologicalGroup G]` hypothesis of `GeneralizationLinter.Test.PartsAssembly.continuous_mul_inv` can be split into `ContinuousInv G`, `ContinuousMul G`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "allow" in
set_option generalizeTypeclasses.strictnessGuard false in
theorem continuous_mul_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G) :
    g * g⁻¹ = 1 ∧ Continuous fun p : G × G ↦ p.1 * p.2⁻¹ :=
  ⟨mul_inv_cancel g, by fun_prop⟩

#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "allow" in
theorem continuous_mul_inv' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G) :
    g * g⁻¹ = 1 ∧ Continuous fun p : G × G ↦ p.1 * p.2⁻¹ :=
  ⟨mul_inv_cancel g, by fun_prop⟩

/-! ### A weakening to one parent is not a split into all of them -/

/--
warning: the `[IsTopologicalGroup G]` hypothesis of `GeneralizationLinter.Test.PartsAssembly.continuous_mul'` can be weakened to `ContinuousMul G`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "allow" in
theorem continuous_mul' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G) :
    g * g⁻¹ = 1 ∧ Continuous fun p : G × G ↦ p.1 * p.2 :=
  ⟨mul_inv_cancel g, by fun_prop⟩

/-! ### A class with a field of its own is not rebuilt from its parent -/

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.PartsAssembly.base_eq` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem base_eq {α : Type} [Rich α] : (Base.x : α) = Base.x := rfl

end GeneralizationLinter.Test.PartsAssembly
