/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.Algebra.Group.Defs
import GeneralizationLinter

/-!
# Weakening a declaration to a fixpoint

Weakening one hypothesis can leave another one stronger than the rest of the declaration needs:
here `[Act α]` is what needs `[Rich α]` rather than `[Base α]`, so `[Rich α]` can only be weakened
once `[Act α]` has been. The linter should report the weakening it reaches once nothing more can
be weakened, one message per original hypothesis.
-/

namespace GeneralizationLinter.Test.Fixpoint

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

/-- A mixin stated over `Rich`. -/
class Act (α : Type) [Rich α] : Prop where
  act : True

/-- The weaker mixin, stated over `Base`. -/
class ActBase (α : Type) [Base α] : Prop where
  act : True

instance {α : Type} [Rich α] [Act α] : ActBase α := ⟨trivial⟩

theorem useActBase (α : Type) [Base α] [ActBase α] : True := trivial

class Goal (α : Type) : Prop where
  goal : True

/-! ### An earlier binder freed by weakening a later one -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.weakenFreesEarlier` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[Act α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.weakenFreesEarlier` can be weakened to `ActBase α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem weakenFreesEarlier {α : Type} [Rich α] [Act α] : True := useActBase α

/-! ### An earlier binder freed by dropping a later one -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.dropFreesEarlier` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[Act α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.dropFreesEarlier` can be removed (dropped).

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem dropFreesEarlier {α : Type} [Rich α] [Act α] : (Base.x : α) = Base.x := rfl

/-! ### Two weakenings of one binder compose -/

class L3 (α : Type) where
  z : α

class L2 (α : Type) extends L3 α where
  w : α

class L1 (α : Type) extends L2 α where
  v : α

class M2 (α : Type) [L2 α] : Prop where
  m : True

class M3 (α : Type) [L3 α] : Prop where
  m : True

instance {α : Type} [L2 α] [M2 α] : M3 α := ⟨trivial⟩

theorem useM3 (α : Type) [L3 α] [M3 α] : True := trivial

/--
warning: the `[L1 α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.weakeningsCompose` can be weakened to `L3 α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[M2 α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.weakeningsCompose` can be weakened to `M3 α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem weakeningsCompose {α : Type} [L1 α] [M2 α] : True := useM3 α

/-! ### A split shifts the binders after it -/

class P (α : Type) : Prop where
  p : True

class Q (α : Type) : Prop where
  q : True

class PQ (α : Type) : Prop extends P α, Q α

theorem useP (α : Type) [P α] : True := trivial

theorem useQ (α : Type) [Q α] : True := trivial

/--
warning: the `[PQ α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.splitShiftsLater` can be split into `Q α`, `P α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.splitShiftsLater` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[Act α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.splitShiftsLater` can be weakened to `ActBase α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.splitPolicy "allow" in
theorem splitShiftsLater {α : Type} [PQ α] [Rich α] [Act α] : True ∧ True ∧ True :=
  ⟨useP α, useQ α, useActBase α⟩

/-! ### An instance -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.weakenFreesEarlierInstance` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
---
warning: the `[Act α]` hypothesis of `GeneralizationLinter.Test.Fixpoint.weakenFreesEarlierInstance` can be weakened to `ActBase α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
instance weakenFreesEarlierInstance {α : Type} [Rich α] [Act α] : Goal α := ⟨useActBase α⟩

/-! ### A declaration a single pass already settles -/

/--
warning: the `[Group G]` hypothesis of `GeneralizationLinter.Test.Fixpoint.singlePass` can be weakened to `MulOneClass G`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem singlePass {G : Type} [Group G] (a : G) : a * 1 = a := mul_one a

end GeneralizationLinter.Test.Fixpoint
