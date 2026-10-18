/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import Lean.Elab.GuardMsgs

/-! # Several minimal common ancestors

When the requirements on a hypothesis have several incomparable minimal common ancestors, each is a
candidate replacement, the most general first, so one that fails verification falls back to the
next.
-/

public section

namespace MinimalCommonAncestorsTest

class A (α : Type) : Prop
class B (α : Type) : Prop
class Spare (α : Type) : Prop

theorem useBoth (α : Type) [A α] [B α] : True := trivial
theorem useAll (α : Type) [Spare α] [A α] [B α] : True := trivial

/-! ### Falling back to the next ancestor -/

class AFirst (α : Type) : Prop extends A α, B α where
  first : True
class ZLast (α : Type) : Prop extends A α, B α where
  last : True
class Both (α : Type) : Prop extends AFirst α, ZLast α

/-- With `[Spare α]`, `AFirst α` gives back `Both α`, so weakening to `AFirst α` is vacuous. -/
instance bothOfAFirst {α : Type} [AFirst α] [Spare α] : Both α :=
  { toAFirst := inferInstance, last := trivial }

set_option linter.generalizeTypeclasses true

/--
warning: the `[Both α]` hypothesis of `MinimalCommonAncestorsTest.fallback` can be weakened to `ZLast α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem fallback {α : Type} [Spare α] [Both α] : True := useAll α

set_option linter.generalizeTypeclasses false

/-! ### Preferring the more general ancestor -/

class C (α : Type) : Prop
class ABig (α : Type) : Prop extends A α, B α, C α
class ZSmall (α : Type) : Prop extends A α, B α
class Rich (α : Type) : Prop extends ABig α, ZSmall α

set_option linter.generalizeTypeclasses true

/--
warning: the `[Rich α]` hypothesis of `MinimalCommonAncestorsTest.general` can be weakened to `ZSmall α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem general {α : Type} [Rich α] : True := useBoth α

end MinimalCommonAncestorsTest
