/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import Lean.Elab.GuardMsgs

/-! # Conclusion guard

A weakening whose replacements are equivalent to the conclusion, each giving the other by instance
synthesis, turns the declaration into a tautology, and is not suggested. The replacements need not
be the conclusion's class itself. A replacement that gives the conclusion without being given by it
leaves a statement as meaningful as the original, and is suggested.
-/

public section

namespace ConclusionGuardTest

class Base (α : Type) : Prop
class Twin (α : Type) : Prop
instance twinOfBase {α : Type} [Base α] : Twin α := ⟨⟩
instance baseOfTwin {α : Type} [Twin α] : Base α := ⟨⟩

class Extra (α : Type) : Prop
class Mid (α : Type) : Prop extends Base α, Extra α
class Spare (α : Type) : Prop
class Top (α : Type) : Prop extends Mid α, Spare α

theorem baseOf (α : Type) [Extra α] [Base α] : Base α := inferInstance

set_option linter.generalizeTypeclasses true

-- Weakening to the conclusion's class itself makes `[Base α] : Base α`.
#guard_msgs in
theorem same {α : Type} [Top α] : Base α := inferInstance

-- `Base α` and `Twin α` give each other, so `[Base α] : Twin α` assumes its conclusion.
#guard_msgs in
theorem twin {α : Type} [Top α] : Twin α := inferInstance

-- `Mid α` gives `Base α` but not conversely: every `Mid` being a `Base` is a statement in its own
-- right.
/--
warning: the `[Top α]` hypothesis of `ConclusionGuardTest.base` can be weakened to `Mid α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem base {α : Type} [Top α] : Base α := baseOf α

end ConclusionGuardTest
