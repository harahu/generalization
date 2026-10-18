/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import Lean.Elab.GuardMsgs

/-! # Declaration-local `open`

These regressions check that the weakenings of a declaration wrapped in `open … in` are found and
verified with the scoped instances that wrapper brings into scope, as the declaration was
elaborated with them: an edge of the class graph may come from a scoped instance, and so may the
instance that makes a weakening vacuous.
-/

public section

namespace OpenInTest

class Parent (α : Type) where
  pt : α

class Child (α : Type) extends Parent α where
  extra : α

class Other (α : Type) where
  val : α

class Marker (α : Type) where
  mark : α

namespace Bridge

scoped instance otherOfParent {α : Type} [Parent α] : Other α := ⟨Parent.pt⟩

end Bridge

namespace Rebuild

scoped instance childOfMarker {α : Type} [Parent α] [Marker α] : Child α := ⟨Marker.mark⟩

end Rebuild

set_option linter.generalizeTypeclasses true

-- The only path from `Child` to `Other` in the class graph goes through a scoped instance.
/--
warning: the `[Child α]` hypothesis of `OpenInTest.scopedEdge` can be weakened to `Other α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
open scoped Bridge in
theorem scopedEdge {α : Type} [Child α] : (Other.val : α) = Other.val := rfl

-- Opening the namespace brings its scoped instances into scope as well.
/--
warning: the `[Child α]` hypothesis of `OpenInTest.namespaceEdge` can be weakened to `Other α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
open Bridge in
theorem namespaceEdge {α : Type} [Child α] : (Other.val : α) = Other.val := rfl

-- With `Rebuild` open, `[Parent α]` and `[Marker α]` give back `Child α`, so weakening `[Child α]`
-- to `[Parent α]` loses nothing.
#guard_msgs in
open scoped Rebuild in
theorem scopedVacuous {α : Type} [Marker α] [Child α] :
    (Marker.mark : α) = Marker.mark ∧ (Parent.pt : α) = Parent.pt := ⟨rfl, rfl⟩

-- Outside `Rebuild`, the same weakening is a real one.
/--
warning: the `[Child α]` hypothesis of `OpenInTest.unscopedVacuous` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem unscopedVacuous {α : Type} [Marker α] [Child α] :
    (Marker.mark : α) = Marker.mark ∧ (Parent.pt : α) = Parent.pt := ⟨rfl, rfl⟩

end OpenInTest
