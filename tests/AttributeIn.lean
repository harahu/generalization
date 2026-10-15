/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import Lean.Elab.GuardMsgs

/-! # Declaration-local attributes

These regressions check that declarations wrapped in `attribute … in` are analyzed, and that their
weakenings are verified under the attributes the declaration was elaborated with: local instances
must be available, and erased instances must not be.
-/

public section

namespace AttributeInTest

class Parent (α : Type) where
  pt : α
  op : α → α

class Child (α : Type) extends Parent α where
  extra : α

class Other (α : Type) where
  val : α

@[expose, instance_reducible] def otherOfParent {α : Type} [Parent α] : Other α := ⟨Parent.pt⟩

set_option linter.generalizeTypeclasses true

-- Re-elaborating the conclusion against the weakened hypothesis needs the local instance.
/--
warning: the `[Child α]` hypothesis of `AttributeInTest.localInstance` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
attribute [local instance] otherOfParent in
theorem localInstance {α : Type} [Child α] : (Other.val : α) = Parent.pt := rfl

-- Neither the declaration's nor the linter's replay of the local instance outlives the command.
/--
error: failed to synthesize instance of type class
  Other α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type} [Parent α] : Other α := inferInstance

instance (priority := low) otherLow {α : Type} [Parent α] : Other α := ⟨Parent.pt⟩

instance otherHigh {α : Type} [Parent α] : Other α := ⟨Parent.op Parent.pt⟩

-- Re-elaborating the conclusion with `otherHigh` available would give a different statement.
/--
warning: the `[Child α]` hypothesis of `AttributeInTest.erasedInstance` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
attribute [-instance] otherHigh in
theorem erasedInstance {α : Type} [Child α] : (Other.val : α) = Parent.pt := rfl

@[expose] def double {α : Type} [Parent α] (a : α) : α := Parent.op a

theorem double_eq {α : Type} [Parent α] (a : α) : double a = Parent.op a := rfl

-- The proof needs the local simp lemma.
/--
warning: the `[Child α]` hypothesis of `AttributeInTest.localSimp` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
attribute [local simp] double_eq in
theorem localSimp {α : Type} [Child α] (a : α) : double a = Parent.op a := by simp

namespace Hidden

@[expose, instance_reducible] def otherOfParent' {α : Type} [Parent α] : Other α := ⟨Parent.pt⟩

end Hidden

-- Attributes are replayed after the wrappers preceding them, which may be needed to resolve them,
-- and interleave with the other kinds of wrappers.
/--
warning: the `[Child α]` hypothesis of `AttributeInTest.interleaved` can be weakened to `Parent α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
variable {α : Type} in
open Hidden in
attribute [local instance] otherOfParent' in
variable [Child α] in
theorem interleaved : (Other.val : α) = Parent.pt := rfl

end AttributeInTest
