/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import Lean.Elab.GuardMsgs

/-! # Section variables

A weakening of a section variable that an earlier `variable` command declares is suggested, but
graded as one whose binders might have to be modified: the variable is shared with the rest of its
scope, which applying the weakening may split. A binder that the declaration's own command declares
is graded as before, and an `omit` or `include` does not keep a declaration from being analyzed.
-/

public section

namespace SectionVariablesTest

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

class Extra (α : Type) : Prop

set_option linter.generalizeTypeclasses true

section
variable {α : Type} [Rich α]

/--
warning: the `[Rich α]` hypothesis of `SectionVariablesTest.shared` can be weakened to `Base α`, but its binders might have to be modified.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem shared : (Base.x : α) = Base.x := rfl

end

section
variable {α : Type}

/--
warning: the `[Rich α]` hypothesis of `SectionVariablesTest.own` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem own [Rich α] : (Base.x : α) = Base.x := rfl

end

section
variable {α : Type} [Extra α]

/--
warning: the `[Rich α]` hypothesis of `SectionVariablesTest.ownWithOmit` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
omit [Extra α] in
theorem ownWithOmit [Rich α] : (Base.x : α) = Base.x := rfl

end

section
variable {α : Type} [inst : Rich α]

-- The value binds the section variable's name again, which does not make the variable its own.
/--
warning: the `[Rich α]` hypothesis of `SectionVariablesTest.rebound` can be weakened to `Base α`, but its binders might have to be modified.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
theorem rebound (a : α) : (Base.x : α) = Base.x ∧ a = a :=
  (fun (inst : Nat) (_ : inst = inst) => ⟨rfl, rfl⟩) 0 rfl

end

end SectionVariablesTest
