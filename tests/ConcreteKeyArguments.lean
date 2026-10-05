/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter

/-!
# Specializing graph candidates to concrete key arguments

Graph witnesses can generalize constants, repeated arguments, and structured arguments into fresh
placeholders. Those placeholders must be matched back to the original binder before reification.
-/

namespace GeneralizationLinter.Test.ConcreteKeyArguments

class Base (ρ α : Type) where
  left : ρ
  right : α

class Rich (ρ α : Type) extends Base ρ α where
  extra : α

/--
warning: the `[Rich ℕ α]` hypothesis of `GeneralizationLinter.Test.ConcreteKeyArguments.constant` can be weakened to `Base ℕ α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem constant {α : Type} [Rich ℕ α] : (Base.right ℕ : α) = Base.right ℕ := rfl

/--
warning: the `[Rich α α]` hypothesis of `GeneralizationLinter.Test.ConcreteKeyArguments.repeated` can be weakened to `Base α α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem repeated {α : Type} [Rich α α] : (Base.right α : α) = Base.right α := rfl

/--
warning: the `[Rich (List α) α]` hypothesis of `GeneralizationLinter.Test.ConcreteKeyArguments.structured` can be weakened to `Base (List α) α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem structured {α : Type} [Rich (List α) α] :
    (Base.right (List α) : α) = Base.right (List α) := rfl

end GeneralizationLinter.Test.ConcreteKeyArguments
