/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter

/-!
# Matching root-qualified declaration names

Lean removes a leading `_root_` from an elaborated declaration name. The linter must do the same
when matching its source identifier, while retaining suffix matching for namespace and private
prefixes and rejecting auxiliary declarations.
-/

open Lean Elab Command GeneralizationLinter

run_cmd do
  let check (stx : Syntax) (name : Name) (expected : Bool) : CommandElabM Unit := do
    unless declIdMatches stx name == expected do
      throwError "unexpected declaration-name match for {stx} against {name}"
  let ordinary ← `(command| theorem t : True := trivial)
  check ordinary `Foo.t true
  check ordinary `Foo.s false
  let rooted ← `(command| theorem _root_.Foo.t : True := trivial)
  check rooted `Foo.t true
  check rooted `Foo.s false
  check rooted `Bar.t false
  check rooted (.str (.str (.num `_private.RootDeclarations 0) "Foo") "t") true
  check rooted `Foo.t.aux false
  let qualified ← `(command| theorem Foo.t : True := trivial)
  check qualified `Bar.Foo.t true
  let internalRoot ← `(command| theorem Foo._root_.t : True := trivial)
  check internalRoot `Foo._root_.t true
  check internalRoot `Foo.t false
  let helper ← `(command| theorem _root_.Foo.t : True := aux where aux : True := trivial)
  check helper `Foo.t.aux false
  let unnamed ← `(command| instance : Inhabited Nat where default := 0)
  check unnamed `instInhabitedNat true

namespace GeneralizationLinter.Test.RootDeclarations

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

/-! A control declaration with an ordinary source identifier. -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.RootDeclarations.ordinary` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem ordinary {α : Type} [Rich α] : (Base.x : α) = Base.x := rfl

namespace Nested

/-! The declaration escapes the current namespace; its proof still uses the current scope. -/

/--
warning: the `[Rich α]` hypothesis of `GeneralizationLinter.Test.RootDeclarations.rooted` can be weakened to `Base α`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem _root_.GeneralizationLinter.Test.RootDeclarations.rooted {α : Type} [Rich α] :
    (Base.x : α) = Base.x := rfl

end Nested

end GeneralizationLinter.Test.RootDeclarations
