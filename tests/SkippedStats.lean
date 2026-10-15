/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public meta import GeneralizationLinter.Frontend.Linter
public meta import Lean.Elab.GuardMsgs

/-! # Statistics for skipped declarations

Every theorem a command elaborates has a statistics record, including the theorems the linter does
not analyze, whose record says why. Skipped records carry no heartbeat count, so they are stable.
-/

public section

namespace SkippedStatsTest

class Parent (α : Type) where
  pt : α

class Child (α : Type) extends Parent α where
  extra : α

set_option linter.generalizeTypeclasses true
set_option generalizeTypeclasses.stats true

/--
info: GL_STATS {"decl":"SkippedStatsTest.inNotation","outcome":"skipped","reason":"unsupported wrapper Lean.Parser.Command.notation"}
-/
#guard_msgs in
local notation "𝒫" => Parent.pt in
theorem inNotation {α : Type} [Child α] : (Parent.pt : α) = Parent.pt := rfl

/--
info: GL_STATS {"decl":"SkippedStatsTest.mutualA","outcome":"skipped","reason":"unsupported command Lean.Parser.Command.mutual"}
---
info: GL_STATS {"decl":"SkippedStatsTest.mutualB","outcome":"skipped","reason":"unsupported command Lean.Parser.Command.mutual"}
-/
#guard_msgs in
mutual
theorem mutualA {α : Type} [Child α] : (Parent.pt : α) = Parent.pt := rfl
theorem mutualB {α : Type} [Child α] : (Parent.pt : α) = Parent.pt := rfl
end

/--
info: GL_STATS {"decl":"SkippedStatsTest.disabled","outcome":"skipped","reason":"linter disabled"}
-/
#guard_msgs in
set_option linter.generalizeTypeclasses false in
theorem disabled {α : Type} [Child α] : (Parent.pt : α) = Parent.pt := rfl

section
variable {α : Type} [Child α] [Inhabited α]

/--
info: GL_STATS {"decl":"SkippedStatsTest.omitted","outcome":"skipped","reason":"omitted variables"}
-/
#guard_msgs in
omit [Inhabited α] in
theorem omitted : (Parent.pt : α) = Parent.pt := rfl

end

/--
info: GL_STATS {"decl":"SkippedStatsTest.withWhere","outcome":"skipped","reason":"termination hints or where block"}
---
info: GL_STATS {"decl":"_private.tests.SkippedStats.0.SkippedStatsTest.withWhere.aux","outcome":"skipped","reason":"termination hints or where block"}
-/
#guard_msgs in
theorem withWhere {α : Type} [Child α] : (Parent.pt : α) = Parent.pt := aux
where aux : (Parent.pt : α) = Parent.pt := rfl

/--
info: GL_STATS {"decl":"SkippedStatsTest.equations","outcome":"skipped","reason":"unsupported value"}
-/
#guard_msgs in
theorem equations {α : Type} [Child α] : Nat → (Parent.pt : α) = Parent.pt
  | 0 => rfl
  | _ + 1 => rfl

-- Commands that elaborate no theorem have no record.
#guard_msgs in
mutual
def defA (n : Nat) : Nat := n
def defB (n : Nat) : Nat := n
end

end SkippedStatsTest
