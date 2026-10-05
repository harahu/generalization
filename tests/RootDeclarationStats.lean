/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter
import Lean.Elab.GuardMsgs

/-!
# Coverage statistics for root-qualified declarations

Both public and private root-qualified theorems must be analyzed and emit a verified weakening.
Inspect the statistics as JSON so the test does not depend on heartbeat counts or private-name
prefixes containing the current module name.
-/

open Lean Elab Command

namespace GeneralizationLinter.Test.RootDeclarationStats

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

namespace Nested

run_cmd do
  for (id, visibility) in [("rooted", ""), ("privateRooted", "private ")] do
    let name := s!"GeneralizationLinter.Test.RootDeclarationStats.{id}"
    let source := s!"set_option linter.generalizeTypeclasses true in \
      set_option generalizeTypeclasses.stats true in \
      {visibility}theorem _root_.{name} " ++
      "{α : Type} [Rich α] : (Base.x : α) = Base.x := rfl"
    let .ok cmd := Parser.runParserCategory (← getEnv) `command source
      | throwError "could not parse the test declaration"
    let saved := (← get).messages
    modify fun s => { s with messages := {} }
    let messages ← Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages cmd
    modify fun s => { s with messages := saved }
    let mut records : Array Json := #[]
    let mut warnings : Nat := 0
    for message in messages.toList do
      if message.severity == .error then
        throwError "test declaration failed: {message.data}"
      if message.severity == .warning then warnings := warnings + 1
      let text ← message.data.toString
      if text.startsWith "GL_STATS " then
        let .ok record := Json.parse ((text.splitOn "GL_STATS ")[1]!)
          | throwError "invalid statistics JSON"
        records := records.push record
    unless records.size == 1 && warnings == 1 do
      throwError "expected one statistics record and one weakening, got {records.size} and {warnings}"
    let record := records[0]!
    let .ok declName := record.getObjValAs? String "decl"
      | throwError "missing declaration name"
    unless (if visibility.isEmpty then declName == name else
        declName.startsWith "_private." && declName.endsWith name) do
      throwError "unexpected declaration name: {declName}"
    let .ok outcome := record.getObjValAs? String "outcome"
      | throwError "missing analysis outcome"
    unless outcome == "analyzed" do
      throwError "root-qualified declaration was not analyzed"
    let .ok emits := record.getObjValAs? (Array Json) "emits"
      | throwError "missing weakening statistics"
    unless emits.size == 1 do
      throwError "expected one weakening"
    let .ok grade := emits[0]!.getObjValAs? String "grade"
      | throwError "missing verification grade"
    unless grade == "holds: true true true" do
      throwError "expected one fully verified weakening"

end Nested

end GeneralizationLinter.Test.RootDeclarationStats
