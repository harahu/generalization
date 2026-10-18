/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter
import Lean.Elab.GuardMsgs

/-!
# Truncation statistics

A declaration's statistics record says whether one of the linter's own heartbeat budgets ran out
while analyzing it, and so whether a lack of weakenings may only mean a truncated analysis. The flag
belongs to that declaration alone: it is not carried over to the next one, and running out of the
budget of a build (`generalizeTypeclasses.buildHeartbeats`) is a verdict on the weakening, not a
truncation. Inspect the statistics as JSON so the test does not depend on heartbeat counts.
-/

open Lean Elab Command

namespace GeneralizationLinter.Test.TruncationStats

class Base (α : Type) where
  x : α

class Rich (α : Type) extends Base α where
  y : α

run_cmd do
  for (id, opts, expected) in [
      ("truncated", "set_option generalizeTypeclasses.perCandidateHeartbeats 1000 in ", true),
      ("fits", "", false),
      ("exceedsBuild", "set_option generalizeTypeclasses.buildHeartbeats 1 in ", false)] do
    let source := s!"set_option linter.generalizeTypeclasses true in \
      set_option generalizeTypeclasses.stats true in {opts}\
      theorem GeneralizationLinter.Test.TruncationStats.{id} " ++
      "{α : Type} [Rich α] : (Base.x : α) = Base.x ∧ (List.range 40).length = 40 := " ++
      "⟨rfl, by decide⟩"
    let .ok cmd := Parser.runParserCategory (← getEnv) `command source
      | throwError "could not parse the test declaration"
    let saved := (← get).messages
    modify fun s => { s with messages := {} }
    let messages ← Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages cmd
    modify fun s => { s with messages := saved }
    let mut records : Array Json := #[]
    for message in messages.toList do
      if message.severity == .error then
        throwError "{id} failed to elaborate: {message.data}"
      let text ← message.data.toString
      if text.startsWith "GL_STATS " then
        let .ok record := Json.parse ((text.splitOn "GL_STATS ")[1]!)
          | throwError "invalid statistics JSON"
        records := records.push record
    let #[record] := records | throwError "expected one statistics record for {id}"
    unless record.getObjValAs? String "outcome" matches .ok "analyzed" do
      throwError "{id} was not analyzed"
    let .ok truncated := record.getObjValAs? Bool "truncated"
      | throwError "missing truncation flag for {id}"
    unless truncated == expected do
      throwError "expected {id} to report truncated = {expected}"

end GeneralizationLinter.Test.TruncationStats
