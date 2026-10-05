/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter

/-!
# Retaining substitutions with graph witnesses

Witness generation keeps its original order and expansion bound. Each retained substitution
reconstructs the original query, including repeated, structured, sparse, and closed arguments.
-/

open Lean GeneralizationLinter

private def checkWitnesses (pattern : Array Expr) (levels : UniverseLevels) : IO Unit := do
  let query : Vertex := { name := `Probe, pattern, levels }
  for includeSubsumers in [false, true] do
    let ws := query.matchedWitnesses includeSubsumers
    unless ws.map (·.vertex) == query.witnesses includeSubsumers do
      throw (IO.userError "Witness order, universe variants, or expansion bound changed")
    for w in ws do
      unless w.specialize? w.vertex.pattern == some pattern do
        throw (IO.userError "Witness substitution does not reconstruct its query")

#eval do
  let real := Expr.const `Real []
  let closed := Expr.lam `x (.const `Nat []) (.bvar 0) .default
  let patterns : Array (Array Expr) := #[
    #[], #[.bvar 0], #[.bvar 3], #[real, .bvar 0], #[.bvar 0, .bvar 0],
    #[mkApp (.const `List []) (.bvar 0), .bvar 0],
    #[mkApp2 (.const `Prod []) (.bvar 0) (.bvar 0)],
    #[closed, .bvar 0], Array.replicate 7 (.bvar 0), Array.replicate 8 (.bvar 0)]
  for pattern in patterns do
    for levels in ([.polymorphic, .concrete #[.zero]] : List UniverseLevels) do
      checkWitnesses pattern levels
  let query : Vertex := {
    name := `Probe
    pattern := #[real, .bvar 0]
    levels := .polymorphic
  }
  let generic := #[Expr.bvar 0, Expr.bvar 1]
  let some w := (query.matchedWitnesses true).find?
      (fun (w : VertexWitness) => w.vertex.pattern == generic) |
    throw (IO.userError "Missing generic scalar/carrier witness")
  unless w.specialize? #[.bvar 0, .bvar 1] == some #[real, .bvar 0] do
    throw (IO.userError "Concrete scalar/carrier mapping was lost")
  unless (w.specialize? #[.bvar 2]).isNone do
    throw (IO.userError "Accepted an unbound placeholder")
  let nested := Expr.lam `x (.const `Nat []) (.app (.bvar 1) (.bvar 0)) .default
  let expected := Expr.lam `x (.const `Nat []) (.app real (.bvar 0)) .default
  unless w.specialize? #[nested] == some #[expected] do
    throw (IO.userError "Substitution changed a bound variable")
