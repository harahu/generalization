/-
Copyright (c) 2026 Noah Lang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Lang
-/
module

import Lean.Meta.Basic
import Lean.Meta.Instances
import Lean.Meta.FunInfo

import GeneralizationLinter.Graph.Canonicalization
public import GeneralizationLinter.Graph.ClassGraph

namespace GeneralizationLinter

open Lean Meta
open Std (HashMap HashSet)

/-! # Class graph cache -/

/-
Allocate storage for the result of `ClassGraph.scanInstance` on each instance it has run on, beside
that instance's `declStamp`. Scanning every instance takes several seconds on all of Mathlib, while
looking each one up takes milliseconds, so a rebuild scans only the instances it has not seen. Every
change to the instance set rebuilds the graph: `attribute [instance]`/`[-instance]` on an imported
constant, `open scoped`/`end` on an imported scoped instance, and each new local instance.
-/
initialize instanceScanCacheRef :
    IO.Ref (HashMap Name (UInt64 × Option ClassEdge × Option Name)) ← IO.mkRef {}


/-- Allocate storage for the cached `ClassGraph` and the instance set it was built from. -/
initialize classGraphCacheRef :
    IO.Ref (Option (PHashMap Name Meta.InstanceEntry × ClassGraph)) ← IO.mkRef none


/-- For debugging: counts how many times `cachedClassGraph` has rebuilt the graph. -/
initialize graphBuildCountRef : IO.Ref Nat ← IO.mkRef 0


private unsafe def sameInstanceSetImpl (a b : PHashMap Name Meta.InstanceEntry) : Bool := ptrEq a b

/-
Do `a` and `b` denote the same instance set? Object identity is exact here: the map is persistent, so
any change allocates a new one, and the cached graph keeps its map alive. A spurious `false` costs a
rebuild, never soundness. Hashing the contents instead is a fold over ~40k entries, measured at 72ms
per declaration.
-/
@[implemented_by sameInstanceSetImpl]
private def sameInstanceSet (_a _b : PHashMap Name Meta.InstanceEntry) : Bool := false


/-- Cached class graph. -/
public def cachedClassGraph : MetaM ClassGraph := do
  let env ← getEnv
  let instances := (instanceExtension.getState env).instanceNames
  let cached? ← classGraphCacheRef.get
  if let some (instances', G) := cached? then
    if sameInstanceSet instances' instances then return G
  -- Only instances can produce edges. We enforce this restriction because the linter targets
  -- non-explicit binders for weakening, and non-explicit binders are resolved either using instance
  -- synthesis, or unification with instance synthesis as a fallback. So, when we analyze a
  -- declaration, we know that the current binder could be resolved, and we need to make sure that
  -- the weakened version we suggest can also be resolved, which is guaranteed (-ish) when there's a
  -- path in the class graph from the stronger to the weaker class, precisely because each edge of
  -- the class graph corresponds to an instance that instance synthesis can actually make use of.
  -- Imported instances come first and local ones after them, so that the same instances give the
  -- same edges in the same order.
  let imported := instances.foldl (init := (#[] : Array Name)) fun names name _ =>
    -- Filter out local constants.
    if env.constants.map₂.contains name then names else names.push name
  let localNames := env.constants.map₂.foldl (init := (#[] : Array Name)) fun names name _ =>
    -- Filter out constants that aren't instances.
    if instances.contains name then names.push name else names
  let mut edges : Array ClassEdge := #[]
  let mut subHeads : HashSet Name := {}
  -- Updating the map in place, rather than through the reference, avoids copying it per insertion.
  -- A concurrent rebuild may overwrite the insertions, which costs a rescan, never a wrong result.
  let mut scans ← instanceScanCacheRef.get
  for name in imported ++ localNames do
    let stamp ← declStamp name
    let hit? := scans[name]?.bind fun (s, r) => if s == stamp then some r else none
    let (edge?, subHead?) ← match hit? with
      | some r => pure r
      | none => do
        let r ← ClassGraph.scanInstance name
        scans := scans.insert name (stamp, r)
        pure r
    if let some e := edge? then edges := edges.push e
    if let some h := subHead? then subHeads := subHeads.insert h
  instanceScanCacheRef.set scans
  -- Instances that contribute no edge, such as the ones `open scoped Classical` brings into scope,
  -- leave the condensation as it was, so reuse it. The subsingleton verdicts are decided afresh,
  -- since synthesis can make use of any instance.
  let G ← match cached? with
    | some (_, G') =>
      if G'.edges == edges then ClassGraph.assemble edges subHeads G'.condensation
      else ClassGraph.assemble edges subHeads
    | none => ClassGraph.assemble edges subHeads
  graphBuildCountRef.modify (· + 1)
  classGraphCacheRef.set (some (instances, G))
  return G
