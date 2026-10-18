/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import GeneralizationLinter

/-!
# Class graph cache

The cached class graph follows the instances in scope as they change and change back. Instances
that contribute no edge leave the graph's condensation as it was, but not its subsingleton verdicts,
which synthesis decides with every instance in scope.
-/

open Lean Meta

namespace GeneralizationLinter.Test.GraphCache

class Strong (α : Type) : Prop
class Weak (α : Type) : Prop
instance strongWeak {α : Type} [Strong α] : Weak α := ⟨⟩

/-- A data-carrying class whose applications are subsingletons, which needs `Marker` to show. -/
class Data (α : Type) where
  val : Unit
class RichData (α : Type) extends Data α
class Marker (α : Type) : Prop
instance subsingletonData {α : Type} [Marker α] : Subsingleton (Data α) :=
  ⟨fun ⟨()⟩ ⟨()⟩ => rfl⟩

namespace Markers
scoped instance anyMarker (α : Type) : Marker α := ⟨⟩
end Markers

/-- The vertices of `G` whose class is `n`. -/
def verticesOf (G : ClassGraph) (n : Name) : Array Vertex :=
  G.edges.foldl (init := #[]) fun vs e =>
    let vs := if e.src.name == n then vs.push e.src else vs
    if e.tgt.name == n then vs.push e.tgt else vs

/-- Check that `Strong` reaches `Weak` iff `edge`, and that `Data` is a subsingleton iff `sub`. -/
def check (edge sub : Bool) : MetaM Unit := do
  let G ← cachedClassGraph
  let reaches := (verticesOf G ``Strong).any fun s =>
    (verticesOf G ``Weak).any (G.condensation.reaches s ·)
  unless reaches == edge do throwError "expected Strong to reach Weak: {edge}"
  let subsingleton := (verticesOf G ``Data).any G.isSubsingleton
  unless subsingleton == sub do throwError "expected Data to be a subsingleton: {sub}"

run_meta check true false
attribute [-instance] strongWeak in run_meta check false false
run_meta check true false
open scoped Markers in run_meta check true true
run_meta check true false
instance : Weak Nat := ⟨⟩
run_meta check true false

end GeneralizationLinter.Test.GraphCache
