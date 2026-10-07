/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Algebra.Field.Subfield.Defs
public meta import GeneralizationLinter.Graph.Vertex
public meta import GeneralizationLinter.Analysis.ReSynth
import GeneralizationLinter

/-!
# Equivalent hypotheses found in Tau Ceti

Check the strictness guard on the original signatures and the proposed replacements, including
rebuilt dependent binders. Negative cases ensure that these rules leave genuine weakenings alone.
The implications trusted by the guard are proved separately in `tests/BridgeRules.lean`.
-/

open Lean Meta Elab Command GeneralizationLinter CategoryTheory

meta def assertVacuous (sig : Syntax) (n : Nat) (repls : Array Vertex) (expected : Bool) :
    Term.TermElabM Unit := do
  let ty ← Term.elabType sig
  Term.synthesizeSyntheticMVarsNoPostponing
  let actual ← weakeningVacuous ty n repls
  unless actual == expected do
    throwError "expected vacuity {expected}, got {actual} for {ty}"

-- A finite-dimensional domain is a division ring (a named Mathlib bridge).
run_elab do
  assertVacuous (← `(∀ (k D : Type) [Field k] [DivisionRing D] [Algebra k D]
      [FiniteDimensional k D], True)) 1
    #[⟨``Ring, #[.bvar 0], .polymorphic⟩, ⟨``IsDomain, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (k D : Type) [Field k] [DivisionRing D] [Algebra k D], True)) 1
    #[⟨``Ring, #[.bvar 0], .polymorphic⟩, ⟨``IsDomain, #[.bvar 0], .polymorphic⟩] false

-- Algebraicity recovers the field; the domain assumptions alone do not.
run_elab do
  assertVacuous (← `(∀ (k E : Type) [Field k] [Field E] [Algebra k E]
      [Algebra.IsAlgebraic k E], True)) 1
    #[⟨``CommRing, #[.bvar 0], .polymorphic⟩, ⟨``Nontrivial, #[.bvar 0], .polymorphic⟩,
      ⟨``NoZeroDivisors, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (k E : Type) [Field k] [Field E] [Algebra k E], True)) 1
    #[⟨``CommRing, #[.bvar 0], .polymorphic⟩, ⟨``Nontrivial, #[.bvar 0], .polymorphic⟩,
      ⟨``NoZeroDivisors, #[.bvar 0], .polymorphic⟩] false

-- Finiteness recovers a field, including from a finite Euclidean domain.
run_elab do
  assertVacuous (← `(∀ (E : Type) [Field E] [Finite E], True)) 0
    #[⟨``CommRing, #[.bvar 0], .polymorphic⟩, ⟨``IsDomain, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (E : Type) [Field E] [Finite E], True)) 0
    #[⟨``EuclideanDomain, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (E : Type) [Field E], True)) 0
    #[⟨``CommRing, #[.bvar 0], .polymorphic⟩, ⟨``IsDomain, #[.bvar 0], .polymorphic⟩] false

-- An algebra over a ring has inverses for addition, with the existing operations.
run_elab do
  assertVacuous (← `(∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A], True)) 1
    #[⟨``Semiring, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A], True)) 1
    #[⟨``CommSemiring, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R A : Type) [CommSemiring R] [Ring A] [Algebra R A], True)) 1
    #[⟨``Semiring, #[.bvar 0], .polymorphic⟩] false

-- Groupoids keep the same category.
run_elab do
  assertVacuous (← `(∀ (C : Type) [CategoryTheory.Groupoid.{0} C] (X Y : C) (f : X ⟶ Y), True)) 0
    #[⟨``CategoryTheory.Category, #[.bvar 0], .concrete #[.zero, .zero]⟩,
      ⟨``CategoryTheory.IsGroupoid, #[.bvar 0], .concrete #[.zero, .zero]⟩] true

-- Cancellation and commutativity rebuild the bundled algebraic structures.
run_elab do
  assertVacuous (← `(∀ (M : Type) [AddCancelCommMonoid M], True)) 0
    #[⟨``AddCommMonoid, #[.bvar 0], .polymorphic⟩,
      ⟨``IsLeftCancelAdd, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (N : Type) [AddLeftCancelMonoid N], True)) 0
    #[⟨``AddMonoid, #[.bvar 0], .polymorphic⟩, ⟨``IsLeftCancelAdd, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (N : Type) [AddRightCancelMonoid N], True)) 0
    #[⟨``AddMonoid, #[.bvar 0], .polymorphic⟩, ⟨``IsRightCancelAdd, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (N : Type) [RightCancelMonoid N], True)) 0
    #[⟨``Monoid, #[.bvar 0], .polymorphic⟩, ⟨``IsRightCancelMul, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (G : Type) [CommGroup G], True)) 0
    #[⟨``Group, #[.bvar 0], .polymorphic⟩, ⟨``IsMulCommutative, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (G : Type) [CommGroup G], True)) 0
    #[⟨``Group, #[.bvar 0], .polymorphic⟩] false
run_elab do
  assertVacuous (← `(∀ (R : Type) [CommRing R], True)) 0
    #[⟨``Ring, #[.bvar 0], .polymorphic⟩,
      ⟨``IsCentralScalar, #[.bvar 0, .bvar 0], .polymorphic⟩] true

-- This IsDomain rejection is already covered by NoZeroDivisors.to_isDomain.
run_elab do
  assertVacuous (← `(∀ (k : Type) [Ring k] [IsDomain k], True)) 1
    #[⟨``Nontrivial, #[.bvar 0], .polymorphic⟩,
      ⟨``IsLeftCancelMulZero, #[.bvar 0], .polymorphic⟩] true

-- Norm compatibility is precisely the extra field of NormedSpace.
run_elab do
  assertVacuous (← `(∀ (K N : Type) [NormedField K] [SeminormedAddCommGroup N]
      [NormedSpace K N], True)) 2
    #[⟨``_root_.Module, #[.bvar 0, .bvar 1], .polymorphic⟩,
      ⟨``NormSMulClass, #[.bvar 0, .bvar 1], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (K N : Type) [NormedField K] [SeminormedAddCommGroup N]
      [NormedSpace K N], True)) 2
    #[⟨``_root_.Module, #[.bvar 0, .bvar 1], .polymorphic⟩] false

-- Scalar compatibility rebuilds Algebra only when the tower law remains.
run_elab do
  assertVacuous (← `(∀ (A R : Type) [CommSemiring A] [CommSemiring R] [Algebra A R], True)) 2
    #[⟨``_root_.Module, #[.bvar 0, .bvar 1], .polymorphic⟩,
      ⟨``IsScalarTower, #[.bvar 0, .bvar 1, .bvar 1], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (A R : Type) [CommSemiring A] [CommSemiring R] [Algebra A R], True)) 2
    #[⟨``_root_.Module, #[.bvar 0, .bvar 1], .polymorphic⟩] false

-- The class fields of ConnectedSpace, IsGalois, and Unique are class-valued too.
run_elab do
  assertVacuous (← `(∀ (X : Type) [TopologicalSpace X] [ConnectedSpace X], True)) 1
    #[⟨``PreconnectedSpace, #[.bvar 0], .polymorphic⟩,
      ⟨``Nonempty, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L], True)) 3
    #[⟨``Normal, #[.bvar 0, .bvar 1], .polymorphic⟩,
      ⟨``Algebra.IsSeparable, #[.bvar 0, .bvar 1], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (X : Type) [Unique X], True)) 0
    #[⟨``Inhabited, #[.bvar 0], .polymorphic⟩, ⟨``Subsingleton, #[.bvar 0], .polymorphic⟩] true

-- Multiplicative and additive maps preserve the remaining ring operations.
run_elab do
  assertVacuous (← `(∀ (F A B : Type) [NonAssocSemiring A] [NonAssocSemiring B]
      [FunLike F A B] [RingHomClass F A B], True)) 3
    #[⟨``MonoidHomClass, #[.bvar 0, .bvar 1, .bvar 2], .polymorphic⟩,
      ⟨``AddMonoidHomClass, #[.bvar 0, .bvar 1, .bvar 2], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (F A B : Type) [NonAssocRing A] [NonAssocRing B]
      [FunLike F A B] [RingHomClass F A B], True)) 3
    #[⟨``MonoidHomClass, #[.bvar 0, .bvar 1, .bvar 2], .polymorphic⟩,
      ⟨``AddHomClass, #[.bvar 0, .bvar 1, .bvar 2], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (S K : Type) [DivisionRing K] [SetLike S K] [SubfieldClass S K], True)) 2
    #[⟨``AddSubmonoidWithOneClass, #[.bvar 0, .bvar 1], .polymorphic⟩,
      ⟨``SubmonoidClass, #[.bvar 0, .bvar 1], .polymorphic⟩,
      ⟨``InvMemClass, #[.bvar 0, .bvar 1], .polymorphic⟩,
      ⟨``AddSubgroupClass, #[.bvar 0, .bvar 1], .polymorphic⟩] true

-- Linear order supplies 0 ≤ 1; over a field, weak monotonicity is strict.
run_elab do
  assertVacuous (← `(∀ (R : Type) [CommRing R] [LinearOrder R] [IsOrderedRing R], True)) 2
    #[⟨``IsOrderedAddMonoid, #[.bvar 0], .polymorphic⟩,
      ⟨``PosMulMono, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R], True)) 2
    #[⟨``IsOrderedAddMonoid, #[.bvar 0], .polymorphic⟩,
      ⟨``PosMulMono, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R], True)) 2
    #[⟨``IsOrderedAddMonoid, #[.bvar 0], .polymorphic⟩,
      ⟨``MulPosMono, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R], True)) 2
    #[⟨``IsOrderedAddMonoid, #[.bvar 0], .polymorphic⟩,
      ⟨``PosMulStrictMono, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [CommRing R] [PartialOrder R] [IsOrderedRing R], True)) 2
    #[⟨``IsOrderedAddMonoid, #[.bvar 0], .polymorphic⟩,
      ⟨``PosMulMono, #[.bvar 0], .polymorphic⟩] false

-- The scalar action here is the canonical self-action of multiplication.
run_elab do
  assertVacuous (← `(∀ (R : Type) [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R],
      True)) 2
    #[⟨``ContinuousAdd, #[.bvar 0], .polymorphic⟩,
      ⟨``ContinuousSMul, #[.bvar 0, .bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [Ring R] [TopologicalSpace R] [IsTopologicalRing R], True)) 2
    #[⟨``IsTopologicalAddGroup, #[.bvar 0], .polymorphic⟩,
      ⟨``ContinuousSMul, #[.bvar 0, .bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [Ring R] [TopologicalSpace R] [IsTopologicalRing R], True)) 2
    #[⟨``ContinuousAdd, #[.bvar 0], .polymorphic⟩,
      ⟨``ContinuousMul, #[.bvar 0], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (R : Type) [Ring R] [TopologicalSpace R] [IsTopologicalRing R], True)) 2
    #[⟨``ContinuousAdd, #[.bvar 0], .polymorphic⟩] false

-- An unrelated self-action must not be mistaken for multiplication.
run_elab do
  assertVacuous (← `(∀ (R : Type) [Ring R] [TopologicalSpace R] [SMul R R]
      [IsTopologicalRing R], True)) 3
    #[⟨``ContinuousAdd, #[.bvar 0], .polymorphic⟩,
      ⟨``ContinuousSMul, #[.bvar 0, .bvar 0], .polymorphic⟩] false

-- Smooth self-action and the manifold hypothesis rebuild smooth multiplication.
run_elab do
  assertVacuous (← `(∀ (𝕜 H E : Type) [NontriviallyNormedField 𝕜] [TopologicalSpace H]
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
      (G : Type) [Mul G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G], True)) 7
    #[⟨``IsManifold, #[.bvar 0, .bvar 1, .bvar 2], .polymorphic⟩,
      ⟨``ContMDiffSMul, #[.bvar 0, .bvar 0, .bvar 1, .bvar 2, .bvar 2], .polymorphic⟩] true
run_elab do
  assertVacuous (← `(∀ (𝕜 H E : Type) [NontriviallyNormedField 𝕜] [TopologicalSpace H]
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
      (G : Type) [Mul G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G], True)) 7
    #[⟨``ContMDiffSMul, #[.bvar 0, .bvar 0, .bvar 1, .bvar 2, .bvar 2], .polymorphic⟩] false
