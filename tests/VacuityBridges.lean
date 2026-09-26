/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import GeneralizationLinter

/-!
# Vacuity bridges

Each `GeneralizationLinter.vacuityBridges` entry lets the strictness guard see that a weakening is
undone by a Mathlib declaration. Each is pinned here by a weakening the linter suggests with the
guard off and withholds with it on.
-/

namespace GeneralizationLinter.Test.VacuityBridges

/-! ### A finite Galois group makes the extension Galois (`IsGaloisGroup.isGalois`) -/

/--
warning: the `[IsGalois K L]` hypothesis of `GeneralizationLinter.Test.VacuityBridges.card_gal` can be weakened to `IsGaloisGroup Gal(L/K) K L`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
set_option generalizeTypeclasses.strictnessGuard false in
theorem card_gal (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : 0 < Nat.card Gal(L/K) :=
  IsGaloisGroup.card_eq_finrank Gal(L/K) K L ▸ Module.finrank_pos

#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem card_gal' (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : 0 < Nat.card Gal(L/K) :=
  IsGaloisGroup.card_eq_finrank Gal(L/K) K L ▸ Module.finrank_pos

end GeneralizationLinter.Test.VacuityBridges
