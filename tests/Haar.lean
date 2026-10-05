/-
Copyright (c) 2026 Harald Husum and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum, The Tau Ceti contributors
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import GeneralizationLinter

/-!
# A concrete scalar in the Haar-measure theorem

This reproduces the theorem and proof from `TauCeti.MeasureTheory.Measure.Haar.NormedSpace` with
the original `InnerProductSpace ℝ E` hypothesis. The graph candidate must preserve the concrete
scalar ℝ when replacing that hypothesis with `NormedSpace ℝ E`.
-/

open MeasureTheory MeasureTheory.Measure Metric Module

namespace GeneralizationLinter.Test.Haar

/--
warning: the `[InnerProductSpace ℝ E]` hypothesis of `GeneralizationLinter.Test.Haar.ballMeasure` can be weakened to `NormedSpace ℝ E`.

Note: This linter can be disabled with `set_option linter.generalizeTypeclasses false`
-/
#guard_msgs in
set_option linter.generalizeTypeclasses true in
theorem ballMeasure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [mu.IsAddHaarMeasure] (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
  rw [measureReal_def, mu.addHaar_ball_of_pos x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

-- Applying the reported edit leaves the statement and proof unchanged.
theorem ballMeasureApplied {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [mu.IsAddHaarMeasure] (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
  rw [measureReal_def, mu.addHaar_ball_of_pos x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

end GeneralizationLinter.Test.Haar
