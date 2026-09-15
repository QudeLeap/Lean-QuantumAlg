/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.AmplitudeEstimation.Basic
public import QuantumAlg.Algorithms.AmplitudeEstimation.Endpoint

/-!
# Amplitude estimation

The public endpoint selects its phase width, prepares the complete owned
register, executes the source-correct query ladder, measures into actual
classical cells, and packs the returned phase bits. Its complete Output and
independent native budgets belong to the same execution.
-/
