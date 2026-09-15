/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.General.Projections
public import QuantumAlg.Algorithms.OrderFinding.General.PublicCounts
public import QuantumAlg.Algorithms.OrderFinding.General.ClassicalCounts

/-!
# General order finding

The complete native endpoint preserves the original source input window and
success bound. The actual measured sample drives finite classical recovery;
public projections expose independent native space and depth limits.
-/
