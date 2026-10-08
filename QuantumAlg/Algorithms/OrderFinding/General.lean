/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Projections
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.ClassicalCounts
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Counts
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.GateCounts

public import QuantumAlg.Algorithms.OrderFinding.Native.Macros
public import QuantumAlg.Util.Order.Finding.Signed

/-!
# General order finding

The complete native endpoint preserves the original source input window and
success bound. The actual measured sample drives finite classical recovery;
public projections expose independent native space and classical-operation limits.
Every complete execution retains exactly one declared source query.
Its native peripheral gate counts are proved for that same execution path.
-/
