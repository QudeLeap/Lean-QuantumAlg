/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle.Canonical
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Projections
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Counts
public import QuantumAlg.Util.Nat.ChooseTwo
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Endpoint

/-! # Exact dyadic sampling at the minimum target width -/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint.Canonical

noncomputable section

/-- The same complete sample and retained decoder use the minimum target register. -/
public def algorithm (N t : Nat) :=
  NativeEndpoint.algorithm t (targetWidth N)

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint.Canonical
