/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle.Canonical
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Projections
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.GateCounts
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.ClassicalCounts
public import QuantumAlg.Util.Nat.ChooseTwo
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Util.Order.Finding
import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# General order finding on signed inputs and canonical register widths

The mathematical integer base is represented by its canonical residue in the
original borrowed input cell. Both widths are fixed by the modulus, so the
source window and the complete resource bounds need no extra access premise.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint.Canonical

noncomputable section

/-- Canonical sizing uses only the public modulus and its nontriviality certificate. -/
@[expose] public def modulusSpec {N : Nat} (modulus : 2 ≤ N) :
    ClassicalAlgorithms.Modular.ModulusSpec (targetWidth N) where
  modulus := N
  two_le := modulus
  le_capacity := orderFinding_targetWidth_fits N

/-- The fixed canonical execution depends only on the public modulus. -/
public def algorithm {N : Nat} (modulus : 2 ≤ N) :=
  SourceNativeEndpoint.algorithm (modulusSpec modulus) (phaseWidth N)

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint.Canonical
