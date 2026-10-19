/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Model
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Native
public import QuantumAlg.Primitives.QFT.Native.Inverse
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Core.Base.Oracle.Placement.Construction

/-!
# Actual declared ECDLP unitary sampling word

Two native known-order preparations and two native inverse Fourier transforms
execute in parallel. The sole query retains the complete original point bank.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Prepare both exponent registers and leave the entire point register untouched. -/
public def preparations (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    UnitaryCircuit AlgorithmGate.model (model I) (layout I) :=
  UnitaryCircuit.onBinaryPrefix (Layout.pointWidth E)
    (UnitaryCircuit.parallelBinary
      (FiniteCyclicDLP.OrderPreparation.Native.circuit (model I) (problem I) expansion)
      (FiniteCyclicDLP.OrderPreparation.Native.circuit (model I) (problem I) expansion))

/-- Invoke the original model-owned group action once at the actual placement. -/
public def oracleLayer (I : ECDLPInstance E) :
    UnitaryCircuit AlgorithmGate.model (model I) (layout I) :=
  .query (OracleModel.Application.onPlacement (model I) ()
    (QuantumSignature.qubits (Layout.totalQubits I)).canonicalPlacement)

/-- Transform both exponent registers in parallel while preserving the point bank. -/
public def inverseQFTs (I : ECDLPInstance E) :
    UnitaryCircuit AlgorithmGate.model (model I) (layout I) :=
  UnitaryCircuit.onBinaryPrefix (Layout.pointWidth E)
    (UnitaryCircuit.parallelBinary
      (QuantumFourierTransform.Native.inverseCircuit (model I)
        (FiniteCyclicDLP.orderWidth (problem I)))
      (QuantumFourierTransform.Native.inverseCircuit (model I)
        (FiniteCyclicDLP.orderWidth (problem I))))

/-- Execute the complete preparation-query-readout unitary word. -/
public def circuit (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    UnitaryCircuit AlgorithmGate.model (model I) (layout I) :=
  ((preparations I expansion).seq (oracleLayer I)).seq (inverseQFTs I)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
