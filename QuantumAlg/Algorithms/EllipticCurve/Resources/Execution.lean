/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Input
import all QuantumAlg.Core.Algorithm.Solves

/-!
# The named generic measured ECDLP solver

The factory contains the complete actual streaming run used by the public
existential main. Canonical Boundary theorem owners retain the first/reused
state, event, quantum-time, storage and borrowed/reference contracts directly.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
open FiniteCyclicDLP
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract


variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

namespace Execution

/-- The original borrowed public-point context used by the generic public problem. -/
public def inputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  Spec.inputContext E I

/-- The original complete bank and checked-result context used by the generic public problem. -/
public def outputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  Spec.outputContext E I

end Execution

/-- The named solver has exactly the same complete actual run as the registered main. -/
public def algorithm (fieldTail : Nat) (_sameWidth : fieldTail.succ = p.size)
    (_fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (count : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (Execution.inputContext E I) (Execution.outputContext E I)
      (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  run := run E fieldTail (ECDLP.Canonical.problem I) points seed I.subgroupOrder
    (Semantics.radixUnit p fieldTail.succ odd) I.subgroupOrder_prime.two_le count


end

end QuantumAlg.EllipticCurve.LogicalResources
