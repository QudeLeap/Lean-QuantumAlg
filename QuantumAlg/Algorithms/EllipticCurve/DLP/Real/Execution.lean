/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Scalar
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.ClassicalSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model

/-!
# Full declared ECDLP recovery at arbitrary positive real failure targets

The public order determines its own certified preparation expansion. One
complete named execution supplies success, all output/reference fibers,
borrowed restoration, complete-run quantum time and the original scalar resources.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget

noncomputable section
open Canonical.QueryModel Canonical.QueryModel.Recovery
variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The public order alone fixes the certified preparation expansion. -/
public def sourceExpansion (I : ECDLPInstance E) :
    FiniteCyclicDLP.OrderExpansion I.subgroupOrder :=
  FiniteCyclicDLP.OrderExecution.canonicalExpansion (Canonical.problem I)

/-- The real target selects the original complete code with a locally calibrated count. -/
public abbrev algorithm (I : ECDLPInstance E) (η : Real) :=
  realWholeAlgorithm I (sourceExpansion I) I.subgroupOrder_prime.two_le η

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget
