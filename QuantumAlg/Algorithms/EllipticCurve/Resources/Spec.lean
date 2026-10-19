/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract

/-!
# Pure original ECC success contracts without the old execution dependency

The original success definitions are reexported from the pure Recovery.Contract owner.
Accepted equations, exceptional-error conditions and repetition thresholds remain
independent of the streaming execution.

The accepted equation, finite exceptional-error condition and success threshold
remain independent of the streaming implementation. No resource allowance or
old protocol execution is imported to obtain these mathematical definitions.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

end

end QuantumAlg.EllipticCurve.LogicalResources
