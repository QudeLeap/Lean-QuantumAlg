/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Recovery.Execution
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model.Bounds
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract

/-!
# Original selected exponent events pass the actual candidate condition

The original selected event already determines the raw inverse-success flag,
recovered secret word and reconstruction flag. Its natural scalar acts on the
original public base and target points. The original order and Fourier width
internally prove that encoding the secret does not truncate it. The secret is
a proof witness and is never an input to the actual recovery circuit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {kind : ProblemKind} {ctx : RuntimeCtx kind}

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
