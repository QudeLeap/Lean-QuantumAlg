/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Framing
import all QuantumAlg.Core.Execution.Local.Cells

/-!
# Original sampling and readout with all result cells already resident

The original exponent preparation, measured scalar cascade and inverse QFT
run beside the same terminal cells and both original public inputs. Actual Z
readout overwrites those cells at the end of the round. This local body can
be repeated without growing the live context. The surrounding circuit must
really prepare the input and workspace; this construction makes no input-state
or success-probability claim by itself.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual original gates and readout reuse the complete resident terminal context. -/
def samplingReadout (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty) (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)) :=
  (frameLocal
    (Circuit.underMeasurementCells (samplingPrefix E fieldTail odd problem points)
      (samplingPrefix_isLocal E fieldTail odd problem points) 2 (2 * orderWidth problem))
    (Circuit.underMeasurementCells_isLocal (samplingPrefix E fieldTail odd problem points)
      (samplingPrefix_isLocal E fieldTail odd problem points) 2 (2 * orderWidth problem))
    (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem))).seq
      (PublicInput.measurements E (orderWidth problem))

/-- The entire round body acts within the same existing systems and result cells. -/
theorem samplingReadout_isLocal (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    (samplingReadout E fieldTail odd problem points).IsLocal :=
  ⟨frameLocal_isLocal _ _ _ _, frameLocal_isLocal _ _ _ _⟩

/-- Every visited context contains precisely the same quantum and classical resident resources. -/
theorem samplingReadout_visited (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (samplingReadout E fieldTail odd problem points).Path)
    (visited : RuntimeCtx .quantum)
    (present : visited ∈ (samplingReadout E fieldTail odd problem points).visitedContexts path) :
    visited = PublicInput.terminal E (orderWidth problem) :=
  local_visited _ (samplingReadout_isLocal E fieldTail odd problem points) path visited present

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
