/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Context
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Context
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Run

/-!
# One complete paid P-256 window algorithm

The sole run allocates and prepares its bank and tables, performs three actual
checked attempts and packs the result. No proof-side secret or quality evidence
is an argument to this construction. Correctness and budgets are proved separately.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

/-- One literal paid factory execution on the unchanged original public input frame. -/
public def algorithm (I : DomainParameters.PublicKeyInstance) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (Pre I) (Post I) OutputShape where
  run := Factory.paidRun (services := .empty)
    (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
