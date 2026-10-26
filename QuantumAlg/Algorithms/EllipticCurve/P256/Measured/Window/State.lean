/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Context
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Context
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Zero

/-! # Physical output-state promise of the complete paid P-256 window run -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open Execution ClassicalRoutines.EllipticCurve PrimeFieldShortWeierstrass

/-- Every observed optional result leaves the complete retained owned bank in physical zero. -/
def zeroRequirement (I : DomainParameters.PublicKeyInstance) :
    StateRequirement (Pre I) (Post I) :=
  StateRequirement.marginal (Post I).borrowedSelectionᶜ
    (.read (CandidateCheck.Native.batchResultRead
      (Factory.tableContext (Factory.publicFrame I) (Factory.publicFrame_noQuantum I)) 256 260))
    (fun _ _ => .pure (NormalizedVector.ket
      (Factory.paidRunZeroSeed (Factory.publicFrame I) (Factory.publicFrame_noQuantum I))))

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
