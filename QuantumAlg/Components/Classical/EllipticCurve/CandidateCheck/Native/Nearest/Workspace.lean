/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Sampling.TailResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Workspace

/-!
# Exact nearest-recovery workspace coordinates

The extra product-width half word is charged beside every existing preparation
cell. Checked inversion and candidate verification retain their actual separate
scratch scopes; the persistent seven-cell destinations remain unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

noncomputable section

open Execution QuantumAlg.ClassicalRoutines
open NumberTheory.Checked.SignedReduction

/-- Exact actual scratch maximum, including the paid half word used by nearest scaling. -/
lemma recoveryTailScratchSpace_eq_bits (kind : ProblemKind)
    (fieldWidth sampleWidth : Nat) :
    recoveryTailScratchSpace kind fieldWidth sampleWidth =
      SpacePool.ofShape (.bits (max
        (27 * sampleWidth + 9 * signedWidth sampleWidth + 17)
        (27 * fieldWidth + 9 * signedWidth fieldWidth + 15))) := by
  rw [recoveryTailScratchSpace, attemptScratchSpace,
    CandidateCheck.Native.exposure_active, CandidateCheck.Native.verification_scratch]
  ext axis
  cases axis with
  | classicalBits =>
      simp [FiniteCyclicDLP.RawRecovery.Nearest.preparationShapes,
        FiniteCyclicDLP.RawRecovery.Native.preparationShapes,
        FiniteCyclicDLP.RawRecovery.Native.scaleDivisionShape,
        FirstAccepted.selectionScratchSpace, SpacePool.ofShape, SpacePool.max, Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [FiniteCyclicDLP.RawRecovery.Nearest.preparationShapes,
        FiniteCyclicDLP.RawRecovery.Native.preparationShapes,
        FiniteCyclicDLP.RawRecovery.Native.scaleDivisionShape,
        FirstAccepted.selectionScratchSpace, SpacePool.ofShape, SpacePool.max]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
