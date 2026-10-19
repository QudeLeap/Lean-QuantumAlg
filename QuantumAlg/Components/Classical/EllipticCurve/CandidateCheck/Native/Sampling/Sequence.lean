/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding.Sequence

/-!
# The actual native sampling boundary before persistent candidate checking

The original fixed sampling child is split into its original two sections.
The same checked recovery then consumes the same stored result. The witness
retains all actual events, states, paths, chronological depths and space peaks.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The real sampled attempt exposes both native sections before the same checked recovery. -/
def candidateCheck_sampledAttempt_seqOperationalEquiv
    (first second : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit.OperationalEquiv
      (sampledAttempt (first.seq second) curve modulus sample base target)
      ((sampleUnderPersistent first width scalarWidth).seq
        ((sampleUnderPersistent second width scalarWidth).seq
          (persistentAttempt curve modulus sample base target))) :=
  ((candidateCheck_sampleUnderPersistent_seqOperationalEquiv first second width scalarWidth).append
    (persistentAttempt curve modulus sample base target)).trans
      (Circuit.seqAssocOperationalEquiv
        (sampleUnderPersistent first width scalarWidth)
        (sampleUnderPersistent second width scalarWidth)
        (persistentAttempt curve modulus sample base target))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
