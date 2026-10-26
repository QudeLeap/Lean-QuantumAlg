/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Transport
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Input
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Seed
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest

/-!
# Actual three-round recycled-window sampling with paid nearest recovery

Seven persistent checker destinations are allocated once. Every round really
resets all 854 systems, loads the same fixed affine point, executes the same 34
window/table drivers and consumes their actual chronological result cells in
the original paid nearest recovery and checked first-success latch. The final
option is packed once after all three complete attempts. Probability and
point-action laws are separate contracts of this literal syntax.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Recovery

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve

/-- Original caller references, public classical arithmetic and one fixed affine seed. -/
structure Parameters (ctx : RuntimeCtx .quantum) where
  sampler : Sampling.Parameters ctx
  curve : CurveSpec 256
  order : ModulusSpec 260
  base : CInputRef ctx (PointShape 256)
  target : CInputRef ctx (PointShape 256)
  seedX : Fin (2 ^ 256)
  seedY : Fin (2 ^ 256)

namespace Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  (original : Parameters ctx)

/-- The same sampling references surround the actual persistent checker cells. -/
def samplerParameters := Recovery.parameters original.sampler

/-- One existing point scratch cell serves the entire actual all-bank reset. -/
def cleanupParameters : Cleanup.Parameters
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) where
  sameWires := original.samplerParameters.sameWires
  output := original.samplerParameters.output 0

/-- Every attempt begins with the real 854 MZ/reset word and the same native affine loader. -/
def restart : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) true :=
  .embed (ContextEmbedding.identity _)
    (original.cleanupParameters.prepared
      (Initialization.placedProgram original.cleanupParameters original.seedX original.seedY))

/-- The literal 34 allocating windows follow that same complete actual physical restart. -/
def sample : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) true :=
  original.restart.seq (Sampling.circuit original.samplerParameters)

/-- Actual nearest pack/decode/split, candidate verification and first-success selection. -/
def attempt : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) true :=
  original.sample.seq
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      original.curve original.order (pairedInput original.sampler) original.base original.target)

/-- Every public attempt count retains the same real chronological sampler and checker. -/
def attempts (count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260)
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) true :=
  Circuit.forRange count fun _ => original.attempt

/-- Exactly three actual attempts execute 102 complete point/table drivers before final packing. -/
def run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model services) ctx
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.batchResultCtx ctx 256 260)
    (.option (.unsignedWord 260)) where
  code := ((ClassicalRoutines.EllipticCurve.CandidateCheck.Native.retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).seq
      (original.attempts (services := services) 3)).seq
        (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.packBatchResult
          (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
  output := Output.all _
    (.read (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.batchResultRead ctx 256 260))

end Parameters

end

end Recovery

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
