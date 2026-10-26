/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Reinitialized

/-!
# Three actual attempts followed by complete terminal bank cleanup

The retained seven checker destinations and one lexical feedback frame are
the same as in the recorded recovery run. After the third actual attempt, the
existing feedback result cell is reused to measure and correct every one of
the 854 original physical systems. The feedback frame is then released and
the original optional result is packed. The terminal cleanup has its own
chronological measurement records and introduces no new qubits or cells.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx)

/-- The existing reused feedback result cell resets the same sampler wires. -/
def finalizedCleanup {inner : RuntimeCtx .quantum}
    (sampler : Sampling.Parameters inner) : Cleanup.Parameters inner :=
  ⟨sampler.sameWires, sampler.output 0⟩

/-- Exact inner attempt loop and terminal reset, shared by the actual run and its proof. -/
def finalizedInnerBody {inner : RuntimeCtx .quantum}
    (inputs : Inputs inner) (sampler : Sampling.Parameters inner)
    (checkers : Checkers inner) (count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner true :=
  let cleanup := finalizedCleanup sampler
  (Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers).seq
    (.embed (ContextEmbedding.identity inner) cleanup.circuit)

/-- The original scoped attempts, then the real whole-bank reset while its
reused feedback result cell is still in scope. -/
def scopedAttemptsFinalized (count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260)
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) true :=
  let retained := original.transport
    (Recovery.persistentTransport ctx) (Recovery.persistent_wires ctx)
  withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260)
    256 256 fun lift same scratch fresh =>
      let sampler := retained.samplerParameters lift same scratch fresh
      let inputs := retained.transport lift same
      let checkers := (Checkers.retained ctx).transport lift
      inputs.finalizedInnerBody (services := services) sampler checkers count

/-- One retained checker frame, three actual attempts, terminal cleanup and
the same final packed optional result. -/
def runFinalized : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model services) ctx
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.batchResultCtx ctx 256 260)
    (.option (.unsignedWord 260)) where
  code := ((ClassicalRoutines.EllipticCurve.CandidateCheck.Native.retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).seq
      (original.scopedAttemptsFinalized (services := services) 3)).seq
        (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.packBatchResult
          (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
  output := Output.all _
    (.read (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.batchResultRead ctx 256 260))

end

end Storage.Inputs

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
