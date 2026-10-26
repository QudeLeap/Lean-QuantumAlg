/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Transport
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Input
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Seed
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch

/-!
# Real fresh-feedback storage around three complete sampling and recovery attempts

The same seven checker cells are retained once. One lexical feedback scope
then surrounds the actual restart, thirty-four allocating window drivers and
paid nearest recovery of every attempt. Its 514 cells are released before the
original optional batch result is packed. The allocating sampler is executed
directly in the fixed inner context; no allocating child is embedded as an
allocation-free circuit and no second persistent checker context is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve

/-- The seven original retained destinations, with no replacement checker allocation. -/
structure Checkers (ctx : RuntimeCtx .quantum) where
  inverseSuccess : CWriteRef ctx .bit
  candidate : CWriteRef ctx (.unsignedWord 260)
  reconstruction : CWriteRef ctx .bit
  scalarResult : CWriteRef ctx (PointShape 256)
  targetAccepted : CWriteRef ctx .bit
  accepted : CWriteRef ctx .bit
  selected : CWriteRef ctx (.unsignedWord 260)

namespace Checkers

/-- Read the literal destinations created by the existing one-time retain program. -/
def retained (ctx : RuntimeCtx .quantum) : Checkers
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) where
  inverseSuccess :=
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentInverseSuccess ctx 256 260
  candidate := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCandidate ctx 256 260
  reconstruction :=
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentReconstruction ctx 256 260
  scalarResult := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentScalar ctx 256 260
  targetAccepted :=
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentTargetAccepted ctx 256 260
  accepted := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentAccepted ctx 256 260
  selected := ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentSelected ctx 256 260

/-- All seven same physical checker destinations stay live through feedback allocation. -/
def transport {outer inner : RuntimeCtx .quantum} (checkers : Checkers outer)
    (lift : Transport outer inner) : Checkers inner where
  inverseSuccess := lift.liftWrite checkers.inverseSuccess
  candidate := lift.liftWrite checkers.candidate
  reconstruction := lift.liftWrite checkers.reconstruction
  scalarResult := lift.liftWrite checkers.scalarResult
  targetAccepted := lift.liftWrite checkers.targetAccepted
  accepted := lift.liftWrite checkers.accepted
  selected := lift.liftWrite checkers.selected

end Checkers

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)

/-- Real all-bank measured reset and the same paid native fixed affine loader. -/
def restart (output : CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  let cleanup : Cleanup.Parameters ctx := ⟨original.sameWires, output⟩
  .embed (ContextEmbedding.identity ctx)
    (cleanup.prepared (Initialization.placedProgram cleanup original.seedX original.seedY))

/-- Existing chronological samples flow directly into the explicit seven checker refs. -/
def attempt (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  ((original.restart (sampler.output 0)).seq (Sampling.circuit sampler)).seq
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest.attemptInto
      original.curve original.order (Recovery.pairedInput sampler) original.base original.target
      checkers.inverseSuccess checkers.candidate checkers.reconstruction checkers.scalarResult
      checkers.targetAccepted checkers.accepted checkers.selected)

/-- Allocate feedback once at the original retained context and reuse it for every attempt. -/
def scopedAttempts (count : Nat) :
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
      Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers

/-- The scratch scope has exited before the unchanged original result allocation and read. -/
def run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model services) ctx
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.batchResultCtx ctx 256 260)
    (.option (.unsignedWord 260)) where
  code := ((ClassicalRoutines.EllipticCurve.CandidateCheck.Native.retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).seq
      (original.scopedAttempts (services := services) 3)).seq
        (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.packBatchResult
          (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
  output := Output.all _
    (.read (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.batchResultRead ctx 256 260))

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
