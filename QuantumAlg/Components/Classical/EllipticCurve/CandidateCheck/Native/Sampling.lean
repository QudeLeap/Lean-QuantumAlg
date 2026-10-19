/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Run

/-!
# Actual sampling interleaved with persistent candidate checking

Each round executes the supplied original fixed-context sampling circuit and immediately
consumes its stored sample in the original complete checked recovery. The
original seven persistent destinations are allocated once and reused by every
round. Only after the finite loop is the actual optional result retained and
packed. This construction supplies no probability or preparation hypothesis;
those guarantees must be proved for the supplied physical sampling circuit.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Sample and immediately check the new stored value using the existing persistent destinations. -/
def sampledAttempt (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth)
      (persistentCtx ctx width scalarWidth) :=
  (sampleUnderPersistent sampleCode width scalarWidth).seq
    (persistentAttempt curve modulus sample base target)

/-- Every actual sampling round uses the same result cells and original first-success latches. -/
def sampledAttempts (sampleCode : Circuit model ctx ctx false)
    (count : Nat) (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth)
      (persistentCtx ctx width scalarWidth) :=
  Circuit.forRange count fun _ =>
    sampledAttempt sampleCode curve modulus sample base target

/-- Allocate once, interleave actual sampling and checking, then retain and pack the result once. -/
def sampledRecoveryTail (sampleCode : Circuit model ctx ctx false)
    (count : Nat) (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model ctx (batchResultCtx ctx width scalarWidth) :=
  ((retainPersistent ctx width scalarWidth).seq
    (sampledAttempts sampleCode count curve modulus sample base target)).seq
      (packBatchResult ctx width scalarWidth)

/-- The complete actual output reads the one final optional result and lists all live entries. -/
def sampledRecoveryRun (sampleCode : Circuit model ctx ctx false)
    (count : Nat) (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    AlgorithmRun model ctx (batchResultCtx ctx width scalarWidth)
      (.option (.unsignedWord scalarWidth)) where
  code := sampledRecoveryTail sampleCode count curve modulus sample base target
  output := Output.all (batchResultCtx ctx width scalarWidth)
    (.read (batchResultRead ctx width scalarWidth))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
