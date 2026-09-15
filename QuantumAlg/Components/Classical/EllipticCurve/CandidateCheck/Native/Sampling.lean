/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Run

/-!
# Actual sampling interleaved with persistent candidate checking

Each round executes the supplied actual local sampling circuit and immediately
consumes its stored sample in the original complete checked recovery. The
original seven persistent destinations are allocated once and reused by every
round. Only after the finite loop is the actual optional result retained and
packed. This construction supplies no probability or preparation hypothesis;
those guarantees must be proved for the supplied physical sampling circuit.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- Sample and immediately check the new stored value using the existing persistent destinations. -/
def sampledAttempt (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  (underPersistent sampleCode supported width scalarWidth).seq
    (persistentAttempt curve modulus sample base target)

/-- Every actual sampling round uses the same result cells and original first-success latches. -/
def sampledAttempts (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (count : Nat) (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  Circuit.forRange count fun _ =>
    sampledAttempt sampleCode supported curve modulus sample base target

/-- Allocate once, interleave actual sampling and checking, then retain and pack the result once. -/
def sampledRecoveryTail (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (count : Nat) (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit ctx (batchResultCtx ctx width scalarWidth) :=
  ((retainPersistent ctx width scalarWidth).seq
    (sampledAttempts sampleCode supported count curve modulus sample base target)).seq
      (packBatchResult ctx width scalarWidth)

/-- The complete actual output reads the one final optional result and lists all live entries. -/
def sampledRecoveryRun (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (count : Nat) (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    AlgorithmRun ctx (batchResultCtx ctx width scalarWidth)
      (.option (.unsignedWord scalarWidth)) where
  code := sampledRecoveryTail sampleCode supported count curve modulus sample base target
  output := Output.all (batchResultCtx ctx width scalarWidth)
    (.read (batchResultRead ctx width scalarWidth))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
