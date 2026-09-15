/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Readout
import all QuantumAlg.Core.Execution.Store

/-!
# Complete live output of native general order finding

The result option is retained alongside the actual source-sampling quantum
systems, original borrowed base and measured phase cells. Native recovery
reads those same operands underneath the final result allocation.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The original optional candidate word, with its full phase-width capacity. -/
def outputShape (t : Nat) : CShape := .option (.unsignedWord (t + 1))

def resultKey (t width : Nat) : StorageKey := (NativeSampling.post t width).canonicalFreshKey

theorem resultFresh (t width : Nat) : resultKey t width ∉ (NativeSampling.post t width).keys :=
  (NativeSampling.post t width).canonicalFreshKey_fresh

/-- Every original input, sampled system and classical result remains live. -/
def post (t width : Nat) : RuntimeCtx .quantum :=
  (NativeSampling.post t width).addRetained
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- The real retained final optional result. -/
def resultRef (t width : Nat) : CWriteRef (post t width) (outputShape t) :=
  CWriteRef.retainedHead (NativeSampling.post t width)
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- Read the original borrowed modular base without copying it. -/
def baseInput (t width : Nat) : CInputRef (post t width) (.canonicalResidue width) :=
  (NativeSampling.baseRef t width).underRetained
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- Read the same actual measured-and-packed phase bits. -/
def sampleInput (t width : Nat) : CInputRef (post t width) (.bits t) :=
  (NativeSampling.sampleRef t width).underRetained
    (resultKey t width) (outputShape t) (resultFresh t width)

theorem post_quantumWires (t width : Nat) :
    (post t width).quantumWires = (NativeSampling.post t width).quantumWires := rfl

/-- Final result allocation preserves the actual original base operand. -/
theorem baseInput_read (t width : Nat) (store : Store (NativeSampling.post t width)) :
    (store.pushRetained (resultKey t width) (outputShape t) (resultFresh t width)).read
      (baseInput t width) = store.read (NativeSampling.baseRef t width) :=
  Store.read_pushRetained_underRetained store _ _ _ _

/-- Final result allocation preserves the actual source-sampling result. -/
theorem sampleInput_read (t width : Nat) (store : Store (NativeSampling.post t width)) :
    (store.pushRetained (resultKey t width) (outputShape t) (resultFresh t width)).read
      (sampleInput t width) = store.read (NativeSampling.sampleRef t width) :=
  Store.read_pushRetained_underRetained store _ _ _ _

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
