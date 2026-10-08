/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Exact-grid native order-finding execution

The real source sampler writes its phase word. A retained finite decoder then
reads that same word and materializes the unsigned result while keeping every
phase system, target system and measurement cell live.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

open QuantumAlg.Execution

private theorem samplePreNoQuantum_internal : Sampling.Native.pre.quantumWires = [] := rfl

/-- The source sample starts with no live quantum wires. -/
public theorem samplePreNoQuantum : Sampling.Native.pre.quantumWires = [] :=
  samplePreNoQuantum_internal

/-- The source sampler instantiated on the empty classical frame. -/
@[expose, reducible] public def samplePost (t width : Nat) : RuntimeCtx .quantum :=
  Sampling.Native.Framed.post Sampling.Native.pre samplePreNoQuantum t width

/-- The actual source sampler keeps its canonical lexical storage keys. -/
public def sampleCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (Sampling.Native.model access) Sampling.Native.pre (samplePost t width) :=
  Sampling.Native.Framed.code Sampling.Native.pre samplePreNoQuantum access

/-- The same source sampler whose Born output law is proved. -/
@[expose, reducible] public def sampleRun {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    AlgorithmRun (Sampling.Native.model access)
      Sampling.Native.pre (samplePost t width) (.bits t) :=
  Sampling.Native.Framed.run Sampling.Native.pre samplePreNoQuantum access

/-- One fresh word follows the complete native sample. -/
public def resultKey (t width : Nat) : StorageKey :=
  (samplePost t width).canonicalFreshKey

public theorem resultFresh (t width : Nat) :
    resultKey t width ∉ (samplePost t width).keys :=
  (samplePost t width).canonicalFreshKey_fresh

/-- The decoded result is retained beside the actual sample and all live systems. -/
@[expose, reducible] public def post (t width : Nat) : RuntimeCtx .quantum :=
  (samplePost t width).addRetained
    (resultKey t width) (.unsignedWord t) (resultFresh t width)

/-- Structural read of the phase bits already written by the source sampler. -/
def sampleInput (t width : Nat) :
    CInputRef (samplePost t width) (.bits t) :=
  .storage (Sampling.Native.Framed.resultRef
    Sampling.Native.pre samplePreNoQuantum t width).toCStorageRef

/-- The finite decoder writes its unsigned result into the fresh retained cell. -/
def decoderCode {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (Sampling.Native.model access)
      (samplePost t width) (post t width) :=
  ClassicalRoutines.TerminalDecode.routine (model := Sampling.Native.model access)
    (samplePost t width) t .bigEndian (sampleInput t width)
    (resultKey t width) (resultFresh t width)

/-- Actual sampling followed by the stored-bit decoder. -/
def code {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    Circuit (Sampling.Native.model access) Sampling.Native.pre (post t width) :=
  .seq (sampleCode access) (decoderCode access)

/-- Read the retained unsigned word and list every live entry. -/
def run {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    AlgorithmRun (Sampling.Native.model access)
      Sampling.Native.pre (post t width) (.unsignedWord t) where
  code := code access
  output := Output.all (post t width)
    (.read (ClassicalRoutines.TerminalDecode.resultRef
      (samplePost t width) t (resultKey t width) (resultFresh t width)))

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
