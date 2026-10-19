/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.Readout
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Specification
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Core.Execution.Output

/-!
# Connected native general order-finding execution

The actual source sample retains its borrowed canonical base and measured
phase word. One finite native recovery circuit then reads those same cells
and writes a retained optional order candidate. All live cells and quantum
systems remain in the final manifest. Distribution and success theorems are
separate obligations of this connected execution.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The retained final result has one extra bit for the order candidate. -/
@[expose] public def outputShape (t : Nat) : CShape := .option (.unsignedWord (t + 1))

/-- A fresh result key follows the complete retained source sample. -/
@[expose] public def resultKey (t width : Nat) : StorageKey :=
  (SourceNativeSampling.post t width).canonicalFreshKey

/-- The final result key is absent from all source-sample cells. -/
public lemma resultFresh (t width : Nat) :
    resultKey t width ∉ (SourceNativeSampling.post t width).keys :=
  (SourceNativeSampling.post t width).canonicalFreshKey_fresh

/-- The final context retains the original base, qubits, measurements and option. -/
@[expose, reducible] public def post (t width : Nat) : RuntimeCtx .quantum :=
  (SourceNativeSampling.post t width).addRetained
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- The actual option cell written by the finite recovery circuit. -/
def resultRef (t width : Nat) : CWriteRef (post t width) (outputShape t) :=
  CWriteRef.retainedHead (SourceNativeSampling.post t width)
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- Recovery reads the original borrowed base through one retained-cell extension. -/
def baseInput (t width : Nat) :
    CInputRef (post t width) (.canonicalResidue width) :=
  (SourceNativeSampling.baseRef t width).underRetained
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- Recovery reads the actual packed phase result through that same extension. -/
def sampleInput (t width : Nat) : CInputRef (post t width) (.bits t) :=
  (SourceNativeSampling.sampleRef t width).underRetained
    (resultKey t width) (outputShape t) (resultFresh t width)

/-- The selected native word program performs finite continued-fraction recovery. -/
def recoveryCode {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) :
    Circuit (Sampling.Native.Framed.model t width) (post t width) (post t width) :=
  ClassicalRoutines.OrderRecovery.Native.into
    (model := Sampling.Native.Framed.model t width)
    (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec width t) (baseInput t width)
    (sampleInput t width) (resultRef t width)

/-- Allocate the output option and then run the actual finite recovery program. -/
def recoveryStage {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) :
    Circuit (Sampling.Native.Framed.model t width)
      (SourceNativeSampling.post t width) (post t width) :=
  .seq (.retain (model := Sampling.Native.Framed.model t width)
    (SourceNativeSampling.post t width) (resultKey t width)
    (outputShape t) (resultFresh t width)) (recoveryCode spec t)

/-- One interpreter executes the source sample and its dependent classical recovery. -/
def code {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) :
    Circuit (Sampling.Native.Framed.model t width) (pre width) (post t width) :=
  .seq (SourceNativeSampling.code t width) (recoveryStage spec t)

/-- The final result reads the retained option without discarding live inputs. -/
def run {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) :
    AlgorithmRun (Sampling.Native.Framed.model t width)
      (pre width) (post t width) (outputShape t) where
  code := code spec t
  output := Output.all (post t width)
    (.read (.storage (resultRef t width).toCStorageRef))

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
