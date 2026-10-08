/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Space
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Space
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Resident and auxiliary space of exact native order finding

All source qubits, measurement cells and the packed phase word stay live.
The retained decoder adds one unsigned result word and no quantum system.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

/-- Independent complete live capacity including the decoded word. -/
def spaceBudget (t width : Nat) : SpacePool .quantum :=
  Sampling.Native.spaceBudget t width +
    SpacePool.ofShape (.unsignedWord t)

private theorem post_resident_eq (t width : Nat) :
    (post t width).residentSpace = spaceBudget t width := by
  rw [post, RuntimeCtx.residentSpace_addRetained,
    Sampling.Native.Framed.post_residentSpace Sampling.Native.pre samplePreNoQuantum]
  ext axis
  cases axis <;> simp [spaceBudget, SpacePool.ofShape, Sampling.Native.spaceBudget,
    Sampling.Native.Framed.residentBudget, Sampling.Native.pre]
  omega

private theorem post_auxiliary_eq (t width : Nat) :
    (post t width).auxiliarySpace = spaceBudget t width := by
  rw [post, RuntimeCtx.auxiliarySpace_addRetained,
    Sampling.Native.Framed.post_auxiliarySpace Sampling.Native.pre samplePreNoQuantum]
  ext axis
  cases axis <;> simp [spaceBudget, SpacePool.ofShape, Sampling.Native.spaceBudget,
    Sampling.Native.Framed.auxiliaryBudget, Sampling.Native.pre]
  omega

/-- Every complete execution path fits the independent resident capacity. -/
theorem code_resident_le {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    (code access).peakResidentSpace path ≤ spaceBudget t width := by
  change (Circuit.seq (sampleCode access)
    (decoderCode access)).Path at path
  change (Circuit.seq (sampleCode access)
    (decoderCode access)).peakResidentSpace path ≤ _
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · exact (Sampling.Native.Framed.code_residentSpace
      Sampling.Native.pre samplePreNoQuantum access path.1).trans
      (le_add_of_nonneg_right zero_le)
  · exact (ClassicalRoutines.TerminalDecode.terminalDecode_routine_resident_le
      (model := Sampling.Native.model access)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) path.2).trans_eq
        (post_resident_eq t width)

/-- The same capacity bounds fresh systems and retained decoder storage. -/
theorem code_auxiliary_le {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    (code access).peakAuxiliarySpace path ≤ spaceBudget t width := by
  change (Circuit.seq (sampleCode access)
    (decoderCode access)).Path at path
  change (Circuit.seq (sampleCode access)
    (decoderCode access)).peakAuxiliarySpace path ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · exact (Sampling.Native.Framed.code_auxiliarySpace
      Sampling.Native.pre samplePreNoQuantum access path.1).trans
      (le_add_of_nonneg_right zero_le)
  · exact (ClassicalRoutines.TerminalDecode.terminalDecode_routine_auxiliary_le
      (model := Sampling.Native.model access)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) path.2).trans_eq
        (post_auxiliary_eq t width)

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
