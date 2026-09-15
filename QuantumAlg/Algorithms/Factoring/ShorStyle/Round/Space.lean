/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual live space during a reusable Shor quantum round

Selected gates, actual Z writes, packing and reload all retain the incoming
bank and classical cells. Scoped reset temporarily adds one classical bit.
The bound follows every visited runtime context, including that scratch;
neither a quantum auxiliary nor a previous result is omitted.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

private theorem parent_space :
    ctx.residentSpace ≤ SpacePool.ofShape (.finite 2) + ctx.residentSpace ∧
      ctx.auxiliarySpace ≤ SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace :=
  ⟨fun _ => Nat.le_add_left _ _, fun _ => Nat.le_add_left _ _⟩

private theorem visited_spaces (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    (path : (code N sameWires parameter cells result).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code N sameWires parameter cells result).visitedContexts path) :
    frame.residentSpace ≤ SpacePool.ofShape (.finite 2) + ctx.residentSpace ∧
      frame.auxiliarySpace ≤ SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace := by
  change frame ∈ [ctx] ++
    ((Circuit.measurementSequence (readouts N sameWires cells)).visitedContexts path.2.1 ++
      ([ctx] ++ ((ZReset.BankScope.code (NativePlacement.qubits N sameWires)).visitedContexts
        path.2.2.2.1 ++ [ctx]))) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with same | measured | same | reset | same
  · subst frame
    exact parent_space
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact parent_space
  · subst frame
    exact parent_space
  · exact ⟨(Circuit.residentSpace_le_peak_of_visited _ path.2.2.2.1 frame reset).trans_eq
      (ZReset.BankScope.zResetBankScope_peakResidentSpace _ path.2.2.2.1),
      (Circuit.auxiliarySpace_le_peak_of_visited _ path.2.2.2.1 frame reset).trans_eq
      (ZReset.BankScope.zResetBankScope_peakAuxiliarySpace _ path.2.2.2.1)⟩
  · subst frame
    exact parent_space

/-- Resident space counts every incoming system and result plus the actual reset scratch bit. -/
theorem resident_le (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    (path : (code N sameWires parameter cells result).Path) :
    (code N sameWires parameter cells result).peakResidentSpace path ≤
      SpacePool.ofShape (.finite 2) + ctx.residentSpace :=
  Circuit.peakResidentSpace_le_of_visited _ path _
    (fun frame present => (visited_spaces N sameWires parameter cells result path frame present).1)

/-- The same executed contexts bound auxiliary storage with all original roles unchanged. -/
theorem auxiliary_le (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    (path : (code N sameWires parameter cells result).Path) :
    (code N sameWires parameter cells result).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_le_of_visited _ path _
    (fun frame present => (visited_spaces N sameWires parameter cells result path frame present).2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
