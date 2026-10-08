/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual live space of the reusable-bank round

The selected unitary, all Z writes, packing and reload retain the same complete
runtime context. Only the scoped reset adds one finite two-valued classical
cell while its body runs. Resident and auxiliary peaks therefore add that
one scratch bit to their respective incoming roles. No quantum capacity grows
between rounds, and all existing measured and packed results remain counted.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private theorem parent_space :
    ctx.residentSpace ≤ SpacePool.ofShape (.finite 2) + ctx.residentSpace ∧
      ctx.auxiliarySpace ≤ SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace :=
  ⟨fun _ => Nat.le_add_left _ _, fun _ => Nat.le_add_left _ _⟩

private theorem visited_spaces {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈
      (code m ell width sameWires parameter N generator target cells result).visitedContexts path) :
    frame.residentSpace ≤ SpacePool.ofShape (.finite 2) + ctx.residentSpace ∧
      frame.auxiliarySpace ≤ SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace := by
  change frame ∈ List.append (α := RuntimeCtx .quantum) [ctx]
    (List.append (α := RuntimeCtx .quantum)
      ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).visitedContexts path.2.1)
      (List.append (α := RuntimeCtx .quantum) [ctx]
        (List.append (α := RuntimeCtx .quantum)
          (Circuit.visitedContexts (ZReset.BankScope.code
            (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) BitWord.model)
            path.2.2.2.1) [ctx]))) at present
  simp only [List.append_eq, List.mem_append, List.mem_singleton] at present
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
      (ZReset.BankScope.zResetBankScope_peakResidentSpace
        (operations := BitWord.model) _ path.2.2.2.1),
      (Circuit.auxiliarySpace_le_peak_of_visited _ path.2.2.2.1 frame reset).trans_eq
      (ZReset.BankScope.zResetBankScope_peakAuxiliarySpace
        (operations := BitWord.model) _ path.2.2.2.1)⟩
  · subst frame
    exact parent_space

/-- Resident peak counts the original bank and outputs plus the real one-bit reset scratch. -/
theorem shortDLP_runtimeRound_resident_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).peakResidentSpace path ≤
      SpacePool.ofShape (.finite 2) + ctx.residentSpace :=
  Circuit.peakResidentSpace_le_of_visited _ path _
    (fun frame present =>
      (visited_spaces m ell width sameWires parameter N generator target cells result
        path frame present).1)

/-- Auxiliary peak uses the same actual entries with their unchanged declared roles. -/
theorem shortDLP_runtimeRound_auxiliary_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_le_of_visited _ path _
    (fun frame present =>
      (visited_spaces m ell width sameWires parameter N generator target cells result
        path frame present).2)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
