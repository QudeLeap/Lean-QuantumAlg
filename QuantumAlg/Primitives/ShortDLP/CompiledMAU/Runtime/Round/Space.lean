/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual live space of the reusable-bank round

The selected unitary, all Z writes, packing and reload retain the same complete
runtime context. The parent reset allocates one finite two-valued classical cell for each
physical bank wire before executing its fixed body. Resident and auxiliary
peaks include all those simultaneously live result cells. No quantum capacity grows
between rounds, and all existing measured and packed results remain counted.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

/-- Exact temporary classical capacity allocated by the simultaneous bank reset. -/
def resetSpace (m ell width : Nat) : SpacePool .quantum :=
  totalQubits (registerParameters m ell width) • SpacePool.ofShape (.finite 2)

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private lemma parent_space :
    ctx.residentSpace ≤ resetSpace m ell width + ctx.residentSpace ∧
      ctx.auxiliarySpace ≤ resetSpace m ell width + ctx.auxiliarySpace :=
  ⟨fun _ => Nat.le_add_left _ _, fun _ => Nat.le_add_left _ _⟩

private lemma visited_spaces {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈
      (code m ell width sameWires parameter N generator target cells result).visitedContexts path) :
    frame.residentSpace ≤ resetSpace m ell width + ctx.residentSpace ∧
      frame.auxiliarySpace ≤ resetSpace m ell width + ctx.auxiliarySpace := by
  change frame ∈ List.append (α := RuntimeCtx .quantum) [ctx]
    (List.append (α := RuntimeCtx .quantum)
      ((Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).visitedContexts path.2.1)
      (List.append (α := RuntimeCtx .quantum) [ctx]
        (List.append (α := RuntimeCtx .quantum)
          (Circuit.visitedContexts (ZReset.BankParallel.code
            (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) BitWord.model)
            path.2.2.2.1) [ctx]))) at present
  simp only [List.append_eq, List.mem_append, List.mem_singleton] at present
  rcases present with same | measured | same | reset | same
  · subst frame
    exact parent_space m ell width
  · rw [Circuit.measurementSequence_visitedContexts] at measured
    have same := (List.mem_replicate.mp measured).2
    subst frame
    exact parent_space m ell width
  · subst frame
    exact parent_space m ell width
  · have resident := ZReset.BankParallel.code_peakResidentSpace (services := .empty)
      (operations := BitWord.model)
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) path.2.2.2.1
    have auxiliary := ZReset.BankParallel.code_peakAuxiliarySpace (services := .empty)
      (operations := BitWord.model)
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) path.2.2.2.1
    rw [shortDLP_runtimeRound_systemCount m ell width sameWires] at resident auxiliary
    exact ⟨(Circuit.residentSpace_le_peak_of_visited _ path.2.2.2.1 frame reset).trans_eq resident,
      (Circuit.auxiliarySpace_le_peak_of_visited _ path.2.2.2.1 frame reset).trans_eq auxiliary⟩
  · subst frame
    exact parent_space m ell width

/-- The reset and reload stage reaches exactly the complete bank of classical scratch cells. -/
lemma shortDLP_runtimeResetReload_resident (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).peakResidentSpace path =
      resetSpace m ell width + ctx.residentSpace := by
  rcases path with ⟨resetPath, reloadPath⟩
  change ((ZReset.BankParallel.code
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
      BitWord.model).seq
    (Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := .empty)
      (RuntimePlacement.reloadProgram m ell width sameWires N))).peakResidentSpace
      (resetPath, reloadPath) = _
  rw [Circuit.peakResidentSpace_seq, ZReset.BankParallel.code_peakResidentSpace,
    Circuit.peakResidentSpace_unitary,
    shortDLP_runtimeRound_systemCount m ell width sameWires]
  exact SpacePool.max_eq_left (fun _ => Nat.le_add_left _ _)

/-- Those same simultaneous cells have auxiliary roles, with no extra quantum workspace. -/
lemma shortDLP_runtimeResetReload_auxiliary (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).peakAuxiliarySpace path =
      resetSpace m ell width + ctx.auxiliarySpace := by
  rcases path with ⟨resetPath, reloadPath⟩
  change ((ZReset.BankParallel.code
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
      BitWord.model).seq
    (Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := .empty)
      (RuntimePlacement.reloadProgram m ell width sameWires N))).peakAuxiliarySpace
      (resetPath, reloadPath) = _
  rw [Circuit.peakAuxiliarySpace_seq, ZReset.BankParallel.code_peakAuxiliarySpace,
    Circuit.peakAuxiliarySpace_unitary,
    shortDLP_runtimeRound_systemCount m ell width sameWires]
  exact SpacePool.max_eq_left (fun _ => Nat.le_add_left _ _)

/-- Resident peak includes the original bank, outputs and complete simultaneous reset scratch. -/
lemma shortDLP_runtimeRound_resident_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).peakResidentSpace path ≤
      resetSpace m ell width + ctx.residentSpace :=
  Circuit.peakResidentSpace_le_of_visited _ path _
    (fun frame present =>
      (visited_spaces m ell width sameWires parameter N generator target cells result
        path frame present).1)

/-- Auxiliary peak uses the same actual entries with their unchanged declared roles. -/
lemma shortDLP_runtimeRound_auxiliary_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).peakAuxiliarySpace path ≤
      resetSpace m ell width + ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_le_of_visited _ path _
    (fun frame present =>
      (visited_spaces m ell width sameWires parameter N generator target cells result
        path frame present).2)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
