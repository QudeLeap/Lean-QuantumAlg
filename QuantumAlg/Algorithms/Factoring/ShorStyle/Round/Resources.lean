/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Placement.Resources

/-!
# Complete native events and depth of one actual same-bank Shor round

The stored sampler value selects a real compiled member. Every original phase
position is then measured and its finite result packed. Full-bank measurement
and correction precede the real constant-X reload on that same bank. These
last stages are included even after the useful phase result has been stored;
no state preparation replaces reset or hides its native operations.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Independent complete reset and reload allowance for the four-word physical bank. -/
def resetEnvelope (N : Nat) : ResourcePool .quantum :=
  ZReset.Bank.envelope (4 * modulusBits N) +
    ResourcePool.singleton (.gate (.builtin "x")) (4 * modulusBits N)

/-- Every actual quantum member, phase measurement, pack, reset and reload is counted. -/
def eventEnvelope (N : Nat) : ResourcePool .quantum :=
  NativeQuantum.eventBudget N +
    (phaseBits N • ResourcePool.singleton (Circuit.zEvent 2) +
      (ResourcePool.singleton
        (.classicalOperation (.nominalEncoding (.packFiniteBits (phaseBits N)))) +
        resetEnvelope N))

/-- Independent serial depth includes useful readout and the full mandatory bank reuse work. -/
def depthBound (N : Nat) : Nat :=
  NativeQuantum.depthBound N + phaseBits N + 1 + 12 * modulusBits N

include sameWires in
private theorem systemCount : ctx.systemCount = 4 * modulusBits N := by
  change ctx.quantumWires.length = _
  rw [sameWires, QuantumLayout.wires_length]
  exact NativeQuantum.totalQubits_eq_four_mul N

private theorem selected_pool_le (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (selected N sameWires parameter).Path) :
    (selected N sameWires parameter).resourcePool path ≤ NativeQuantum.eventBudget N := by
  rcases path with ⟨value, path⟩
  change ResourcePool.ofList (NativePlacement.memberProgram N sameWires value).eventTrace ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact NativePlacement.member_pool_le N sameWires value

private theorem measurement_pool (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (readouts N sameWires cells)).Path) :
    (Circuit.measurementSequence (readouts N sameWires cells)).resourcePool path =
      phaseBits N • ResourcePool.singleton (Circuit.zEvent 2) := by
  rw [Circuit.measurementSequence_qubit_resourcePool
    (readouts N sameWires cells) (readouts_qubits N sameWires cells), readouts_length]

/-- Full-bank reset and reload obey their independent complete native-coordinate allowance. -/
theorem resetReload_pool_le (path : (resetReload N sameWires).Path) :
    (resetReload N sameWires).resourcePool path ≤ resetEnvelope N := by
  have reset := ZReset.BankScope.zResetBankScope_resourcePool_le
    (NativePlacement.qubits N sameWires) path.1
  have budget := congrArg ZReset.Bank.envelope (systemCount N sameWires)
  change ResourcePool.ofList
    ((ZReset.BankScope.code (NativePlacement.qubits N sameWires)).eventTrace path.1 ++
      (NativePlacement.reloadProgram N sameWires).eventTrace) ≤ _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact add_le_add (reset.trans_eq budget) (NativePlacement.reload_pool_le N sameWires)

/-- The actual selected round path includes its complete native bank reuse suffix. -/
theorem code_pool_le (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    (path : (code N sameWires parameter cells result).Path) :
    (code N sameWires parameter cells result).resourcePool path ≤ eventEnvelope N := by
  change ResourcePool.ofList ((selected N sameWires parameter).eventTrace path.1 ++
    ((Circuit.measurementSequence (readouts N sameWires cells)).eventTrace path.2.1 ++
      ([(packing N cells result).event] ++ (resetReload N sameWires).eventTrace path.2.2.2))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (selected_pool_le N sameWires parameter path.1)
    (add_le_add (measurement_pool N sameWires cells path.2.1).le
      (add_le_add le_rfl (resetReload_pool_le N sameWires path.2.2.2)))

private theorem selected_unitDepth_le
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (selected N sameWires parameter).Path) :
    (selected N sameWires parameter).depth (fun _ => 1) path ≤ NativeQuantum.depthBound N := by
  rcases path with ⟨value, path⟩
  exact NativePlacement.member_unitDepth_le N sameWires value

/-- Every real reset pair and sequential X load is counted in the bank reuse duration. -/
theorem resetReload_unitDepth_le (path : (resetReload N sameWires).Path) :
    (resetReload N sameWires).depth (fun _ => 1) path ≤ 12 * modulusBits N := by
  have reset := (ZReset.BankScope.zResetBankScope_unitDepth
    (NativePlacement.qubits N sameWires) path.1).trans
      (congrArg (fun width => 2 * width) (systemCount N sameWires))
  have loaded := NativePlacement.reload_unitDepth_le N sameWires
  change (ZReset.BankScope.code (NativePlacement.qubits N sameWires)).depth (fun _ => 1) path.1 +
    (NativePlacement.reloadProgram N sameWires).evaluatedEventDepth (fun _ => 1) ≤ _
  omega

/-- The complete actual round has its independently bounded native unit duration. -/
theorem code_unitDepth_le (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    (path : (code N sameWires parameter cells result).Path) :
    (code N sameWires parameter cells result).depth (fun _ => 1) path ≤ depthBound N := by
  have selected := selected_unitDepth_le N sameWires parameter path.1
  have measured := (Circuit.measurementSequence_unitDepth
    (readouts N sameWires cells) path.2.1).trans (readouts_length N sameWires cells)
  have reused := resetReload_unitDepth_le N sameWires path.2.2.2
  change (NativeRound.selected N sameWires parameter).depth (fun _ => 1) path.1 +
    ((Circuit.measurementSequence (readouts N sameWires cells)).depth (fun _ => 1) path.2.1 +
      (1 + (resetReload N sameWires).depth (fun _ => 1) path.2.2.2)) ≤ _
  unfold depthBound
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
