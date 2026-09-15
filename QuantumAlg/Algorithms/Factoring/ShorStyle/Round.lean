/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Placement
import all QuantumAlg.Primitives.ZReset.Bank.Scope
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# One actual Shor member on the reusable owned bank

The retained sampler parameter selects the compiled modular-power member by
an actual classical read. The original phase wires are Z measured into real
finite cells and the charged packing instruction writes their ordered bits.
The existing bank is then reset through measurements and corrections and
reloaded by the shared constant-X sequence. No quantum preparation occurs in
this round. All classical results remain in the complete live manifest.

The surrounding sampler and repetition supply the real cells and the owned
bank. The structural wire equality describes placement; it does not certify
a quantum state or supply a probability distribution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- The measured positions are exactly the original ordered phase positions. -/
def phaseWire (index : Fin (phaseBits N)) : Fin ctx.systemCount :=
  NativePlacement.wireEquiv N sameWires
    ((OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).logical_idx index)

/-- Actual phase positions have dimension two after the complete bank correspondence. -/
theorem phaseWire_dimension (index : Fin (phaseBits N)) :
    (ctx.quantumLayout.wire (phaseWire N sameWires index)).dimension = 2 :=
  NativePlacement.qubits N sameWires _

/-- One real source phase position writes its own actual finite register. -/
def readout (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (index : Fin (phaseBits N)) : ZReadout ctx where
  wire := phaseWire N sameWires index
  output := by
    rw [phaseWire_dimension]
    exact cells index

/-- The physical Z instructions retain the original big-endian phase outcome order. -/
def readouts (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2)) : List (ZReadout ctx) :=
  List.ofFn (readout N sameWires cells)

/-- The closed packing operation reads those same cells into the retained phase result. -/
def packing (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N))) :
    ClassicalOp (.fixedVector (phaseBits N) (.finite 2)) (.bits (phaseBits N)) ctx ctx :=
  .packFiniteBits (phaseBits N) ctx
    (.fixedVector fun index => .storage (cells index).toCStorageRef) result

/-- A runtime branch reads the complete actual sampler parameter to select its native member. -/
def selected (parameter : CInputRef ctx (ParameterShape (modulusBits N))) : Circuit ctx ctx :=
  .branch parameter (fun value =>
    .unitary (NativePlacement.memberProgram N sameWires value)
      (NativePlacement.member_physicalIdx N sameWires value))

/-- Real reset and constant-X reload act on the same bank without allocating another system. -/
def resetReload : Circuit ctx ctx :=
  .seq (ZReset.BankScope.code (NativePlacement.qubits N sameWires))
    (.unitary (NativePlacement.reloadProgram N sameWires)
      (NativePlacement.reload_physicalIdx N sameWires))

/-- Every member has its actual quantum execution, stored measurement result and bank reuse. -/
def code (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N))) : Circuit ctx ctx :=
  .seq (selected N sameWires parameter)
    (.seq (Circuit.measurementSequence (readouts N sameWires cells))
      (.seq (.classical (packing N cells result)) (resetReload N sameWires)))

/-- Complete output reads the real packed phase and keeps the entire original live context. -/
def run (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N))) :
    AlgorithmRun ctx ctx (.bits (phaseBits N)) where
  code := code N sameWires parameter cells result
  output := Output.all ctx (.read (.storage result.toCStorageRef))

theorem readouts_length (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2)) :
    (readouts N sameWires cells).length = phaseBits N := List.length_ofFn

theorem readouts_qubits (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (item : ZReadout ctx) (present : item ∈ readouts N sameWires cells) :
    (ctx.quantumLayout.wire item.wire).dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact phaseWire_dimension N sameWires index

/-- Reset's classical scratch is lexical; every incoming live key survives in Output. -/
theorem output_listing (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N))) :
    (run N sameWires parameter cells result).output.listing = ctx.keys := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
