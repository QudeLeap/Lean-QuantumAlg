/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement
import all QuantumAlg.Primitives.ZReset.Bank.Scope
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# One actual short-DLP round on the same owned quantum bank

The first instruction reads an existing finite classical parameter and selects
the actual compiled two-exponentiation circuit. The original exponent wires
are Z measured into actual existing finite cells and a charged pack instruction
writes their bits to an existing result cell. Scoped reset then measures and
corrects the same whole bank, and the literal X reload restores its source seed.

The round neither prepares quantum systems nor retains new result cells.
Only the reset's real one-bit lexical scratch is temporary. Its complete Output
retains the bank, parameter, measurement cells and packed result. Repetition
must provide distinct parameter/result storage and record each packed outcome
through actual classical instructions before the next round overwrites it.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- The original two exponent registers determine the ordered result width. -/
abbrev resultBits : Nat := firstBits (registerParameters m ell width) + ell

/-- Original measured logical positions, transported through the actual bank's wire records. -/
def measuredWire (index : Fin (resultBits m ell width)) : Fin ctx.systemCount :=
  RuntimePlacement.wireEquiv m ell width sameWires
    ((ShortDLP.measurement (registerParameters m ell width)).logical_idx index)

/-- Each measured position is the same actual dimension-two source wire. -/
theorem shortDLP_runtimeMeasuredWire_dimension (index : Fin (resultBits m ell width)) :
    (ctx.quantumLayout.wire (measuredWire m ell width sameWires index)).dimension = 2 :=
  RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires _

/-- A source measurement writes directly to its designated existing finite register. -/
def readout (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (index : Fin (resultBits m ell width)) : ZReadout ctx where
  wire := measuredWire m ell width sameWires index
  output := by
    rw [shortDLP_runtimeMeasuredWire_dimension]
    exact cells index

/-- The actual single-wire Z instructions preserve the original source outcome order. -/
def readouts (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2)) :
    List (ZReadout ctx) := List.ofFn (readout m ell width sameWires cells)

/-- The packing instruction reads precisely those actual per-wire finite result cells. -/
def packing (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width))) :
    ClassicalOp (.fixedVector (resultBits m ell width) (.finite 2))
      (.bits (resultBits m ell width)) ctx ctx :=
  .packFiniteBits (resultBits m ell width) ctx
    (.fixedVector fun index => .storage (cells index).toCStorageRef) result

/-- Runtime dispatch reads the real retained parameter before executing its actual gate member. -/
def selected {shape : CShape} (parameter : CInputRef ctx shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ) : Circuit ctx ctx :=
  .branch parameter (fun value =>
    .unitary (RuntimePlacement.memberProgram m ell width sameWires N
      (generator value) (target value))
      (RuntimePlacement.shortDLP_runtimeMember_physicalIdx m ell width sameWires N
        (generator value) (target value)))

/-- Reset and actual X reload return the same bank to its original source seed. -/
def resetReload (N : Nat) : Circuit ctx ctx :=
  .seq (ZReset.BankScope.code
    (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires))
    (.unitary (RuntimePlacement.reloadProgram m ell width sameWires N)
      (RuntimePlacement.shortDLP_runtimeReload_physicalIdx m ell width sameWires N))

/-- One actual parameter-selected member, measured and packed result, and reset/reload sequence. -/
def code {shape : CShape} (parameter : CInputRef ctx shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width))) : Circuit ctx ctx :=
  .seq (selected m ell width sameWires parameter N generator target)
    (.seq (Circuit.measurementSequence (readouts m ell width sameWires cells))
      (.seq (.classical (packing m ell width cells result))
        (resetReload m ell width sameWires N)))

/-- The complete result manifest reads the packed cell and retains every actual runtime entry. -/
def run {shape : CShape} (parameter : CInputRef ctx shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width))) :
    AlgorithmRun ctx ctx (.bits (resultBits m ell width)) where
  code := code m ell width sameWires parameter N generator target cells result
  output := Output.all ctx (.read (.storage result.toCStorageRef))

/-- The constructed Z list has exactly the original source measurement width. -/
theorem shortDLP_runtimeReadouts_length
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2)) :
    (readouts m ell width sameWires cells).length = resultBits m ell width :=
  List.length_ofFn

/-- Every actual Z instruction uses the dimension-two native coordinate. -/
theorem shortDLP_runtimeReadouts_qubits
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (item : ZReadout ctx) (present : item ∈ readouts m ell width sameWires cells) :
    (ctx.quantumLayout.wire item.wire).dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact shortDLP_runtimeMeasuredWire_dimension m ell width sameWires index

/-- Complete output preserves the same live keys after the real round and scratch scope. -/
theorem shortDLP_runtimeRound_output_listing {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width))) :
    (run m ell width sameWires parameter N generator target cells result).output.listing =
      ctx.keys := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
