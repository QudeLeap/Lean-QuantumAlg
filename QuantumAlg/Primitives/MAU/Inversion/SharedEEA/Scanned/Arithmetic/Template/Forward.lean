/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Prefix

/-!
# Actual preparation and restoration of a forward streaming stage

A paid CNOT copies the existing root control into the clean conjunction
wire. The following actual traversal returns that same wire to zero at the
selected boundary. The root control, address and all prefix systems remain
in their original locations. Descending source stages can invert this
complete unitary construction rather than inventing a reverse instrument.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The original Ctrl prepares the actual conjunction wire by one charged native CNOT. -/
def startGate (width : Nat) : GateSpec (encoding width) :=
  .cnot (SelectionFrame.enable width) (conjunctionBit width)
    (source_conjunction_ne width (SharedEEA.controlBit width))

private lemma start_step (width : Nat) (state : Data width) :
    (startGate width).step state =
      if state.1.control then (conjunctionBit width).flip state else state := rfl

private lemma start_fields (width : Nat) (state : Data width) :
    ((startGate width).step state).1 = state.1 ∧
      ((startGate width).step state).2.1 = state.2.1 ∧
      ((startGate width).step state).2.2.1 = state.2.2.1 := by
  rw [start_step]
  split <;> exact ⟨rfl, rfl, rfl⟩

private lemma start_base (width : Nat) (state : Data width) :
    (flagEquiv width ((startGate width).step state)).1 = (flagEquiv width state).1 := by
  rw [start_step]
  split <;> rfl

private lemma start_flag (width : Nat) (state : Data width) :
    ((startGate width).step state).2.2.2 = (state.2.2.2 ^^ state.1.control) :=
  cnotStep_get_target (SelectionFrame.enable width) (conjunctionBit width) state

/-- The paid initial CNOT and the original native traversal form one actual unitary stage. -/
def forwardProgram (width : Nat) (stage : Stage) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  ((startGate width).program (QubitLayout.canonical _) .empty).seq (program width stage)

/-- A forward stage executes exactly its selected original prefix and restores the moving flag. -/
lemma forwardProgram_apply_prefix (width : Nat) (positive : 1 ≤ width) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (forwardProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode ((flagEquiv width).symm
          (if state.1.control then
            ThresholdStream.word (baseAction width stage) (state.2.1.toNat + 1)
              (flagEquiv width state).1
            else (flagEquiv width state).1, false)))) := by
  let started := (startGate width).step state
  have fields := start_fields width state
  have prepared : started.2.2.2 = started.1.control := by
    change ((startGate width).step state).2.2.2 =
      ((startGate width).step state).1.control
    rw [start_flag, fields.1, zero]
    simp
  have cleanStarted : started.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    fields.2.2.trans clean
  have withinStarted : started.2.1.toNat < width + 3 := by
    change ((startGate width).step state).2.1.toNat < _
    rw [fields.2.1]
    exact within
  rw [forwardProgram, UnitaryCircuit.applyNormalized_seq]
  have preparation := (GateSpec.realizes (QubitLayout.canonical _) .empty
    (startGate width) environment).apply_encoded_ket state
  rw [preparation]
  have actual := program_apply_prefix width positive stage environment started
    cleanStarted prepared withinStarted
  dsimp only [started] at actual
  rw [start_base, fields.1, fields.2.1] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
