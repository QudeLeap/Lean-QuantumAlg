/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.Native.EEAFrame.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.Controlled
import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection.Controlled
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Core.Execution.QubitReadouts

/-!
# Actual native active arithmetic and inactive preservation

Every coherent control expands an actual instruction list inside the original
complete frame. The supplied final control and all borrowed dirty coordinates
are retained. Phase correction uses actual H-CNOT-H gates and literal inverse
product lists; no arbitrary-circuit control or event relabeling is used.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA ProductPlacement EncodedBit GateSpec

/-- The typed complete-frame native circuit carrier. -/
abbrev NativeCircuit (width : Nat) :=
  UnitaryCircuit AlgorithmGate.model .empty (nativeLayout width).toQuantum

/-- Actual native control of a reversible source word, with arbitrary borrowed bits restored. -/
def controlled (width : Nat) (active : Bool) (source : List (GateSpec (frameEncoding width))) :
    NativeCircuit width :=
  NativeFrameControl.program width active source (nativeLayout width)

/-- Exact ordered native expansion, including two physical X gates for negative selection. -/
lemma controlled_trace (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) :
    (controlled width active source).eventTrace =
      (NativeFrameControl.gates width active source).map (event .empty) :=
  NativeFrameControl.nativeFrameControl_trace width active source (nativeLayout width)

/-- The complete native coordinate pool comes from the actual expanded instruction list. -/
lemma controlled_cost (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) :
    (controlled width active source).eventCost =
      ResourcePool.ofList ((NativeFrameControl.gates width active source).map (event .empty)) :=
  programList_eventCost (nativeLayout width) .empty _

/-- Extend a real unconditional native word by identity on the unchanged final control. -/
def uncontrolled (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    NativeCircuit width :=
  UnitaryCircuit.onBinaryPrefix 1 body

/-- Actual physical prefix placement preserves every original event and its order. -/
lemma uncontrolled_trace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    (uncontrolled width body).eventTrace = body.eventTrace := by
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace 1 body

/-- Literal XOR copies the numerator into the arbitrary original accumulator. -/
def copyGates (width : Nat) : List (GateSpec (frameEncoding width)) :=
  Word.xorIntoGates (FramePorts.numerator width) (FramePorts.accumulator width)
    (fun index => (FramePorts.accumulator_numerator_ne width index index).symm)

/-- The actual complete-frame CNOT word used in the inactive sector. -/
def copy (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width) :=
  programList (QubitLayout.canonical _) .empty (copyGates width)

/-- Read the saved accumulator in the original measurement mask's little-endian order. -/
def inactiveWord (width : Nat) : Word (frameEncoding width) width :=
  ⟨fun index => (FramePorts.accumulator width).bit index.rev⟩

/-- The original uncontrolled phase member remains the mathematical inactive-block comparator. -/
def inactiveMask (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2))) :
    UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width) :=
  Word.PhaseCorrection.program (QubitLayout.canonical _) .empty
    (inactiveWord width) (QubitReadouts.mask value)

private def liftedInactiveWord (width : Nat) :
    Word (NativeFrameControl.encoding width) width :=
  ⟨fun index => BinaryLabelEncoding.prodLeftBit (frameEncoding width) BinaryLabelEncoding.bool
    ((inactiveWord width).bit index)⟩

private lemma inactive_separated (width : Nat) (index : Fin width) :
    (NativeFrameControl.control width).wire ≠ ((liftedInactiveWord width).bit index).wire :=
  prodRightBit_wire_ne_prodLeftBit_wire (frameEncoding width) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit ((inactiveWord width).bit index)

/-- Actual H-CNOT-H blocks cancel the inactive character while retaining the control. -/
def inactiveCorrection (width : Nat)
    (value : CShape.Value (.fixedVector width (.finite 2))) : NativeCircuit width :=
  Word.PhaseCorrection.Controlled.program (nativeLayout width) .empty
    (NativeFrameControl.control width) (liftedInactiveWord width) (inactive_separated width)
    false (QubitReadouts.mask value)

/-- Both coherent sectors execute their own actual product or XOR-save instruction lists. -/
def save (modulus : Nat) : NativeCircuit modulus.size :=
  (NativeProductFrame.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus)
    (nativeLayout modulus.size)).seq (controlled modulus.size false (copyGates modulus.size))

/-- Actual forward EEA is selected by the original quantum control with exact phase. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) : NativeCircuit modulus.size :=
  NativeEEAFrame.Controlled.forward modulus prime true (nativeLayout modulus.size)

/-- The literal reversed backward word supplies the reused controlled forward. -/
def reusedForward (modulus : Nat) (prime : Nat.Prime modulus) : NativeCircuit modulus.size :=
  NativeEEAFrame.Controlled.reusedForward modulus prime true (nativeLayout modulus.size)

/-- The same FullPlacement and arbitrary-dirty restoration select the complete EEA adjoint. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) : NativeCircuit modulus.size :=
  NativeEEAFrame.Controlled.backward modulus prime true (nativeLayout modulus.size)

/-- Both sectors use the same actual stored vector and the appropriate literal phase correction. -/
def correction (modulus : Nat)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) : NativeCircuit modulus.size :=
  (ReusedProduct.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus) true
    (QubitReadouts.mask value) (nativeLayout modulus.size)).seq
      (inactiveCorrection modulus.size value)

/-- The actual final three-CNOT exchange retains the original final quantum control. -/
def swap (width : Nat) : NativeCircuit width :=
  uncontrolled width (FrameSwap.program width)

/-- The actual native prefix before the unconditional H/Z/store/reset measurement sequence. -/
def beforeReset (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus) :
    NativeCircuit modulus.size :=
  match operation with
  | .division => (forward modulus prime).seq (save modulus)
  | .multiplication => save modulus

/-- The stored measurement mask selects this exact complete native suffix. -/
def suffix (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) : NativeCircuit modulus.size :=
  match operation with
  | .division => (backward modulus prime).seq ((correction modulus value).seq (swap modulus.size))
  | .multiplication => (reusedForward modulus prime).seq
      ((correction modulus value).seq ((backward modulus prime).seq (swap modulus.size)))

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
