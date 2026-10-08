/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Base
import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import Mathlib.Tactic.Ring

/-!
# Reuse the one dirty bit across the two recursive HRS calls

Each child circuit acts on its own word and the same final dirty bit. Its
sibling word is an untouched tensor factor [HRS16, paper.tex:232-260]. The
typed prefix and middle constructors place the original construction on those
existing fields; no logical basis permutation or compatibility circuit is
introduced.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

private theorem lowChildWidth (low high : Nat) :
    (BinaryLabelEncoding.finIdentity high).width + (oneDirtyEncoding low).width =
      (bridgeEncoding low high).width := by
  change high + (low + 1) = high + low + 1
  omega

/-- Insert the inactive high word before the low child. -/
def placeLowChild (low high : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding low).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (bridgeEncoding low high).width).toQuantum :=
  UnitaryCircuit.castCanonicalQubitWidth (lowChildWidth low high)
    (UnitaryCircuit.onCanonicalBinarySuffix
      (BinaryLabelEncoding.finIdentity high).width program)

private theorem lowChildCastIndex_encode (low high : Nat)
    (lowWord : Fin (2 ^ low)) (highWord : Fin (2 ^ high)) (dirty : Bool) :
    UnitaryCircuit.castQubitWidthIndex
        (lowChildWidth low high)
        ((BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity high)
          (oneDirtyEncoding low)).encode (highWord, (lowWord, dirty))) =
      (bridgeEncoding low high).encode ((lowWord, highWord), dirty) := by
  apply Fin.ext
  change (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * lowWord.val + 2 ^ (low + 1) * highWord.val =
    (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * (lowWord.val + 2 ^ low * highWord.val)
  simp only [pow_add, pow_one]
  ring

/-- The low recursive call preserves the high word and restores the shared dirty bit. -/
theorem hrsPlaceLowChild_realizes (low high : Nat) (constant : Fin (2 ^ low))
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding low).width).toQuantum)
    (h : UnitaryCircuit.Realizes (oneDirtyEncoding low) program (oneDirtyOutput constant)) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (placeLowChild low high program)
      (fun state => ((addWord constant state.1.1, state.1.2), state.2)) where
  apply_encoded_ket := by
    rintro ⟨⟨lowWord, highWord⟩, dirty⟩
    have run := (UnitaryCircuit.Realizes.onBinarySuffix
      (left := BinaryLabelEncoding.finIdentity high) h).apply_encoded_ket
        (highWord, (lowWord, dirty))
    let sourceInput := NormalizedVector.ket
        ((QubitLayout.canonical
          ((BinaryLabelEncoding.finIdentity high).width +
            (oneDirtyEncoding low).width)).basisEquiv.symm
          ((BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity high)
            (oneDirtyEncoding low)).encode (highWord, (lowWord, dirty))))
    let sourceOutput := NormalizedVector.ket
        ((QubitLayout.canonical
          ((BinaryLabelEncoding.finIdentity high).width +
            (oneDirtyEncoding low).width)).basisEquiv.symm
          ((BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity high)
            (oneDirtyEncoding low)).encode
              (highWord, (addWord constant lowWord, dirty))))
    have inputCast : lowChildWidth low high ▸ sourceInput =
        NormalizedVector.ket
          ((QubitLayout.canonical (bridgeEncoding low high).width).basisEquiv.symm
            ((bridgeEncoding low high).encode ((lowWord, highWord), dirty))) := by
      dsimp only [sourceInput]
      exact (UnitaryCircuit.castCanonicalQubitWidth_ket
        (lowChildWidth low high)
        ((BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity high)
          (oneDirtyEncoding low)).encode (highWord, (lowWord, dirty)))).trans
          (congrArg (fun index => NormalizedVector.ket
            ((QubitLayout.canonical (bridgeEncoding low high).width).basisEquiv.symm
              index)) (lowChildCastIndex_encode low high lowWord highWord dirty))
    have outputCast : lowChildWidth low high ▸ sourceOutput =
        NormalizedVector.ket
          ((QubitLayout.canonical (bridgeEncoding low high).width).basisEquiv.symm
            ((bridgeEncoding low high).encode
              ((addWord constant lowWord, highWord), dirty))) := by
      dsimp only [sourceOutput]
      exact (UnitaryCircuit.castCanonicalQubitWidth_ket
        (lowChildWidth low high)
        ((BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity high)
          (oneDirtyEncoding low)).encode
            (highWord, (addWord constant lowWord, dirty)))).trans
          (congrArg (fun index => NormalizedVector.ket
            ((QubitLayout.canonical (bridgeEncoding low high).width).basisEquiv.symm
              index))
            (lowChildCastIndex_encode low high
              (addWord constant lowWord) highWord dirty))
    calc
      _ = (placeLowChild low high program).applyNormalized
          (lowChildWidth low high ▸ sourceInput) :=
        congrArg (placeLowChild low high program).applyNormalized inputCast.symm
      _ = lowChildWidth low high ▸
          (UnitaryCircuit.onCanonicalBinarySuffix
            (BinaryLabelEncoding.finIdentity high).width program).applyNormalized
              sourceInput :=
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized
          (lowChildWidth low high)
          (UnitaryCircuit.onCanonicalBinarySuffix
            (BinaryLabelEncoding.finIdentity high).width program) sourceInput
      _ = lowChildWidth low high ▸ sourceOutput := congrArg
        (fun state => lowChildWidth low high ▸ state)
        (show (UnitaryCircuit.onCanonicalBinarySuffix
            (BinaryLabelEncoding.finIdentity high).width program).applyNormalized
              sourceInput = sourceOutput by
          simpa only [sourceInput, sourceOutput, oneDirtyOutput] using run)
      _ = _ := outputCast

/-- Adding the inactive sibling changes neither the native ledger nor the evaluated depth. -/
theorem hrsPlaceLowChild_resources (low high : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding low).width).toQuantum)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (placeLowChild low high program).eventCost = program.eventCost ∧
      (placeLowChild low high program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign := by
  constructor
  · exact (UnitaryCircuit.castCanonicalQubitWidth_eventCost (lowChildWidth low high)
      (UnitaryCircuit.onCanonicalBinarySuffix
        (BinaryLabelEncoding.finIdentity high).width program)).trans
          (UnitaryCircuit.onCanonicalBinarySuffix_eventCost
            (BinaryLabelEncoding.finIdentity high).width program)
  · exact (UnitaryCircuit.castCanonicalQubitWidth_evaluatedEventDepth
      (lowChildWidth low high)
      (UnitaryCircuit.onCanonicalBinarySuffix
        (BinaryLabelEncoding.finIdentity high).width program) assign).trans
          (UnitaryCircuit.onCanonicalBinarySuffix_evaluatedEventDepth
            (BinaryLabelEncoding.finIdentity high).width assign program)

/-- Run the high child around the untouched low word. -/
def placeHighChild (low high : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding high).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (bridgeEncoding low high).width).toQuantum :=
  UnitaryCircuit.onBinaryMiddle low program

/-- The high recursive call preserves the low word and restores the shared dirty bit. -/
theorem hrsPlaceHighChild_realizes (low high : Nat) (constant : Fin (2 ^ high))
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding high).width).toQuantum)
    (h : UnitaryCircuit.Realizes (oneDirtyEncoding high) program (oneDirtyOutput constant)) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (placeHighChild low high program)
      (fun state => ((state.1.1, addWord constant state.1.2), state.2)) := by
  have placed := UnitaryCircuit.Realizes.onBinaryMiddle
    (middle := BinaryLabelEncoding.finIdentity low) h
  have relabeled := UnitaryCircuit.Realizes.relabel (bridgeGrouping low high) placed
  apply relabeled.congrStep
  rintro ⟨⟨lowWord, highWord⟩, dirty⟩
  rfl

/-- Middle placement preserves the child's actual native ledger and evaluated depth. -/
theorem hrsPlaceHighChild_resources (low high : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding high).width).toQuantum)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (placeHighChild low high program).eventCost = program.eventCost ∧
      (placeHighChild low high program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign := by
  exact ⟨UnitaryCircuit.unitaryCircuit_onBinaryMiddle_eventCost low program,
    UnitaryCircuit.unitaryCircuit_onBinaryMiddle_evaluatedEventDepth low assign program⟩

end

end QuantumAlg.MAU.Addition.HRS
