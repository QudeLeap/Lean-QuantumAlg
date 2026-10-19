/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Base
import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Split
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import Mathlib.Tactic.Ring

/-!
# Return the HRS recursive split to the original word interface

The bridge encoding keeps the original word's physical high/low bit order.
Joining therefore changes only the semantic view and the provably equal width;
it does not insert a gate, a query, or a zero-cost operator permutation.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

private lemma bridgeOneDirtyWidth (width : Nat) :
    (bridgeEncoding (lowWidth width) (highWidth width)).width =
      (oneDirtyEncoding width).width := by
  change highWidth width + lowWidth width + 1 = width + 1
  have split := hrsSplit_width_sum width
  omega

/-- Keep the actual construction and expose the equal unsplit carrier width. -/
def joinProgram (width : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum :=
  UnitaryCircuit.castCanonicalQubitWidth (bridgeOneDirtyWidth width) program

private lemma joinCastIndex_encode (width : Nat)
    (words : Fin (2 ^ lowWidth width) × Fin (2 ^ highWidth width))
    (dirty : Bool) :
    UnitaryCircuit.castQubitWidthIndex (bridgeOneDirtyWidth width)
        ((bridgeEncoding (lowWidth width) (highWidth width)).encode (words, dirty)) =
      (oneDirtyEncoding width).encode (joinWord width words, dirty) := by
  apply Fin.ext
  change (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * (words.1.val + 2 ^ lowWidth width * words.2.val) =
    (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * (joinWord width words).val
  rw [hrsJoin_value]

/-- Exact action transported through the semantic split and join views. -/
lemma hrsJoinProgram_realizes (width : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).toQuantum)
    (step : BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width) →
      BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width))
    (h : UnitaryCircuit.Realizes (bridgeEncoding (lowWidth width) (highWidth width))
      program environment step) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width) (joinProgram width program) environment
      (fun state =>
        let output := step ((splitWord width) state.1, state.2)
        (joinWord width output.1, output.2)) where
  apply_encoded_ket := by
    rintro ⟨input, dirty⟩
    have run := h.apply_encoded_ket ((splitWord width) input, dirty)
    let sourceInput := NormalizedVector.ket
      ((QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).basisEquiv.symm
        ((bridgeEncoding (lowWidth width) (highWidth width)).encode
          ((splitWord width) input, dirty)))
    let output := step ((splitWord width) input, dirty)
    let sourceOutput := NormalizedVector.ket
      ((QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).basisEquiv.symm
        ((bridgeEncoding (lowWidth width) (highWidth width)).encode output))
    have inputCast : bridgeOneDirtyWidth width ▸ sourceInput =
        NormalizedVector.ket
          ((QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
            ((oneDirtyEncoding width).encode (input, dirty))) := by
      dsimp only [sourceInput]
      exact (UnitaryCircuit.castCanonicalQubitWidth_ket
        (bridgeOneDirtyWidth width)
        ((bridgeEncoding (lowWidth width) (highWidth width)).encode
          ((splitWord width) input, dirty))).trans
          (congrArg (fun index => NormalizedVector.ket
            ((QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
              index)) ((joinCastIndex_encode width ((splitWord width) input) dirty).trans
                (congrArg (fun joined => (oneDirtyEncoding width).encode (joined, dirty))
                  (hrsJoin_split width input))))
    have outputCast : bridgeOneDirtyWidth width ▸ sourceOutput =
        NormalizedVector.ket
          ((QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
            ((oneDirtyEncoding width).encode
              (joinWord width output.1, output.2))) := by
      dsimp only [sourceOutput]
      exact (UnitaryCircuit.castCanonicalQubitWidth_ket
        (bridgeOneDirtyWidth width)
        ((bridgeEncoding (lowWidth width) (highWidth width)).encode output)).trans
          (congrArg (fun index => NormalizedVector.ket
            ((QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
              index)) (joinCastIndex_encode width output.1 output.2))
    calc
      _ = (joinProgram width program).applyNormalized environment
          (bridgeOneDirtyWidth width ▸ sourceInput) :=
        congrArg ((joinProgram width program).applyNormalized environment) inputCast.symm
      _ = bridgeOneDirtyWidth width ▸ program.applyNormalized environment sourceInput :=
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized
          (bridgeOneDirtyWidth width) program sourceInput environment
      _ = bridgeOneDirtyWidth width ▸ sourceOutput := congrArg
        (fun state => bridgeOneDirtyWidth width ▸ state)
        (show program.applyNormalized environment sourceInput = sourceOutput by
          simpa only [sourceInput, sourceOutput, output] using run)
      _ = _ := outputCast

/-- Joining the semantic view retains the actual native ledger and depth. -/
lemma hrsJoinProgram_resources (width : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).toQuantum)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (joinProgram width program).eventCost = program.eventCost ∧
      (joinProgram width program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign := by
  exact ⟨UnitaryCircuit.castCanonicalQubitWidth_eventCost
      (bridgeOneDirtyWidth width) program,
    UnitaryCircuit.castCanonicalQubitWidth_evaluatedEventDepth
      (bridgeOneDirtyWidth width) program assign⟩

end

end QuantumAlg.MAU.Addition.HRS
