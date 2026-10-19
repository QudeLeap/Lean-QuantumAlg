/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.Projector.Zero.SourceWork
import all QuantumAlg.Components.Encoded.BitGates.ZeroReadout
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Util.FinPow

/-!
# Original tensor labels of the native zero-projector flip

The native negative controls read exactly the block-ancilla prefix. The phase
flip preserves both that prefix and every original signal coordinate, including
the actual signal position temporarily used as arbitrary work.
-/

namespace QuantumAlg.ZeroProjector.SourceWork
noncomputable section

/-- The original phase, block-ancilla and signal labels in their specified tensor order. -/
def triple {m n : Nat} (phase : Fin 2) (ancilla : Fin (2 ^ m)) (signal : Fin (2 ^ n)) :
    Fin (2 ^ (1 + (m + n))) := prodEquiv (phase, prodEquiv (ancilla, signal))

/-- A source control reads its original block-ancilla bit and no signal bit. -/
lemma sourceBit_get_triple {m n : Nat} (phase : Fin 2)
    (ancilla : Fin (2 ^ m)) (signal : Fin (2 ^ n)) (index : Fin m) :
    (sourceBit m n index).get (triple phase ancilla signal) =
      (BinaryLabelEncoding.finIdentityBit m index).get ancilla := by
  change (prodEquiv (m := 1) (n := m + n) (phase, prodEquiv (ancilla, signal))).val.testBit
      (WireAddress.bitIndex (⟨1 + index.val, by omega⟩ : Fin (1 + (m + n)))).val =
    ancilla.val.testBit (WireAddress.bitIndex index).val
  have position :
      (WireAddress.bitIndex (⟨1 + index.val, by omega⟩ : Fin (1 + (m + n)))).val =
        n + (WireAddress.bitIndex index).val := by
    dsimp [WireAddress.bitIndex]
    omega
  rw [position]
  exact (prodEquiv_testBit_right (m := 1) phase (prodEquiv (ancilla, signal))
    (⟨n + (WireAddress.bitIndex index).val, by
      have bounded := (WireAddress.bitIndex index).isLt
      omega⟩ : Fin (m + n))).trans
    (prodEquiv_testBit_left ancilla signal (WireAddress.bitIndex index))

/-- All native negative controls select precisely the original zero block. -/
lemma source_zero_iff {m n : Nat} (phase : Fin 2)
    (ancilla : Fin (2 ^ m)) (signal : Fin (2 ^ n)) :
    (∀ index, (sourceBit m n index).get (triple phase ancilla signal) = false) ↔
      ancilla = 0 := by
  simp only [sourceBit_get_triple]
  exact BinaryLabelEncoding.finIdentity_all_zero_iff m ancilla

/-- The actual output lens flips only the leading phase factor of the tensor label. -/
lemma outputBit_flip_triple {m n : Nat} (phase : Fin 2)
    (ancilla : Fin (2 ^ m)) (signal : Fin (2 ^ n)) :
    (outputBit m n).flip (triple phase ancilla signal) =
      triple (WireAddress.flipBit (0 : Fin 1) phase) ancilla signal := by
  change WireAddress.flipBit (0 : Fin (1 + (m + n)))
    (prodEquiv (phase, prodEquiv (ancilla, signal))) = _
  exact (BinaryLabelEncoding.prodEquiv_flip_left (BinaryLabelEncoding.finIdentity 1)
    (BinaryLabelEncoding.finIdentity (m + n)) (0 : Fin 1) phase
    (prodEquiv (ancilla, signal))).symm

/-- Full normalized-basis action of the real circuit, including restoration of arbitrary work. -/
lemma program_apply_triple (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel)
    (phase : Fin 2) (ancilla : Fin (2 ^ m)) (signal : Fin (2 ^ n))
      (environment : oracles.Interpretation) :
    ((program m n positive physical oracles).applyNormalized environment)
      (NormalizedVector.ket (physical.basisEquiv.symm (triple phase ancilla signal))) =
      NormalizedVector.ket (physical.basisEquiv.symm
        (if ancilla = 0 then
          triple (WireAddress.flipBit (0 : Fin 1) phase) ancilla signal
        else triple phase ancilla signal)) := by
  have actual := (program_realizes m n positive physical oracles environment).apply_encoded_ket
    (triple phase ancilla signal)
  change ((program m n positive physical oracles).applyNormalized environment)
      (NormalizedVector.ket (physical.basisEquiv.symm (triple phase ancilla signal))) =
    NormalizedVector.ket (physical.basisEquiv.symm
      (if ∀ index, (sourceBit m n index).get (triple phase ancilla signal) = false then
        (outputBit m n).flip (triple phase ancilla signal)
      else triple phase ancilla signal)) at actual
  simpa only [source_zero_iff, outputBit_flip_triple] using actual

end
end QuantumAlg.ZeroProjector.SourceWork
