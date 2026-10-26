/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Born
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model

/-!
# Pure nearest output coordinates on original recoverable Fourier events

The complete original big-endian raw frequencies yield the exact nearest
candidate word and both success flags. These output-cell identities require
no sampler or candidate-checker execution.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open QuantumAlg.Execution
open PrimeFieldShortWeierstrass FiniteCyclicDLP ECDLP.Measured
open FiniteCyclicDLP.Canonical.Probability (SecretInput residueIndex)
open ClassicalAlgorithms.Modular
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Decoding any physical raw pair returns its complete packed integer without a source cutoff. -/
lemma decodedTerminal_rawExponentInput_pair (problem : KnownOrderProblem E.GroupPoint)
    (raw : Branch (orderWidth problem)) :
    decodedTerminal (rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw)) =
      (prodEquiv raw).val := by
  rw [rawExponentInput_pair]
  change ClassicalAlgorithms.TerminalDecode.decodeNat
    { order := .bigEndian,
      bits := Canonical.BornBridge.measurementOutcome problem (prodEquiv raw) } = _
  rw [ClassicalAlgorithms.TerminalDecode.decodeNat_bigEndian]
  exact congrArg Fin.val (Canonical.BornBridge.fullRegisterIndex_measurementOutcome problem _)

lemma leftRaw_rawExponentInput_pair (problem : KnownOrderProblem E.GroupPoint)
    (raw : Branch (orderWidth problem)) :
    leftRaw (rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw)) =
        raw.1.val := by
  rw [leftRaw, decodedTerminal_rawExponentInput_pair]
  simpa only [Equiv.symm_apply_apply] using (prodEquiv_symm_fst_val (prodEquiv raw)).symm

lemma rightRaw_rawExponentInput_pair (problem : KnownOrderProblem E.GroupPoint)
    (raw : Branch (orderWidth problem)) :
    rightRaw (rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw)) =
        raw.2.val := by
  rw [rightRaw, decodedTerminal_rawExponentInput_pair]
  simpa only [Equiv.symm_apply_apply] using (prodEquiv_symm_snd_val (prodEquiv raw)).symm

/-- Every emitted recoverable raw-bit mask gives the exact nearest output cells. -/
lemma nearest_outputCells_recoverableEvent (problem : KnownOrderProblem E.GroupPoint)
    (prime : problem.order.Prime) (input : SecretInput problem)
    (bits : Fin (2 * orderWidth problem) → Bool)
    (accepted : recoverableExponentEvent problem input bits = true)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order) :
    Nearest.outputCellsInput spec (rawExponentInput problem bits) =
      .product (.bit true)
        (.product (CShape.wordOfNat (orderWidth problem) input.secret.val) (.bit true)) := by
  obtain ⟨raw, window, rfl⟩ := of_decide_eq_true accepted
  obtain ⟨output, recovered, candidate, verified⟩ :=
    recoverableWindow_nearest_output_recovers problem prime input spec sameOrder raw window
  have outputSome : Nearest.outputOfNormalized spec
      (Nearest.normalizeInput spec (rawExponentInput problem
        (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw))) =
        some output := by
    change Nearest.outputOf spec (leftRaw (rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw)))
      (rightRaw (rawExponentInput problem
        (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) raw))) =
        some output
    rw [leftRaw_rawExponentInput_pair, rightRaw_rawExponentInput_pair]
    exact recovered
  rw [Nearest.outputCellsInput, Nearest.outputCellsNormalized_of_some spec _ output outputSome,
    candidate, verified]

end

end QuantumAlg.EllipticCurve.FullRange
