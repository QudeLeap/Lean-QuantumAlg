/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Probability.Failure
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Validity
import all QuantumAlg.Util.PMF.TwoOutput

/-!
# The complete actual P-256 run returns the original secret with probability at least 124/125

The actual checked output support eliminates every wrong scalar. The actual
three-round failure bound then applies to the same normalized output distribution.
No independence assumption, caller preparation certificate, restricted reference,
or secret-dependent executable run is introduced.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution PrimeFieldShortWeierstrass
open FiniteCyclicDLP.Canonical.Probability (SecretInput)

attribute [local irreducible] Circuit.execute Circuit.pathFintype

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- A different scalar has zero probability in the actual complete paid output law. -/
lemma paidRun_wrong_probability_zero (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState)
    (value : (CShape.unsignedWord 260).Value)
    (different : value ≠ CShape.wordOfNat 260 input.secret.val) :
    (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).outputDistribution environment supplied
        (.optionSome value) = 0 := by
  by_contra nonzero
  let actual := paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
    (publicBaseRef I) (publicTargetRef I)
  have supported : CShape.Value.optionSome value ∈
      (actual.outputDistribution environment supplied).support :=
    (PMF.mem_support_iff _ _).mpr nonzero
  obtain ⟨record, present, output⟩ :=
    (PMF.mem_support_map_iff actual.result
      (actual.executionDistribution environment supplied) (.optionSome value)).mp supported
  have positive := (ExecutionState.mem_support_toPMF_iff
    (actual.execute environment Reference supplied.state)
    (actual.execute_normalized environment supplied) record).mp present
  exact different
    (paidRun_supported_secret I environment input supplied valid record positive value output)

/-- Three actual checked rounds return the original bounded secret
with probability at least 124/125. -/
lemma paidRun_secret_probability_ge (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState) :
    ENNReal.ofReal ((124 : ℝ) / 125) ≤
      (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
        (publicBaseRef I) (publicTargetRef I)).outputDistribution environment supplied
          (.optionSome (CShape.wordOfNat 260 input.secret.val)) := by
  let distribution := (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
    (publicBaseRef I) (publicTargetRef I)).outputDistribution environment supplied
  let wanted := CShape.wordOfNat 260 input.secret.val
  have zero : ∀ value, value ≠ .optionNone → value ≠ .optionSome wanted →
      distribution value = 0 := by
    intro value absent different
    cases value with
    | optionNone => exact False.elim (absent rfl)
    | optionSome value =>
        exact paidRun_wrong_probability_zero I environment input supplied valid value
          (fun same => different (congrArg CShape.Value.optionSome same))
  have lower := QuantumAlg.PMF.success_ge_of_failure_le distribution .optionNone
    (.optionSome wanted) (by intro same; cases same) zero
    (ENNReal.ofReal ((1 : ℝ) / 125)) (paidRun_none_le I environment supplied valid)
  have floor : 1 - ENNReal.ofReal ((1 : ℝ) / 125) =
      ENNReal.ofReal ((124 : ℝ) / 125) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (show (0 : ℝ) ≤ 1 / 125 by norm_num)]
    norm_num
  exact floor ▸ lower

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
