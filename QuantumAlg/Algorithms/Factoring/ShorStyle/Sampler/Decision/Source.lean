/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Packing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.ParameterReadout

/-!
# The actual residue decision writes the original RSA parameter

The established source choice is consumed by the real initialized decision
program. Every accepted nonunit retains its computed GCD as an early factor;
total rejection produces the original default unit and empty factor. The
local modulus and zero-result facts are supplied by the actual enclosing
allocation and scan, rather than requested from the algorithm caller.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The native decision writes the source's complete parameter for the actual scan choice. -/
theorem samplerDecision_source (input : Input N)
    (value : Fin (2 ^ residueSamplingBits N))
    (output : CWriteRef (Layout.context ctx (modulusBits N)) (ParameterShape (modulusBits N)))
    (store : Store (Layout.context ctx (modulusBits N)))
    (sourceChoice : Proposal.selection (Layout.shared ctx (modulusBits N)) store =
      RSA.firstValidResidue (RSA.classifyResidueProposals N
        (RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount value)))
    (modulusValue : (store.read
      (FirstAccepted.cellRead (Layout.modulusCell ctx (modulusBits N)))).toNat = N)
    (resultZero : (store.read
      (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N)))).toNat = 0) :
    (step (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
      (Layout.gcdResultCell ctx (modulusBits N)) output store).1.read
        (FirstAccepted.cellRead output) = parameterValue input value := by
  let shared := Layout.shared ctx (modulusBits N)
  let scratch := Layout.scratch ctx (modulusBits N)
  let gcdResult := Layout.gcdResultCell ctx (modulusBits N)
  let initialized := initializationStore shared scratch store
  let candidate := (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat
  have separated := Layout.samplerLayout_accepted_separated ctx (modulusBits N)
  have initializedFields := Layout.samplerLayout_initialized_fields store
  have initializedInputs := Layout.samplerLayout_initialization_inputs store
  have candidateRead : initialized.read (FirstAccepted.cellRead scratch.candidate) =
      store.read (FirstAccepted.cellRead shared.selector.selected) := initializedFields.1
  have unitRead : initialized.read (FirstAccepted.cellRead shared.selector.selected) =
      CShape.wordOfNat (modulusBits N) 1 := initializedFields.2.1
  have flagRead : initialized.read (FirstAccepted.cellRead scratch.eligible) = .bit false :=
    initializedFields.2.2
  have acceptedRead : (initialized.read (FirstAccepted.cellRead shared.selector.accepted)).toBool =
      (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool :=
    congrArg CShape.Value.toBool initializedInputs.1
  have modulusRead : (initialized.read shared.modulus).toNat = N :=
    (congrArg CShape.Value.toNat initializedInputs.2.1).trans modulusValue
  have zeroRead : (initialized.read (FirstAccepted.cellRead gcdResult)).toNat = 0 :=
    (congrArg CShape.Value.toNat initializedInputs.2.2).trans resultZero
  have oneFits : 1 < CShape.wordModulus (modulusBits N) :=
    input.modulus_gt_one.trans_le input.register_fits
  have oneValue : (CShape.wordOfNat (modulusBits N) 1).toNat = 1 := by
    simp only [CShape.wordOfNat_val, Nat.mod_eq_of_lt oneFits]
  have zeroValue : (CShape.wordOfNat (modulusBits N) 0).toNat = 0 := by
    simp only [CShape.wordOfNat_val, Nat.zero_mod]
  have observed :
      (if (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool then
        some candidate else none) =
      RSA.firstValidResidue (RSA.classifyResidueProposals N
        (RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount value)) := sourceChoice
  rw [decision_read, decisionAcceptance_store, acceptedRead]
  cases accepted : (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool with
  | false =>
      have rejectedSource : RSA.firstValidResidue (RSA.classifyResidueProposals N
          (RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount value)) = none := by
        exact observed.symm.trans
          (if_neg (fun positive => Bool.false_ne_true (accepted.symm.trans positive)))
      have prepared : RSA.prepareResidueFromBits N (modulusBits N) residueProposalCount value =
          RSA.prepareResidue N none := by
        change RSA.prepareResidue N _ = _
        exact congrArg (RSA.prepareResidue N) rejectedSource
      have expected := sampler_parameterValue_of_none input value prepared
      rw [if_neg Bool.false_ne_true,
        decisionRejected_fields shared scratch separated.candidateUnit
          separated.candidateFlag initialized, unitRead, flagRead]
      apply sampler_parameterValue_eq_of_components input value
      · exact oneValue.trans expected.1.symm
      · exact expected.2.1.symm
      · exact zeroValue.trans expected.2.2.symm
  | true =>
      have selectedSource : RSA.firstValidResidue (RSA.classifyResidueProposals N
          (RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount value)) =
            some candidate := by
        exact observed.symm.trans (if_pos accepted)
      have prepared : RSA.prepareResidueFromBits N (modulusBits N) residueProposalCount value =
          RSA.prepareResidue N (some candidate) := by
        change RSA.prepareResidue N _ = _
        exact congrArg (RSA.prepareResidue N) selectedSource
      obtain ⟨_, _, eligible⟩ :=
        RSA.exists_eligible_of_firstValidResidue_classify_eq_some selectedSource
      have positive : 0 < candidate := eligible.1
      have below : candidate < N := eligible.2
      rw [if_pos rfl,
        decisionAccepted_fields shared scratch gcdResult separated initialized zeroRead]
      rw [candidateRead, unitRead, flagRead, modulusRead, oneValue]
      by_cases coprime : Nat.Coprime candidate N
      · have expected := sampler_parameterValue_of_coprime input value prepared below coprime
        refine (if_pos (show Nat.gcd candidate N = 1 from coprime)).trans ?_
        apply sampler_parameterValue_eq_of_components input value
        · exact expected.1.symm
        · exact expected.2.1.symm
        · exact zeroValue.trans expected.2.2.symm
      · have expected := sampler_parameterValue_of_not_coprime input value prepared
          positive below coprime
        have candidateFits : candidate < CShape.wordModulus (modulusBits N) :=
          CShape.Value.toNat_lt (store.read (FirstAccepted.cellRead shared.selector.selected))
        have gcdFits : Nat.gcd candidate N < CShape.wordModulus (modulusBits N) :=
          (Nat.gcd_le_left N positive).trans_lt candidateFits
        have gcdValue : (CShape.wordOfNat (modulusBits N) (Nat.gcd candidate N)).toNat =
            Nat.gcd candidate N := by
          simp only [CShape.wordOfNat_val, Nat.mod_eq_of_lt gcdFits]
        refine (if_neg (show Nat.gcd candidate N ≠ 1 from coprime)).trans ?_
        apply sampler_parameterValue_eq_of_components input value
        · exact oneValue.trans expected.1.symm
        · exact expected.2.1.symm
        · exact gcdValue.trans expected.2.2.symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
