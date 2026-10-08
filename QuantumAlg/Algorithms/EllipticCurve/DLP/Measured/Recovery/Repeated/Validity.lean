/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Candidate
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity

/-!
# The same actual packed word is the original unique secret

Within the original subgroup order, the actual selected word's natural-scalar
point equation identifies the original secret. Final retained packing exposes
that same word. This endpoint lemma consumes the support invariants proved by
actual initialization and iteration; it supplies no secret to the program and
asserts no sampling independence or probability bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
  {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem selected_word_eq_secret (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (bounded : value.toNat < problem.order)
    (correct : value.toNat • problem.generator.toMathlib = problem.target.toMathlib) :
    value = CShape.wordOfNat (orderWidth problem) input.secret.val := by
  have decoded := (bounded_groupScalar_eq_target_iff problem input value.toNat bounded).mp correct
  have fits : input.secret.val < 2 ^ orderWidth problem :=
    lt_of_lt_of_le (residueIndex problem input.secret).isLt (order_le_fourierModulus problem)
  cases value with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      change word.val = input.secret.val % 2 ^ orderWidth problem
      rw [Nat.mod_eq_of_lt fits]
      exact decoded

/-- Every actual returned word is the original secret when the established invariants hold. -/
theorem packBatchResult_supported_secret {model : ExecutionModel}
    {placement : RuntimeCtx model.kind}
    [BitWord.Selected model]
    (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx placement (Canonical.Layout.fieldWidth E) (orderWidth problem))
      Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted placement (Canonical.Layout.fieldWidth E)
        (orderWidth problem)).toCStorageRef)).toBool = true →
      let selected := entry.1.read (.storage (persistentSelected placement
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef)
      selected.toNat < problem.order ∧
        selected.toNat • problem.generator.toMathlib = problem.target.toMathlib)
    (result : Store
      (batchResultCtx placement (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      (model.HiddenState ×
        (H × (packBatchResult placement (Canonical.Layout.fieldWidth E)
          (orderWidth problem)).Path)))
    (positive : 0 < (((packBatchResult placement (Canonical.Layout.fieldWidth E)
      (orderWidth problem)).execute Reference state).block result).mass)
    (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (output : result.1.read (batchResultRead placement (Canonical.Layout.fieldWidth E)
      (orderWidth problem)) = .optionSome value) :
    value = CShape.wordOfNat (orderWidth problem) input.secret.val := by
  refine packBatchResult_supported_property
    (fun value => value = CShape.wordOfNat (orderWidth problem) input.secret.val)
    state ?_ result positive value output
  intro entry present accepted
  have valid := holds entry present accepted
  exact selected_word_eq_secret problem input _ valid.1 valid.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
