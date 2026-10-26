/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Basic

/-!
# Exact actual-record scalar composition

The second component reads the first component's literal returned Store.
Both original paths and the arbitrary reference remain explicit, without
normalizing a concrete program or expanding its finite outcome carrier.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument

/-- An exact local ket column lifts beside every untouched reference ket. -/
lemma Instrument.reference_applyVec_ket {R : Register}
    (operator : HilbertOperator R) (initial final : R.Index) (scalar : Complex)
    (actual : operator.applyVec (NormalizedVector.ket (R := R) initial).vec =
      scalar • (NormalizedVector.ket (R := R) final).vec)
    {Reference : Register} (reference : Reference.Index) :
    (referenceLift Reference operator).applyVec
        (NormalizedVector.ket (R := R.prod Reference) (initial, reference)).vec =
      scalar • (NormalizedVector.ket (R := R.prod Reference) (final, reference)).vec := by
  classical
  ext row
  rcases row with ⟨localIndex, referenceIndex⟩
  rw [HilbertOperator.applyVec_ket]
  have column := congrArg (fun vector : HilbertVector R => vector localIndex) actual
  rw [HilbertOperator.applyVec_ket] at column
  change operator localIndex initial * (if referenceIndex = reference then (1 : Complex) else 0) = _
  rw [column]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change (scalar * (if localIndex = final then 1 else 0)) *
      (if referenceIndex = reference then 1 else 0) =
    scalar * (if (localIndex, referenceIndex) = (final, reference) then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {allowAllocation : Bool}
  {FirstOutcome SecondOutcome : Type} [Fintype FirstOutcome] [Fintype SecondOutcome]
  {first second : Circuit (.quantum gates oracles operations services)
    ctx ctx allowAllocation}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- Composition retains exactly both actual component paths and their intermediate Store. -/
lemma instrument_seq_record (head : Instrument first FirstOutcome environment)
    (tail : Instrument second SecondOutcome environment)
    (store : Execution.Store ctx) (firstOutcome : FirstOutcome) (secondOutcome : SecondOutcome) :
    (head.seq tail).record store (firstOutcome, secondOutcome) =
      let middle := head.record store firstOutcome
      let final := tail.record middle.1 secondOutcome
      (final.1, (middle.2, final.2)) := rfl

/-- Actual full-reference branch amplitudes multiply at the same literal intermediate Store. -/
lemma instrument_seq_reference_applyVec (head : Instrument first FirstOutcome environment)
    (tail : Instrument second SecondOutcome environment)
    (store : Execution.Store ctx) (firstOutcome : FirstOutcome) (secondOutcome : SecondOutcome)
    (Reference : Register) (initial middle final : HilbertVector (ctx.register.prod Reference))
    (firstScalar secondScalar : Complex)
    (headAction : (referenceLift Reference (head.operator store firstOutcome)).applyVec initial =
      firstScalar • middle)
    (tailAction : (referenceLift Reference
      (tail.operator (head.record store firstOutcome).1 secondOutcome)).applyVec middle =
        secondScalar • final) :
    (referenceLift Reference
      ((head.seq tail).operator store (firstOutcome, secondOutcome))).applyVec initial =
        (firstScalar * secondScalar) • final := by
  change (referenceLift Reference
    (tail.operator (head.record store firstOutcome).1 secondOutcome *
      head.operator store firstOutcome)).applyVec initial = _
  rw [referenceLift_mul, HilbertOperator.mul_applyVec, headAction,
    HilbertOperator.applyVec_smul, tailAction, smul_smul]

end

end QuantumAlg.Execution
