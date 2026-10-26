/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Sequence

/-!
# Vector actions through complete actual recorded composition

The second factor reads the first component's exact returned Store and
hidden service state. Its operator acts on the same arbitrary reference.
The two actual paths remain in the complete record, while unnormalized
branch vectors compose without selecting or renormalizing an outcome.
-/

namespace QuantumAlg.Execution.RecordedInstrument

noncomputable section

open Instrument

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}
  {First Last : Type} [Fintype First] [Fintype Last]
  {first last : Circuit (.quantum gates oracles operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum gates oracles operations services).Environment}

/-- Both actual paths and the final complete service record are retained in their original order. -/
lemma seq_record (head : RecordedInstrument first First environment)
    (tail : RecordedInstrument last Last environment)
    (original : Store ctx × services.HiddenState) (a : First) (b : Last) :
    (head.seq tail).record original (a, b) =
      let middle := head.record original a
      let final := tail.record middle.1 b
      (final.1, (middle.2, final.2)) := rfl

/-- The second matrix reads the literal complete record returned by the first component. -/
lemma seq_operator (head : RecordedInstrument first First environment)
    (tail : RecordedInstrument last Last environment)
    (original : Store ctx × services.HiddenState) (a : First) (b : Last) :
    (head.seq tail).operator original (a, b) =
      tail.operator (head.record original a).1 b * head.operator original a := rfl

/-- Exact scalar actions compose on raw vectors beside the same arbitrary reference. -/
lemma seq_reference_applyVec (head : RecordedInstrument first First environment)
    (tail : RecordedInstrument last Last environment)
    (original : Store ctx × services.HiddenState) (a : First) (b : Last)
    (Reference : Register) (initial middle final : HilbertVector (ctx.register.prod Reference))
    (firstScalar lastScalar : Complex)
    (headAction : (referenceLift Reference (head.operator original a)).applyVec initial =
      firstScalar • middle)
    (tailAction : (referenceLift Reference
      (tail.operator (head.record original a).1 b)).applyVec middle = lastScalar • final) :
    (referenceLift Reference ((head.seq tail).operator original (a, b))).applyVec initial =
      (firstScalar * lastScalar) • final := by
  change (referenceLift Reference
    (tail.operator (head.record original a).1 b * head.operator original a)).applyVec initial = _
  rw [referenceLift_mul, HilbertOperator.mul_applyVec, headAction,
    HilbertOperator.applyVec_smul, tailAction, smul_smul]

end

end QuantumAlg.Execution.RecordedInstrument
