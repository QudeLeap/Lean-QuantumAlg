/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Recorded.Weight

/-!
# Normalization of a common recorded branch scalar

The actual complete recorded instrument preserves the mass of one input ket.
If every outcome acts on that ket with the same scalar and a basis output,
its squared magnitude sums to one over the actual finite outcome type. This
uses the complete instrument rather than a separately postulated outcome law.
-/

namespace QuantumAlg.Execution.RecordedInstrument

noncomputable section

open Instrument
open scoped BigOperators

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Outcome : Type} [Fintype Outcome]
  {code : Circuit (.quantum gates oracles operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- A common ket coefficient of every outcome of the actual instrument is normalized. -/
lemma common_scalar_sum_norm_sq
    (actual : RecordedInstrument code Outcome environment)
    (Reference : Register) (original : Store ctx × services.HiddenState)
    (initial : (ctx.register.prod Reference).Index)
    (final : Outcome → (ctx.register.prod Reference).Index) (scalar : ℂ)
    (action : ∀ outcome,
      (referenceLift Reference (actual.operator original outcome)).applyVec
          (NormalizedVector.ket (R := ctx.register.prod Reference) initial : HilbertVector _) =
        scalar • (NormalizedVector.ket (R := ctx.register.prod Reference) (final outcome) :
          HilbertVector _)) :
    (∑ _outcome : Outcome, ‖scalar‖ ^ 2) = 1 := by
  classical
  let inputKet : HilbertVector (ctx.register.prod Reference) :=
    (NormalizedVector.ket (R := ctx.register.prod Reference) initial).vec
  have ketNorm : ‖inputKet‖ = 1 :=
    NormalizedVector.norm_ket (R := ctx.register.prod Reference) initial
  have ketBound : ‖inputKet‖ ≤ 1 := ketNorm.le
  have complete :
      (∑ outcome : Outcome,
        ‖(referenceLift Reference (actual.operator original outcome)).applyVec inputKet‖ ^ 2) =
      ‖inputKet‖ ^ 2 :=
    actual.recorded_sum_norm_sq Reference (History := Unit)
      (Classical.decEq _) (original.1, (original.2, ())) inputKet ketBound
  have same :
      (∑ outcome : Outcome,
        ‖(referenceLift Reference (actual.operator original outcome)).applyVec
          inputKet‖ ^ 2) =
        ∑ _outcome : Outcome, ‖scalar‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro outcome _
    rw [action, norm_smul, NormalizedVector.norm_ket, mul_one]
  exact same.symm.trans (complete.trans (by rw [ketNorm, one_pow]))

end

end QuantumAlg.Execution.RecordedInstrument
