/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared

/-!
# Complete source histories and the original measured sampler paths

The prepared stages are the original reset, native H and measured point plus
Fourier instructions. Structural list equality identifies their actual code
with the unchanged sampler. Their history bijection retains every measured
record and adds only the unique paths of the real native H and final identity.
This coordinate identity does not assert a preparation or Born law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

variable (parameters : Parameters ctx)

/-- The real native H instruction beside the same original source stage. -/
def preparedStage (index : WindowIndex) (Reference : Register) :
    PreparedStage ctx BitWord.model services (SourceRegister.prod Reference) where
  stage := parameters.sourceStage index Reference
  prepare := QuantumFourierTransform.Semiclassical.Window.preparation
    (index.lowerWidth + 1) (parameters.ports index)

/-- Each prepared block is literally the original measured sampler block. -/
lemma preparedStage_code (index : WindowIndex) (Reference : Register) :
    (parameters.preparedStage (services := services) index Reference).code =
      parameters.block index := rfl

/-- The same symbolic list retains the original windows, references and instruction order. -/
def preparedStages (indices : List WindowIndex) (Reference : Register) :
    List (PreparedStage ctx BitWord.model services (SourceRegister.prod Reference)) :=
  indices.map (fun index => parameters.preparedStage index Reference)

/-- Removing only native preparation metadata leaves exactly the original source-stage list. -/
lemma preparedStages_stages (indices : List WindowIndex) (Reference : Register) :
    (parameters.preparedStages (services := services) indices Reference).map
        PreparedStage.stage =
      parameters.sourceStages indices Reference := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      exact congrArg (List.cons (parameters.sourceStage index Reference)) ih

/-- Structural composition is the same actual sampling program, including its final identity. -/
lemma preparedStages_sequence (indices : List WindowIndex) (Reference : Register) :
    PreparedStage.sequence (parameters.preparedStages (services := services) indices Reference) =
      parameters.sequence indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      exact congrArg (Circuit.seq (parameters.block index)) ih

/-- All source-stage records correspond bijectively to the same actual sampling paths. -/
def sourceHistoryEquiv (indices : List WindowIndex) (Reference : Register) (History : Type) :
    parameters.SourceRecords (services := services) indices Reference History ≃
      History × (parameters.sequence (services := services) indices).Path :=
  (Equiv.cast (congrArg (fun stages => Stage.Records stages History)
    (parameters.preparedStages_stages (services := services) indices Reference).symm)).trans
    ((PreparedStage.historyEquiv (parameters.preparedStages indices Reference) History).trans
      (Equiv.prodCongr (Equiv.refl History)
        (Equiv.cast (congrArg (fun code :
          Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true =>
            code.Path)
          (parameters.preparedStages_sequence indices Reference)))))

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
