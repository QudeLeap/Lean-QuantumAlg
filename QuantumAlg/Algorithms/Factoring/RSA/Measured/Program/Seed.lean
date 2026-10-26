/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Kernel

/-!
# Physical successor seed after the complete actual measured RSA execution

Every actual nonempty batch completes all physical resets and its literal
reload. The complete chronological suffix and paid final selector preserve
that seed, with no incoming seed premise [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
variable {environment : MeasuredRSAModel.Environment}

/-- The chronological actual later suffix retains its true physical seed even when empty. -/
lemma rsaMeasuredParent_laterBatches_seeded (input : Input N) (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1))
      ((Circuit.forRange laterCount fun index =>
        nextBatch base noQuantum N input (laterCount + 1) index.succ).execute
          environment Reference state) :=
  measuredForRange_seeded (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ) environment
    (memberSeed base noQuantum N (laterCount + 1))
    (fun index _ _ _ actual => rsaMeasuredParent_nextBatch_seeded_any base noQuantum N
      (laterCount + 1) input index.succ environment actual) state seeded

/-- Actual positive execution establishes its final seed without an input seed premise. -/
lemma rsaMeasuredParent_positiveCode_seeded (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (MeasuredRSAModel.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1))
      ((positiveCode base noQuantum N input laterCount).execute environment Reference state) := by
  let allocated : Circuit MeasuredRSAModel base
      (Recycling.ClassicalFrame.context base N (laterCount + 1)) :=
    Recycling.ClassicalFrame.allocate base N (laterCount + 1)
  let drawn : Circuit MeasuredRSAModel (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (Recycling.ClassicalFrame.context base N (laterCount + 1)) := firstSource base N laterCount
  let prepared : Circuit MeasuredRSAModel (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    ShortDLP.CompiledMAU.Recycling.Measured.prepare
      (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat
  let completed : Circuit MeasuredRSAModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    batchBody base noQuantum N input (laterCount + 1) 0
  let later : Circuit MeasuredRSAModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    Circuit.forRange laterCount fun index =>
      nextBatch base noQuantum N input (laterCount + 1) index.succ
  let chosen : Circuit MeasuredRSAModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    select base noQuantum N (laterCount + 1)
  refine BasisSeeded.seq (environment := environment) allocated
    (drawn.seq (prepared.seq (completed.seq (later.seq chosen)))) _ state ?_
  refine BasisSeeded.seq (environment := environment)
    drawn (prepared.seq (completed.seq (later.seq chosen))) _ _ ?_
  refine BasisSeeded.seq (environment := environment)
    prepared (completed.seq (later.seq chosen)) _ _ ?_
  refine BasisSeeded.seq (environment := environment) completed (later.seq chosen) _ _ ?_
  refine BasisSeeded.seq (environment := environment) later chosen _ _ ?_
  exact rsaMeasuredParent_select_seeded (environment := environment)
    base noQuantum N (laterCount + 1)
    (memberSeed base noQuantum N (laterCount + 1)) _
    (rsaMeasuredParent_laterBatches_seeded base noQuantum N input laterCount environment _
      (rsaMeasuredParent_batchBody_seeded_any
        base noQuantum N (laterCount + 1) input 0 environment _))

end

end QuantumAlg.Factoring.RSA.Measured.Program
