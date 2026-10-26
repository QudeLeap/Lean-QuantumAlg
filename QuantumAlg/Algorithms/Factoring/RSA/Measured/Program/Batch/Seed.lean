/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Batch
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Members.Seed

/-!
# Every complete actual batch establishes its successor seed

The real nonempty member bank always finishes its full reset/reload.
Classical recovery preserves that seed, and a preceding actual source draw
does not require an incoming seed promise [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution EkeraHastadStyle.Canonical

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The complete actual batch establishes its seed without an incoming state promise. -/
lemma rsaMeasuredParent_batchBody_seeded_any (input : Input N) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((batchBody base noQuantum N input count batch).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (members base noQuantum N input count batch)
    (recover base noQuantum N input count batch) (memberSeed base noQuantum N count) state
    (rsaMeasuredParent_recover_seeded (environment := environment) base noQuantum input count batch
      (memberSeed base noQuantum N count) _
      (rsaMeasuredParent_members_seeded_any base noQuantum N input count batch environment state))

/-- Every actual later fresh-source batch supplies the same full physical successor seed. -/
lemma rsaMeasuredParent_nextBatch_seeded_any (input : Input N) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((nextBatch base noQuantum N input count batch).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) (memberSeed base noQuantum N count) state
    (rsaMeasuredParent_batchBody_seeded_any base noQuantum N count input batch environment _)

end

end QuantumAlg.Factoring.RSA.Measured.Program
