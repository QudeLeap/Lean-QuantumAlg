/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Members

/-!
# The real nonempty member bank always establishes its physical seed

There are two required members before any configured additional members.
The first complete actual member supplies the seed needed by its suffix;
every real member restarts the same bank, including the last
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Every configured actual member sequence establishes its seed, even for an unseeded input. -/
lemma rsaMeasuredParent_members_seeded_any (input : Input N) (count : Nat) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((members base noQuantum N input count batch).execute environment Reference state) := by
  let first : Fin membersPerBatch := ⟨0, by unfold membersPerBatch; omega⟩
  exact BasisSeeded.seq (environment := environment)
    (member base noQuantum N input count batch first)
    (Circuit.forRange (configuration.additionalMembers + 1)
      fun index => member base noQuantum N input count batch index.succ)
    (memberSeed base noQuantum N count) state
    (measuredForRange_seeded (Recycling.ClassicalFrame.context base N count)
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (configuration.additionalMembers + 1)
      (fun index => member base noQuantum N input count batch index.succ) environment
      (memberSeed base noQuantum N count)
      (fun index _ _ _ actual => rsaMeasuredParent_member_seeded base noQuantum N input count batch
        index.succ environment actual)
      ((member base noQuantum N input count batch first).execute environment Reference state)
      (rsaMeasuredParent_member_seeded base noQuantum N input count batch first environment state))

end

end QuantumAlg.Factoring.RSA.Measured.Program
