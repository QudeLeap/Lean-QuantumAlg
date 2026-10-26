/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Born

/-!
# Original RSA selected-source law of the actual measured member

Every original nontrivial-modulus input has the same original terminal Born
law at its actual stored parameter. Oddness and good-key assumptions are
unnecessary for this semantic equality [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured

noncomputable section

open EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

/-- Every original input and stored parameter has the unchanged complete source Born law. -/
lemma measuredRSA_memberBornWeight {N : Nat} (input : Input N)
    [NeZero (modulusWord N).toNat] (parameter : (ParameterShape N).Value)
    (readout : MemberReadouts (shortLogBits N) (tradeoffBits N)) :
    memberFourierWeight (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N)
      (parameterGenerator N parameter) (parameterTargetWord N parameter)
      (measuredMemberFrequencies (shortLogBits N) (tradeoffBits N) readout).1
      (measuredMemberFrequencies (shortLogBits N) (tradeoffBits N) readout).2 =
        (selectedOutcomePMF parameter
          (measuredMemberTerminalEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
            readout)).toReal := by
  have domain : 1 < N ∧ N < 2 ^ arithmeticBits N :=
    ⟨input.modulus_gt_one, modulus_lt_arithmeticCapacity N⟩
  rw [selectedOutcomePMF, dif_pos domain]
  exact measuredMemberBorn_of_modulusEq (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (modulusWord N) N (measuredRSA_modulusWord_toNat N) (parameterUnit parameter)
    (parameterTarget parameter)
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N domain.1 domain.2) readout

end

end QuantumAlg.Factoring.RSA.Measured
