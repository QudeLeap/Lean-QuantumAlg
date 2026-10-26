/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Terminal
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Born

/-!
# Exact source Born weights through the unchanged public modulus equality

A finite arithmetic word represents its public modulus exactly. Transporting
the two static units along that equality changes neither the original
terminal label nor its original full Fourier Born weight
[GN96, 9511007.tex:214-266; EH17, source.tex:878-966].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

/-- Exact word/modulus transport preserves the complete original terminal Born probability. -/
lemma measuredMemberBorn_of_modulusEq (m ell width : Nat) (modulus : BitVec width)
    [NeZero modulus.toNat] (N : Nat) (same : modulus.toNat = N)
    (generator target : (ZMod N)ˣ) (encoding : UnitEncoding N (workspaceBits width))
    (readout : MemberReadouts m ell) :
    memberFourierWeight m ell width modulus
      (cast (congrArg (fun value : Nat => (ZMod value)ˣ) same.symm) generator)
      (cast (congrArg (fun value : Nat => (ZMod value)ˣ) same.symm) target)
      (measuredMemberFrequencies m ell readout).1
      (measuredMemberFrequencies m ell readout).2 =
        (((measurement (registerParameters m ell width)).outcomePMF
          (BornProbability.evolvedState encoding generator target))
          (measuredMemberTerminalEquiv m ell width readout)).toReal := by
  subst N
  exact memberFourierWeight_ideal m ell width modulus generator target encoding
    (measuredMemberFrequencies m ell readout).1 (measuredMemberFrequencies m ell readout).2

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
