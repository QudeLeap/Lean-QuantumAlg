/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Util.RSA.KeyGeneration

/-!
# Canonical Ekerå–Håstad batch distribution

This module couples the internally sampled residue to sixteen independent
terminal measurements of the one real selected short-DLP member.  The closed
value projection is the same 120-pair recovery used by the typed classical
tail; no detached generator distribution or caller-supplied state appears at
this boundary.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical

noncomputable section

/-! ## Source-faithful theorem-side key average -/

/-- One complete internally sampled batch, averaged over the canonical
same-bit RSA key generator.  Key generation is theorem-side and uncharged;
the executable batch still receives only each generated modulus. -/
def keygenSampledBatchOutput (b : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits b)) :
    PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits b nonempty).bind fun pair =>
    (sampledBatchOutputPMF (inputOfKeyPair pair)).map fun output =>
      (pair.p, pair.q, output)

/-- Every supported successful output of the key-averaged law is one of the
two primes generated in that same branch. -/
theorem keygenSampledBatchOutput_some_sound (b : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits b)) {p q factor : Nat}
    (member : (p, q, some factor) ∈
      (keygenSampledBatchOutput b nonempty).support) :
    factor = p ∨ factor = q := by
  rw [keygenSampledBatchOutput, PMF.mem_support_bind_iff] at member
  rcases member with ⟨pair, _pairMember, outputMember⟩
  rw [PMF.mem_support_map_iff] at outputMember
  rcases outputMember with ⟨output, outputMember, outputEq⟩
  have leftEq : pair.p = p := congrArg Prod.fst outputEq
  have restEq : (pair.q, output) = (q, some factor) :=
    congrArg Prod.snd outputEq
  have rightEq : pair.q = q := congrArg Prod.fst restEq
  have factorEq : output = some factor := congrArg Prod.snd restEq
  subst p
  subst q
  rw [factorEq] at outputMember
  have sound := sampledBatchOutputPMF_some_sound
    (inputOfKeyPair pair) outputMember
  exact (semiprimeOfKeyPair pair).nontrivial_factor_eq_declared
    sound.1 sound.2.1 sound.2.2

end

end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
