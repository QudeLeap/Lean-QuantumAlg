/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Coordinates
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage.Macros
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Util.Nat.ChooseTwo

/-!
# Same-bit identities for original EH source parameters

The original exponent widths specialize to explicit same-bit formulas.
Public statistics apply these identities to the actual canonical query
count and the original Hadamard and inverse-QFT constructions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma firstBits_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) : ShortDLP.firstBits (parameters pair.modulus) =
      n + 1 + (n + 2) / 2 := by
  simp only [ShortDLP.firstBits, parameters, shortLogBits_sameBit pair positive,
    tradeoffBits_sameBit pair positive, RSA.GeneratorOrder.m, RSA.GeneratorOrder.ell]
  omega

private lemma ell_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) :
    (parameters pair.modulus).ell = (n + 2) / 2 := by
  simp only [parameters, tradeoffBits_sameBit pair positive, RSA.GeneratorOrder.ell]

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
