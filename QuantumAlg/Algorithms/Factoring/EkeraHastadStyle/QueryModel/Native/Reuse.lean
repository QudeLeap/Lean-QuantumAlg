/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Program
import all QuantumAlg.Primitives.ZReset.Bank.Scope

/-!
# A paid subsequent sample on the original live oracle bank

The existing bank is first reset by actual Z measurements and stored-outcome
corrections inside one real classical scratch scope. The same parameter read,
XOR member, exponent measurements and charged pack then execute in place.
Every earlier classical cell stays live. There is no new quantum allocation
or release, and no free initialization premise.

An initial sample uses the separate actual preparation constructor. This
subsequent-sample constructor charges one reset before its member, so a caller
can use it only between successive samples and omit an unnecessary final reset.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Reset the same physical bank with a real one-cell classical scope. -/
def resetBank : Circuit (context base noQuantum N) (context base noQuantum N) :=
  ZReset.BankScope.code
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N))

/-- Pay for reset, then execute the original member and actual result writes in place. -/
def reuse (input : Input N) (parameter : CInputRef base (ParameterShape N)) :
    Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq (resetBank base noQuantum N) (body base noQuantum N input parameter)

/-- The reused sample reads the same packed result and exposes every surviving entry. -/
def reuseRun (input : Input N) (parameter : CInputRef base (ParameterShape N)) :
    AlgorithmRun (context base noQuantum N) (context base noQuantum N)
      (.bits (measurementBits N)) where
  code := reuse base noQuantum N input parameter
  output := Output.all (context base noQuantum N)
    (.read (.storage (resultRef base noQuantum N).toCStorageRef))

/-- Reuse preserves the complete live manifest of the original bank and result cells. -/
theorem nativeOracle_reuse_output_listing (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) :
    (reuseRun base noQuantum N input parameter).output.listing =
      (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
