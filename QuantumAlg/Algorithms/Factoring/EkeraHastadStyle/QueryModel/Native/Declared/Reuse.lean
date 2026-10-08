/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program
import all QuantumAlg.Primitives.ZReset.Bank.Scope

/-!
# Paid reuse of the declared EH quantum bank

A later sample resets the same live physical bank, then executes one
selected group-query member, physical exponent measurements and paid
packing in the same model. No new quantum bank is allocated.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- Reset the original live bank with the actual one-cell classical scratch scope. -/
def resetBank : Circuit (model input) (Native.context base noQuantum N)
    (Native.context base noQuantum N) :=
  ZReset.BankScope.code
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)) BitWord.model

/-- Pay for reset before one more complete declared member and result write. -/
def reuse (parameter : CInputRef base (ParameterShape N)) :
    Circuit (model input) (Native.context base noQuantum N)
      (Native.context base noQuantum N) :=
  .seq (resetBank base noQuantum N input)
    (body base noQuantum N input parameter)

/-- Read the overwritten packed exponent result while retaining every cell and wire. -/
def reuseRun (parameter : CInputRef base (ParameterShape N)) :
    AlgorithmRun (model input) (Native.context base noQuantum N)
      (Native.context base noQuantum N) (.bits (measurementBits N)) where
  code := reuse base noQuantum N input parameter
  output := Output.all (Native.context base noQuantum N)
    (.read (.storage (Native.resultRef base noQuantum N).toCStorageRef))

/-- Reuse preserves the complete original live manifest. -/
theorem reuse_output_listing (parameter : CInputRef base (ParameterShape N)) :
    (reuseRun base noQuantum N input parameter).output.listing =
      (Native.context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
