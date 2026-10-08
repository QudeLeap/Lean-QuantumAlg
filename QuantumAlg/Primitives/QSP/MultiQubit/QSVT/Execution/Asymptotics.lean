/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Asymptotics
import all QuantumAlg.Util.Asymptotics
import Mathlib.Tactic

/-!
# Asymptotic classes of the explicit QSVT execution limits

The closed bounds retain a constant cost at degree zero. Their eventual
asymptotic class is the source O((m+1)L) for each source-ancilla width m.
The same width-independent constants also bound all positive degrees.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution

/-- The real route's explicit native gate limit has the source asymptotic order. -/
public theorem realExecution_gate_bigO (m : Nat) :
    NatBigO (fun L => 15 * ((40 * m + 3) * L + 2)) (fun L => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 600
  filter_upwards [Filter.eventually_ge_atTop 1] with L positive
  nlinarith

/-- The complex route's explicit native gate limit has the source asymptotic order. -/
public theorem complexExecution_gate_bigO (m : Nat) :
    NatBigO (fun L => 15 * ((40 * m + 20) * L + 19)) (fun L => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 600
  filter_upwards [Filter.eventually_ge_atTop 1] with L positive
  nlinarith

/-- The full real execution, including queries, has the same depth order. -/
public theorem realExecution_depth_bigO (m : Nat) :
    NatBigO (fun L => 15 * ((40 * m + 4) * L + 2)) (fun L => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 600
  filter_upwards [Filter.eventually_ge_atTop 1] with L positive
  nlinarith

/-- The full complex execution, including queries, has the same depth order. -/
public theorem complexExecution_depth_bigO (m : Nat) :
    NatBigO (fun L => 15 * ((40 * m + 21) * L + 20)) (fun L => (m + 1) * L) := by
  apply NatBigO.of_eventually_le_const_mul 615
  filter_upwards [Filter.eventually_ge_atTop 1] with L positive
  nlinarith

end QuantumAlg.QSP.MultiQubit.QSVT.Execution
