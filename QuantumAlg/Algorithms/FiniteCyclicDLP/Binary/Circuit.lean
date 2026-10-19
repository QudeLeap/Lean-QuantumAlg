/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Oracle
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Native
public import QuantumAlg.Primitives.QFT.Native.Inverse
public import QuantumAlg.Primitives.QFT.Native.Inverse.Depth
public import QuantumAlg.Primitives.QFT.Native.Inverse.Resources
public import QuantumAlg.Core.Base.UnitaryCircuit.Layout.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
public import QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Native unitary stage on the binary finite-cyclic DLP bank

The two reviewed-width exponent registers are prepared by the actual
Shukla--Vedula words, the sole granted group-action query is executed once,
and both registers are transformed by generated inverse-QFT words.  Every
subcircuit is placed on the complete binary-qubit layout, so the binary group
workspace remains present in the same execution and in its space ledger.
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary.Circuit

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Physical relocation from the canonical register to the second exponent block. -/
public def secondShift (P : KnownOrderProblem G) : Nat ↪ Nat where
  toFun identity := OrderPreparation.width P + identity
  inj' := fun _ _ same => Nat.add_left_cancel same

/-- The second copy of a native word carries the actual shifted physical identities. -/
public abbrev secondLayout (P : KnownOrderProblem G) :
    QuantumLayout (OrderPreparation.width P) :=
  (OrderPreparation.layout P).relabel (secondShift P)

/-- The two consecutive exponent layouts have distinct physical identities. -/
public lemma binaryCircuit_exponentLayouts_disjoint (P : KnownOrderProblem G) :
    List.Disjoint (OrderPreparation.layout P).identities
      (secondLayout P).identities := by
  apply List.disjoint_left.mpr
  intro identity inFirst inSecond
  obtain ⟨first, firstEq⟩ := List.mem_ofFn.mp inFirst
  obtain ⟨second, secondEq⟩ := List.mem_ofFn.mp inSecond
  change first.val = identity at firstEq
  change OrderPreparation.width P + second.val = identity at secondEq
  omega

/-- Appending the two exponent blocks gives the oracle's canonical exponent layout. -/
public lemma binaryCircuit_pairLayout_eq_exponentLayout (P : KnownOrderProblem G) :
    QuantumLayout.append (OrderPreparation.layout P) (secondLayout P)
      (binaryCircuit_exponentLayouts_disjoint P) = OrderOracle.exponentLayout P := by
  apply QuantumLayout.eq_of_wire_eq
  funext index
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · simp [OrderOracle.exponentLayout, OrderPreparation.layout, secondLayout,
      QuantumLayout.append,
      QuantumSignature.canonicalPlacement, QuantumSignature.place,
      QuantumSignature.qubits]
  · simp only [QuantumLayout.append, Fin.append_right]
    simp [OrderOracle.exponentLayout, OrderPreparation.layout, secondLayout, secondShift,
      QuantumLayout.relabel, QuantumWire.relabel,
      QuantumSignature.canonicalPlacement, QuantumSignature.place,
      QuantumSignature.qubits, Nat.add_comm]

/-- Pair two words on the exact two-register exponent layout. -/
public def pairCircuit (P : KnownOrderProblem G)
    (left : UnitaryCircuit AlgorithmGate.model (Oracle.model P)
      (OrderPreparation.layout P))
    (right : UnitaryCircuit AlgorithmGate.model (Oracle.model P)
      (secondLayout P)) :
    UnitaryCircuit AlgorithmGate.model (Oracle.model P)
      (OrderOracle.exponentLayout P) :=
  (UnitaryCircuit.tensor left right (binaryCircuit_exponentLayouts_disjoint P)).castLayout
    (binaryCircuit_pairLayout_eq_exponentLayout P)

/-- Extend an exponent-register word by identity on the encoded group register. -/
public def withWorkspace (P : KnownOrderProblem G)
    (body : UnitaryCircuit AlgorithmGate.model (Oracle.model P)
      (OrderOracle.exponentLayout P)) :
    UnitaryCircuit AlgorithmGate.model (Oracle.model P) (Oracle.layout P) :=
  UnitaryCircuit.tensor body
    (UnitaryCircuit.identity AlgorithmGate.model (Oracle.model P)
      (Oracle.workspaceLayout P))
    (Oracle.binaryOracle_exponent_workspace_disjoint P)

/-- Both independent range preparations execute in parallel on their actual registers. -/
public def preparations (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model (Oracle.model P) (Oracle.layout P) :=
  withWorkspace P (pairCircuit P
    (OrderPreparation.Native.circuit (Oracle.model P) P expansion)
    ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).relabel
      (secondShift P)))

/-- Both independent inverse QFTs execute in parallel on their actual registers. -/
public def inverseQFTs (P : KnownOrderProblem G) :
    UnitaryCircuit AlgorithmGate.model (Oracle.model P) (Oracle.layout P) :=
  withWorkspace P (pairCircuit P
    (QuantumFourierTransform.Native.inverseCircuit
      (Oracle.model P) (OrderPreparation.width P))
    ((QuantumFourierTransform.Native.inverseCircuit
      (Oracle.model P) (OrderPreparation.width P)).relabel (secondShift P)))

/-- One complete native preparation-query-inverse-QFT unitary stage. -/
public def circuit (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model (Oracle.model P) (Oracle.layout P) :=
  let queried := (preparations P expansion).seq (Oracle.circuit AlgorithmGate.model P)
  queried.seq (inverseQFTs P)

/-- Parallel preparation preserves both actual ledgers without serializing their depths. -/
public lemma binaryCircuit_preparations_eventCost (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (preparations P expansion).eventCost =
      (OrderPreparation.Native.circuit (Oracle.model P) P expansion).eventCost +
        (OrderPreparation.Native.circuit (Oracle.model P) P expansion).eventCost := by
  rw [preparations, withWorkspace, pairCircuit,
    UnitaryCircuit.tensor_native_eventCost, UnitaryCircuit.identity_eventCost,
    add_zero, UnitaryCircuit.castLayout_eventCost,
    UnitaryCircuit.tensor_native_eventCost, UnitaryCircuit.relabel_eventCost]

/-- The two identical preparation branches have the depth of one actual branch. -/
public lemma binaryCircuit_preparations_unit_depth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (preparations P expansion).evaluatedEventDepth (fun _ => 1) =
      (OrderPreparation.Native.circuit (Oracle.model P) P expansion).evaluatedEventDepth
        (fun _ => 1) := by
  rw [preparations, withWorkspace, pairCircuit,
    UnitaryCircuit.tensor_native_evaluatedEventDepth,
    UnitaryCircuit.evaluatedEventDepth_identity, Nat.max_zero,
    UnitaryCircuit.castLayout_evaluatedEventDepth,
    UnitaryCircuit.tensor_native_evaluatedEventDepth,
    UnitaryCircuit.relabel_evaluatedEventDepth, Nat.max_self]

/-- Parallel inverse QFTs preserve both generated native ledgers. -/
public lemma binaryCircuit_inverseQFTs_eventCost (P : KnownOrderProblem G) :
    (inverseQFTs P).eventCost =
      (QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P)).eventCost +
      (QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P)).eventCost := by
  rw [inverseQFTs, withWorkspace, pairCircuit,
    UnitaryCircuit.tensor_native_eventCost, UnitaryCircuit.identity_eventCost,
    add_zero, UnitaryCircuit.castLayout_eventCost,
    UnitaryCircuit.tensor_native_eventCost, UnitaryCircuit.relabel_eventCost]

/-- The two identical inverse QFT branches have the depth of one generated word. -/
public lemma binaryCircuit_inverseQFTs_unit_depth (P : KnownOrderProblem G) :
    (inverseQFTs P).evaluatedEventDepth (fun _ => 1) =
      OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
        (if OrderPreparation.width P / 2 = 0 then 0 else 3) := by
  rw [inverseQFTs, withWorkspace, pairCircuit,
    UnitaryCircuit.tensor_native_evaluatedEventDepth,
    UnitaryCircuit.evaluatedEventDepth_identity, Nat.max_zero,
    UnitaryCircuit.castLayout_evaluatedEventDepth,
    UnitaryCircuit.tensor_native_evaluatedEventDepth,
    UnitaryCircuit.relabel_evaluatedEventDepth, Nat.max_self]
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth
    (Oracle.model P) (OrderPreparation.width P)

/-- The complete native ledger is derived from its two preparations, one query and two QFTs. -/
public lemma binaryCircuit_circuit_eventCost (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (circuit P expansion).eventCost =
      ((OrderPreparation.Native.circuit (Oracle.model P) P expansion).eventCost +
        (OrderPreparation.Native.circuit (Oracle.model P) P expansion).eventCost) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (Oracle.model P))
        (.oracle .ux) +
      ((QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P)).eventCost +
       (QuantumFourierTransform.Native.inverseCircuit
        (Oracle.model P) (OrderPreparation.width P)).eventCost) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    binaryCircuit_preparations_eventCost, Oracle.binaryOracle_circuit_eventCost,
      binaryCircuit_inverseQFTs_eventCost]

/-- Exact max-plus depth of one complete unitary sampling cycle. -/
public lemma binaryCircuit_circuit_unit_depth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    (circuit P expansion).evaluatedEventDepth (fun _ => 1) =
      (OrderPreparation.Native.circuit (Oracle.model P) P expansion).evaluatedEventDepth
        (fun _ => 1) + 1 +
      (OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
        (if OrderPreparation.width P / 2 = 0 then 0 else 3)) := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, binaryCircuit_preparations_unit_depth,
    Oracle.binaryOracle_circuit_unit_depth, binaryCircuit_inverseQFTs_unit_depth]

/-- Exact native one-qubit count of the complete unitary sampling stage. -/
public lemma binaryCircuit_circuit_singleQubit_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (Oracle.model P))
      (.gate .singleQubit) (circuit P expansion).eventCost =
        2 * OrderPreparation.singleQubitCount expansion +
          2 * (OrderPreparation.width P + 3 * (OrderPreparation.width P).choose 2) := by
  rw [binaryCircuit_circuit_eventCost]
  simp only [ResourcePool.count_add]
  rw [OrderPreparation.Native.circuit_singleQubit_count,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count]
  simp
  omega

/-- Exact native CNOT count of the complete unitary sampling stage. -/
public lemma binaryCircuit_circuit_cnot_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (Oracle.model P))
      (.gate .cnot) (circuit P expansion).eventCost =
        2 * OrderPreparation.cnotCount expansion +
          2 * (2 * (OrderPreparation.width P).choose 2 +
            3 * (OrderPreparation.width P / 2)) := by
  rw [binaryCircuit_circuit_eventCost]
  simp only [ResourcePool.count_add]
  rw [OrderPreparation.Native.circuit_cnot_count,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count]
  simp
  omega

/-- The complete native sampling stage contains no Toffoli occurrence. -/
public lemma binaryCircuit_circuit_toffoli_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (Oracle.model P))
      (.gate .toffoli) (circuit P expansion).eventCost = 0 := by
  rw [binaryCircuit_circuit_eventCost]
  simp only [ResourcePool.count_add]
  rw [OrderPreparation.Native.circuit_toffoli_count,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count]
  simp

/-- The complete native sampling stage invokes its sole granted oracle once. -/
public lemma binaryCircuit_circuit_ux_count (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (Oracle.model P))
      (.oracle .ux) (circuit P expansion).eventCost = 1 := by
  rw [binaryCircuit_circuit_eventCost]
  simp only [ResourcePool.count_add]
  rw [OrderPreparation.Native.circuit_oracle_count
      (Oracle.model P) P expansion .ux,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count
      (Oracle.model P) (.oracle .ux) (OrderPreparation.width P)]
  simp

end

end QuantumAlg.FiniteCyclicDLP.Binary.Circuit
