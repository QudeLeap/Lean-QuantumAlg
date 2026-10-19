/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.CliffordT
public import QuantumAlg.Components.Gates.Rotation.Operator
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Components.GateModel.CliffordT
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Gate.OperatorNorm.Reindex
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Strict single-qubit Clifford+T words and exact-phase rotation certificates

Letters H, S and T execute their literal tokens in the strict H/S/T/CNOT
model, on one fixed physical qubit. The oracle declaration is retained but
no word emits a query. Counts and dependency depth come from these actual
instructions. Basis transport preserves the original operator-norm error;
rotation certificates never quotient out global phase.
-/

namespace QuantumAlg.CliffordT

open Gate

noncomputable section

/-- One physical qubit with canonical identity zero. -/
public def layout : QuantumLayout 1 := (QuantumSignature.qubits 1).canonicalPlacement.layout

/-- Express a mathematical one-qubit operator in the physical layout's basis. -/
public def physicalOperator (operator : UnitaryOperator (Qubits 1)) :
    UnitaryOperator layout.register :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm operator

/-- Actual T-coordinate count in any strict target circuit. -/
public def circuitTCount {oracles : OracleModel} {count : Nat} {ambient : QuantumLayout count}
    (circuit : UnitaryCircuit CliffordTGate.model oracles ambient) : Nat :=
  ResourcePool.count (model := .quantum CliffordTGate.model oracles)
    (.gate CliffordTGate.Token.t) circuit.eventCost

/-- The single-qubit subset of the literal strict target alphabet. -/
public inductive Letter where
  | h
  | s
  | t
  deriving DecidableEq, Repr

namespace Letter

/-- The exact mathematical operator of one letter. -/
public def op : Letter → UnitaryOperator (Qubits 1)
  | .h => HOp
  | .s => SOp
  | .t => TOp

/-- One actual literal target instruction on the canonical physical qubit. -/
public def circuit (oracles : OracleModel) :
    Letter → UnitaryCircuit CliffordTGate.model oracles layout
  | .h => .native (GateModel.Application.canonical CliffordTGate.model .hadamard)
  | .s => .native (GateModel.Application.canonical CliffordTGate.model .s)
  | .t => .native (GateModel.Application.canonical CliffordTGate.model .t)

/-- The literal event emitted by the actual target letter. -/
public def event (oracles : OracleModel) :
    Letter → Resource.Event (.quantum CliffordTGate.model oracles)
  | .h => .gate .hadamard
  | .s => .gate .s
  | .t => .gate .t

@[simp] lemma op_h : Letter.h.op = HOp := rfl
@[simp] lemma op_s : Letter.s.op = SOp := rfl
@[simp] lemma op_t : Letter.t.op = TOp := rfl

lemma circuit_matrix (oracles : OracleModel) {environment : oracles.Interpretation}
    (a : Letter) :
    (a.circuit oracles).matrix environment = physicalOperator a.op := by
  cases a
  · exact (UnitaryCircuit.native_matrix environment _).trans
      (GateModel.Application.gateApplication_canonical_operator CliffordTGate.model .hadamard)
  · exact (UnitaryCircuit.native_matrix environment _).trans
      (GateModel.Application.gateApplication_canonical_operator CliffordTGate.model .s)
  · exact (UnitaryCircuit.native_matrix environment _).trans
      (GateModel.Application.gateApplication_canonical_operator CliffordTGate.model .t)

lemma circuit_eventTrace (oracles : OracleModel) (a : Letter) :
    (a.circuit oracles).eventTrace = [a.event oracles] := by cases a <;> rfl

lemma circuit_eventCost (oracles : OracleModel) (a : Letter) :
    (a.circuit oracles).eventCost = ResourcePool.singleton (a.event oracles) := by
  cases a <;> rfl

lemma circuit_unit_event_depth (oracles : OracleModel) (a : Letter) :
    (a.circuit oracles).evaluatedEventDepth (fun _ => 1) = 1 := by cases a <;> rfl

lemma event_injective (oracles : OracleModel) : Function.Injective (event oracles) := by
  intro a b same
  cases a <;> cases b <;> simp_all [event]

lemma event_inj (oracles : OracleModel) (a b : Letter) :
    a.event oracles = b.event oracles ↔ a = b := (event_injective oracles).eq_iff

lemma count_event_circuit (oracles : OracleModel) (a b : Letter) :
    ResourcePool.count (b.event oracles) (a.circuit oracles).eventCost =
      if a = b then 1 else 0 := by
  simp only [circuit_eventCost, ResourcePool.count_singleton, event_inj]

lemma circuit_tCount (oracles : OracleModel) (a : Letter) :
    circuitTCount (a.circuit oracles) = if a = .t then 1 else 0 :=
  count_event_circuit oracles a .t

end Letter

/-- The unitary of a word; the first letter acts first. -/
public def evalOp : List Letter → UnitaryOperator (Qubits 1)
  | [] => 1
  | a :: w => evalOp w * a.op

@[simp] lemma evalOp_nil : evalOp [] = 1 := rfl

@[simp] lemma evalOp_cons (a : Letter) (w : List Letter) :
    evalOp (a :: w) = evalOp w * a.op := rfl

lemma evalOp_singleton (a : Letter) : evalOp [a] = a.op := by
  simp

/-- Concatenation composes in time order: `w₁` acts first. -/
lemma evalOp_append (w₁ w₂ : List Letter) : evalOp (w₁ ++ w₂) = evalOp w₂ * evalOp w₁ := by
  induction w₁ with
  | nil => simp
  | cons a w ih => simp [ih, mul_assoc]

lemma evalOp_replicate (n : Nat) (a : Letter) : evalOp (List.replicate n a) = a.op ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, evalOp_cons, ih, pow_succ a.op n]

/-- Execute a word in time order, retaining its literal strict target model. -/
public def ofWord (oracles : OracleModel) : List Letter →
    UnitaryCircuit CliffordTGate.model oracles layout
  | [] => UnitaryCircuit.identity CliffordTGate.model oracles layout
  | a :: w => (a.circuit oracles).seq (ofWord oracles w)

@[simp] lemma ofWord_nil (oracles : OracleModel) :
    ofWord oracles [] = UnitaryCircuit.identity CliffordTGate.model oracles layout := rfl

@[simp] lemma ofWord_cons (oracles : OracleModel) (a : Letter) (w : List Letter) :
    ofWord oracles (a :: w) = (a.circuit oracles).seq (ofWord oracles w) := rfl

lemma ofWord_matrix (oracles : OracleModel) {environment : oracles.Interpretation}
    (w : List Letter) :
    (ofWord oracles w).matrix environment = physicalOperator (evalOp w) := by
  induction w with
  | nil => exact (UnitaryOperator.unitaryOperator_reindex_one _).symm
  | cons a w ih =>
      rw [ofWord_cons, UnitaryCircuit.seq_matrix, ih, Letter.circuit_matrix, evalOp_cons]
      exact (UnitaryOperator.unitaryOperator_reindex_mul _ _ _).symm

lemma ofWord_eventTrace (oracles : OracleModel) (w : List Letter) :
    (ofWord oracles w).eventTrace = w.map (Letter.event oracles) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [ofWord_cons, UnitaryCircuit.seq_eventTrace, Letter.circuit_eventTrace, ih]
      rfl

lemma ofWord_eventCost (oracles : OracleModel) (w : List Letter) :
    (ofWord oracles w).eventCost = ResourcePool.ofList (w.map (Letter.event oracles)) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, ofWord_eventTrace]

/-- Actual target-event multiplicity equals the corresponding source-letter multiplicity. -/
lemma ofWord_count_event (oracles : OracleModel) (w : List Letter) (b : Letter) :
    ResourcePool.count (b.event oracles) (ofWord oracles w).eventCost = w.count b := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [ofWord_cons, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ih,
        Letter.count_event_circuit, List.count_cons]
      by_cases same : a = b
      · subst b
        simp [add_comm]
      · simp [same]

lemma ofWord_tCount (oracles : OracleModel) (w : List Letter) :
    circuitTCount (ofWord oracles w) = w.count .t := ofWord_count_event oracles w .t

lemma ofWord_unit_event_depth (oracles : OracleModel) (w : List Letter) :
    (ofWord oracles w).evaluatedEventDepth (fun _ => 1) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [ofWord_cons, UnitaryCircuit.evaluatedEventDepth_seq,
        Letter.circuit_unit_event_depth, ih, List.length_cons, Nat.add_comm]

lemma ofWord_eventDepth_le (oracles : OracleModel) (w : List Letter) :
    (ofWord oracles w).evaluatedEventDepth (fun _ => 1) ≤ w.length :=
  (ofWord_unit_event_depth oracles w).le

/-- A word whose unitary is within operator-norm distance `ε` of the standard
Z-rotation `rotZStdOp θ`, with no global-phase slack. -/
public structure RotationCertificate (θ ε : ℝ) where
  /-- The Clifford+T word, first letter acting first. -/
  word : List Letter
  /-- The operator-norm closeness bound. -/
  close :
    HilbertOperator.opNorm
      ((evalOp word : HilbertOperator (Qubits 1)) - (rotZStdOp θ : HilbertOperator (Qubits 1))) ≤ ε

namespace RotationCertificate

variable {θ ε : ℝ}

/-- The actual strict target word has the certificate's unchanged exact-phase error bound. -/
public def toApproxRealization (c : RotationCertificate θ ε) (oracles : OracleModel) :
    UnitaryCircuit.ApproxRealization CliffordTGate.model oracles layout
      (fun _ => physicalOperator (rotZStdOp θ)) ε where
  circuit := ofWord oracles c.word
  error_le := by
    intro environment
    rw [ofWord_matrix]
    exact (HilbertOperator.opNorm_reindex_sub
      (QuantumSignature.qubitsIndexEquiv 1).symm (evalOp c.word) (rotZStdOp θ)).le.trans c.close

lemma toApproxRealization_circuit (c : RotationCertificate θ ε) (oracles : OracleModel) :
    (c.toApproxRealization oracles).circuit = ofWord oracles c.word := rfl

/-- Count actual T letters in the certified word. -/
public def tCount (c : RotationCertificate θ ε) : Nat := c.word.count .t

lemma toApproxRealization_tCount (c : RotationCertificate θ ε) (oracles : OracleModel) :
    circuitTCount (c.toApproxRealization oracles).circuit = c.tCount :=
  ofWord_tCount oracles c.word

/-- Any bound at least as large is also a valid bound. -/
public def weaken (c : RotationCertificate θ ε) {ε' : ℝ} (h : ε ≤ ε') : RotationCertificate θ ε' :=
  ⟨c.word, c.close.trans h⟩

@[simp]
lemma weaken_word (c : RotationCertificate θ ε) {ε' : ℝ} (h : ε ≤ ε') :
    (c.weaken h).word = c.word := rfl

/-- An exact word is a zero-error certificate. -/
public def exact (w : List Letter) (h : evalOp w = rotZStdOp θ) : RotationCertificate θ 0 :=
  ⟨w, by rw [h, sub_self, HilbertOperator.opNorm_zero]⟩

@[simp]
lemma exact_word (w : List Letter) (h : evalOp w = rotZStdOp θ) : (exact w h).word = w := rfl

/-- A zero-error certificate realizes `rotZStdOp θ` exactly. -/
public def toExactRealization (c : RotationCertificate θ 0) (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization CliffordTGate.model oracles layout
      (fun _ => physicalOperator (rotZStdOp θ)) :=
  (c.toApproxRealization oracles).toExact

lemma evalOp_eq_of_zero (c : RotationCertificate θ 0) : evalOp c.word = rotZStdOp θ := by
  apply Subtype.ext
  have h0 : HilbertOperator.opNorm
      ((evalOp c.word : HilbertOperator (Qubits 1)) - (rotZStdOp θ : HilbertOperator (Qubits 1))) =
        0 :=
    le_antisymm c.close (HilbertOperator.opNorm_nonneg _)
  exact sub_eq_zero.mp (HilbertOperator.opNorm_eq_zero_iff.mp h0)

end RotationCertificate

/-! ## Concrete exact certificates

The empty word, `S^4`, and `T^8` are exact-phase words for the trivial
rotation `rotZStdOp 0 = 1`. Exact words for nontrivial angles such as
`rotZStdOp π = -i • Z` need the scalar identity `(S H)^3 = e^{iπ/4} • 1`, which
is part of the Clifford+T identity library rather than this interface. -/

/-- The empty word realizes `rotZStdOp 0` exactly. -/
public def RotationCertificate.nil : RotationCertificate 0 0 :=
  RotationCertificate.exact [] (by simp)

/-- `S^4 = 1` realizes `rotZStdOp 0` exactly. -/
public def RotationCertificate.sPowFour : RotationCertificate 0 0 :=
  RotationCertificate.exact (List.replicate 4 .s)
    (by rw [evalOp_replicate, Letter.op_s, SOp_pow_four, rotZStdOp_zero])

/-- `T^8 = 1` realizes `rotZStdOp 0` exactly, with T-count `8`. -/
public def RotationCertificate.tPowEight : RotationCertificate 0 0 :=
  RotationCertificate.exact (List.replicate 8 .t)
    (by rw [evalOp_replicate, Letter.op_t, TOp_pow_eight, rotZStdOp_zero])

lemma RotationCertificate.tPowEight_tCount : RotationCertificate.tPowEight.tCount = 8 := by
  decide

lemma RotationCertificate.sPowFour_tCount : RotationCertificate.sPowFour.tCount = 0 := by
  decide

end

end QuantumAlg.CliffordT
