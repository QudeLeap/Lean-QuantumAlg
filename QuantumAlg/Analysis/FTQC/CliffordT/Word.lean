/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.Gate.OperatorNorm
public import QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates

/-!
# Single-qubit Clifford+T words

A word over the alphabet `{H, S, T}` denotes both a unitary (`evalOp`) and a
circuit (`ofWord`), with the first letter acting first:
`evalOp (a :: w) = evalOp w * a.op`. The circuit's T-count is the number of
`t` letters.

`RotationCertificate θ ε` records a word whose unitary is within operator-norm
distance `ε` of the standard Z-rotation `rotZStdOp θ = diag(e^{-iθ/2}, e^{iθ/2})`,
with no global-phase slack. The Clifford+T matrix group contains every scalar
`e^{ikπ/4}` (`(S H)^3 = e^{iπ/4} · 1`), so an approximation that is only
correct up to such a phase can always be completed to an exact-phase word; in
particular gridsynth-style outputs are representable as certificates. The
one-branch phase gate is `phaseGateOp θ = e^{iθ/2} • rotZStdOp θ`, so phase
gates and controlled phases reduce to exact-phase Z-rotations.

Certificates are the interface between rotation synthesis (which produces
words) and circuit compilation (which consumes `ApproxRealization`s and
T-counts). Checking a certificate and proving Clifford+T identities are
separate concerns.
-/

section

namespace QuantumAlg.CliffordT

open Gate

noncomputable section

/-- A letter of the single-qubit Clifford+T alphabet. -/
public inductive Letter where
  | h
  | s
  | t
  deriving DecidableEq, Repr

namespace Letter

/-- The unitary of one letter. -/
public def op : Letter → UnitaryOperator (Qubits 1)
  | .h => HOp
  | .s => SOp
  | .t => TOp

/-- The one-gate circuit of one letter, on the canonical placement `[0]`. -/
public def circuit : Letter → UnitaryCircuit (Qubits 1)
  | .h => H
  | .s => S
  | .t => T

/-- The strict event of one letter. -/
public def event : Letter → Resource.Event .quantum
  | .h => atomicEvent (.builtin "hadamard")
  | .s => atomicEvent (.builtin "s")
  | .t => tEvent

@[simp] theorem op_h : Letter.h.op = HOp := rfl
@[simp] theorem op_s : Letter.s.op = SOp := rfl
@[simp] theorem op_t : Letter.t.op = TOp := rfl

@[simp] theorem circuit_h : Letter.h.circuit = H := rfl
@[simp] theorem circuit_s : Letter.s.circuit = S := rfl
@[simp] theorem circuit_t : Letter.t.circuit = T := rfl

@[simp] theorem event_t : Letter.t.event = tEvent := rfl

@[simp]
theorem circuit_matrix (a : Letter) : a.circuit.matrix = a.op := by
  cases a <;> rfl

@[simp]
theorem circuit_physical_idx (a : Letter) : a.circuit.physical_idx = [0] := by
  cases a <;> rfl

@[simp]
theorem circuit_eventTrace (a : Letter) : a.circuit.eventTrace = [a.event] := by
  cases a <;> rfl

@[simp]
theorem circuit_eventCost (a : Letter) : a.circuit.eventCost = ResourcePool.singleton a.event := by
  cases a <;> rfl

@[simp]
theorem circuit_unit_event_depth (a : Letter) :
    a.circuit.evaluatedEventDepth (fun _ => 1) = 1 := by
  cases a <;> rfl

theorem event_injective : Function.Injective Letter.event := by
  intro a b hab
  cases a <;> cases b <;> first | rfl | exact absurd hab (by decide)

@[simp]
theorem event_inj (a b : Letter) : a.event = b.event ↔ a = b :=
  event_injective.eq_iff

/-- Not a simp lemma: `simp` already reaches the right-hand side through
`circuit_eventCost`, `ResourcePool.count_singleton`, and `event_inj`. -/
theorem count_event_circuit (a b : Letter) :
    ResourcePool.count b.event a.circuit.eventCost = if a = b then 1 else 0 := by
  rw [circuit_eventCost, ResourcePool.count_singleton]
  simp

@[simp]
theorem circuit_tCount (a : Letter) : a.circuit.tCount = if a = .t then 1 else 0 :=
  count_event_circuit a .t

end Letter

/-! ## Words -/

/-- The unitary of a word; the first letter acts first. -/
public def evalOp : List Letter → UnitaryOperator (Qubits 1)
  | [] => 1
  | a :: w => evalOp w * a.op

@[simp] theorem evalOp_nil : evalOp [] = 1 := rfl

@[simp] theorem evalOp_cons (a : Letter) (w : List Letter) :
    evalOp (a :: w) = evalOp w * a.op := rfl

theorem evalOp_singleton (a : Letter) : evalOp [a] = a.op := by
  simp

/-- Concatenation composes in time order: `w₁` acts first. -/
theorem evalOp_append (w₁ w₂ : List Letter) : evalOp (w₁ ++ w₂) = evalOp w₂ * evalOp w₁ := by
  induction w₁ with
  | nil => simp
  | cons a w ih => simp [ih, mul_assoc]

theorem evalOp_replicate (n : Nat) (a : Letter) : evalOp (List.replicate n a) = a.op ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, evalOp_cons, ih, pow_succ a.op n]

/-- The circuit of a word: letters sequenced in time order on the canonical
placement `[0]`. -/
public def ofWord : List Letter → UnitaryCircuit (Qubits 1)
  | [] => UnitaryCircuit.identity (Qubits 1) [0] (by simp)
  | a :: w => UnitaryCircuit.seq a.circuit (ofWord w)

@[simp] theorem ofWord_nil : ofWord [] = UnitaryCircuit.identity (Qubits 1) [0] (by simp) := rfl

@[simp] theorem ofWord_cons (a : Letter) (w : List Letter) :
    ofWord (a :: w) = UnitaryCircuit.seq a.circuit (ofWord w) := rfl

@[simp]
theorem ofWord_matrix (w : List Letter) : (ofWord w).matrix = evalOp w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      apply Subtype.ext
      rw [ofWord_cons, UnitaryCircuit.seq_matrix, ih, Letter.circuit_matrix, evalOp_cons]
      rfl

@[simp]
theorem ofWord_eventTrace (w : List Letter) : (ofWord w).eventTrace = w.map Letter.event := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

theorem ofWord_eventCost (w : List Letter) :
    (ofWord w).eventCost = ResourcePool.ofList (w.map Letter.event) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, ofWord_eventTrace]

/-- The number of occurrences of a letter's event is the letter count. -/
theorem ofWord_count_event (w : List Letter) (b : Letter) :
    ResourcePool.count b.event (ofWord w).eventCost = w.count b := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [ofWord_cons, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ih,
        Letter.count_event_circuit, List.count_cons]
      by_cases hab : a = b
      · subst hab
        simp [add_comm]
      · simp [hab]

@[simp]
theorem ofWord_tCount (w : List Letter) : (ofWord w).tCount = w.count .t :=
  ofWord_count_event w .t

theorem ofWord_unit_event_depth (w : List Letter) :
    (ofWord w).evaluatedEventDepth (fun _ => 1) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih, add_comm]

theorem ofWord_eventDepth_le (w : List Letter) :
    (ofWord w).evaluatedEventDepth (fun _ => 1) ≤ w.length :=
  (ofWord_unit_event_depth w).le

/-! ## Rotation certificates -/

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

/-- The certified circuit as an approximate realization of `rotZStdOp θ`. -/
public def toApproxRealization (c : RotationCertificate θ ε) :
    UnitaryCircuit.ApproxRealization (rotZStdOp θ) ε where
  circuit := ofWord c.word
  error_le := by
    rw [ofWord_matrix]
    exact c.close

@[simp]
theorem toApproxRealization_circuit (c : RotationCertificate θ ε) :
    c.toApproxRealization.circuit = ofWord c.word := rfl

/-- The T-count of the certified word. -/
public def tCount (c : RotationCertificate θ ε) : Nat :=
  c.word.count .t

theorem toApproxRealization_tCount (c : RotationCertificate θ ε) :
    c.toApproxRealization.circuit.tCount = c.tCount :=
  ofWord_tCount c.word

/-- Any bound at least as large is also a valid bound. -/
public def weaken (c : RotationCertificate θ ε) {ε' : ℝ} (h : ε ≤ ε') : RotationCertificate θ ε' :=
  ⟨c.word, c.close.trans h⟩

@[simp]
theorem weaken_word (c : RotationCertificate θ ε) {ε' : ℝ} (h : ε ≤ ε') :
    (c.weaken h).word = c.word := rfl

/-- An exact word is a zero-error certificate. -/
public def exact (w : List Letter) (h : evalOp w = rotZStdOp θ) : RotationCertificate θ 0 :=
  ⟨w, by rw [h, sub_self, HilbertOperator.opNorm_zero]⟩

@[simp]
theorem exact_word (w : List Letter) (h : evalOp w = rotZStdOp θ) : (exact w h).word = w := rfl

/-- A zero-error certificate realizes `rotZStdOp θ` exactly. -/
public def toExactRealization (c : RotationCertificate θ 0) :
    UnitaryCircuit.ExactRealization (rotZStdOp θ) :=
  c.toApproxRealization.toExact

theorem evalOp_eq_of_zero (c : RotationCertificate θ 0) : evalOp c.word = rotZStdOp θ := by
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

theorem RotationCertificate.tPowEight_tCount : RotationCertificate.tPowEight.tCount = 8 := by
  decide

theorem RotationCertificate.sPowFour_tCount : RotationCertificate.sPowFour.tCount = 0 := by
  decide

end

end QuantumAlg.CliffordT

end
