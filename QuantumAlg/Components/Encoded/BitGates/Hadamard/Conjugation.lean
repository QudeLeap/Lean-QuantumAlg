/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import Mathlib.Tactic.Ring

/-!
# Exact Hadamard conjugation of an actual conditional bit flip

This is the shared linear-algebra proof for literal H, program, H sequences.
Its premise concerns the complete encoded-ket action of that same program;
the circuit, event trace and physical gates are never recovered from a
predicate or a resource witness. Small elementary gates and restored-work
MCX constructions can therefore use the same exact-phase proof.
-/

namespace QuantumAlg.EncodedBit

open NormalizedVector

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  (layout : QubitLayout encoding.width) (oracles : OracleModel)

/-- The literal addressed H, actual program, addressed H sequence. -/
def conjugateHadamard (target : EncodedBit encoding)
    (program : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum) :
    UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  ((target.hadamard layout oracles).seq program).seq (target.hadamard layout oracles)

/-- Conjugating an actual conditional target flip gives its exact conditional phase. -/
theorem conjugateHadamard_applyVec_encoded_ket (target : EncodedBit encoding)
    (program : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum)
    (predicate : Data → Prop) [DecidablePred predicate]
    (unchanged : ∀ state, predicate (target.flip state) ↔ predicate state)
    (actual : ∀ state, program.applyVec
        (ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      if predicate state then
        (ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode (target.flip state)))).vec
      else (ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec)
    (state : Data) :
    (target.conjugateHadamard layout oracles program).applyVec
        (ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      if predicate state ∧ target.get state = true then
        -(ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec
      else (ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  simp only [conjugateHadamard, UnitaryCircuit.applyVec_seq]
  rw [hadamard_applyVec_encoded_ket]
  simp only [UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_add]
  rw [actual state, actual (target.flip state)]
  simp only [unchanged]
  by_cases active : predicate state
  <;> simp only [active, if_true, if_false, true_and, false_and, flip_flip]
  all_goals
    rw [hadamard_applyVec_encoded_ket target layout oracles state,
      hadamard_applyVec_encoded_ket target layout oracles (target.flip state)]
    simp only [get_flip_self, flip_flip]
    cases target.get state
    <;> simp only [Bool.not, Bool.false_eq_true, if_true, if_false]
    <;> ext index
    <;> simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    <;> ring_nf
    <;> norm_num [invSqrt2_sq]

/-- The same literal construction adds exactly its two existing Hadamard occurrences. -/
theorem conjugateHadamard_eventTrace (target : EncodedBit encoding)
    (program : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum) :
    (target.conjugateHadamard layout oracles program).eventTrace =
      [.gate .singleQubit] ++ program.eventTrace ++
        [.gate .singleQubit] := by
  simp only [conjugateHadamard, UnitaryCircuit.seq_eventTrace, hadamard_eventTrace]

end

end QuantumAlg.EncodedBit
