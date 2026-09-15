/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Physical query geometry and mathematical Walsh-Hadamard readout

The n query wires precede the target wire, and their values have the same
explicit big-endian encoding in both the physical and binary descriptions.
The readout and evolved-state descriptions are mathematical observations;
the actual preparation, writes and output live in the separate execution
owners. This geometry supports the common query circuit described in
[dW19, qcnotes.tex:1193,1288].
-/

namespace QuantumAlg.WalshHadamard.Readout

open NormalizedVector Gate

noncomputable section

variable {n : Nat}

/-- Canonical physical placement of the `n` input qubits and one target
qubit. -/
def layout (n : ℕ) : QubitLayout (n + 1) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp] theorem layout_systemIdx (n : ℕ) :
    (layout n).systemIdx = List.range (n + 1) := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]
  simpa [Nat.succ_eq_add_one] using
    (List.range_succ_eq_map (n := n)).symm

/-- Canonically placed normalized input `|0^n⟩|1⟩`. -/
def inputState (n : ℕ) : QubitLayout.State (layout n) where
  state := PureState.ofNormalized (WalshHadamard.input n)
    (layout n).systemIdx
  system_idx_eq := rfl

/-- Select the first `n` logical qubits and leave the target qubit unmeasured. -/
def measurement (n : ℕ) : TerminalZMeasure (layout n) n :=
  zMeasureAt (layout n)
    (fun index => ⟨index.val, Nat.lt_add_right 1 index.isLt⟩)
    (fun _ _ h => Fin.ext (Fin.mk.inj h))

/-- Big-endian terminal outcome corresponding to one input-register label. -/
def measurementOutcome (n : ℕ) (value : Fin (2 ^ n)) :
    TerminalZMeasure.Outcome n :=
  fun outputIndex => value.val.testBit (n - 1 - outputIndex.val)

theorem measurementOutcome_injective (n : ℕ) :
    Function.Injective (measurementOutcome n) := by
  intro left right h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < n
  · let outputIndex : Fin n := ⟨n - 1 - bit, by omega⟩
    have hreverse : n - 1 - outputIndex.val = bit := by
      dsimp [outputIndex]
      omega
    have hout := congrFun h outputIndex
    simpa [measurementOutcome, hreverse] using hout
  · have hnbit : n ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ n ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hnbit
    rw [Nat.testBit_lt_two_pow (left.isLt.trans_le hpow),
      Nat.testBit_lt_two_pow (right.isLt.trans_le hpow)]

@[simp] theorem measurement_readout_prod (value : Fin (2 ^ n))
    (target : Fin (2 ^ 1)) :
    (measurement n).readout (prodEquiv (value, target)) =
      measurementOutcome n value := by
  funext outputIndex
  change (prodEquiv (value, target)).val.testBit
      (n + 1 - 1 - outputIndex.val) =
    value.val.testBit (n - 1 - outputIndex.val)
  have hindex :
      n + 1 - 1 - outputIndex.val = 1 + (n - 1 - outputIndex.val) := by
    omega
  rw [hindex]
  exact prodEquiv_testBit_left value target
    ⟨n - 1 - outputIndex.val, by omega⟩

theorem measurement_readout_eq_outcome_iff
    (basis : Fin (2 ^ (n + 1))) (value : Fin (2 ^ n)) :
    (measurement n).readout basis = measurementOutcome n value ↔
      (prodEquiv.symm basis).1 = value := by
  have hself :
      (measurement n).readout basis =
        measurementOutcome n (prodEquiv.symm basis).1 := by
    simpa using measurement_readout_prod
      (n := n) (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact measurementOutcome_injective n (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (measurementOutcome n) h)

/-- The shared Walsh-Hadamard circuit has the canonical layout used by the
terminal measurement descriptor. -/
theorem circuit_physical_idx (f : Oracle n) :
    (WalshHadamard.circuit f).physical_idx = (layout n).systemIdx := by
  rw [WalshHadamard.circuit_physical_idx, layout_systemIdx]

/-- Evolve the canonical input by the very circuit whose resources are later
projected. -/
def evolvedState (circuit : UnitaryCircuit (Qubits (n + 1)))
    (circuit_layout : circuit.physical_idx = (layout n).systemIdx) :
    QubitLayout.State (layout n) :=
  { state := PureState.ofNormalized
      (UnitaryCircuit.applyNormalized circuit (WalshHadamard.input n))
      circuit.physical_idx
    system_idx_eq := circuit_layout }

/-- The terminally measured normalized state is exactly the vector produced by
the same circuit witness. -/
@[simp] theorem evolvedState_normalized_coe
    (circuit : UnitaryCircuit (Qubits (n + 1)))
    (circuit_layout : circuit.physical_idx = (layout n).systemIdx) :
    (evolvedState circuit circuit_layout).state.state.vec =
      UnitaryCircuit.applyVec circuit
        (WalshHadamard.input n : HilbertVector (Qubits (n + 1))) := rfl

end

end QuantumAlg.WalshHadamard.Readout
