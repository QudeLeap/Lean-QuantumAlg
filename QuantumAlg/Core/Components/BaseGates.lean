/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Core.Components.Gates

/-!
# Toffoli/CNOT/X circuit atoms

This module exposes the reversible classical gate family used by the
arithmetic-circuit resource route: X, CNOT, and Toffoli/CCNOT atoms.  The
Toffoli gate is the controlled-controlled-NOT gate and is the standard
reversible classical primitive [dW19, qcnotes.tex:984-988].
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

/-- Names of the base reversible classical atoms accepted by the MAU
same-Circuit audit. -/
def CircuitHistory.IsBaseGateAtomName (name : String) : Prop :=
  name = "x" ∨ name = "cnot" ∨ name = "toffoli"

namespace CircuitHistory

/-- A circuit history whose leaves are only X, CNOT, and Toffoli atoms.  This is
the mechanical audit predicate used before an arithmetic witness may be treated
as bottoming out in the selected reversible gate family. -/
def IsBaseGateStructured : CircuitHistory → Prop
  | id => True
  | atom name => IsBaseGateAtomName name
  | seq left right => left.IsBaseGateStructured ∧ right.IsBaseGateStructured
  | tensor left right => left.IsBaseGateStructured ∧ right.IsBaseGateStructured
  | inverse body => body.IsBaseGateStructured
  | controlled _ body => body.IsBaseGateStructured
  | iterate _ body => body.IsBaseGateStructured
  | indexedProduct _ _ start step =>
      start.IsBaseGateStructured ∧ ∀ j, (step j).IsBaseGateStructured

@[simp] theorem isBaseGateStructured_id :
    CircuitHistory.id.IsBaseGateStructured := by
  trivial

@[simp] theorem isBaseGateStructured_atom (name : String) :
    (CircuitHistory.atom name).IsBaseGateStructured = IsBaseGateAtomName name :=
  rfl

@[simp] theorem isBaseGateStructured_seq (left right : CircuitHistory) :
    (CircuitHistory.seq left right).IsBaseGateStructured =
      (left.IsBaseGateStructured ∧ right.IsBaseGateStructured) :=
  rfl

@[simp] theorem isBaseGateStructured_tensor (left right : CircuitHistory) :
    (CircuitHistory.tensor left right).IsBaseGateStructured =
      (left.IsBaseGateStructured ∧ right.IsBaseGateStructured) :=
  rfl

@[simp] theorem isBaseGateStructured_inverse (body : CircuitHistory) :
    (CircuitHistory.inverse body).IsBaseGateStructured =
      body.IsBaseGateStructured :=
  rfl

@[simp] theorem isBaseGateStructured_controlled (controlLabel : String)
    (body : CircuitHistory) :
    (CircuitHistory.controlled controlLabel body).IsBaseGateStructured =
      body.IsBaseGateStructured :=
  rfl

@[simp] theorem isBaseGateStructured_iterate (count : Nat)
    (body : CircuitHistory) :
    (CircuitHistory.iterate count body).IsBaseGateStructured =
      body.IsBaseGateStructured :=
  rfl

@[simp] theorem isBaseGateStructured_indexedProduct (label : String)
    (count : Nat) (start : CircuitHistory) (step : Fin count → CircuitHistory) :
    (CircuitHistory.indexedProduct label count start step).IsBaseGateStructured =
      (start.IsBaseGateStructured ∧ ∀ j, (step j).IsBaseGateStructured) :=
  rfl

@[simp] theorem isBaseGateAtomName_x : IsBaseGateAtomName "x" := Or.inl rfl

@[simp] theorem isBaseGateAtomName_cnot : IsBaseGateAtomName "cnot" :=
  Or.inr (Or.inl rfl)

@[simp] theorem isBaseGateAtomName_toffoli : IsBaseGateAtomName "toffoli" :=
  Or.inr (Or.inr rfl)

@[simp] theorem not_isBaseGateAtomName_endpoint :
    ¬ IsBaseGateAtomName "endpoint" := by
  simp [IsBaseGateAtomName]

end CircuitHistory

/-! ## Wire-addressed basis permutations -/

namespace WireAddress

/-- Big-endian wire index used by the named qubit gates in this library:
wire `0` is the most significant basis bit of a `Qubits n` label. -/
def bitIndex {n : Nat} (wire : Fin n) : Fin n :=
  ⟨n - 1 - wire.val, by omega⟩

theorem bitIndex_injective {n : Nat} : Function.Injective (bitIndex (n := n)) := by
  intro left right h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [bitIndex] at hv
  omega

/-- Convert a little-endian bit index (`0` is the least significant bit) to the
library's big-endian wire index (`0` is the most significant wire). -/
def littleEndianWire {n : Nat} (bit : Fin n) : Fin n :=
  bitIndex bit

@[simp] theorem bitIndex_littleEndianWire {n : Nat} (bit : Fin n) :
    bitIndex (littleEndianWire bit) = bit := by
  apply Fin.ext
  dsimp [bitIndex, littleEndianWire]
  omega

@[simp] theorem littleEndianWire_bitIndex {n : Nat} (wire : Fin n) :
    littleEndianWire (bitIndex wire) = wire := by
  apply Fin.ext
  dsimp [bitIndex, littleEndianWire]
  omega

/-- Flip one addressed wire of a computational-basis label. -/
def flipBit {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ (bitIndex target).val,
    Nat.xor_lt_two_pow x.isLt
      (Nat.pow_lt_pow_right one_lt_two (bitIndex target).isLt)⟩

theorem bit_flipBit {n : Nat} (target bit : Fin n) (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex bit).val =
      (x.val.testBit (bitIndex bit).val ^^ decide (target = bit)) := by
  change (x.val ^^^ 2 ^ (bitIndex target).val).testBit (bitIndex bit).val =
    (x.val.testBit (bitIndex bit).val ^^ decide (target = bit))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact ⟨fun h => bitIndex_injective (Fin.val_injective h), fun h => by cases h; rfl⟩

theorem bit_flipBit_self {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex target).val =
      !x.val.testBit (bitIndex target).val := by
  simp [bit_flipBit]

theorem bit_flipBit_of_ne {n : Nat} {target bit : Fin n} (hne : target ≠ bit)
    (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex bit).val =
      x.val.testBit (bitIndex bit).val := by
  simp [bit_flipBit, hne]

theorem flipBit_flipBit {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    flipBit target (flipBit target x) = x := by
  unfold flipBit
  ext
  simp [Nat.xor_assoc]

/-- Flips of two addressed wires commute on computational-basis labels. -/
theorem flipBit_comm {n : Nat} (left right : Fin n) (x : Fin (2 ^ n)) :
    flipBit left (flipBit right x) =
      flipBit right (flipBit left x) := by
  unfold flipBit
  ext
  change
    (x.val ^^^ 2 ^ (bitIndex right).val) ^^^ 2 ^ (bitIndex left).val =
      (x.val ^^^ 2 ^ (bitIndex left).val) ^^^ 2 ^ (bitIndex right).val
  rw [Nat.xor_assoc, Nat.xor_assoc]
  rw [Nat.xor_comm (2 ^ (bitIndex right).val) (2 ^ (bitIndex left).val)]

/-- Addressed X/NOT action on computational-basis labels. -/
def xMap {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  flipBit target x

/-- Addressed X/NOT basis-label permutation. -/
def xPerm {n : Nat} (target : Fin n) : Equiv.Perm (Fin (2 ^ n)) where
  toFun := xMap target
  invFun := xMap target
  left_inv := flipBit_flipBit target
  right_inv := flipBit_flipBit target

/-- Addressed CNOT action on computational-basis labels. -/
def cnotMap {n : Nat} (control target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if x.val.testBit (bitIndex control).val then flipBit target x else x

theorem cnotMap_cnotMap {n : Nat} {control target : Fin n} (hct : control ≠ target)
    (x : Fin (2 ^ n)) :
    cnotMap control target (cnotMap control target x) = x := by
  unfold cnotMap
  by_cases hc : x.val.testBit (bitIndex control).val
  · simp [hc, bit_flipBit_of_ne (target := target) (bit := control) (Ne.symm hct),
      flipBit_flipBit]
  · simp [hc]

/-- Addressed CNOT basis-label permutation. -/
def cnotPerm {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := cnotMap control target
  invFun := cnotMap control target
  left_inv := cnotMap_cnotMap hct
  right_inv := cnotMap_cnotMap hct

/-- Addressed Toffoli/CCNOT action on computational-basis labels. -/
def toffoliMap {n : Nat} (controlA controlB target : Fin n) (x : Fin (2 ^ n)) :
    Fin (2 ^ n) :=
  if x.val.testBit (bitIndex controlA).val && x.val.testBit (bitIndex controlB).val then
    flipBit target x
  else
    x

theorem toffoliMap_toffoliMap {n : Nat} {controlA controlB target : Fin n}
    (ha : controlA ≠ target) (hb : controlB ≠ target) (x : Fin (2 ^ n)) :
    toffoliMap controlA controlB target
      (toffoliMap controlA controlB target x) = x := by
  unfold toffoliMap
  by_cases hgate :
      x.val.testBit (bitIndex controlA).val && x.val.testBit (bitIndex controlB).val
  · have haBit :
        (flipBit target x).val.testBit (bitIndex controlA).val =
          x.val.testBit (bitIndex controlA).val := by
        exact bit_flipBit_of_ne (target := target) (bit := controlA) (Ne.symm ha) x
    have hbBit :
        (flipBit target x).val.testBit (bitIndex controlB).val =
          x.val.testBit (bitIndex controlB).val := by
        exact bit_flipBit_of_ne (target := target) (bit := controlB) (Ne.symm hb) x
    simp [hgate, haBit, hbBit, flipBit_flipBit]
  · simp [hgate]

/-- Addressed Toffoli/CCNOT basis-label permutation. -/
@[nolint unusedArguments]
def toffoliPerm {n : Nat} (controlA controlB target : Fin n)
    (_hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := toffoliMap controlA controlB target
  invFun := toffoliMap controlA controlB target
  left_inv := toffoliMap_toffoliMap ha hb
  right_inv := toffoliMap_toffoliMap ha hb

end WireAddress

namespace Gate

/-! ## Toffoli gate -/

/-- The Toffoli gate on three qubits, with qubits 0 and 1 controlling qubit 2. -/
def Toffoli : Gate (Qubits 3) :=
  ofPerm (Equiv.swap 6 7)

/-- The Toffoli gate is unitary by construction as a permutation gate. -/
theorem Toffoli_mem_unitaryGroup :
    (Toffoli : HilbertOperator (Qubits 3)) ∈
      Matrix.unitaryGroup (Fin (2 ^ 3)) ℂ :=
  Toffoli.unitary

/-- `Toffoli` swaps `|110>` and `|111>` and fixes the other basis states. -/
theorem Toffoli_apply_ket (x : Fin (2 ^ 3)) :
    Toffoli.apply (PureState.ket x) =
      PureState.ket (R := Qubits 3) (Equiv.swap (6 : Fin (2 ^ 3)) 7 x) := by
  rw [Toffoli, ofPerm_apply_ket, Equiv.swap_inv]

/-- Addressed X/NOT gate on an `n`-qubit register. -/
def xOn {n : Nat} (target : Fin n) : Gate (Qubits n) :=
  ofPerm (WireAddress.xPerm target)

/-- Addressed CNOT gate on an `n`-qubit register. -/
def cnotOn {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    Gate (Qubits n) :=
  ofPerm (WireAddress.cnotPerm control target hct)

/-- Addressed Toffoli/CCNOT gate on an `n`-qubit register. -/
def toffoliOn {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    Gate (Qubits n) :=
  ofPerm (WireAddress.toffoliPerm controlA controlB target hab ha hb)

/-- Addressed X/NOT acts by flipping exactly the selected basis-label wire. -/
theorem xOn_apply_ket {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    (xOn target).apply (PureState.ket x) =
      PureState.ket (R := Qubits n) (WireAddress.flipBit target x) := by
  rw [xOn, ofPerm_apply_ket]
  rfl

/-- Addressed CNOT acts by the corresponding controlled basis-label flip. -/
theorem cnotOn_apply_ket {n : Nat} (control target : Fin n)
    (hct : control ≠ target) (x : Fin (2 ^ n)) :
    (cnotOn control target hct).apply (PureState.ket x) =
      PureState.ket (R := Qubits n) (WireAddress.cnotMap control target x) := by
  rw [cnotOn, ofPerm_apply_ket]
  rfl

/-- Addressed Toffoli/CCNOT acts by the corresponding double-controlled
basis-label flip. -/
theorem toffoliOn_apply_ket {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target)
    (x : Fin (2 ^ n)) :
    (toffoliOn controlA controlB target hab ha hb).apply (PureState.ket x) =
      PureState.ket (R := Qubits n)
        (WireAddress.toffoliMap controlA controlB target x) := by
  rw [toffoliOn, ofPerm_apply_ket]
  rfl

end Gate

/-! ## Base-gate resource profiles -/

namespace BaseGateProfile

/-- Resource profile for one X/NOT atom in the MAU gate-family model. -/
def x : ModularArithmeticResourceProfile where
  logicalQubits := 1
  dataQubits := 1
  workQubits := 0
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := 0
  tGates := 0
  cnotGates := 0
  singleQubitGates := 1
  circuitDepth := 1
  toffoliDepth := 0
  classicalArithmetic := ClassicalArithmeticProfile.zero

/-- Resource profile for one CNOT atom in the MAU gate-family model. -/
def cnot : ModularArithmeticResourceProfile where
  logicalQubits := 2
  dataQubits := 2
  workQubits := 0
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := 0
  tGates := 0
  cnotGates := 1
  singleQubitGates := 0
  circuitDepth := 1
  toffoliDepth := 0
  classicalArithmetic := ClassicalArithmeticProfile.zero

/-- Resource profile for one Toffoli atom in the MAU gate-family model. -/
def toffoli : ModularArithmeticResourceProfile where
  logicalQubits := 3
  dataQubits := 3
  workQubits := 0
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := 1
  tGates := 0
  cnotGates := 0
  singleQubitGates := 0
  circuitDepth := 1
  toffoliDepth := 1
  classicalArithmetic := ClassicalArithmeticProfile.zero

/-- Resource profile for one addressed X/NOT atom on an `n`-qubit register. -/
def xOn (n : Nat) : ModularArithmeticResourceProfile :=
  { x with logicalQubits := n, dataQubits := n }

/-- Resource profile for one addressed CNOT atom on an `n`-qubit register. -/
def cnotOn (n : Nat) : ModularArithmeticResourceProfile :=
  { cnot with logicalQubits := n, dataQubits := n }

/-- Resource profile for one addressed Toffoli atom on an `n`-qubit register. -/
def toffoliOn (n : Nat) : ModularArithmeticResourceProfile :=
  { toffoli with logicalQubits := n, dataQubits := n }

@[simp] theorem x_elementaryGateCount :
    x.elementaryGateCount = 1 :=
  rfl

@[simp] theorem cnot_elementaryGateCount :
    cnot.elementaryGateCount = 1 :=
  rfl

@[simp] theorem toffoli_elementaryGateCount :
    toffoli.elementaryGateCount = 1 :=
  rfl

@[simp] theorem xOn_elementaryGateCount (n : Nat) :
    (xOn n).elementaryGateCount = 1 :=
  rfl

@[simp] theorem cnotOn_elementaryGateCount (n : Nat) :
    (cnotOn n).elementaryGateCount = 1 :=
  rfl

@[simp] theorem toffoliOn_elementaryGateCount (n : Nat) :
    (toffoliOn n).elementaryGateCount = 1 :=
  rfl

end BaseGateProfile

namespace Circuit

/-! ## Base-gate circuit atoms -/

/-- One X/NOT atom as a typed circuit. -/
def xAtom : Circuit (Qubits 1) :=
  Circuit.atom "x" (Gate.X : HilbertOperator (Qubits 1)) Gate.X.unitary
    BaseGateProfile.x.toResourceProfile BaseGateProfile.x.circuitDepth
    BaseGateProfile.x.oracleQueries

/-- One CNOT atom as a typed circuit. -/
def cnotAtom : Circuit (Qubits 2) :=
  Circuit.atom "cnot" (Gate.CNOT : HilbertOperator (Qubits 2)) Gate.CNOT.unitary
    BaseGateProfile.cnot.toResourceProfile BaseGateProfile.cnot.circuitDepth
    BaseGateProfile.cnot.oracleQueries

/-- One Toffoli atom as a typed circuit. -/
def toffoliAtom : Circuit (Qubits 3) :=
  Circuit.atom "toffoli" (Gate.Toffoli : HilbertOperator (Qubits 3))
    Gate.Toffoli.unitary BaseGateProfile.toffoli.toResourceProfile
    BaseGateProfile.toffoli.circuitDepth BaseGateProfile.toffoli.oracleQueries

/-- One addressed X/NOT atom as a typed circuit on an `n`-qubit register. -/
def xOnAtom {n : Nat} (target : Fin n) : Circuit (Qubits n) :=
  Circuit.atom "x" (Gate.xOn target : HilbertOperator (Qubits n))
    (Gate.xOn target).unitary (BaseGateProfile.xOn n).toResourceProfile
    (BaseGateProfile.xOn n).circuitDepth (BaseGateProfile.xOn n).oracleQueries

/-- One addressed CNOT atom as a typed circuit on an `n`-qubit register. -/
def cnotOnAtom {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    Circuit (Qubits n) :=
  Circuit.atom "cnot" (Gate.cnotOn control target hct : HilbertOperator (Qubits n))
    (Gate.cnotOn control target hct).unitary
    (BaseGateProfile.cnotOn n).toResourceProfile
    (BaseGateProfile.cnotOn n).circuitDepth
    (BaseGateProfile.cnotOn n).oracleQueries

/-- One addressed Toffoli atom as a typed circuit on an `n`-qubit register. -/
def toffoliOnAtom {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    Circuit (Qubits n) :=
  Circuit.atom "toffoli"
    (Gate.toffoliOn controlA controlB target hab ha hb : HilbertOperator (Qubits n))
    (Gate.toffoliOn controlA controlB target hab ha hb).unitary
    (BaseGateProfile.toffoliOn n).toResourceProfile
    (BaseGateProfile.toffoliOn n).circuitDepth
    (BaseGateProfile.toffoliOn n).oracleQueries

@[simp] theorem xAtom_resources :
    xAtom.resources = BaseGateProfile.x.toResourceProfile :=
  rfl

@[simp] theorem cnotAtom_resources :
    cnotAtom.resources = BaseGateProfile.cnot.toResourceProfile :=
  rfl

@[simp] theorem toffoliAtom_resources :
    toffoliAtom.resources = BaseGateProfile.toffoli.toResourceProfile :=
  rfl

@[simp] theorem xOnAtom_resources {n : Nat} (target : Fin n) :
    (xOnAtom target).resources = (BaseGateProfile.xOn n).toResourceProfile :=
  rfl

@[simp] theorem cnotOnAtom_resources {n : Nat} (control target : Fin n)
    (hct : control ≠ target) :
    (cnotOnAtom control target hct).resources =
      (BaseGateProfile.cnotOn n).toResourceProfile :=
  rfl

@[simp] theorem toffoliOnAtom_resources {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    (toffoliOnAtom controlA controlB target hab ha hb).resources =
      (BaseGateProfile.toffoliOn n).toResourceProfile :=
  rfl

@[simp] theorem xAtom_history :
    xAtom.history = CircuitHistory.atom "x" :=
  rfl

@[simp] theorem cnotAtom_history :
    cnotAtom.history = CircuitHistory.atom "cnot" :=
  rfl

@[simp] theorem toffoliAtom_history :
    toffoliAtom.history = CircuitHistory.atom "toffoli" :=
  rfl

@[simp] theorem xOnAtom_history {n : Nat} (target : Fin n) :
    (xOnAtom target).history = CircuitHistory.atom "x" :=
  rfl

@[simp] theorem cnotOnAtom_history {n : Nat} (control target : Fin n)
    (hct : control ≠ target) :
    (cnotOnAtom control target hct).history = CircuitHistory.atom "cnot" :=
  rfl

@[simp] theorem toffoliOnAtom_history {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    (toffoliOnAtom controlA controlB target hab ha hb).history =
      CircuitHistory.atom "toffoli" :=
  rfl

theorem xAtom_isBaseGateStructured :
    xAtom.history.IsBaseGateStructured := by
  simp [xAtom_history]

theorem cnotAtom_isBaseGateStructured :
    cnotAtom.history.IsBaseGateStructured := by
  simp [cnotAtom_history]

theorem toffoliAtom_isBaseGateStructured :
    toffoliAtom.history.IsBaseGateStructured := by
  simp [toffoliAtom_history]

theorem xOnAtom_isBaseGateStructured {n : Nat} (target : Fin n) :
    (xOnAtom target).history.IsBaseGateStructured := by
  simp [xOnAtom_history]

theorem cnotOnAtom_isBaseGateStructured {n : Nat} (control target : Fin n)
    (hct : control ≠ target) :
    (cnotOnAtom control target hct).history.IsBaseGateStructured := by
  simp [cnotOnAtom_history]

theorem toffoliOnAtom_isBaseGateStructured {n : Nat}
    (controlA controlB target : Fin n) (hab : controlA ≠ controlB)
    (ha : controlA ≠ target) (hb : controlB ≠ target) :
    (toffoliOnAtom controlA controlB target hab ha hb).history.IsBaseGateStructured := by
  simp [toffoliOnAtom_history]

end Circuit

/-! ## Bundled base-gate circuits -/

/-- A typed circuit together with a proof that its history bottoms out only in
X/CNOT/Toffoli atoms and that its projected counters are the supplied modular
arithmetic profile. -/
structure BaseGateCircuit (R : Register) where
  /-- The typed circuit witness. -/
  circuit : Circuit R
  /-- Gate-family profile projected from the same circuit witness. -/
  profile : ModularArithmeticResourceProfile
  /-- The circuit history contains only base reversible classical atoms. -/
  structured : circuit.history.IsBaseGateStructured
  /-- Coarse `ResourceProfile` counters agree with the projected gate-family profile. -/
  resources_eq : circuit.resources = profile.toResourceProfile
  /-- Circuit depth agrees with the gate-family profile. -/
  depth_eq : circuit.depth = profile.circuitDepth
  /-- Query depth agrees with the gate-family profile. -/
  queryDepth_eq : circuit.queryDepth = profile.oracleQueries

namespace BaseGateCircuit

/-- Empty base-gate circuit. -/
def identity (R : Register) : BaseGateCircuit R where
  circuit := Circuit.identity R
  profile := ModularArithmeticResourceProfile.zero
  structured := by
    trivial
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- One X/NOT atom as a bundled base-gate circuit. -/
def x : BaseGateCircuit (Qubits 1) where
  circuit := Circuit.xAtom
  profile := BaseGateProfile.x
  structured := Circuit.xAtom_isBaseGateStructured
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- One CNOT atom as a bundled base-gate circuit. -/
def cnot : BaseGateCircuit (Qubits 2) where
  circuit := Circuit.cnotAtom
  profile := BaseGateProfile.cnot
  structured := Circuit.cnotAtom_isBaseGateStructured
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- One Toffoli atom as a bundled base-gate circuit. -/
def toffoli : BaseGateCircuit (Qubits 3) where
  circuit := Circuit.toffoliAtom
  profile := BaseGateProfile.toffoli
  structured := Circuit.toffoliAtom_isBaseGateStructured
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- One addressed X/NOT atom as a bundled base-gate circuit. -/
def xOn {n : Nat} (target : Fin n) : BaseGateCircuit (Qubits n) where
  circuit := Circuit.xOnAtom target
  profile := BaseGateProfile.xOn n
  structured := Circuit.xOnAtom_isBaseGateStructured target
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- One addressed CNOT atom as a bundled base-gate circuit. -/
def cnotOn {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    BaseGateCircuit (Qubits n) where
  circuit := Circuit.cnotOnAtom control target hct
  profile := BaseGateProfile.cnotOn n
  structured := Circuit.cnotOnAtom_isBaseGateStructured control target hct
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- One addressed Toffoli atom as a bundled base-gate circuit. -/
def toffoliOn {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    BaseGateCircuit (Qubits n) where
  circuit := Circuit.toffoliOnAtom controlA controlB target hab ha hb
  profile := BaseGateProfile.toffoliOn n
  structured :=
    Circuit.toffoliOnAtom_isBaseGateStructured controlA controlB target hab ha hb
  resources_eq := rfl
  depth_eq := rfl
  queryDepth_eq := rfl

/-- Sequentially compose two bundled base-gate circuits on the same register. -/
def seq {R : Register} (left right : BaseGateCircuit R) : BaseGateCircuit R where
  circuit := Circuit.seq left.circuit right.circuit
  profile := ModularArithmeticResourceProfile.sequential left.profile right.profile
  structured := by
    change left.circuit.history.IsBaseGateStructured ∧
      right.circuit.history.IsBaseGateStructured
    exact ⟨left.structured, right.structured⟩
  resources_eq := by
    rw [Circuit.seq_resources, left.resources_eq, right.resources_eq]
    symm
    ext <;>
      simp [ModularArithmeticResourceProfile.toResourceProfile,
        ResourceProfile.sequential,
        ModularArithmeticResourceProfile.elementaryGateCount_sequential]
  depth_eq := by
    change left.circuit.depth + right.circuit.depth =
      left.profile.circuitDepth + right.profile.circuitDepth
    rw [left.depth_eq, right.depth_eq]
  queryDepth_eq := by
    change left.circuit.queryDepth + right.circuit.queryDepth =
      left.profile.oracleQueries + right.profile.oracleQueries
    rw [left.queryDepth_eq, right.queryDepth_eq]

@[simp] theorem identity_profile (R : Register) :
    (identity R).profile = ModularArithmeticResourceProfile.zero :=
  rfl

@[simp] theorem x_profile : x.profile = BaseGateProfile.x := rfl

@[simp] theorem cnot_profile : cnot.profile = BaseGateProfile.cnot := rfl

@[simp] theorem toffoli_profile : toffoli.profile = BaseGateProfile.toffoli := rfl

@[simp] theorem xOn_profile {n : Nat} (target : Fin n) :
    (xOn target).profile = BaseGateProfile.xOn n :=
  rfl

@[simp] theorem cnotOn_profile {n : Nat} (control target : Fin n)
    (hct : control ≠ target) :
    (cnotOn control target hct).profile = BaseGateProfile.cnotOn n :=
  rfl

@[simp] theorem toffoliOn_profile {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    (toffoliOn controlA controlB target hab ha hb).profile =
      BaseGateProfile.toffoliOn n :=
  rfl

@[simp] theorem seq_profile {R : Register} (left right : BaseGateCircuit R) :
    (seq left right).profile =
      ModularArithmeticResourceProfile.sequential left.profile right.profile :=
  rfl

@[simp] theorem seq_circuit {R : Register} (left right : BaseGateCircuit R) :
    (seq left right).circuit = Circuit.seq left.circuit right.circuit :=
  rfl

end BaseGateCircuit

/-! ## Wire-addressed base-gate programs -/

/-- One addressed X/CNOT/Toffoli operation over an `n`-qubit register. -/
inductive BaseGateOp (n : Nat) where
  | x (target : Fin n)
  | cnot (control target : Fin n) (hct : control ≠ target)
  | toffoli (controlA controlB target : Fin n)
      (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target)

namespace BaseGateOp

/-- Classical basis-label action of one addressed base-gate operation. -/
def applyLabel {n : Nat} : BaseGateOp n → Fin (2 ^ n) → Fin (2 ^ n)
  | x target, label => WireAddress.flipBit target label
  | cnot control target _hct, label => WireAddress.cnotMap control target label
  | toffoli controlA controlB target _hab _ha _hb, label =>
      WireAddress.toffoliMap controlA controlB target label

/-- Bundle one addressed operation as a base-gate circuit witness. -/
def toCircuit {n : Nat} : BaseGateOp n → BaseGateCircuit (Qubits n)
  | x target => BaseGateCircuit.xOn target
  | cnot control target hct => BaseGateCircuit.cnotOn control target hct
  | toffoli controlA controlB target hab ha hb =>
      BaseGateCircuit.toffoliOn controlA controlB target hab ha hb

@[simp] theorem toCircuit_x {n : Nat} (target : Fin n) :
    (BaseGateOp.x target).toCircuit = BaseGateCircuit.xOn target :=
  rfl

@[simp] theorem toCircuit_cnot {n : Nat} (control target : Fin n)
    (hct : control ≠ target) :
    (BaseGateOp.cnot control target hct).toCircuit =
      BaseGateCircuit.cnotOn control target hct :=
  rfl

@[simp] theorem toCircuit_toffoli {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    (BaseGateOp.toffoli controlA controlB target hab ha hb).toCircuit =
      BaseGateCircuit.toffoliOn controlA controlB target hab ha hb :=
  rfl

/-- The circuit witness for one addressed operation acts on basis kets by the
same classical label map. -/
theorem toCircuit_circuit_apply_ket {n : Nat} (op : BaseGateOp n)
    (label : Fin (2 ^ n)) :
    Circuit.apply op.toCircuit.circuit
        ((PureState.ket (R := Qubits n) label : PureState (Qubits n)) :
          StateVector (Qubits n)) =
      (PureState.ket (R := Qubits n) (op.applyLabel label) :
        StateVector (Qubits n)) := by
  cases op with
  | x target =>
      have h :=
        congrArg
          (fun state : PureState (Qubits n) => (state : StateVector (Qubits n)))
          (Gate.xOn_apply_ket target label)
      simpa [toCircuit, applyLabel, BaseGateCircuit.xOn, Circuit.xOnAtom,
        Circuit.atom, Circuit.apply, Gate.applyVec] using h
  | cnot control target hct =>
      have h :=
        congrArg
          (fun state : PureState (Qubits n) => (state : StateVector (Qubits n)))
          (Gate.cnotOn_apply_ket control target hct label)
      simpa [toCircuit, applyLabel, BaseGateCircuit.cnotOn, Circuit.cnotOnAtom,
        Circuit.atom, Circuit.apply, Gate.applyVec] using h
  | toffoli controlA controlB target hab ha hb =>
      have h :=
        congrArg
          (fun state : PureState (Qubits n) => (state : StateVector (Qubits n)))
          (Gate.toffoliOn_apply_ket controlA controlB target hab ha hb label)
      simpa [toCircuit, applyLabel, BaseGateCircuit.toffoliOn, Circuit.toffoliOnAtom,
        Circuit.atom, Circuit.apply, Gate.applyVec] using h

end BaseGateOp

/-- A finite wire-addressed base-gate program. -/
abbrev BaseGateProgram (n : Nat) := List (BaseGateOp n)

namespace BaseGateProgram

/-- Singleton addressed X/NOT program. -/
def x {n : Nat} (target : Fin n) : BaseGateProgram n :=
  [BaseGateOp.x target]

/-- Singleton addressed CNOT program. -/
def cnot {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    BaseGateProgram n :=
  [BaseGateOp.cnot control target hct]

/-- Singleton addressed Toffoli/CCNOT program. -/
def toffoli {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target)
    (hb : controlB ≠ target) : BaseGateProgram n :=
  [BaseGateOp.toffoli controlA controlB target hab ha hb]

/-- Fold a wire-addressed base-gate program into one typed circuit witness. -/
def toCircuit {n : Nat} : BaseGateProgram n → BaseGateCircuit (Qubits n)
  | [] => BaseGateCircuit.identity (Qubits n)
  | op :: rest => BaseGateCircuit.seq (toCircuit rest) op.toCircuit

/-- Classical basis-label action of a program, in list execution order. -/
def applyLabel {n : Nat} : BaseGateProgram n → Fin (2 ^ n) → Fin (2 ^ n)
  | [], label => label
  | op :: rest, label => applyLabel rest (op.applyLabel label)

@[simp] theorem toCircuit_nil {n : Nat} :
    toCircuit ([] : BaseGateProgram n) = BaseGateCircuit.identity (Qubits n) :=
  rfl

@[simp] theorem toCircuit_cons {n : Nat} (op : BaseGateOp n) (rest : BaseGateProgram n) :
    toCircuit (op :: rest) =
      BaseGateCircuit.seq (toCircuit rest) op.toCircuit :=
  rfl

@[simp] theorem applyLabel_nil {n : Nat} (label : Fin (2 ^ n)) :
    applyLabel ([] : BaseGateProgram n) label = label :=
  rfl

@[simp] theorem applyLabel_cons {n : Nat} (op : BaseGateOp n)
    (rest : BaseGateProgram n) (label : Fin (2 ^ n)) :
    applyLabel (op :: rest) label = applyLabel rest (op.applyLabel label) :=
  rfl

@[simp] theorem applyLabel_x {n : Nat} (target : Fin n)
    (label : Fin (2 ^ n)) :
    applyLabel (x target) label = WireAddress.flipBit target label :=
  rfl

@[simp] theorem applyLabel_cnot {n : Nat} (control target : Fin n)
    (hct : control ≠ target) (label : Fin (2 ^ n)) :
    applyLabel (cnot control target hct) label =
      WireAddress.cnotMap control target label :=
  rfl

@[simp] theorem applyLabel_toffoli {n : Nat}
    (controlA controlB target : Fin n) (hab : controlA ≠ controlB)
    (ha : controlA ≠ target) (hb : controlB ≠ target)
    (label : Fin (2 ^ n)) :
    applyLabel (toffoli controlA controlB target hab ha hb) label =
      WireAddress.toffoliMap controlA controlB target label :=
  rfl

/-- The folded program circuit acts on basis kets by the program's classical
label semantics. -/
theorem toCircuit_apply_ket {n : Nat} :
    ∀ (program : BaseGateProgram n) (label : Fin (2 ^ n)),
      Circuit.apply (toCircuit program).circuit
          ((PureState.ket (R := Qubits n) label : PureState (Qubits n)) :
            StateVector (Qubits n)) =
        (PureState.ket (R := Qubits n) (applyLabel program label) :
          StateVector (Qubits n))
  | [], label => by
      change (1 : Gate (Qubits n)).applyVec
          ((PureState.ket (R := Qubits n) label : PureState (Qubits n)) :
            StateVector (Qubits n)) =
        (PureState.ket (R := Qubits n) label : StateVector (Qubits n))
      rw [Gate.one_applyVec]
  | op :: rest, label => by
      change (((toCircuit rest).circuit.matrix * op.toCircuit.circuit.matrix).applyVec
          ((PureState.ket (R := Qubits n) label : PureState (Qubits n)) :
            StateVector (Qubits n))) =
        (PureState.ket (R := Qubits n) (applyLabel rest (op.applyLabel label)) :
          StateVector (Qubits n))
      rw [Gate.mul_applyVec]
      have hop := BaseGateOp.toCircuit_circuit_apply_ket op label
      change op.toCircuit.circuit.matrix.applyVec
          ((PureState.ket (R := Qubits n) label : PureState (Qubits n)) :
            StateVector (Qubits n)) =
        (PureState.ket (R := Qubits n) (op.applyLabel label) :
          StateVector (Qubits n)) at hop
      rw [hop]
      exact toCircuit_apply_ket rest (op.applyLabel label)

/-- One addressed base-gate operation is self-inverse on basis labels. -/
theorem applyLabel_applyLabel_op {n : Nat} (op : BaseGateOp n)
    (label : Fin (2 ^ n)) :
    op.applyLabel (op.applyLabel label) = label := by
  cases op with
  | x target =>
      exact WireAddress.flipBit_flipBit target label
  | cnot control target hct =>
      exact WireAddress.cnotMap_cnotMap hct label
  | toffoli controlA controlB target _hab ha hb =>
      exact WireAddress.toffoliMap_toffoliMap ha hb label

/-- Program concatenation as the sequential network-composition operation. -/
def append {n : Nat} (first second : BaseGateProgram n) : BaseGateProgram n :=
  first ++ second

/-- Reverse a program for cleanup/uncomputation.  The selected base-gate family
is self-inverse, so reversing the list gives the inverse basis-label action. -/
def inverse {n : Nat} (program : BaseGateProgram n) : BaseGateProgram n :=
  program.reverse

@[simp] theorem append_nil {n : Nat} (program : BaseGateProgram n) :
    append program [] = program := by
  simp [append]

@[simp] theorem nil_append {n : Nat} (program : BaseGateProgram n) :
    append [] program = program := by
  simp [append]

@[simp] theorem inverse_nil {n : Nat} :
    inverse ([] : BaseGateProgram n) = [] := by
  rfl

@[simp] theorem inverse_cons {n : Nat} (op : BaseGateOp n)
    (rest : BaseGateProgram n) :
    inverse (op :: rest) = append (inverse rest) [op] := by
  simp [inverse, append]

@[simp] theorem inverse_x {n : Nat} (target : Fin n) :
    inverse (x target) = x target := by
  simp [inverse, x]

@[simp] theorem inverse_cnot {n : Nat} (control target : Fin n)
    (hct : control ≠ target) :
    inverse (cnot control target hct) = cnot control target hct := by
  simp [inverse, cnot]

@[simp] theorem inverse_toffoli {n : Nat}
    (controlA controlB target : Fin n) (hab : controlA ≠ controlB)
    (ha : controlA ≠ target) (hb : controlB ≠ target) :
    inverse (toffoli controlA controlB target hab ha hb) =
      toffoli controlA controlB target hab ha hb := by
  simp [inverse, toffoli]

theorem applyLabel_append {n : Nat} (first second : BaseGateProgram n)
    (label : Fin (2 ^ n)) :
    applyLabel (append first second) label =
      applyLabel second (applyLabel first label) := by
  induction first generalizing label with
  | nil =>
      simp [append]
  | cons op rest ih =>
      simpa [append, applyLabel] using ih (op.applyLabel label)

theorem applyLabel_inverse_applyLabel {n : Nat} (program : BaseGateProgram n)
    (label : Fin (2 ^ n)) :
    applyLabel (inverse program) (applyLabel program label) = label := by
  induction program generalizing label with
  | nil =>
      simp [inverse]
  | cons op rest ih =>
      rw [inverse_cons, applyLabel_append]
      change op.applyLabel
          (applyLabel (inverse rest) (applyLabel rest (op.applyLabel label))) = label
      rw [ih (op.applyLabel label)]
      exact applyLabel_applyLabel_op op label

theorem applyLabel_applyLabel_inverse {n : Nat} (program : BaseGateProgram n)
    (label : Fin (2 ^ n)) :
    applyLabel program (applyLabel (inverse program) label) = label := by
  induction program generalizing label with
  | nil =>
      simp [inverse]
  | cons op rest ih =>
      rw [inverse_cons, applyLabel_append]
      simp only [applyLabel_cons, applyLabel_nil]
      rw [applyLabel_applyLabel_op op (applyLabel (inverse rest) label)]
      exact ih label

end BaseGateProgram

end

end QuantumAlg
