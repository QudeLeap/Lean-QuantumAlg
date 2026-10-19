/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Converted.CommonBank
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Reference
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Unitary.StoreFilter

/-!
# Actual false-circuit coordinate conversions in the streaming workspace

The authoritative bank is literally readyContext width 2. The existing native
readyProgram is placed at the cellsPlacement positions; no old local compiler or
true-circuit consumer is introduced. The full classical result-cell frame survives every
actual unitary instruction. Its empty quantum factor is removed only by the explicit
previously constructed basis equivalence. Arbitrary dirty arithmetic, all private
control/memory values and arbitrary Reference remain unrestricted.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Placement (width m : Nat) :=
  Recovery.Point.cellsPlacement (Recovery.Layout.bank width) 2 (2 * m)

/-- Every native ready wire is placed at its actual retained-cell workspace position. -/
private lemma dimensions (width m : Nat) (index : Fin (Recovery.Layout.bank width).systemCount) :
    ((Recovery.Layout.bank width).quantumLayout.wire index).dimension =
      ((Recovery.Layout.terminal width m).quantumLayout.wire
        ((Placement width m).position index)).dimension :=
  ((Placement width m).contextEmbedding_position_dimension index).symm

/-- The result-cell frame is quantum-empty, so every actual quantum wire is a ready-bank wire. -/
private lemma position_surjective (width m : Nat) :
    Function.Surjective (Placement width m).position := by
  intro target
  obtain ⟨source, same⟩ := (Placement width m).positions.surjective target
  cases source with
  | inl source => exact ⟨source, same⟩
  | inr source =>
      exact Fin.elim0 (Fin.cast (Recovery.Layout.Reference.frame_systemCount_zero width m) source)

/-- The placement reads exactly the original ready-bank basis, including arbitrary dirty wires. -/
private lemma selectedInput_eq (width m : Nat)
    (basis : (Recovery.Layout.terminal width m).register.Index) :
    UnitaryCircuit.selectedInput (Recovery.Layout.bank width).quantumLayout
        (Recovery.Layout.terminal width m).quantumLayout
        (Placement width m).position (dimensions width m) basis =
      ((Placement width m).basis basis).1 := by
  funext index
  apply Fin.ext
  change (basis ((Placement width m).position index)).val = _
  exact ((Placement width m).split_local_value basis index).symm

/-- The original physical placement has no unselected quantum coordinate. -/
private lemma complement_eq (width m : Nat)
    (row column : (Recovery.Layout.terminal width m).register.Index) :
    (Recovery.Layout.terminal width m).quantumLayout.restrictComplementBasis
        (Finset.univ.map (Placement width m).position) row =
      (Recovery.Layout.terminal width m).quantumLayout.restrictComplementBasis
        (Finset.univ.map (Placement width m).position) column := by
  funext index
  obtain ⟨source, same⟩ := position_surjective width m index.val
  have present : index.val ∈ Finset.univ.map (Placement width m).position := by
    rw [← same]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ source)
  exact False.elim ((Finset.mem_compl.mp index.property) present)

/-- A direct native placement of the existing complete arithmetic conversion program. -/
def coordinateProgram (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit AlgorithmGate.model .empty (Recovery.Layout.terminal width m).quantumLayout :=
  UnitaryCircuit.placeAt (Recovery.Layout.bank width).quantumLayout
    (Recovery.Layout.terminal width m).quantumLayout
    (Placement width m).position (dimensions width m)
    (Encoding.readyProgram width 2 modulus coefficient coordinate)

/-- This real conversion is an explicit allocation-free circuit constructor. -/
def coordinateCircuit (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (Recovery.Layout.terminal width m) (Recovery.Layout.terminal width m) false :=
  .unitary (coordinateProgram width m modulus coefficient coordinate)

/-- Every conversion operator includes identity on the original arbitrary Reference. -/
def coordinateOperator (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    UnitaryOperator ((Recovery.Layout.terminal width m).register.prod Reference) :=
  UnitaryOperator.prodTensor
    ((coordinateProgram width m modulus coefficient coordinate).matrix environment.quantum)
    (1 : UnitaryOperator Reference)

/-- Actual physical placement is the existing ready operator beside the complete cell frame. -/
lemma coordinateOperator_outer (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    (coordinateOperator (environment := environment)
      width m modulus coefficient coordinate Reference : Matrix _ _ ℂ) =
      (Encoding.coordinateOperator (environment := environment) width 2 modulus coefficient
        coordinate
        (ResidualReference width m Reference) : Matrix _ _ ℂ).submatrix
          ((Placement width m).referenceBasis Reference)
          ((Placement width m).referenceBasis Reference) := by
  ext row column
  change (UnitaryOperator.prodTensor
      ((coordinateProgram width m modulus coefficient coordinate).matrix environment.quantum)
      (1 : UnitaryOperator Reference)) row column = _
  rw [UnitaryOperator.prodTensor_apply]
  change ((coordinateProgram width m modulus coefficient coordinate).matrix environment.quantum)
    row.1 column.1 *
    (if row.2 = column.2 then 1 else 0) = _
  rw [coordinateProgram, UnitaryCircuit.placeAt_matrix, UnitaryCircuit.operatorAt_entry,
    selectedInput_eq, selectedInput_eq, if_pos (complement_eq width m row.1 column.1), mul_one]
  change ((Encoding.readyProgram width 2 modulus coefficient coordinate).matrix environment.quantum)
      ((Placement width m).basis row.1).1 ((Placement width m).basis column.1).1 *
        (if row.2 = column.2 then 1 else 0) =
    (UnitaryOperator.prodTensor
      ((Encoding.readyProgram width 2 modulus coefficient coordinate).matrix environment.quantum)
      (1 : UnitaryOperator (ResidualReference width m Reference)))
      (((Placement width m).basis row.1).1, (((Placement width m).basis row.1).2, row.2))
      (((Placement width m).basis column.1).1, (((Placement width m).basis column.1).2, column.2))
  rw [UnitaryOperator.prodTensor_apply]
  have frame := Recovery.Layout.Reference.frame_basis_unique width m
    ((Placement width m).basis row.1).2 ((Placement width m).basis column.1).2
  change _ =
    ((Encoding.readyProgram width 2 modulus coefficient coordinate).matrix environment.quantum)
    ((Placement width m).basis row.1).1 ((Placement width m).basis column.1).1 *
      (if (((Placement width m).basis row.1).2, row.2) =
        (((Placement width m).basis column.1).2, column.2) then 1 else 0)
  simp only [Prod.mk.injEq, frame, true_and]

/-- Actual unitary execution preserves each complete Store and its entire classical cell frame. -/
lemma coordinate_store_density (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Recovery.Layout.terminal width m)) :
    storeDensity ((coordinateCircuit width m modulus coefficient coordinate).execute environment
      Reference state) final =
      (coordinateOperator (environment := environment)
        width m modulus coefficient coordinate Reference : Matrix _ _ ℂ) *
        storeDensity state final *
        (coordinateOperator (environment := environment)
          width m modulus coefficient coordinate Reference :
          Matrix _ _ ℂ).conjTranspose :=
  congrArg DensityOperator.matrix
    (Circuit.unitary_store_filter (environment := environment) (coordinateProgram width m modulus
      coefficient coordinate)
      state (fun stored => stored = final))

/-- Complete resident private coordinates, without observing their quantum values. -/
private def privateBits (control memory : Fin 2) :
  Recovery.Reference.Measured.CommonBank.Exponents 2 :=
  Fin.cons control (Fin.cons memory Fin.elim0)

private lemma privateBits_eq_iff (leftControl leftMemory rightControl rightMemory : Fin 2) :
    privateBits leftControl leftMemory = privateBits rightControl rightMemory ↔
      leftControl = rightControl ∧ leftMemory = rightMemory := by
  constructor
  · intro same
    exact ⟨congrFun same 0, congrFun same 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual ready private positions are exactly the authoritative terminal control/memory wires.
-/
private lemma exponentPosition_terminal (width m : Nat) (index : Fin 2) :
    (Placement width m).position (Recovery.Reference.Measured.CommonBank.exponentPosition width
      2 index) =
      Recovery.Layout.position width m index.castSucc := by
  apply (Recovery.Layout.terminal width m).quantumLayout.position_eq_of_identity_eq
  have placed := congrArg QuantumWire.identity
    ((Placement width m).contextEmbedding_position_wire
      (Recovery.Reference.Measured.CommonBank.exponentPosition width 2 index))
  change ((Recovery.Layout.terminal width m).quantumLayout.wire
      ((Placement width m).position
        (Recovery.Reference.Measured.CommonBank.exponentPosition width 2 index))).identity =
    ((readyContext width 2).quantumLayout.wire
      (Recovery.Reference.Measured.CommonBank.exponentPosition width 2 index)).identity at placed
  rw [Recovery.Reference.Measured.CommonBank.exponentPosition_wire] at placed
  exact placed.trans (congrArg QuantumWire.identity
    (Recovery.Layout.position_wire width m index.castSucc)).symm

/-- Existing streaming coordinates expose the same arithmetic, selector, private bits and Reference.
-/
lemma ready_coordinates (width m : Nat) (Reference : Register) (control memory : Fin 2)
    (bank : Bank width m Reference) :
    Recovery.Reference.Measured.CommonBank.coordinates width 2 (ResidualReference width m Reference)
      ((Placement width m).referenceBasis Reference
        ((Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
          (control, (memory, bank)))) = (privateBits control memory, bank) := by
  let physical := (Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
    (control, (memory, bank))
  let ready := (Placement width m).referenceBasis Reference physical
  have point : (pointBasis width (0 : Fin 2) ready.1).1 =
      MeasuredPointAddition.label width control bank.2.1 bank.1 := by
    change ((Inner width).referenceBasis (ResidualReference width m Reference) ready).1 = _
    dsimp only [ready, physical]
    rw [Recovery.Stage.PointCoordinates.coordinates_symm, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have label := pointBasis_label width (0 : Fin 2) ready.1
  have arithmetic := congrArg (pointSharedBasis width) (label.symm.trans point)
  have selector := congrArg (pointSelector width) (label.symm.trans point)
  simp only [pointSharedBasis_label] at arithmetic
  simp only [pointSelector_label] at selector
  apply Prod.ext
  · funext index
    apply Fin.ext
    have selected := Recovery.Reference.Measured.CommonBank.coordinates_exponent_value width 2
      (ResidualReference width m Reference) ready index
    have placed := (Placement width m).split_local_value physical.1
      (Recovery.Reference.Measured.CommonBank.exponentPosition width 2 index)
    change (ready.1 (Recovery.Reference.Measured.CommonBank.exponentPosition width 2 index)).val =
      (physical.1 ((Placement width m).position
        (Recovery.Reference.Measured.CommonBank.exponentPosition width 2 index))).val at placed
    rw [exponentPosition_terminal] at placed
    refine selected.trans (placed.trans ?_)
    fin_cases index
    · exact Recovery.Stage.PointCoordinates.coordinates_control_value width m Reference
        control memory bank
    · exact Recovery.Stage.PointCoordinates.coordinates_memory_value width m Reference
        control memory bank
  · apply Prod.ext
    · exact (Recovery.Reference.Measured.CommonBank.coordinates_arithmetic width 2
        (ResidualReference width m Reference) ready).trans arithmetic
    · apply Prod.ext
      · exact (Recovery.Reference.Measured.CommonBank.coordinates_selector width 2
          (ResidualReference width m Reference) ready).trans selector
      · change ready.2 = bank.2.2
        dsimp only [ready, physical]
        rw [Recovery.Stage.PointCoordinates.coordinates_symm, Equiv.apply_symm_apply]
        rfl

/-- The actual streaming conversion is the same bank operator at every private C/M coordinate. -/
lemma coordinateOperator_rows (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) (leftControl leftMemory rightControl rightMemory : Fin 2)
    (row column : Bank width m Reference) :
    (coordinateOperator (environment := environment)
      width m modulus coefficient coordinate Reference : Matrix _ _ ℂ)
      ((Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
        (leftControl, (leftMemory, row)))
      ((Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
        (rightControl, (rightMemory, column))) =
      if leftControl = rightControl ∧ leftMemory = rightMemory then
        Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
          modulus coefficient coordinate
          (ResidualReference width m Reference) row column
      else 0 := by
  have pulled (control memory : Fin 2) (bank : Bank width m Reference) :
      (Placement width m).referenceBasis Reference
        ((Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
          (control, (memory, bank))) =
        (Recovery.Reference.Measured.CommonBank.coordinates width 2
          (ResidualReference width m Reference)).symm (privateBits control memory, bank) := by
    apply (Recovery.Reference.Measured.CommonBank.coordinates width 2
      (ResidualReference width m Reference)).injective
    rw [ready_coordinates, Equiv.apply_symm_apply]
  rw [coordinateOperator_outer, Matrix.submatrix_apply, pulled, pulled,
    Recovery.Reference.Converted.coordinateOperator_common_entry]
  exact if_congr (privateBits_eq_iff leftControl leftMemory rightControl rightMemory) rfl rfl

/-- Only the explicitly empty quantum cell-frame factor disappears from the conversion bank. -/
lemma bankCoordinateOperator_common (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    (Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
      modulus coefficient coordinate
      (ResidualReference width m Reference)).submatrix
        (Recovery.Layout.Reference.bankBasis width m Reference).symm
        (Recovery.Layout.Reference.bankBasis width m Reference).symm =
      Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
        modulus coefficient coordinate
        Reference := by
  have δ {P Q : Prop} (first : Decidable P) (second : Decidable Q) (same : P ↔ Q) :
      @ite ℂ P first 1 0 = @ite ℂ Q second 1 0 := by
    cases first with
    | isTrue yes =>
      cases second with
      | isTrue _ => rfl
      | isFalse no => exact False.elim (no (same.mp yes))
    | isFalse no =>
      cases second with
      | isTrue yes => exact False.elim (no (same.mpr yes))
      | isFalse _ => rfl
  ext row column
  simp only [Recovery.Reference.Converted.bankCoordinateOperator, Matrix.submatrix_apply,
    Recovery.Layout.Reference.bankBasis_symm]
  exact congrArg₂ (fun value branch : ℂ => value * branch) rfl
    (δ _ _ Prod.mk_right_inj)

/-- Pair conversion runs the two actual allocation-free native instructions, X then Y. -/
def pairCircuit (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (Recovery.Layout.terminal width m) (Recovery.Layout.terminal width m) false :=
  (coordinateCircuit width m modulus coefficient .x).seq
    (coordinateCircuit width m modulus coefficient .y)

def pairOperator (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    Matrix ((Recovery.Layout.terminal width m).register.prod Reference).Index
      ((Recovery.Layout.terminal width m).register.prod Reference).Index ℂ :=
  (coordinateOperator (environment := environment)
    width m modulus coefficient .y Reference : Matrix _ _ ℂ) *
    (coordinateOperator (environment := environment)
      width m modulus coefficient .x Reference : Matrix _ _ ℂ)

/-- The actual pair preserves each complete Store, including every original result-cell value. -/
lemma pair_store_density (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Recovery.Layout.terminal width m)) :
    storeDensity ((pairCircuit width m modulus coefficient).execute environment Reference state)
      final =
      pairOperator (environment := environment)
        width m modulus coefficient Reference * storeDensity state final *
        (pairOperator (environment := environment)
          width m modulus coefficient Reference).conjTranspose := by
  have sequence := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (environment := environment)
      (coordinateCircuit width m modulus coefficient .x)
      (coordinateCircuit width m modulus coefficient .y) state final)
  change storeDensity ((pairCircuit width m modulus coefficient).execute environment Reference
    state)
      final = storeDensity
    ((coordinateCircuit width m modulus coefficient .y).execute environment Reference
      ((coordinateCircuit width m modulus coefficient .x).execute environment Reference state))
      final at sequence
  rw [sequence, coordinate_store_density, coordinate_store_density]
  simp only [pairOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Mathematical rearrangement of the existing physical C/M/bank coordinates only. -/
def bankFirstCoordinates (width m : Nat) (Reference : Register) :
    ((Recovery.Layout.terminal width m).register.prod Reference).Index ≃
      Bank width m Reference × (Fin 2 × Fin 2) :=
  (Recovery.Stage.PointCoordinates.coordinates width m Reference).trans
    ((Equiv.prodAssoc (Fin 2) (Fin 2) (Bank width m Reference)).symm.trans
      (Equiv.prodComm _ _))

/-- The actual conversion is block diagonal at the original control/memory quantum indices. -/
lemma coordinateOperator_bankFirst (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    (coordinateOperator (environment := environment)
      width m modulus coefficient coordinate Reference : Matrix _ _ ℂ).submatrix
      (bankFirstCoordinates width m Reference).symm (bankFirstCoordinates width m Reference).symm =
        Matrix.blockDiagonal (fun _ : Fin 2 × Fin 2 =>
          Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
            modulus coefficient coordinate
            (ResidualReference width m Reference)) := by
  ext row column
  change (coordinateOperator (environment := environment)
    width m modulus coefficient coordinate Reference : Matrix _ _ ℂ)
    ((Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
      (row.2.1, (row.2.2, row.1)))
    ((Recovery.Stage.PointCoordinates.coordinates width m Reference).symm
      (column.2.1, (column.2.2, column.1))) =
      if row.2 = column.2 then
        Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
          modulus coefficient coordinate
          (ResidualReference width m Reference) row.1 column.1 else 0
  rw [coordinateOperator_rows]
  simp only [Prod.ext_iff]

/-- Both actual pair factors act in X-then-Y order on that same full streaming bank. -/
lemma pairOperator_bankFirst (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    (pairOperator (environment := environment) width m modulus coefficient Reference).submatrix
      (bankFirstCoordinates width m Reference).symm (bankFirstCoordinates width m Reference).symm =
        Matrix.blockDiagonal (fun _ : Fin 2 × Fin 2 =>
          Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
            coefficient
            (ResidualReference width m Reference)) := by
  let basis := bankFirstCoordinates width m Reference
  unfold pairOperator
  rw [← Matrix.submatrix_mul_equiv _ _ basis.symm basis.symm basis.symm,
    coordinateOperator_bankFirst, coordinateOperator_bankFirst, ← Matrix.blockDiagonal_mul]
  rfl

/-- The streaming pair bank is precisely the old pair bank after the explicit empty-frame basis. -/
lemma bankPairOperator_common (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
      coefficient
      (ResidualReference width m Reference)).submatrix
        (Recovery.Layout.Reference.bankBasis width m Reference).symm
        (Recovery.Layout.Reference.bankBasis width m Reference).symm =
      Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
        coefficient Reference := by
  let basis := Recovery.Layout.Reference.bankBasis width m Reference
  unfold Recovery.Reference.Converted.bankPairOperator
  rw [← Matrix.submatrix_mul_equiv _ _ basis.symm basis.symm basis.symm,
    bankCoordinateOperator_common, bankCoordinateOperator_common]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
