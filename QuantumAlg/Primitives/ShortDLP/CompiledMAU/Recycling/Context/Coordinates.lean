/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Placement
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Execution.Context.Layout

/-!
# Clean carrier coordinates in the actual owned context

Finite control values are transported only
through the actual physical wire's dimension equality. Update identities leave
every arithmetic and reference coordinate untouched. These internal coordinate
proofs do not assume a clean caller state or introduce an executable basis change.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.ContextCoordinates

noncomputable section

open Execution

attribute [local instance] Placement.arithmeticWidth_neZero

private lemma source_update {width : Nat} (modulus : Fin (2 ^ width + 1))
    [NeZero modulus.val] (positive : 0 < modulus.val)
    (label : (Carrier.full modulus.val).Index) (bit : Fin 2) :
    Function.update (Carrier.embedding modulus positive label) 0 bit =
      Carrier.embedding modulus positive (bit, label.2) := by
  let original : Fin (1 + (workspaceEncoding width).width) → Fin 2 :=
    (QuantumSignature.qubitsIndexEquiv (1 + (workspaceEncoding width).width)).symm
      (prodEquiv (label.1, Carrier.workspaceWord modulus positive label.2))
  let changed : Fin (1 + (workspaceEncoding width).width) → Fin 2 :=
    (QuantumSignature.qubitsIndexEquiv (1 + (workspaceEncoding width).width)).symm
      (prodEquiv (bit, Carrier.workspaceWord modulus positive label.2))
  change Function.update (β := fun _ : Fin (1 + (workspaceEncoding width).width) => Fin 2)
    original 0 bit = changed
  funext index
  induction index using Fin.addCases with
  | left first =>
      fin_cases first
      change Function.update original 0 bit 0 = changed 0
      exact (Function.update_self _ _ _).trans
        (Carrier.embedding_control modulus positive (bit, label.2)).symm
  | right tail =>
      have different : Fin.natAdd 1 tail ≠ (0 : Fin (1 + (workspaceEncoding width).width)) := by
        intro equal
        have values := congrArg Fin.val equal
        change 1 + tail.val = 0 at values
        omega
      have unchanged : Function.update original 0 bit (Fin.natAdd 1 tail) =
          original (Fin.natAdd 1 tail) := Function.update_of_ne different bit original
      refine unchanged.trans ?_
      exact (congrFun (Gate.suffixDecoded (workspaceEncoding width).width label.1
        (Carrier.workspaceWord modulus positive label.2)) tail).trans
          (congrFun (Gate.suffixDecoded (workspaceEncoding width).width bit
            (Carrier.workspaceWord modulus positive label.2)) tail).symm

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Cast an outcome to the actual wire type, without an executable conversion or new storage. -/
def physicalBit (bit : Fin 2) :
    Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension :=
  Fin.cast (congrArg PNat.val (control_qubit base noQuantum m ell width)).symm bit

lemma physicalBit_zero : physicalBit base noQuantum m ell width 0 = 0 := by
  apply Fin.ext
  rfl

lemma physicalBit_injective : Function.Injective (physicalBit base noQuantum m ell width) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg
    (fun value : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension => value.val) equal
  exact values

private lemma basis_update (source : (Carrier.physical width).Index) (bit : Fin 2) :
    Function.update (Placement.basis base noQuantum m ell width source)
        (control base noQuantum m ell width) (physicalBit base noQuantum m ell width bit) =
      Placement.basis base noQuantum m ell width (Function.update source 0 bit) := by
  let positions := positionsOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width)
  funext actual
  obtain ⟨index, rfl⟩ := positions.surjective actual
  apply Fin.ext
  by_cases first : index = 0
  · subst index
    have targetSelf :
        Function.update (Placement.basis base noQuantum m ell width source)
            (control base noQuantum m ell width) (physicalBit base noQuantum m ell width bit)
            (positions 0) = physicalBit base noQuantum m ell width bit :=
      Function.update_self _ _ _
    have sourceSelf : Function.update source 0 bit 0 = bit := Function.update_self _ _ _
    have targetValue := congrArg
      (fun value : Fin ((Context base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension => value.val) targetSelf
    have sourceValue := congrArg (fun value : Fin 2 => value.val) sourceSelf
    have same := basisOfEqualWires_value (Arithmetic.layout width).toQuantum
      (Context base noQuantum m ell width).quantumLayout
      (context_wires base noQuantum m ell width) (Function.update source 0 bit) 0
    exact targetValue.trans (sourceValue.symm.trans same.symm)
  · have outside : positions index ≠ control base noQuantum m ell width := by
      intro equal
      exact first (positions.injective equal)
    rw [Function.update_of_ne outside]
    have left := basisOfEqualWires_value (Arithmetic.layout width).toQuantum
      (Context base noQuantum m ell width).quantumLayout
      (context_wires base noQuantum m ell width) source index
    have right := basisOfEqualWires_value (Arithmetic.layout width).toQuantum
      (Context base noQuantum m ell width).quantumLayout
      (context_wires base noQuantum m ell width) (Function.update source 0 bit) index
    calc
      _ = (source index).val := left
      _ = (Function.update source 0 bit index).val :=
        (congrArg (fun value : Fin ((Arithmetic.layout width).toQuantum.wire index).dimension =>
          value.val) (Function.update_of_ne first bit source)).symm
      _ = _ := right.symm

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

/-- The logical control value equals the label of the actual first physical wire. -/
lemma embedding_control (label : (Carrier.full modulus.val).Index) :
    Placement.embedding base noQuantum m ell width modulus positive label
        (control base noQuantum m ell width) =
      physicalBit base noQuantum m ell width label.1 := by
  apply Fin.ext
  have actual := basisOfEqualWires_value (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) (Carrier.embedding modulus positive label) 0
  exact actual.trans (congrArg Fin.val (Carrier.embedding_control modulus positive label))

/-- Updating the actual control changes no power/auxiliary coordinate of the encoded seed. -/
lemma embedding_update (label : (Carrier.full modulus.val).Index) (bit : Fin 2) :
    Function.update (Placement.embedding base noQuantum m ell width modulus positive label)
        (control base noQuantum m ell width) (physicalBit base noQuantum m ell width bit) =
      Placement.embedding base noQuantum m ell width modulus positive (bit, label.2) := by
  change Function.update (Placement.basis base noQuantum m ell width
      (Carrier.embedding modulus positive label)) (control base noQuantum m ell width)
        (physicalBit base noQuantum m ell width bit) = _
  rw [basis_update, source_update]
  rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.ContextCoordinates
