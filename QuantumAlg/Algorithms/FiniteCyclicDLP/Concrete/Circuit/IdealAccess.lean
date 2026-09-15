/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary
import Mathlib.Logic.Equiv.Fintype

/-!
# Ideal finite-cyclic access on an arbitrary clean tail

This module extends the prescribed finite-cyclic group action from an
injectively encoded clean tail to a permutation of the complete computational
basis.  Every width remains symbolic; concrete algorithms only supply their
tail encoding, clean group embedding, and analysis-only subroutine label.
-/

section

namespace QuantumAlg
namespace FiniteCyclicDLP
namespace ConcreteCircuitAccess
namespace Ideal

noncomputable section

universe u

variable {G : Type u} [Group G]
variable {P : KnownOrderProblem G}
variable {Tail : Type}

/-- Semantic exponent pair and group workspace prescribed by the oracle. -/
abbrev SemanticInput (P : KnownOrderProblem G) :=
  (Fin (2 ^ orderWidth P) × Fin (2 ^ orderWidth P)) × G

/-- Full binary encoding obtained by placing the arbitrary tail after both
exponent registers. -/
def fullEncoding (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) :
    BinaryLabelEncoding
      ((Fin (2 ^ orderWidth P) × Fin (2 ^ orderWidth P)) × Tail) :=
  BinaryLabelEncoding.prod (exponentEncoding P) tailEncoding

/-- Clean source label before the prescribed group action. -/
def sourceLabel (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (input : SemanticInput P) :
    Fin (2 ^ (orderWidth P + orderWidth P + tailEncoding.width)) :=
  (fullEncoding P tailEncoding).encode (input.1, cleanTail input.2)

/-- Semantic input after the branch-fixed right group multiplication. -/
def targetInput (P : KnownOrderProblem G) (input : SemanticInput P) :
    SemanticInput P :=
  (input.1,
    input.2 * P.toSourceScope.oracleMultiplier
      input.1.1.val input.1.2.val)

/-- Clean target label after the prescribed group action. -/
def targetLabel (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (input : SemanticInput P) :
    Fin (2 ^ (orderWidth P + orderWidth P + tailEncoding.width)) :=
  sourceLabel P tailEncoding cleanTail (targetInput P input)

/-- A faithful tail encoding and injective clean embedding distinguish all
semantic source inputs. -/
theorem sourceLabel_injective (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) :
    Function.Injective (sourceLabel P tailEncoding cleanTail) := by
  intro left right equality
  have fields := (fullEncoding P tailEncoding).encode_injective equality
  have branchEquality : left.1 = right.1 :=
    congrArg (fun fields => fields.1) fields
  have pointEquality : left.2 = right.2 :=
    cleanTail_injective (congrArg (fun fields => fields.2) fields)
  exact Prod.ext branchEquality pointEquality

/-- Retaining the exponent pair makes the prescribed semantic update
injective. -/
theorem targetInput_injective (P : KnownOrderProblem G) :
    Function.Injective (targetInput P) := by
  rintro ⟨leftBranch, leftPoint⟩ ⟨rightBranch, rightPoint⟩ equality
  have branchEquality : leftBranch = rightBranch :=
    congrArg Prod.fst equality
  cases branchEquality
  have shiftedEquality := congrArg Prod.snd equality
  exact Prod.ext rfl (mul_right_cancel shiftedEquality)

/-- Target labels remain injective because the semantic update and source
encoding are both injective. -/
theorem targetLabel_injective (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) :
    Function.Injective (targetLabel P tailEncoding cleanTail) := by
  intro left right equality
  apply targetInput_injective P
  apply sourceLabel_injective P tailEncoding cleanTail cleanTail_injective
  exact equality

/-- Total basis permutation extending the prescribed clean group action. -/
def permutation (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) :
    Equiv.Perm
      (Fin (2 ^ (orderWidth P + orderWidth P + tailEncoding.width))) :=
  let _ : Finite (SemanticInput P) :=
    Finite.of_injective (sourceLabel P tailEncoding cleanTail)
      (sourceLabel_injective P tailEncoding cleanTail cleanTail_injective)
  Classical.choose
    (Equiv.Perm.exists_extending_pair
      (sourceLabel P tailEncoding cleanTail)
      (targetLabel P tailEncoding cleanTail)
      (sourceLabel_injective P tailEncoding cleanTail cleanTail_injective)
      (targetLabel_injective P tailEncoding cleanTail cleanTail_injective))

/-- The total permutation agrees with the prescribed action on every clean
semantic source. -/
theorem permutation_sourceLabel (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail)
    (input : SemanticInput P) :
    permutation P tailEncoding cleanTail cleanTail_injective
        (sourceLabel P tailEncoding cleanTail input) =
      targetLabel P tailEncoding cleanTail input := by
  let _ : Finite (SemanticInput P) :=
    Finite.of_injective (sourceLabel P tailEncoding cleanTail)
      (sourceLabel_injective P tailEncoding cleanTail cleanTail_injective)
  exact (Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (sourceLabel P tailEncoding cleanTail)
      (targetLabel P tailEncoding cleanTail)
      (sourceLabel_injective P tailEncoding cleanTail cleanTail_injective)
      (targetLabel_injective P tailEncoding cleanTail cleanTail_injective))) input

/-- Ideal unitary induced by the total basis permutation. -/
def operator (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) :
    UnitaryOperator
      (Qubits (orderWidth P + orderWidth P + tailEncoding.width)) :=
  UnitaryOperator.ofPerm
    (permutation P tailEncoding cleanTail cleanTail_injective).symm

/-- The ideal unitary has the prescribed clean basis action. -/
theorem operator_basisAction (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail)
    (input : SemanticInput P) :
    (operator P tailEncoding cleanTail cleanTail_injective).apply
        (NormalizedVector.ket
          (sourceLabel P tailEncoding cleanTail input)) =
      NormalizedVector.ket
        (targetLabel P tailEncoding cleanTail input) := by
  rw [operator, UnitaryOperator.ofPerm_apply_ket]
  exact congrArg NormalizedVector.ket
    (permutation_sourceLabel P tailEncoding cleanTail
      cleanTail_injective input)

/-- Fixed analysis-only coordinate for the ideal clean-tail group action. -/
def oracleSubroutineLabel (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) : Resource.SubroutineLabel :=
  { family := "finite-cyclic-dlp"
    name := "ideal-clean-tail-group-action"
    parameters := [P.order, orderWidth P, tailEncoding.width] }

namespace EndpointDeclarations

/-- One ideal clean-tail group-action leaf at a caller-selected placement. -/
def oracleLeafAt (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail)
    (systemIdx : List Nat) :
    UnitaryLeaf (Qubits (orderWidth P + orderWidth P + tailEncoding.width)) :=
  UnitaryLeaf.subroutine (oracleSubroutineLabel P tailEncoding) systemIdx
    (operator P tailEncoding cleanTail cleanTail_injective)

end EndpointDeclarations

/-- Analysis-only ideal oracle circuit on the complete natural carrier. -/
def oracleCircuit (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) :
    UnitaryCircuit (Qubits (orderWidth P + orderWidth P + tailEncoding.width)) :=
  UnitaryCircuit.ofLeaf
    (EndpointDeclarations.oracleLeafAt P tailEncoding cleanTail
      cleanTail_injective
      (List.range (orderWidth P + orderWidth P + tailEncoding.width)))
    List.nodup_range

@[simp] theorem oracleCircuit_physical_idx (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) :
    (oracleCircuit P tailEncoding cleanTail cleanTail_injective).physical_idx =
      List.range (orderWidth P + orderWidth P + tailEncoding.width) :=
  rfl

/-- The analysis-only circuit inherits the ideal unitary's clean action. -/
theorem oracleCircuit_basisAction (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail)
    (input : SemanticInput P) :
    (oracleCircuit P tailEncoding cleanTail cleanTail_injective).applyNormalized
        (NormalizedVector.ket
          (sourceLabel P tailEncoding cleanTail input)) =
      NormalizedVector.ket
        (targetLabel P tailEncoding cleanTail input) := by
  change (operator P tailEncoding cleanTail cleanTail_injective).apply
      (NormalizedVector.ket (sourceLabel P tailEncoding cleanTail input)) = _
  exact operator_basisAction P tailEncoding cleanTail cleanTail_injective input

/-- Package the ideal permutation circuit as a clean-tail concrete access. -/
def access (P : KnownOrderProblem G)
    (tailEncoding : BinaryLabelEncoding Tail) (cleanTail : G → Tail)
    (cleanTail_injective : Function.Injective cleanTail) : ConcreteCircuitAccess P where
  Tail := Tail
  tailEncoding := tailEncoding
  cleanTail := cleanTail
  cleanTail_injective := cleanTail_injective
  oracleCircuit :=
    oracleCircuit P tailEncoding cleanTail cleanTail_injective
  oracleCircuit_physical_idx :=
    oracleCircuit_physical_idx P tailEncoding cleanTail
      cleanTail_injective
  realizesClean := by
    intro left right workspace
    change
      (oracleCircuit P tailEncoding cleanTail cleanTail_injective).applyNormalized
          (NormalizedVector.ket
            (sourceLabel P tailEncoding cleanTail
              ((left, right), workspace))) =
        NormalizedVector.ket
          (targetLabel P tailEncoding cleanTail
            ((left, right), workspace))
    exact oracleCircuit_basisAction P tailEncoding cleanTail
      cleanTail_injective ((left, right), workspace)

end

end Ideal
end ConcreteCircuitAccess
end FiniteCyclicDLP
end QuantumAlg

end
