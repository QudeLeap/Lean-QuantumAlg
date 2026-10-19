/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Supplied.Qubits
public import QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Supplied.Qubits
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

/-!
# Native input and internally prepared exponentiation work words

The caller supplies the exponent and arbitrary XOR target on consecutive
physical identities. One zero-state preparation allocates exactly two work
words after them. The native circuit loads and unloads the identity word with
actual gates, so both internal words are returned to zero. All systems remain
live and retained [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits Nat.FixedWidth

def workKey : StorageKey := ⟨1⟩

/-- Only the two missing work words are allocated after the supplied exponent and target. -/
def workQubitLayout (exponentWidth width : Nat) : QubitLayout (width + width) where
  physical_idx wire := exponentWidth + width + wire.val
  physical_idx_injective := by
    intro left right same
    change exponentWidth + width + left.val = exponentWidth + width + right.val at same
    apply Fin.ext
    omega

def workLayout (exponentWidth width : Nat) : QuantumLayout (width + width) :=
  (workQubitLayout exponentWidth width).toQuantumLayout

lemma gidneyExponentWork_identities (exponentWidth width : Nat) :
    (workLayout exponentWidth width).identities =
      List.range' (exponentWidth + width) (width + width) := by
  change List.ofFn (fun wire : Fin (width + width) => exponentWidth + width + wire.val) = _
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

lemma gidneyExponentWork_fresh (exponentWidth width : Nat) :
    workKey ∉ (context (exponentWidth + width)).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

lemma gidneyExponentWork_disjoint (exponentWidth width : Nat) :
    List.Disjoint (workLayout exponentWidth width).identities
      (context (exponentWidth + width)).physicalIdx := by
  rw [gidneyExponentWork_identities, suppliedQubits_physicalIdx]
  apply List.disjoint_left.mpr
  intro wire work original
  have newBound := List.mem_range'.mp work
  have oldBound := List.mem_range.mp original
  omega

/-- Actual post-context after preparation retains the original input and both new work words. -/
public def preparedContext (exponentWidth width : Nat) : RuntimeCtx .quantum :=
  (context (exponentWidth + width)).addOwnedLayout workKey (workLayout exponentWidth width)
    (gidneyExponentWork_fresh exponentWidth width) (gidneyExponentWork_disjoint exponentWidth width)

/-- Both internal words use the declared zero-state preparation. -/
def workPreparation (exponentWidth width : Nat) :
    BasisPreparation (workLayout exponentWidth width) :=
  ⟨(workLayout exponentWidth width).zeroLabel⟩

/-- The actual prepared basis contains two zero words. -/
lemma gidneyExponentWork_prepared_words (exponentWidth width : Nat)
    :
    (prodEquiv (m := width) (n := width)).symm
      ((workQubitLayout exponentWidth width).binaryIndexEquiv
        (workPreparation exponentWidth width).value) =
      (0, 0) := by
  change (prodEquiv (m := width) (n := width)).symm
      (BinaryBasis.bigEndianEquiv (width + width)
        (fun _ : Fin (width + width) => (0 : Fin 2))) = (0, 0)
  rw [BinaryBasis.bigEndianEquiv_zero]
  apply Prod.ext <;> apply Fin.ext
  · simpa using
      (prodEquiv_symm_fst_val (m := width) (n := width)
        (0 : Fin (2 ^ (width + width))))
  · simpa using
      (prodEquiv_symm_snd_val (m := width) (n := width)
        (0 : Fin (2 ^ (width + width))))

/-- Context order places the freshly prepared work before the unchanged supplied input. -/
public lemma gidneyExponentPreparedContext_physical (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).physicalIdx =
      List.range' (exponentWidth + width) (width + width) ++
        List.range (exponentWidth + width) := by
  change ((workLayout exponentWidth width).wires ++
    (context (exponentWidth + width)).quantumWires).map QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (workLayout exponentWidth width).identities ++
    (context (exponentWidth + width)).physicalIdx = _
  rw [gidneyExponentWork_identities, suppliedQubits_physicalIdx]

lemma gidneyExponentPreparedContext_contains (exponentWidth width : Nat) :
    List.range (exponentWidth + 3 * width) ⊆
      (preparedContext exponentWidth width).physicalIdx := by
  intro wire present
  rw [gidneyExponentPreparedContext_physical, List.mem_append]
  have bound := List.mem_range.mp present
  by_cases old : wire < exponentWidth + width
  · exact Or.inr (List.mem_range.mpr old)
  · apply Or.inl
    apply List.mem_range'.mpr
    refine ⟨wire - (exponentWidth + width), by omega, ?_⟩
    simp only [Nat.one_mul]
    omega

end

end QuantumAlg.MAU.Exponentiation.Gidney
