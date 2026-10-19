/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Preparation

/-!
# Actual two-word input and fixed-auxiliary basis assembly

The old context supplies two actual n-bit words. The new auxiliary wires
have the original shared-EEA identities. Their runtime preparation order
is auxiliary, input, target; the native frame order places the first input
inside Work2 and the target after the complete source frame. The explicit
equivalence below reuses the already proved single-input per-wire assembly
and the unchanged target word [LYL+26, sec_EEA/sub_regshare.tex:16-26].

The equivalence and every coordinate law allow arbitrary fresh basis values.
They can therefore serve either the standalone XOR-output circuit or the
original in-place measured-division layout with its different fixed initial
workspace values [LYL+26, sec_point_add/sec_point_add.tex:51-79]. No physical
gate or zero-cost wire permutation is inferred from this representation
equivalence. Actual native gates retain their original physical identities.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseAssembly

noncomputable section

open Execution InversePreparation

private def oldEquiv (width : Nat) :
    (before width).register.Index ≃
      ((InputPreparation.before width).register.Index × Fin (2 ^ width)) :=
  (inputBasisEquiv width).trans
    (Equiv.prodCongr (InputPreparation.inputBasisEquiv width).symm (Equiv.refl _))

/-- The single-input source assembly and the target both retain their exact wire identities. -/
def basisEquiv (width : Nat) :
    (after width).register.Index ≃ (Qubits (OutputCopy.encoding width).width).Index :=
  (assembly width).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (oldEquiv width)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr
          ((InputAssembly.assembly width).trans (InputAssembly.basisEquiv width))
          (Equiv.refl _)).trans (prodEquiv (m := (encoding width).width) (n := width)))))

/-- Read the first original word through the already proved original input basis. -/
def oldInput (width : Nat) (old : (before width).register.Index) :
    (InputPreparation.before width).register.Index :=
  (InputPreparation.inputBasisEquiv width).symm ((inputBasisEquiv width old).1)

/-- Exact assembly holds for all auxiliary values and both arbitrary original words. -/
lemma basisEquiv_assembly (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) :
    basisEquiv width (assembly width (fresh, old)) =
      prodEquiv (m := (encoding width).width) (n := width)
        (InputAssembly.basisEquiv width
          (InputAssembly.assembly width (fresh, oldInput width old)),
          (inputBasisEquiv width old).2) := by
  let encodePair :
      ((InputPreparation.auxiliaryLayout width).register.Index × (before width).register.Index) →
        (Qubits (OutputCopy.encoding width).width).Index := fun pair =>
    prodEquiv (m := (encoding width).width) (n := width)
      (InputAssembly.basisEquiv width
        (InputAssembly.assembly width (pair.1, oldInput width pair.2)),
        (inputBasisEquiv width pair.2).2)
  change encodePair ((assembly width).symm (assembly width (fresh, old))) = encodePair (fresh, old)
  exact congrArg encodePair ((assembly width).symm_apply_apply (fresh, old))

/-- An auxiliary wire keeps its already declared source identity in the complete two-word layout. -/
def auxiliaryPosition (width : Nat) (index : Fin (InputPreparation.auxiliaryWidth width)) :
    Fin (OutputCopy.encoding width).width :=
  ⟨(InputAssembly.auxiliaryPosition width index).val, by
    have bound := (InputAssembly.auxiliaryPosition width index).isLt
    change _ < (encoding width).width + width
    omega⟩

/-- The original first input remains at its source Work2 physical address. -/
def inputPosition (width : Nat) (index : Fin width) : Fin (OutputCopy.encoding width).width :=
  ⟨(InputAssembly.inputPosition width index).val, by
    have bound := (InputAssembly.inputPosition width index).isLt
    change _ < (encoding width).width + width
    omega⟩

/-- The supplied target remains after the original complete source frame. -/
def targetPosition (width : Nat) (index : Fin width) : Fin (OutputCopy.encoding width).width :=
  ⟨(encoding width).width + index.val, by
    have bound := index.isLt
    change _ < (encoding width).width + width
    omega⟩

private lemma auxiliary_rev (width : Nat)
    (index : Fin (InputPreparation.auxiliaryWidth width)) :
    (auxiliaryPosition width index).rev.val =
      width + (InputAssembly.auxiliaryPosition width index).rev.val := by
  simp only [auxiliaryPosition, Fin.val_rev]
  change (encoding width).width + width - (_ + 1) = _
  have bound := (InputAssembly.auxiliaryPosition width index).isLt
  omega

private lemma input_rev (width : Nat) (index : Fin width) :
    (inputPosition width index).rev.val =
      width + (InputAssembly.inputPosition width index).rev.val := by
  simp only [inputPosition, Fin.val_rev]
  change (encoding width).width + width - (_ + 1) = _
  have bound := (InputAssembly.inputPosition width index).isLt
  omega

private lemma target_rev (width : Nat) (index : Fin width) :
    (targetPosition width index).rev.val = index.rev.val := by
  simp only [targetPosition, Fin.val_rev]
  change (encoding width).width + width - ((encoding width).width + index.val + 1) = _
  omega

/-- Every auxiliary position retains its actual original value, with both old words arbitrary. -/
lemma basisEquiv_auxiliary (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin (InputPreparation.auxiliaryWidth width)) :
    (basisEquiv width (assembly width (fresh, old))).val.testBit
      (auxiliaryPosition width index).rev.val = finTwoEquiv (fresh index) := by
  rw [basisEquiv_assembly, auxiliary_rev, prodEquiv_testBit_left]
  exact InputAssembly.basisEquiv_auxiliary width fresh (oldInput width old) index

/-- Every original input bit retains its actual source identity in the joint assembly. -/
lemma basisEquiv_input (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin width) :
    (basisEquiv width (assembly width (fresh, old))).val.testBit
      (inputPosition width index).rev.val =
        (inputBasisEquiv width old).1.val.testBit index.rev.val := by
  rw [basisEquiv_assembly, input_rev, prodEquiv_testBit_left]
  have actual := InputAssembly.basisEquiv_input width fresh (oldInput width old) index
  simpa only [oldInput, Equiv.apply_symm_apply] using actual

/-- Every supplied target bit retains its original rightmost physical identity and value. -/
lemma basisEquiv_target (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin width) :
    (basisEquiv width (assembly width (fresh, old))).val.testBit
      (targetPosition width index).rev.val =
        (inputBasisEquiv width old).2.val.testBit index.rev.val := by
  rw [basisEquiv_assembly, target_rev, prodEquiv_testBit_right]

/-- The fixed preparation produces exactly the literal source initial frame and arbitrary target. -/
lemma prepared_initial (modulus : Nat) (old : (before modulus.size).register.Index) :
    basisEquiv modulus.size
        (assembly modulus.size ((InputPreparation.preparation modulus).value, old)) =
      (OutputCopy.encoding modulus.size).encode
        (InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
          (inputBasisEquiv modulus.size old).2) := by
  rw [basisEquiv_assembly]
  have source := InputPreparedFrame.basisEquiv_prepared_initial modulus
    (oldInput modulus.size old)
  have exactInput : InputPreparation.inputBasisEquiv modulus.size (oldInput modulus.size old) =
      (inputBasisEquiv modulus.size old).1 :=
    (InputPreparation.inputBasisEquiv modulus.size).apply_symm_apply _
  rw [exactInput] at source
  exact congrArg
    (fun frame : Fin (2 ^ (encoding modulus.size).width) =>
      prodEquiv (m := (encoding modulus.size).width) (n := modulus.size)
        (frame, (inputBasisEquiv modulus.size old).2)) source

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseAssembly
