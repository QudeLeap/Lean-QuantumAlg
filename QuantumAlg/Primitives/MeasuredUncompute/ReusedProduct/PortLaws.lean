/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct
import all QuantumAlg.Primitives.MeasuredUncompute.Product.PortLaws
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.Readout

/-!
# Actual product recomputation at the original X/A/Y ports

The same placed native multiplication preserves X, saved A and all Γ,
while accumulating X times A into Y. The complete equations follow from
its existing actual full-label realization and the proved physical word
reads [LYL+26, sec_point_add/sec_point_add.tex:85-101].
-/

namespace QuantumAlg.MeasuredUncompute.ReusedProductPortLaws

noncomputable section

open ProductPlacement ProductReadout

/-- The actual recomputation leaves every bit of X unchanged. -/
lemma compute_input (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) :
    input width (ReusedProduct.computeStep width modulus state) = input width state :=
  (ReusedProductReadout.input_symm width _).trans
    ((ProductPortLaws.step_input width modulus _).trans
      (ReusedProductReadout.input width state))

/-- The actual recomputation leaves the complete saved result in A unchanged. -/
lemma compute_accumulator (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) :
    accumulator width (ReusedProduct.computeStep width modulus state) =
      accumulator width state :=
  (ReusedProductReadout.accumulator_symm width _).trans
    ((ProductPortLaws.step_numerator width modulus _).trans
      (ReusedProductReadout.numerator width state))

/-- Every retained padding and history bit survives both workspace placement and recomputation. -/
lemma compute_history (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) :
    history width (ReusedProduct.computeStep width modulus state) = history width state :=
  (ReusedProductReadout.history_symm width _).trans
    ((product_history width modulus _).trans (ReusedProductReadout.history width state))

/-- The actual existing Y word receives the modular product of X and saved A. -/
lemma compute_numerator (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width)
    (valid : (numerator width state).val < modulus.val) :
    (numerator width (ReusedProduct.computeStep width modulus state)).val =
      ((numerator width state).val + (input width state).val *
        (accumulator width state).val) % modulus.val := by
  have groupedValid :
      (accumulator width ((WorkspaceReuse.placement width).grouping state)).val < modulus.val := by
    rw [ReusedProductReadout.accumulator]
    exact valid
  have arithmetic := ProductPortLaws.step_accumulator width modulus
    ((WorkspaceReuse.placement width).grouping state) groupedValid
  rw [ReusedProductReadout.accumulator, ReusedProductReadout.input,
    ReusedProductReadout.numerator] at arithmetic
  have actual := congrArg (fun value : Fin (2 ^ width) => value.val)
    (ReusedProductReadout.numerator_symm width
      (NativeProductFrame.step width modulus ((WorkspaceReuse.placement width).grouping state)))
  exact actual.trans arithmetic

end

end QuantumAlg.MeasuredUncompute.ReusedProductPortLaws
