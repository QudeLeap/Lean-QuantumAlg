/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word44Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word44State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word44Step0 :
    word44Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word44State1 := by decide +kernel

private def word44Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word44State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word44Step1 :
    word44Chunk1.foldl (fun acc a => a.applyPacked acc)
      word44State1 = word44State2 := by decide +kernel

private def word44Chunk2 : List Letter := [.h, .s, .s, .s, .h, .t, .h, .t]
private def word44State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word44Step2 :
    word44Chunk2.foldl (fun acc a => a.applyPacked acc)
      word44State2 = word44State3 := by decide +kernel

private def word44Chunk3 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word44State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word44Step3 :
    word44Chunk3.foldl (fun acc a => a.applyPacked acc)
      word44State3 = word44State4 := by decide +kernel

private def word44Chunk4 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word44State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word44Step4 :
    word44Chunk4.foldl (fun acc a => a.applyPacked acc)
      word44State4 = word44State5 := by decide +kernel

private def word44Chunk5 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word44State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word44Step5 :
    word44Chunk5.foldl (fun acc a => a.applyPacked acc)
      word44State5 = word44State6 := by decide +kernel

private def word44Chunk6 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word44State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word44Step6 :
    word44Chunk6.foldl (fun acc a => a.applyPacked acc)
      word44State6 = word44State7 := by decide +kernel

private def word44Chunk7 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State8 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((21 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-13 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word44Step7 :
    word44Chunk7.foldl (fun acc a => a.applyPacked acc)
      word44State7 = word44State8 := by decide +kernel

private def word44Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word44State9 : PackedMat2 :=
    ⟨⟨⟨((-33 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 6),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((-33 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 6)⟩,
       ⟨((-33 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word44Step8 :
    word44Chunk8.foldl (fun acc a => a.applyPacked acc)
      word44State8 = word44State9 := by decide +kernel

private def word44Chunk9 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State10 : PackedMat2 :=
    ⟨⟨⟨((53 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-49 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 7)⟩,
       ⟨((13 : Dyadic) * half ^ 7),
        ((-35 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((71 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 7)⟩,
       ⟨((69 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 7),
        ((-51 : Dyadic) * half ^ 7)⟩,
       ⟨((-29 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word44Step9 :
    word44Chunk9.foldl (fun acc a => a.applyPacked acc)
      word44State9 = word44State10 := by decide +kernel

private def word44Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word44State11 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((-53 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 7),
        ((93 : Dyadic) * half ^ 8)⟩,
       ⟨((-97 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-97 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 8)⟩,
       ⟨((19 : Dyadic) * half ^ 7),
        ((93 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 6),
        ((53 : Dyadic) * half ^ 8)⟩,
       ⟨((-13 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word44Step10 :
    word44Chunk10.foldl (fun acc a => a.applyPacked acc)
      word44State10 = word44State11 := by decide +kernel

private def word44Chunk11 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word44State12 : PackedMat2 :=
    ⟨⟨⟨((-51 : Dyadic) * half ^ 8),
        ((183 : Dyadic) * half ^ 9)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-105 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((167 : Dyadic) * half ^ 8),
        ((47 : Dyadic) * half ^ 9)⟩,
       ⟨((17 : Dyadic) * half ^ 6),
        ((-77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 8),
        ((-235 : Dyadic) * half ^ 9)⟩,
       ⟨((-31 : Dyadic) * half ^ 7),
        ((-99 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((39 : Dyadic) * half ^ 8),
        ((-115 : Dyadic) * half ^ 9)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word44Step11 :
    word44Chunk11.foldl (fun acc a => a.applyPacked acc)
      word44State11 = word44State12 := by decide +kernel

private def word44Chunk12 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word44State13 : PackedMat2 :=
    ⟨⟨⟨((315 : Dyadic) * half ^ 9),
        ((-37 : Dyadic) * half ^ 9)⟩,
       ⟨((11 : Dyadic) * half ^ 9),
        ((51 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 9),
        ((129 : Dyadic) * half ^ 8)⟩,
       ⟨((141 : Dyadic) * half ^ 9),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 9),
        ((129 : Dyadic) * half ^ 8)⟩,
       ⟨((-141 : Dyadic) * half ^ 9),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-315 : Dyadic) * half ^ 9),
        ((37 : Dyadic) * half ^ 9)⟩,
       ⟨((11 : Dyadic) * half ^ 9),
        ((51 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word44Step12 :
    word44Chunk12.foldl (fun acc a => a.applyPacked acc)
      word44State12 = word44State13 := by decide +kernel

private def word44Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word44State14 : PackedMat2 :=
    ⟨⟨⟨((173 : Dyadic) * half ^ 10),
        ((89 : Dyadic) * half ^ 8)⟩,
       ⟨((675 : Dyadic) * half ^ 10),
        ((-75 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((361 : Dyadic) * half ^ 10),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((131 : Dyadic) * half ^ 10),
        ((247 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((131 : Dyadic) * half ^ 10),
        ((247 : Dyadic) * half ^ 10)⟩,
       ⟨((361 : Dyadic) * half ^ 10),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-675 : Dyadic) * half ^ 10),
        ((75 : Dyadic) * half ^ 10)⟩,
       ⟨((-173 : Dyadic) * half ^ 10),
        ((-89 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word44Step13 :
    word44Chunk13.foldl (fun acc a => a.applyPacked acc)
      word44State13 = word44State14 := by decide +kernel

private def word44Chunk14 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word44State15 : PackedMat2 :=
    ⟨⟨⟨((1423 : Dyadic) * half ^ 11),
        ((-319 : Dyadic) * half ^ 11)⟩,
       ⟨((883 : Dyadic) * half ^ 11),
        ((73 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-717 : Dyadic) * half ^ 11),
        ((-365 : Dyadic) * half ^ 11)⟩,
       ⟨((-213 : Dyadic) * half ^ 11),
        ((77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-673 : Dyadic) * half ^ 11),
        ((-63 : Dyadic) * half ^ 9)⟩,
       ⟨((57 : Dyadic) * half ^ 11),
        ((465 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((611 : Dyadic) * half ^ 11),
        ((-135 : Dyadic) * half ^ 10)⟩,
       ⟨((-27 : Dyadic) * half ^ 11),
        ((1153 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word44Step14 :
    word44Chunk14.foldl (fun acc a => a.applyPacked acc)
      word44State14 = word44State15 := by decide +kernel

private def word44Chunk15 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State16 : PackedMat2 :=
    ⟨⟨⟨((-1795 : Dyadic) * half ^ 11),
        ((45 : Dyadic) * half ^ 12)⟩,
       ⟨((285 : Dyadic) * half ^ 11),
        ((1007 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((217 : Dyadic) * half ^ 10),
        ((-465 : Dyadic) * half ^ 12)⟩,
       ⟨((-147 : Dyadic) * half ^ 10),
        ((15 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-147 : Dyadic) * half ^ 10),
        ((15 : Dyadic) * half ^ 12)⟩,
       ⟨((217 : Dyadic) * half ^ 10),
        ((-465 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-285 : Dyadic) * half ^ 11),
        ((-1007 : Dyadic) * half ^ 12)⟩,
       ⟨((1795 : Dyadic) * half ^ 11),
        ((-45 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word44Step15 :
    word44Chunk15.foldl (fun acc a => a.applyPacked acc)
      word44State15 = word44State16 := by decide +kernel

private def word44Chunk16 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word44State17 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 12),
        ((-4737 : Dyadic) * half ^ 13)⟩,
       ⟨((-137 : Dyadic) * half ^ 10),
        ((-113 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((355 : Dyadic) * half ^ 12),
        ((-657 : Dyadic) * half ^ 13)⟩,
       ⟨((-1 : Dyadic) * half ^ 7),
        ((-3133 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1895 : Dyadic) * half ^ 12),
        ((-323 : Dyadic) * half ^ 13)⟩,
       ⟨((-619 : Dyadic) * half ^ 11),
        ((-387 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2425 : Dyadic) * half ^ 12),
        ((-563 : Dyadic) * half ^ 13)⟩,
       ⟨((-289 : Dyadic) * half ^ 9),
        ((533 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word44Step16 :
    word44Chunk16.foldl (fun acc a => a.applyPacked acc)
      word44State16 = word44State17 := by decide +kernel

private def word44Chunk17 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word44State18 : PackedMat2 :=
    ⟨⟨⟨((-4221 : Dyadic) * half ^ 13),
        ((-1525 : Dyadic) * half ^ 13)⟩,
       ⟨((227 : Dyadic) * half ^ 13),
        ((-3245 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-77 : Dyadic) * half ^ 13),
        ((989 : Dyadic) * half ^ 12)⟩,
       ⟨((-2763 : Dyadic) * half ^ 13),
        ((251 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-77 : Dyadic) * half ^ 13),
        ((989 : Dyadic) * half ^ 12)⟩,
       ⟨((2763 : Dyadic) * half ^ 13),
        ((-251 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((4221 : Dyadic) * half ^ 13),
        ((1525 : Dyadic) * half ^ 13)⟩,
       ⟨((227 : Dyadic) * half ^ 13),
        ((-3245 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word44Step17 :
    word44Chunk17.foldl (fun acc a => a.applyPacked acc)
      word44State17 = word44State18 := by decide +kernel

private def word44Chunk18 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word44State19 : PackedMat2 :=
    ⟨⟨⟨((1763 : Dyadic) * half ^ 13),
        ((-173 : Dyadic) * half ^ 10)⟩,
       ⟨((-37 : Dyadic) * half ^ 7),
        ((-3601 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 8),
        ((9213 : Dyadic) * half ^ 14)⟩,
       ⟨((225 : Dyadic) * half ^ 10),
        ((-1095 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 8),
        ((-9213 : Dyadic) * half ^ 14)⟩,
       ⟨((225 : Dyadic) * half ^ 10),
        ((-1095 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1763 : Dyadic) * half ^ 13),
        ((-173 : Dyadic) * half ^ 10)⟩,
       ⟨((37 : Dyadic) * half ^ 7),
        ((3601 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word44Step18 :
    word44Chunk18.foldl (fun acc a => a.applyPacked acc)
      word44State18 = word44State19 := by decide +kernel

private def word44Chunk19 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word44State20 : PackedMat2 :=
    ⟨⟨⟨((6223 : Dyadic) * half ^ 15),
        ((8959 : Dyadic) * half ^ 15)⟩,
       ⟨((7727 : Dyadic) * half ^ 15),
        ((-1159 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((21195 : Dyadic) * half ^ 15),
        ((2859 : Dyadic) * half ^ 15)⟩,
       ⟨((-5149 : Dyadic) * half ^ 15),
        ((4341 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5823 : Dyadic) * half ^ 15),
        ((3293 : Dyadic) * half ^ 13)⟩,
       ⟨((-11541 : Dyadic) * half ^ 15),
        ((-8023 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-18231 : Dyadic) * half ^ 15),
        ((47 : Dyadic) * half ^ 11)⟩,
       ⟨((-313 : Dyadic) * half ^ 15),
        ((6975 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word44Step19 :
    word44Chunk19.foldl (fun acc a => a.applyPacked acc)
      word44State19 = word44State20 := by decide +kernel

private def word44Chunk20 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word44State21 : PackedMat2 :=
    ⟨⟨⟨((15693 : Dyadic) * half ^ 15),
        ((9177 : Dyadic) * half ^ 15)⟩,
       ⟨((-1793 : Dyadic) * half ^ 14),
        ((2001 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1161 : Dyadic) * half ^ 14),
        ((1777 : Dyadic) * half ^ 15)⟩,
       ⟨((23143 : Dyadic) * half ^ 15),
        ((-5781 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((23143 : Dyadic) * half ^ 15),
        ((-5781 : Dyadic) * half ^ 15)⟩,
       ⟨((1161 : Dyadic) * half ^ 14),
        ((1777 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1793 : Dyadic) * half ^ 14),
        ((-2001 : Dyadic) * half ^ 14)⟩,
       ⟨((-15693 : Dyadic) * half ^ 15),
        ((-9177 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word44Step20 :
    word44Chunk20.foldl (fun acc a => a.applyPacked acc)
      word44State20 = word44State21 := by decide +kernel

private def word44Chunk21 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word44State22 : PackedMat2 :=
    ⟨⟨⟨((7191 : Dyadic) * half ^ 15),
        ((44203 : Dyadic) * half ^ 17)⟩,
       ⟨((19693 : Dyadic) * half ^ 16),
        ((36647 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-7207 : Dyadic) * half ^ 15),
        ((35485 : Dyadic) * half ^ 17)⟩,
       ⟨((-22419 : Dyadic) * half ^ 16),
        ((37733 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((7207 : Dyadic) * half ^ 15),
        ((-35485 : Dyadic) * half ^ 17)⟩,
       ⟨((-22419 : Dyadic) * half ^ 16),
        ((37733 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((7191 : Dyadic) * half ^ 15),
        ((44203 : Dyadic) * half ^ 17)⟩,
       ⟨((-19693 : Dyadic) * half ^ 16),
        ((-36647 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word44Step21 :
    word44Chunk21.foldl (fun acc a => a.applyPacked acc)
      word44State21 = word44State22 := by decide +kernel

private def word44Chunk22 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word44State23 : PackedMat2 :=
    ⟨⟨⟨((-29173 : Dyadic) * half ^ 17),
        ((-47083 : Dyadic) * half ^ 17)⟩,
       ⟨((71723 : Dyadic) * half ^ 17),
        ((2399 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((39487 : Dyadic) * half ^ 17),
        ((-17631 : Dyadic) * half ^ 16)⟩,
       ⟨((4189 : Dyadic) * half ^ 17),
        ((-18289 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((329 : Dyadic) * half ^ 15),
        ((17649 : Dyadic) * half ^ 17)⟩,
       ⟨((2245 : Dyadic) * half ^ 12),
        ((-10919 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((24741 : Dyadic) * half ^ 16),
        ((3153 : Dyadic) * half ^ 13)⟩,
       ⟨((-11171 : Dyadic) * half ^ 15),
        ((21275 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word44Step22 :
    word44Chunk22.foldl (fun acc a => a.applyPacked acc)
      word44State22 = word44State23 := by decide +kernel

private def word44Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word44State24 : PackedMat2 :=
    ⟨⟨⟨((-96221 : Dyadic) * half ^ 18),
        ((15407 : Dyadic) * half ^ 17)⟩,
       ⟨((-185067 : Dyadic) * half ^ 18),
        ((7055 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((29363 : Dyadic) * half ^ 18),
        ((5743 : Dyadic) * half ^ 14)⟩,
       ⟨((-65715 : Dyadic) * half ^ 18),
        ((-23929 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-115817 : Dyadic) * half ^ 18),
        ((-47539 : Dyadic) * half ^ 18)⟩,
       ⟨((67959 : Dyadic) * half ^ 18),
        ((-71 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((23759 : Dyadic) * half ^ 18),
        ((44423 : Dyadic) * half ^ 18)⟩,
       ⟨((-37869 : Dyadic) * half ^ 18),
        ((35161 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word44Step23 :
    word44Chunk23.foldl (fun acc a => a.applyPacked acc)
      word44State23 = word44State24 := by decide +kernel

private def word44Chunk24 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word44State25 : PackedMat2 :=
    ⟨⟨⟨((54333 : Dyadic) * half ^ 17),
        ((-48791 : Dyadic) * half ^ 17)⟩,
       ⟨((-73913 : Dyadic) * half ^ 18),
        ((-89091 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((76635 : Dyadic) * half ^ 18),
        ((42053 : Dyadic) * half ^ 18)⟩,
       ⟨((41643 : Dyadic) * half ^ 17),
        ((9559 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-41643 : Dyadic) * half ^ 17),
        ((-9559 : Dyadic) * half ^ 18)⟩,
       ⟨((-76635 : Dyadic) * half ^ 18),
        ((-42053 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-73913 : Dyadic) * half ^ 18),
        ((-89091 : Dyadic) * half ^ 18)⟩,
       ⟨((54333 : Dyadic) * half ^ 17),
        ((-48791 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word44Step24 :
    word44Chunk24.foldl (fun acc a => a.applyPacked acc)
      word44State24 = word44State25 := by decide +kernel

private def word44Chunk25 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word44State26 : PackedMat2 :=
    ⟨⟨⟨((-88757 : Dyadic) * half ^ 19),
        ((388863 : Dyadic) * half ^ 20)⟩,
       ⟨((-15141 : Dyadic) * half ^ 16),
        ((-502911 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((9311 : Dyadic) * half ^ 19),
        ((-48427 : Dyadic) * half ^ 20)⟩,
       ⟨((-11365 : Dyadic) * half ^ 16),
        ((285431 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((9311 : Dyadic) * half ^ 19),
        ((-48427 : Dyadic) * half ^ 20)⟩,
       ⟨((11365 : Dyadic) * half ^ 16),
        ((-285431 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((88757 : Dyadic) * half ^ 19),
        ((-388863 : Dyadic) * half ^ 20)⟩,
       ⟨((-15141 : Dyadic) * half ^ 16),
        ((-502911 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word44Step25 :
    word44Chunk25.foldl (fun acc a => a.applyPacked acc)
      word44State25 = word44State26 := by decide +kernel

private def word44Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word44State27 : PackedMat2 :=
    ⟨⟨⟨((290917 : Dyadic) * half ^ 20),
        ((-175123 : Dyadic) * half ^ 21)⟩,
       ⟨((-45297 : Dyadic) * half ^ 19),
        ((-461995 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-337113 : Dyadic) * half ^ 20),
        ((62177 : Dyadic) * half ^ 21)⟩,
       ⟨((-438307 : Dyadic) * half ^ 19),
        ((-34283 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-13947 : Dyadic) * half ^ 20),
        ((1213727 : Dyadic) * half ^ 21)⟩,
       ⟨((-24115 : Dyadic) * half ^ 19),
        ((-539501 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-318559 : Dyadic) * half ^ 20),
        ((200323 : Dyadic) * half ^ 21)⟩,
       ⟨((35859 : Dyadic) * half ^ 18),
        ((381511 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word44Step26 :
    word44Chunk26.foldl (fun acc a => a.applyPacked acc)
      word44State26 = word44State27 := by decide +kernel

private def word44Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word44State28 : PackedMat2 :=
    ⟨⟨⟨((320593 : Dyadic) * half ^ 21),
        ((28279 : Dyadic) * half ^ 19)⟩,
       ⟨((915509 : Dyadic) * half ^ 21),
        ((583763 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-785413 : Dyadic) * half ^ 21),
        ((267379 : Dyadic) * half ^ 20)⟩,
       ⟨((-1237537 : Dyadic) * half ^ 21),
        ((121773 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1237537 : Dyadic) * half ^ 21),
        ((-121773 : Dyadic) * half ^ 21)⟩,
       ⟨((785413 : Dyadic) * half ^ 21),
        ((-267379 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((915509 : Dyadic) * half ^ 21),
        ((583763 : Dyadic) * half ^ 21)⟩,
       ⟨((320593 : Dyadic) * half ^ 21),
        ((28279 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word44Step27 :
    word44Chunk27.foldl (fun acc a => a.applyPacked acc)
      word44State27 = word44State28 := by decide +kernel

private def word44Chunk28 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word44State29 : PackedMat2 :=
    ⟨⟨⟨((137065 : Dyadic) * half ^ 20),
        ((-384943 : Dyadic) * half ^ 22)⟩,
       ⟨((568383 : Dyadic) * half ^ 20),
        ((493867 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1611281 : Dyadic) * half ^ 21),
        ((-323423 : Dyadic) * half ^ 22)⟩,
       ⟨((-110637 : Dyadic) * half ^ 21),
        ((-589663 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-456543 : Dyadic) * half ^ 21),
        ((375161 : Dyadic) * half ^ 20)⟩,
       ⟨((65 : Dyadic) * half ^ 10),
        ((860959 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-27231 : Dyadic) * half ^ 20),
        ((-88181 : Dyadic) * half ^ 18)⟩,
       ⟨((439405 : Dyadic) * half ^ 21),
        ((215659 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word44Step28 :
    word44Chunk28.foldl (fun acc a => a.applyPacked acc)
      word44State28 = word44State29 := by decide +kernel

private def word44Chunk29 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word44State30 : PackedMat2 :=
    ⟨⟨⟨((-494563 : Dyadic) * half ^ 20),
        ((1555037 : Dyadic) * half ^ 23)⟩,
       ⟨((901117 : Dyadic) * half ^ 22),
        ((3610507 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-16703 : Dyadic) * half ^ 18),
        ((2401329 : Dyadic) * half ^ 23)⟩,
       ⟨((1461023 : Dyadic) * half ^ 22),
        ((317939 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((16703 : Dyadic) * half ^ 18),
        ((-2401329 : Dyadic) * half ^ 23)⟩,
       ⟨((1461023 : Dyadic) * half ^ 22),
        ((317939 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-494563 : Dyadic) * half ^ 20),
        ((1555037 : Dyadic) * half ^ 23)⟩,
       ⟨((-901117 : Dyadic) * half ^ 22),
        ((-3610507 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word44Step29 :
    word44Chunk29.foldl (fun acc a => a.applyPacked acc)
      word44State29 = word44State30 := by decide +kernel

private def word44Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word44State31 : PackedMat2 :=
    ⟨⟨⟨((-992295 : Dyadic) * half ^ 23),
        ((-3158321 : Dyadic) * half ^ 23)⟩,
       ⟨((1063037 : Dyadic) * half ^ 23),
        ((-969415 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1179815 : Dyadic) * half ^ 23),
        ((-1831727 : Dyadic) * half ^ 22)⟩,
       ⟨((-2951409 : Dyadic) * half ^ 23),
        ((1088575 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1460151 : Dyadic) * half ^ 21),
        ((885797 : Dyadic) * half ^ 23)⟩,
       ⟨((46447 : Dyadic) * half ^ 18),
        ((516403 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1094453 : Dyadic) * half ^ 22),
        ((513833 : Dyadic) * half ^ 22)⟩,
       ⟨((-515967 : Dyadic) * half ^ 20),
        ((35371 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word44Step30 :
    word44Chunk30.foldl (fun acc a => a.applyPacked acc)
      word44State30 = word44State31 := by decide +kernel

private def word44Chunk31 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word44State32 : PackedMat2 :=
    ⟨⟨⟨((-2641221 : Dyadic) * half ^ 22),
        ((-3042649 : Dyadic) * half ^ 24)⟩,
       ⟨((-241963 : Dyadic) * half ^ 21),
        ((152415 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((534547 : Dyadic) * half ^ 23),
        ((2160117 : Dyadic) * half ^ 23)⟩,
       ⟨((-538671 : Dyadic) * half ^ 20),
        ((3991737 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-534547 : Dyadic) * half ^ 23),
        ((-2160117 : Dyadic) * half ^ 23)⟩,
       ⟨((-538671 : Dyadic) * half ^ 20),
        ((3991737 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2641221 : Dyadic) * half ^ 22),
        ((-3042649 : Dyadic) * half ^ 24)⟩,
       ⟨((241963 : Dyadic) * half ^ 21),
        ((-152415 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word44Step31 :
    word44Chunk31.foldl (fun acc a => a.applyPacked acc)
      word44State31 = word44State32 := by decide +kernel

private def word44Chunk32 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word44State33 : PackedMat2 :=
    ⟨⟨⟨((-9383415 : Dyadic) * half ^ 25),
        ((-6192029 : Dyadic) * half ^ 25)⟩,
       ⟨((380117 : Dyadic) * half ^ 25),
        ((-375119 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((28564685 : Dyadic) * half ^ 25),
        ((-403675 : Dyadic) * half ^ 25)⟩,
       ⟨((-9813843 : Dyadic) * half ^ 25),
        ((292961 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((9813843 : Dyadic) * half ^ 25),
        ((-292961 : Dyadic) * half ^ 21)⟩,
       ⟨((-28564685 : Dyadic) * half ^ 25),
        ((403675 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((380117 : Dyadic) * half ^ 25),
        ((-375119 : Dyadic) * half ^ 23)⟩,
       ⟨((-9383415 : Dyadic) * half ^ 25),
        ((-6192029 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word44Step32 :
    word44Chunk32.foldl (fun acc a => a.applyPacked acc)
      word44State32 = word44State33 := by decide +kernel

private def word44Chunk33 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word44State34 : PackedMat2 :=
    ⟨⟨⟨((25598259 : Dyadic) * half ^ 26),
        ((1506565 : Dyadic) * half ^ 25)⟩,
       ⟨((-43937745 : Dyadic) * half ^ 26),
        ((822815 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((16141957 : Dyadic) * half ^ 26),
        ((3146445 : Dyadic) * half ^ 24)⟩,
       ⟨((-34978479 : Dyadic) * half ^ 26),
        ((6979645 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-5606135 : Dyadic) * half ^ 26),
        ((-12780109 : Dyadic) * half ^ 25)⟩,
       ⟨((19565425 : Dyadic) * half ^ 26),
        ((-9418261 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((2190315 : Dyadic) * half ^ 26),
        ((17384001 : Dyadic) * half ^ 25)⟩,
       ⟨((-3835945 : Dyadic) * half ^ 26),
        ((9169743 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word44Step33 :
    word44Chunk33.foldl (fun acc a => a.applyPacked acc)
      word44State33 = word44State34 := by decide +kernel

private def word44Chunk34 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State35 : PackedMat2 :=
    ⟨⟨⟨((7461833 : Dyadic) * half ^ 26),
        ((5371839 : Dyadic) * half ^ 27)⟩,
       ⟨((46468687 : Dyadic) * half ^ 26),
        ((-16397689 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((6658243 : Dyadic) * half ^ 25),
        ((40762795 : Dyadic) * half ^ 27)⟩,
       ⟨((16712479 : Dyadic) * half ^ 25),
        ((5357617 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-16712479 : Dyadic) * half ^ 25),
        ((-5357617 : Dyadic) * half ^ 27)⟩,
       ⟨((-6658243 : Dyadic) * half ^ 25),
        ((-40762795 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((46468687 : Dyadic) * half ^ 26),
        ((-16397689 : Dyadic) * half ^ 27)⟩,
       ⟨((7461833 : Dyadic) * half ^ 26),
        ((5371839 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word44Step34 :
    word44Chunk34.foldl (fun acc a => a.applyPacked acc)
      word44State34 = word44State35 := by decide +kernel

private def word44Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word44State36 : PackedMat2 :=
    ⟨⟨⟨((-31203293 : Dyadic) * half ^ 27),
        ((116462843 : Dyadic) * half ^ 28)⟩,
       ⟨((4810399 : Dyadic) * half ^ 26),
        ((22623387 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-4510099 : Dyadic) * half ^ 27),
        ((76774783 : Dyadic) * half ^ 28)⟩,
       ⟨((37753771 : Dyadic) * half ^ 26),
        ((49831195 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-4510099 : Dyadic) * half ^ 27),
        ((76774783 : Dyadic) * half ^ 28)⟩,
       ⟨((-37753771 : Dyadic) * half ^ 26),
        ((-49831195 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((31203293 : Dyadic) * half ^ 27),
        ((-116462843 : Dyadic) * half ^ 28)⟩,
       ⟨((4810399 : Dyadic) * half ^ 26),
        ((22623387 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word44Step35 :
    word44Chunk35.foldl (fun acc a => a.applyPacked acc)
      word44State35 = word44State36 := by decide +kernel

private def word44Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word44State37 : PackedMat2 :=
    ⟨⟨⟨((51165973 : Dyadic) * half ^ 27),
        ((-4127595 : Dyadic) * half ^ 28)⟩,
       ⟨((-10510931 : Dyadic) * half ^ 25),
        ((21468311 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((16235267 : Dyadic) * half ^ 27),
        ((-43828559 : Dyadic) * half ^ 27)⟩,
       ⟨((27470947 : Dyadic) * half ^ 27),
        ((125206627 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((212863745 : Dyadic) * half ^ 28),
        ((351115 : Dyadic) * half ^ 23)⟩,
       ⟨((37549509 : Dyadic) * half ^ 28),
        ((21853107 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-47064217 : Dyadic) * half ^ 28),
        ((93209697 : Dyadic) * half ^ 28)⟩,
       ⟨((-38809027 : Dyadic) * half ^ 28),
        ((-9122249 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word44Step36 :
    word44Chunk36.foldl (fun acc a => a.applyPacked acc)
      word44State36 = word44State37 := by decide +kernel

private def word44Chunk37 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word44State38 : PackedMat2 :=
    ⟨⟨⟨((288696003 : Dyadic) * half ^ 29),
        ((17657751 : Dyadic) * half ^ 27)⟩,
       ⟨((225754699 : Dyadic) * half ^ 29),
        ((-44508829 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-277320347 : Dyadic) * half ^ 29),
        ((118401 : Dyadic) * half ^ 27)⟩,
       ⟨((244074761 : Dyadic) * half ^ 29),
        ((-41837473 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-244074761 : Dyadic) * half ^ 29),
        ((41837473 : Dyadic) * half ^ 29)⟩,
       ⟨((277320347 : Dyadic) * half ^ 29),
        ((-118401 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((225754699 : Dyadic) * half ^ 29),
        ((-44508829 : Dyadic) * half ^ 29)⟩,
       ⟨((288696003 : Dyadic) * half ^ 29),
        ((17657751 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word44Step37 :
    word44Chunk37.foldl (fun acc a => a.applyPacked acc)
      word44State37 = word44State38 := by decide +kernel

private def word44Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word44State39 : PackedMat2 :=
    ⟨⟨⟨((-82141863 : Dyadic) * half ^ 28),
        ((375042305 : Dyadic) * half ^ 30)⟩,
       ⟨((119249673 : Dyadic) * half ^ 28),
        ((295912099 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-8686427 : Dyadic) * half ^ 29),
        ((-279991703 : Dyadic) * half ^ 30)⟩,
       ⟨((-36149645 : Dyadic) * half ^ 29),
        ((315179369 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((17593833 : Dyadic) * half ^ 29),
        ((-5604509 : Dyadic) * half ^ 27)⟩,
       ⟨((-2324887 : Dyadic) * half ^ 22),
        ((13731609 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-167738601 : Dyadic) * half ^ 28),
        ((-18553905 : Dyadic) * half ^ 28)⟩,
       ⟨((-39565103 : Dyadic) * half ^ 29),
        ((12586971 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word44Step38 :
    word44Chunk38.foldl (fun acc a => a.applyPacked acc)
      word44State38 = word44State39 := by decide +kernel

private def word44Chunk39 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word44State40 : PackedMat2 :=
    ⟨⟨⟨((59474563 : Dyadic) * half ^ 29),
        ((-579643479 : Dyadic) * half ^ 31)⟩,
       ⟨((429213909 : Dyadic) * half ^ 30),
        ((824577779 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((11454393 : Dyadic) * half ^ 27),
        ((-258336603 : Dyadic) * half ^ 31)⟩,
       ⟨((346058045 : Dyadic) * half ^ 30),
        ((-755074065 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-11454393 : Dyadic) * half ^ 27),
        ((258336603 : Dyadic) * half ^ 31)⟩,
       ⟨((346058045 : Dyadic) * half ^ 30),
        ((-755074065 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((59474563 : Dyadic) * half ^ 29),
        ((-579643479 : Dyadic) * half ^ 31)⟩,
       ⟨((-429213909 : Dyadic) * half ^ 30),
        ((-824577779 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word44Step39 :
    word44Chunk39.foldl (fun acc a => a.applyPacked acc)
      word44State39 = word44State40 := by decide +kernel

private def word44Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word44State41 : PackedMat2 :=
    ⟨⟨⟨((312438857 : Dyadic) * half ^ 30),
        ((-1084443823 : Dyadic) * half ^ 32)⟩,
       ⟨((-541748517 : Dyadic) * half ^ 31),
        ((914835367 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((136948323 : Dyadic) * half ^ 30),
        ((-887761847 : Dyadic) * half ^ 32)⟩,
       ⟨((-1390437887 : Dyadic) * half ^ 31),
        ((-1018679429 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-476610319 : Dyadic) * half ^ 30),
        ((-1116541241 : Dyadic) * half ^ 32)⟩,
       ⟨((65458791 : Dyadic) * half ^ 31),
        ((1664334533 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((21201057 : Dyadic) * half ^ 29),
        ((-83129197 : Dyadic) * half ^ 32)⟩,
       ⟨((999639595 : Dyadic) * half ^ 31),
        ((-1166626231 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word44Step40 :
    word44Chunk40.foldl (fun acc a => a.applyPacked acc)
      word44State40 = word44State41 := by decide +kernel

private def word44Chunk41 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word44State42 : PackedMat2 :=
    ⟨⟨⟨((-67199665 : Dyadic) * half ^ 30),
        ((-276420893 : Dyadic) * half ^ 32)⟩,
       ⟨((366268871 : Dyadic) * half ^ 29),
        ((-287315357 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-61100837 : Dyadic) * half ^ 31),
        ((41420571 : Dyadic) * half ^ 27)⟩,
       ⟨((-321632825 : Dyadic) * half ^ 30),
        ((-1376901127 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((61100837 : Dyadic) * half ^ 31),
        ((-41420571 : Dyadic) * half ^ 27)⟩,
       ⟨((-321632825 : Dyadic) * half ^ 30),
        ((-1376901127 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-67199665 : Dyadic) * half ^ 30),
        ((-276420893 : Dyadic) * half ^ 32)⟩,
       ⟨((-366268871 : Dyadic) * half ^ 29),
        ((287315357 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word44Step41 :
    word44Chunk41.foldl (fun acc a => a.applyPacked acc)
      word44State41 = word44State42 := by decide +kernel

private def word44Chunk42 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word44State43 : PackedMat2 :=
    ⟨⟨⟨((-4172202909 : Dyadic) * half ^ 33),
        ((2954344247 : Dyadic) * half ^ 33)⟩,
       ⟨((3649673787 : Dyadic) * half ^ 33),
        ((1062662167 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1381685431 : Dyadic) * half ^ 33),
        ((2274413805 : Dyadic) * half ^ 33)⟩,
       ⟨((-1180941405 : Dyadic) * half ^ 33),
        ((-604119191 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1180941405 : Dyadic) * half ^ 33),
        ((604119191 : Dyadic) * half ^ 32)⟩,
       ⟨((-1381685431 : Dyadic) * half ^ 33),
        ((-2274413805 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((3649673787 : Dyadic) * half ^ 33),
        ((1062662167 : Dyadic) * half ^ 32)⟩,
       ⟨((-4172202909 : Dyadic) * half ^ 33),
        ((2954344247 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word44Step42 :
    word44Chunk42.foldl (fun acc a => a.applyPacked acc)
      word44State42 = word44State43 := by decide +kernel

private def word44Chunk43 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word44State44 : PackedMat2 :=
    ⟨⟨⟨((2350079733 : Dyadic) * half ^ 34),
        ((1088851147 : Dyadic) * half ^ 32)⟩,
       ⟨((6591463533 : Dyadic) * half ^ 34),
        ((-4717642225 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5914878283 : Dyadic) * half ^ 34),
        ((2460237123 : Dyadic) * half ^ 33)⟩,
       ⟨((-1315042749 : Dyadic) * half ^ 34),
        ((6268532053 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1348057807 : Dyadic) * half ^ 34),
        ((-903740129 : Dyadic) * half ^ 32)⟩,
       ⟨((11189006299 : Dyadic) * half ^ 34),
        ((2299917767 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((9073046813 : Dyadic) * half ^ 34),
        ((-530172975 : Dyadic) * half ^ 32)⟩,
       ⟨((362237637 : Dyadic) * half ^ 34),
        ((-4470771633 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word44Step43 :
    word44Chunk43.foldl (fun acc a => a.applyPacked acc)
      word44State43 = word44State44 := by decide +kernel

private def word44Chunk44 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State45 : PackedMat2 :=
    ⟨⟨⟨((739780677 : Dyadic) * half ^ 34),
        ((-5373414779 : Dyadic) * half ^ 35)⟩,
       ⟨((3292692431 : Dyadic) * half ^ 34),
        ((15843736213 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((48830523 : Dyadic) * half ^ 29),
        ((-9694737683 : Dyadic) * half ^ 35)⟩,
       ⟨((2347645621 : Dyadic) * half ^ 32),
        ((-3518911673 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-2347645621 : Dyadic) * half ^ 32),
        ((3518911673 : Dyadic) * half ^ 35)⟩,
       ⟨((-48830523 : Dyadic) * half ^ 29),
        ((9694737683 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3292692431 : Dyadic) * half ^ 34),
        ((15843736213 : Dyadic) * half ^ 35)⟩,
       ⟨((739780677 : Dyadic) * half ^ 34),
        ((-5373414779 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word44Step44 :
    word44Chunk44.foldl (fun acc a => a.applyPacked acc)
      word44State44 = word44State45 := by decide +kernel

private def word44Chunk45 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word44State46 : PackedMat2 :=
    ⟨⟨⟨((-11754020215 : Dyadic) * half ^ 35),
        ((-22192180607 : Dyadic) * half ^ 36)⟩,
       ⟨((362349087 : Dyadic) * half ^ 29),
        ((-9741189137 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-8476744671 : Dyadic) * half ^ 35),
        ((9196976899 : Dyadic) * half ^ 36)⟩,
       ⟨((819706445 : Dyadic) * half ^ 33),
        ((13118900393 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((5578969323 : Dyadic) * half ^ 34),
        ((-5197918891 : Dyadic) * half ^ 36)⟩,
       ⟨((-1960961747 : Dyadic) * half ^ 35),
        ((-11755570451 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1995835609 : Dyadic) * half ^ 32),
        ((-11436321353 : Dyadic) * half ^ 36)⟩,
       ⟨((6225495735 : Dyadic) * half ^ 35),
        ((34944361783 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word44Step45 :
    word44Chunk45.foldl (fun acc a => a.applyPacked acc)
      word44State45 = word44State46 := by decide +kernel

private def word44Chunk46 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State47 : PackedMat2 :=
    ⟨⟨⟨((-3251939221 : Dyadic) * half ^ 35),
        ((-4104455465 : Dyadic) * half ^ 36)⟩,
       ⟨((-26436004201 : Dyadic) * half ^ 35),
        ((-1596280071 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((600113813 : Dyadic) * half ^ 31),
        ((-5688471137 : Dyadic) * half ^ 34)⟩,
       ⟨((2813931965 : Dyadic) * half ^ 35),
        ((12912259699 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-600113813 : Dyadic) * half ^ 31),
        ((5688471137 : Dyadic) * half ^ 34)⟩,
       ⟨((2813931965 : Dyadic) * half ^ 35),
        ((12912259699 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-3251939221 : Dyadic) * half ^ 35),
        ((-4104455465 : Dyadic) * half ^ 36)⟩,
       ⟨((26436004201 : Dyadic) * half ^ 35),
        ((1596280071 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word44Step46 :
    word44Chunk46.foldl (fun acc a => a.applyPacked acc)
      word44State46 = word44State47 := by decide +kernel

private def word44Chunk47 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word44State48 : PackedMat2 :=
    ⟨⟨⟨((80329241719 : Dyadic) * half ^ 37),
        ((-6906647201 : Dyadic) * half ^ 37)⟩,
       ⟨((-29115743859 : Dyadic) * half ^ 37),
        ((-22280355447 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-48854968207 : Dyadic) * half ^ 37),
        ((29475447297 : Dyadic) * half ^ 37)⟩,
       ⟨((55517737163 : Dyadic) * half ^ 37),
        ((3140480701 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((16913524493 : Dyadic) * half ^ 37),
        ((-52186352685 : Dyadic) * half ^ 37)⟩,
       ⟨((-42037370101 : Dyadic) * half ^ 37),
        ((-1665692239 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-37654063693 : Dyadic) * half ^ 37),
        ((-54722492789 : Dyadic) * half ^ 37)⟩,
       ⟨((-51467358095 : Dyadic) * half ^ 37),
        ((12803374465 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word44Step47 :
    word44Chunk47.foldl (fun acc a => a.applyPacked acc)
      word44State47 = word44State48 := by decide +kernel

private def word44Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State49 : PackedMat2 :=
    ⟨⟨⟨((1677045163 : Dyadic) * half ^ 37),
        ((54003498199 : Dyadic) * half ^ 38)⟩,
       ⟨((7970128691 : Dyadic) * half ^ 37),
        ((59929428145 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-6850827039 : Dyadic) * half ^ 36),
        ((-148946215575 : Dyadic) * half ^ 38)⟩,
       ⟨((-28450673341 : Dyadic) * half ^ 36),
        ((45851657901 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-28450673341 : Dyadic) * half ^ 36),
        ((45851657901 : Dyadic) * half ^ 38)⟩,
       ⟨((-6850827039 : Dyadic) * half ^ 36),
        ((-148946215575 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-7970128691 : Dyadic) * half ^ 37),
        ((-59929428145 : Dyadic) * half ^ 38)⟩,
       ⟨((-1677045163 : Dyadic) * half ^ 37),
        ((-54003498199 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word44Step48 :
    word44Chunk48.foldl (fun acc a => a.applyPacked acc)
      word44State48 = word44State49 := by decide +kernel

private def word44Chunk49 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word44State50 : PackedMat2 :=
    ⟨⟨⟨((-5513909329 : Dyadic) * half ^ 38),
        ((-127178338579 : Dyadic) * half ^ 39)⟩,
       ⟨((-17896231715 : Dyadic) * half ^ 37),
        ((113143448185 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-149011332065 : Dyadic) * half ^ 38),
        ((-82902139911 : Dyadic) * half ^ 39)⟩,
       ⟨((8778242199 : Dyadic) * half ^ 36),
        ((-256455825411 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((169678982661 : Dyadic) * half ^ 38),
        ((113898363269 : Dyadic) * half ^ 39)⟩,
       ⟨((-43388421375 : Dyadic) * half ^ 37),
        ((184124300861 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-7017445197 : Dyadic) * half ^ 38),
        ((-41306372759 : Dyadic) * half ^ 39)⟩,
       ⟨((-60080446691 : Dyadic) * half ^ 37),
        ((30278554101 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word44Step49 :
    word44Chunk49.foldl (fun acc a => a.applyPacked acc)
      word44State49 = word44State50 := by decide +kernel

private def word44Chunk50 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word44State51 : PackedMat2 :=
    ⟨⟨⟨((-146417873757 : Dyadic) * half ^ 39),
        ((-49440815349 : Dyadic) * half ^ 37)⟩,
       ⟨((165631363373 : Dyadic) * half ^ 39),
        ((-57109436339 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-346785838325 : Dyadic) * half ^ 39),
        ((50480847495 : Dyadic) * half ^ 39)⟩,
       ⟨((-80514312637 : Dyadic) * half ^ 39),
        ((-92756109281 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-346785838325 : Dyadic) * half ^ 39),
        ((50480847495 : Dyadic) * half ^ 39)⟩,
       ⟨((80514312637 : Dyadic) * half ^ 39),
        ((92756109281 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((146417873757 : Dyadic) * half ^ 39),
        ((49440815349 : Dyadic) * half ^ 37)⟩,
       ⟨((165631363373 : Dyadic) * half ^ 39),
        ((-57109436339 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word44Step50 :
    word44Chunk50.foldl (fun acc a => a.applyPacked acc)
      word44State50 = word44State51 := by decide +kernel

private def word44Chunk51 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word44State52 : PackedMat2 :=
    ⟨⟨⟨((-61443999609 : Dyadic) * half ^ 39),
        ((-18417559917 : Dyadic) * half ^ 35)⟩,
       ⟨((-98525107617 : Dyadic) * half ^ 38),
        ((90045636995 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((52624876791 : Dyadic) * half ^ 38),
        ((115183766497 : Dyadic) * half ^ 40)⟩,
       ⟨((22893386805 : Dyadic) * half ^ 37),
        ((-167036798493 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-52624876791 : Dyadic) * half ^ 38),
        ((-115183766497 : Dyadic) * half ^ 40)⟩,
       ⟨((22893386805 : Dyadic) * half ^ 37),
        ((-167036798493 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-61443999609 : Dyadic) * half ^ 39),
        ((-18417559917 : Dyadic) * half ^ 35)⟩,
       ⟨((98525107617 : Dyadic) * half ^ 38),
        ((-90045636995 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word44Step51 :
    word44Chunk51.foldl (fun acc a => a.applyPacked acc)
      word44State51 = word44State52 := by decide +kernel

private def word44Chunk52 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word44State53 : PackedMat2 :=
    ⟨⟨⟨((-565733573731 : Dyadic) * half ^ 41),
        ((-409756937015 : Dyadic) * half ^ 41)⟩,
       ⟨((-392054088711 : Dyadic) * half ^ 41),
        ((-498569277087 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-452095841795 : Dyadic) * half ^ 41),
        ((286078889307 : Dyadic) * half ^ 41)⟩,
       ⟨((-1137055241147 : Dyadic) * half ^ 41),
        ((216968538281 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-147858187255 : Dyadic) * half ^ 41),
        ((85619924919 : Dyadic) * half ^ 39)⟩,
       ⟨((-720015965869 : Dyadic) * half ^ 41),
        ((794575541471 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-587381617159 : Dyadic) * half ^ 41),
        ((43419871255 : Dyadic) * half ^ 40)⟩,
       ⟨((-1406895491189 : Dyadic) * half ^ 41),
        ((-478893831221 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word44Step52 :
    word44Chunk52.foldl (fun acc a => a.applyPacked acc)
      word44State52 = word44State53 := by decide +kernel

private def word44Chunk53 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word44State54 : PackedMat2 :=
    ⟨⟨⟨((6159014119 : Dyadic) * half ^ 40),
        ((1135360087 : Dyadic) * half ^ 35)⟩,
       ⟨((-1848532961613 : Dyadic) * half ^ 41),
        ((-91968487291 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((571739723015 : Dyadic) * half ^ 41),
        ((-323947463843 : Dyadic) * half ^ 40)⟩,
       ⟨((100979050005 : Dyadic) * half ^ 39),
        ((73081101167 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-574813826519 : Dyadic) * half ^ 41),
        ((975655923035 : Dyadic) * half ^ 42)⟩,
       ⟨((-720976028853 : Dyadic) * half ^ 41),
        ((167823522995 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((55636964507 : Dyadic) * half ^ 40),
        ((1836214933375 : Dyadic) * half ^ 42)⟩,
       ⟨((-128300010075 : Dyadic) * half ^ 40),
        ((-1860850989851 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word44Step53 :
    word44Chunk53.foldl (fun acc a => a.applyPacked acc)
      word44State53 = word44State54 := by decide +kernel

private def word44Chunk54 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word44State55 : PackedMat2 :=
    ⟨⟨⟨((-245160629127 : Dyadic) * half ^ 41),
        ((1880347131429 : Dyadic) * half ^ 43)⟩,
       ⟨((-68798016503 : Dyadic) * half ^ 40),
        ((-2664964076157 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((3108724243083 : Dyadic) * half ^ 42),
        ((-511900176599 : Dyadic) * half ^ 43)⟩,
       ⟨((-1858487186929 : Dyadic) * half ^ 42),
        ((-957743321031 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((1858487186929 : Dyadic) * half ^ 42),
        ((957743321031 : Dyadic) * half ^ 43)⟩,
       ⟨((-3108724243083 : Dyadic) * half ^ 42),
        ((511900176599 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-68798016503 : Dyadic) * half ^ 40),
        ((-2664964076157 : Dyadic) * half ^ 43)⟩,
       ⟨((-245160629127 : Dyadic) * half ^ 41),
        ((1880347131429 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word44Step54 :
    word44Chunk54.foldl (fun acc a => a.applyPacked acc)
      word44State54 = word44State55 := by decide +kernel

private def word44Chunk55 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word44State56 : PackedMat2 :=
    ⟨⟨⟨((1932617625225 : Dyadic) * half ^ 43),
        ((-3282889870363 : Dyadic) * half ^ 44)⟩,
       ⟨((-1945053541613 : Dyadic) * half ^ 42),
        ((2580200055559 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((3619242614123 : Dyadic) * half ^ 43),
        ((6960062614955 : Dyadic) * half ^ 44)⟩,
       ⟨((158955587151 : Dyadic) * half ^ 39),
        ((-3463361226191 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((874175347191 : Dyadic) * half ^ 42),
        ((6162532008539 : Dyadic) * half ^ 44)⟩,
       ⟨((5211711920573 : Dyadic) * half ^ 43),
        ((1075953219707 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((175672453701 : Dyadic) * half ^ 42),
        ((1957489458001 : Dyadic) * half ^ 44)⟩,
       ⟨((2931544962961 : Dyadic) * half ^ 43),
        ((-5822724708451 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word44Step55 :
    word44Chunk55.foldl (fun acc a => a.applyPacked acc)
      word44State55 = word44State56 := by decide +kernel

private def word44Chunk56 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word44State57 : PackedMat2 :=
    ⟨⟨⟨((-1936072181553 : Dyadic) * half ^ 44),
        ((2374198210541 : Dyadic) * half ^ 44)⟩,
       ⟨((893575066661 : Dyadic) * half ^ 44),
        ((-9011583325885 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((526666137313 : Dyadic) * half ^ 44),
        ((3320511627499 : Dyadic) * half ^ 43)⟩,
       ⟨((2088499013157 : Dyadic) * half ^ 44),
        ((547734470839 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-1129573744143 : Dyadic) * half ^ 43),
        ((390458218961 : Dyadic) * half ^ 43)⟩,
       ⟨((5511449510855 : Dyadic) * half ^ 43),
        ((1307582575235 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((5692890768213 : Dyadic) * half ^ 43),
        ((-1414823624107 : Dyadic) * half ^ 44)⟩,
       ⟨((414836569709 : Dyadic) * half ^ 40),
        ((260624278723 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word44Step56 :
    word44Chunk56.foldl (fun acc a => a.applyPacked acc)
      word44State56 = word44State57 := by decide +kernel

private def word44Chunk57 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word44State58 : PackedMat2 :=
    ⟨⟨⟨((6113968842707 : Dyadic) * half ^ 45),
        ((3147297353205 : Dyadic) * half ^ 44)⟩,
       ⟨((-30982137855033 : Dyadic) * half ^ 45),
        ((1960190701967 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-192234039587 : Dyadic) * half ^ 45),
        ((-610096501323 : Dyadic) * half ^ 43)⟩,
       ⟨((2653032555393 : Dyadic) * half ^ 45),
        ((8208273710709 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-2653032555393 : Dyadic) * half ^ 45),
        ((-8208273710709 : Dyadic) * half ^ 45)⟩,
       ⟨((192234039587 : Dyadic) * half ^ 45),
        ((610096501323 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-30982137855033 : Dyadic) * half ^ 45),
        ((1960190701967 : Dyadic) * half ^ 45)⟩,
       ⟨((6113968842707 : Dyadic) * half ^ 45),
        ((3147297353205 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word44Step57 :
    word44Chunk57.foldl (fun acc a => a.applyPacked acc)
      word44State57 = word44State58 := by decide +kernel

private def word44Chunk58 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word44State59 : PackedMat2 :=
    ⟨⟨⟨((-20910327066305 : Dyadic) * half ^ 46),
        ((2994870521601 : Dyadic) * half ^ 45)⟩,
       ⟨((-21499897571485 : Dyadic) * half ^ 46),
        ((-880291705981 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-62802660363119 : Dyadic) * half ^ 46),
        ((-426642036649 : Dyadic) * half ^ 44)⟩,
       ⟨((-5377677669291 : Dyadic) * half ^ 46),
        ((159131321289 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((1865699467885 : Dyadic) * half ^ 46),
        ((14356245673457 : Dyadic) * half ^ 45)⟩,
       ⟨((-1547436825307 : Dyadic) * half ^ 46),
        ((-34090169016205 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((6870032749183 : Dyadic) * half ^ 46),
        ((147392626295 : Dyadic) * half ^ 45)⟩,
       ⟨((-5109449337221 : Dyadic) * half ^ 46),
        ((21205112318895 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word44Step58 :
    word44Chunk58.foldl (fun acc a => a.applyPacked acc)
      word44State58 = word44State59 := by decide +kernel

private def word44Chunk59 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word44State60 : PackedMat2 :=
    ⟨⟨⟨((25572978427429 : Dyadic) * half ^ 46),
        ((23897827262283 : Dyadic) * half ^ 47)⟩,
       ⟨((2075791508547 : Dyadic) * half ^ 46),
        ((-48425248585917 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((18296167828427 : Dyadic) * half ^ 45),
        ((-26870269269017 : Dyadic) * half ^ 47)⟩,
       ⟨((-16020467214089 : Dyadic) * half ^ 45),
        ((-14750756165195 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((16020467214089 : Dyadic) * half ^ 45),
        ((14750756165195 : Dyadic) * half ^ 47)⟩,
       ⟨((-18296167828427 : Dyadic) * half ^ 45),
        ((26870269269017 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((2075791508547 : Dyadic) * half ^ 46),
        ((-48425248585917 : Dyadic) * half ^ 47)⟩,
       ⟨((25572978427429 : Dyadic) * half ^ 46),
        ((23897827262283 : Dyadic) * half ^ 47)⟩⟩⟩
private lemma word44Step59 :
    word44Chunk59.foldl (fun acc a => a.applyPacked acc)
      word44State59 = word44State60 := by decide +kernel

private def word44Chunk60 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word44State61 : PackedMat2 :=
    ⟨⟨⟨((7243160019385 : Dyadic) * half ^ 43),
        ((35138862624785 : Dyadic) * half ^ 48)⟩,
       ⟨((-451978234973 : Dyadic) * half ^ 46),
        ((1278387499557 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((-32369895607375 : Dyadic) * half ^ 47),
        ((45777945380551 : Dyadic) * half ^ 48)⟩,
       ⟨((-42788983795001 : Dyadic) * half ^ 47),
        ((60512761203053 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((-42788983795001 : Dyadic) * half ^ 47),
        ((60512761203053 : Dyadic) * half ^ 48)⟩,
       ⟨((-32369895607375 : Dyadic) * half ^ 47),
        ((45777945380551 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((451978234973 : Dyadic) * half ^ 46),
        ((-1278387499557 : Dyadic) * half ^ 48)⟩,
       ⟨((-7243160019385 : Dyadic) * half ^ 43),
        ((-35138862624785 : Dyadic) * half ^ 48)⟩⟩⟩
private lemma word44Step60 :
    word44Chunk60.foldl (fun acc a => a.applyPacked acc)
      word44State60 = word44State61 := by decide +kernel

private def word44Chunk61 : List Letter := [.s]
private def word44State62 : PackedMat2 :=
    ⟨⟨⟨((7243160019385 : Dyadic) * half ^ 43),
        ((35138862624785 : Dyadic) * half ^ 48)⟩,
       ⟨((-451978234973 : Dyadic) * half ^ 46),
        ((1278387499557 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((-32369895607375 : Dyadic) * half ^ 47),
        ((45777945380551 : Dyadic) * half ^ 48)⟩,
       ⟨((-42788983795001 : Dyadic) * half ^ 47),
        ((60512761203053 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((32369895607375 : Dyadic) * half ^ 47),
        ((-45777945380551 : Dyadic) * half ^ 48)⟩,
       ⟨((-42788983795001 : Dyadic) * half ^ 47),
        ((60512761203053 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((7243160019385 : Dyadic) * half ^ 43),
        ((35138862624785 : Dyadic) * half ^ 48)⟩,
       ⟨((451978234973 : Dyadic) * half ^ 46),
        ((-1278387499557 : Dyadic) * half ^ 48)⟩⟩⟩
private lemma word44Step61 :
    word44Chunk61.foldl (fun acc a => a.applyPacked acc)
      word44State61 = word44State62 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word44_check : check word44 44 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word44 = word44State62.toMatrix := by
    unfold evalRingPacked
    change ((
      word44Chunk0 ++ word44Chunk1 ++ word44Chunk2 ++ word44Chunk3 ++
      word44Chunk4 ++ word44Chunk5 ++ word44Chunk6 ++ word44Chunk7 ++
      word44Chunk8 ++ word44Chunk9 ++ word44Chunk10 ++ word44Chunk11 ++
      word44Chunk12 ++ word44Chunk13 ++ word44Chunk14 ++ word44Chunk15 ++
      word44Chunk16 ++ word44Chunk17 ++ word44Chunk18 ++ word44Chunk19 ++
      word44Chunk20 ++ word44Chunk21 ++ word44Chunk22 ++ word44Chunk23 ++
      word44Chunk24 ++ word44Chunk25 ++ word44Chunk26 ++ word44Chunk27 ++
      word44Chunk28 ++ word44Chunk29 ++ word44Chunk30 ++ word44Chunk31 ++
      word44Chunk32 ++ word44Chunk33 ++ word44Chunk34 ++ word44Chunk35 ++
      word44Chunk36 ++ word44Chunk37 ++ word44Chunk38 ++ word44Chunk39 ++
      word44Chunk40 ++ word44Chunk41 ++ word44Chunk42 ++ word44Chunk43 ++
      word44Chunk44 ++ word44Chunk45 ++ word44Chunk46 ++ word44Chunk47 ++
      word44Chunk48 ++ word44Chunk49 ++ word44Chunk50 ++ word44Chunk51 ++
      word44Chunk52 ++ word44Chunk53 ++ word44Chunk54 ++ word44Chunk55 ++
      word44Chunk56 ++ word44Chunk57 ++ word44Chunk58 ++ word44Chunk59 ++
      word44Chunk60 ++ word44Chunk61
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word44Step0, word44Step1, word44Step2, word44Step3, word44Step4,
      word44Step5, word44Step6, word44Step7, word44Step8, word44Step9,
      word44Step10, word44Step11, word44Step12, word44Step13, word44Step14,
      word44Step15, word44Step16, word44Step17, word44Step18, word44Step19,
      word44Step20, word44Step21, word44Step22, word44Step23, word44Step24,
      word44Step25, word44Step26, word44Step27, word44Step28, word44Step29,
      word44Step30, word44Step31, word44Step32, word44Step33, word44Step34,
      word44Step35, word44Step36, word44Step37, word44Step38, word44Step39,
      word44Step40, word44Step41, word44Step42, word44Step43, word44Step44,
      word44Step45, word44Step46, word44Step47, word44Step48, word44Step49,
      word44Step50, word44Step51, word44Step52, word44Step53, word44Step54,
      word44Step55, word44Step56, word44Step57, word44Step58, word44Step59,
      word44Step60, word44Step61]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
