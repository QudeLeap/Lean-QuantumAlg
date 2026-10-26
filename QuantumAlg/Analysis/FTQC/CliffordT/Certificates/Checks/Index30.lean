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
private def word30Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word30State1 : PackedMat2 :=
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
private lemma word30Step0 :
    word30Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word30State1 := by decide +kernel

private def word30Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word30State2 : PackedMat2 :=
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
private lemma word30Step1 :
    word30Chunk1.foldl (fun acc a => a.applyPacked acc)
      word30State1 = word30State2 := by decide +kernel

private def word30Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word30State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word30Step2 :
    word30Chunk2.foldl (fun acc a => a.applyPacked acc)
      word30State2 = word30State3 := by decide +kernel

private def word30Chunk3 : List Letter := [.s, .s, .s, .h, .s, .s, .h, .h]
private def word30State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word30Step3 :
    word30Chunk3.foldl (fun acc a => a.applyPacked acc)
      word30State3 = word30State4 := by decide +kernel

private def word30Chunk4 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word30State5 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word30Step4 :
    word30Chunk4.foldl (fun acc a => a.applyPacked acc)
      word30State4 = word30State5 := by decide +kernel

private def word30Chunk5 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word30State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word30Step5 :
    word30Chunk5.foldl (fun acc a => a.applyPacked acc)
      word30State5 = word30State6 := by decide +kernel

private def word30Chunk6 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word30State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((9 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word30Step6 :
    word30Chunk6.foldl (fun acc a => a.applyPacked acc)
      word30State6 = word30State7 := by decide +kernel

private def word30Chunk7 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word30State8 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((19 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word30Step7 :
    word30Chunk7.foldl (fun acc a => a.applyPacked acc)
      word30State7 = word30State8 := by decide +kernel

private def word30Chunk8 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word30State9 : PackedMat2 :=
    ⟨⟨⟨((9 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word30Step8 :
    word30Chunk8.foldl (fun acc a => a.applyPacked acc)
      word30State8 = word30State9 := by decide +kernel

private def word30Chunk9 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word30State10 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((17 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-17 : Dyadic) * half ^ 5)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word30Step9 :
    word30Chunk9.foldl (fun acc a => a.applyPacked acc)
      word30State9 = word30State10 := by decide +kernel

private def word30Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word30State11 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 7),
        ((-13 : Dyadic) * half ^ 7)⟩,
       ⟨((13 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 6)⟩,
       ⟨((119 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 7),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((-5 : Dyadic) * half ^ 7),
        ((-73 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((11 : Dyadic) * half ^ 7),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word30Step10 :
    word30Chunk10.foldl (fun acc a => a.applyPacked acc)
      word30State10 = word30State11 := by decide +kernel

private def word30Chunk11 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word30State12 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 6),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((-91 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 7),
        ((-51 : Dyadic) * half ^ 8)⟩,
       ⟨((-75 : Dyadic) * half ^ 7),
        ((61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 7),
        ((51 : Dyadic) * half ^ 8)⟩,
       ⟨((-75 : Dyadic) * half ^ 7),
        ((61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((91 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word30Step11 :
    word30Chunk11.foldl (fun acc a => a.applyPacked acc)
      word30State11 = word30State12 := by decide +kernel

private def word30Chunk12 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word30State13 : PackedMat2 :=
    ⟨⟨⟨((33 : Dyadic) * half ^ 7),
        ((195 : Dyadic) * half ^ 9)⟩,
       ⟨((-41 : Dyadic) * half ^ 8),
        ((-53 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 8),
        ((-179 : Dyadic) * half ^ 9)⟩,
       ⟨((43 : Dyadic) * half ^ 7),
        ((-177 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 7),
        ((177 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 8),
        ((179 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 8),
        ((-53 : Dyadic) * half ^ 9)⟩,
       ⟨((33 : Dyadic) * half ^ 7),
        ((195 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word30Step12 :
    word30Chunk12.foldl (fun acc a => a.applyPacked acc)
      word30State12 = word30State13 := by decide +kernel

private def word30Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word30State14 : PackedMat2 :=
    ⟨⟨⟨((161 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 7),
        ((-33 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((57 : Dyadic) * half ^ 8)⟩,
       ⟨((-61 : Dyadic) * half ^ 7),
        ((-101 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 9),
        ((-117 : Dyadic) * half ^ 8)⟩,
       ⟨((215 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((29 : Dyadic) * half ^ 9),
        ((-167 : Dyadic) * half ^ 9)⟩,
       ⟨((-37 : Dyadic) * half ^ 9),
        ((-155 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word30Step13 :
    word30Chunk13.foldl (fun acc a => a.applyPacked acc)
      word30State13 = word30State14 := by decide +kernel

private def word30Chunk14 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word30State15 : PackedMat2 :=
    ⟨⟨⟨((-17 : Dyadic) * half ^ 10),
        ((589 : Dyadic) * half ^ 10)⟩,
       ⟨((41 : Dyadic) * half ^ 10),
        ((3 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((443 : Dyadic) * half ^ 10),
        ((11 : Dyadic) * half ^ 8)⟩,
       ⟨((-389 : Dyadic) * half ^ 10),
        ((25 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-443 : Dyadic) * half ^ 10),
        ((-11 : Dyadic) * half ^ 8)⟩,
       ⟨((-389 : Dyadic) * half ^ 10),
        ((25 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 10),
        ((589 : Dyadic) * half ^ 10)⟩,
       ⟨((-41 : Dyadic) * half ^ 10),
        ((-3 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word30Step14 :
    word30Chunk14.foldl (fun acc a => a.applyPacked acc)
      word30State14 = word30State15 := by decide +kernel

private def word30Chunk15 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word30State16 : PackedMat2 :=
    ⟨⟨⟨((-493 : Dyadic) * half ^ 11),
        ((1045 : Dyadic) * half ^ 11)⟩,
       ⟨((625 : Dyadic) * half ^ 11),
        ((27 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((811 : Dyadic) * half ^ 11),
        ((35 : Dyadic) * half ^ 7)⟩,
       ⟨((259 : Dyadic) * half ^ 11),
        ((-25 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((535 : Dyadic) * half ^ 11),
        ((535 : Dyadic) * half ^ 11)⟩,
       ⟨((585 : Dyadic) * half ^ 11),
        ((69 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-1153 : Dyadic) * half ^ 11),
        ((-33 : Dyadic) * half ^ 10)⟩,
       ⟨((-937 : Dyadic) * half ^ 11),
        ((559 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word30Step15 :
    word30Chunk15.foldl (fun acc a => a.applyPacked acc)
      word30State15 = word30State16 := by decide +kernel

private def word30Chunk16 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word30State17 : PackedMat2 :=
    ⟨⟨⟨((-1521 : Dyadic) * half ^ 11),
        ((143 : Dyadic) * half ^ 12)⟩,
       ⟨((589 : Dyadic) * half ^ 10),
        ((59 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 8),
        ((511 : Dyadic) * half ^ 12)⟩,
       ⟨((-467 : Dyadic) * half ^ 11),
        ((77 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-467 : Dyadic) * half ^ 11),
        ((77 : Dyadic) * half ^ 12)⟩,
       ⟨((45 : Dyadic) * half ^ 8),
        ((511 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-589 : Dyadic) * half ^ 10),
        ((-59 : Dyadic) * half ^ 12)⟩,
       ⟨((1521 : Dyadic) * half ^ 11),
        ((-143 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word30Step16 :
    word30Chunk16.foldl (fun acc a => a.applyPacked acc)
      word30State16 = word30State17 := by decide +kernel

private def word30Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word30State18 : PackedMat2 :=
    ⟨⟨⟨((679 : Dyadic) * half ^ 12),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((-2381 : Dyadic) * half ^ 12),
        ((71 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((223 : Dyadic) * half ^ 12),
        ((291 : Dyadic) * half ^ 12)⟩,
       ⟨((1079 : Dyadic) * half ^ 12),
        ((1513 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1079 : Dyadic) * half ^ 12),
        ((-1513 : Dyadic) * half ^ 12)⟩,
       ⟨((-223 : Dyadic) * half ^ 12),
        ((-291 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-2381 : Dyadic) * half ^ 12),
        ((71 : Dyadic) * half ^ 10)⟩,
       ⟨((679 : Dyadic) * half ^ 12),
        ((-47 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word30Step17 :
    word30Chunk17.foldl (fun acc a => a.applyPacked acc)
      word30State17 = word30State18 := by decide +kernel

private def word30Chunk18 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word30State19 : PackedMat2 :=
    ⟨⟨⟨((-19 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((-1299 : Dyadic) * half ^ 11),
        ((-631 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1665 : Dyadic) * half ^ 12),
        ((-181 : Dyadic) * half ^ 12)⟩,
       ⟨((21 : Dyadic) * half ^ 10),
        ((1103 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 10),
        ((1103 : Dyadic) * half ^ 13)⟩,
       ⟨((-1665 : Dyadic) * half ^ 12),
        ((-181 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1299 : Dyadic) * half ^ 11),
        ((631 : Dyadic) * half ^ 13)⟩,
       ⟨((19 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word30Step18 :
    word30Chunk18.foldl (fun acc a => a.applyPacked acc)
      word30State18 = word30State19 := by decide +kernel

private def word30Chunk19 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word30State20 : PackedMat2 :=
    ⟨⟨⟨((493 : Dyadic) * half ^ 14),
        ((-2271 : Dyadic) * half ^ 13)⟩,
       ⟨((-8321 : Dyadic) * half ^ 14),
        ((525 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-7953 : Dyadic) * half ^ 14),
        ((-3677 : Dyadic) * half ^ 14)⟩,
       ⟨((-6561 : Dyadic) * half ^ 14),
        ((1725 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((7953 : Dyadic) * half ^ 14),
        ((3677 : Dyadic) * half ^ 14)⟩,
       ⟨((-6561 : Dyadic) * half ^ 14),
        ((1725 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((493 : Dyadic) * half ^ 14),
        ((-2271 : Dyadic) * half ^ 13)⟩,
       ⟨((8321 : Dyadic) * half ^ 14),
        ((-525 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word30Step19 :
    word30Chunk19.foldl (fun acc a => a.applyPacked acc)
      word30State19 = word30State20 := by decide +kernel

private def word30Chunk20 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word30State21 : PackedMat2 :=
    ⟨⟨⟨((3595 : Dyadic) * half ^ 14),
        ((3645 : Dyadic) * half ^ 15)⟩,
       ⟨((-2509 : Dyadic) * half ^ 14),
        ((-9413 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-75 : Dyadic) * half ^ 13),
        ((-15945 : Dyadic) * half ^ 15)⟩,
       ⟨((1817 : Dyadic) * half ^ 13),
        ((-10763 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2591 : Dyadic) * half ^ 14),
        ((-473 : Dyadic) * half ^ 12)⟩,
       ⟨((6677 : Dyadic) * half ^ 13),
        ((-871 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-6529 : Dyadic) * half ^ 14),
        ((-763 : Dyadic) * half ^ 12)⟩,
       ⟨((-721 : Dyadic) * half ^ 12),
        ((543 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word30Step20 :
    word30Chunk20.foldl (fun acc a => a.applyPacked acc)
      word30State20 = word30State21 := by decide +kernel

private def word30Chunk21 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word30State22 : PackedMat2 :=
    ⟨⟨⟨((-893 : Dyadic) * half ^ 13),
        ((-17663 : Dyadic) * half ^ 16)⟩,
       ⟨((7807 : Dyadic) * half ^ 14),
        ((-12643 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1771 : Dyadic) * half ^ 15),
        ((-23803 : Dyadic) * half ^ 16)⟩,
       ⟨((-16723 : Dyadic) * half ^ 15),
        ((-5511 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1771 : Dyadic) * half ^ 15),
        ((23803 : Dyadic) * half ^ 16)⟩,
       ⟨((-16723 : Dyadic) * half ^ 15),
        ((-5511 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-893 : Dyadic) * half ^ 13),
        ((-17663 : Dyadic) * half ^ 16)⟩,
       ⟨((-7807 : Dyadic) * half ^ 14),
        ((12643 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word30Step21 :
    word30Chunk21.foldl (fun acc a => a.applyPacked acc)
      word30State21 = word30State22 := by decide +kernel

private def word30Chunk22 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word30State23 : PackedMat2 :=
    ⟨⟨⟨((-12781 : Dyadic) * half ^ 16),
        ((34923 : Dyadic) * half ^ 17)⟩,
       ⟨((-25531 : Dyadic) * half ^ 15),
        ((1511 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((361 : Dyadic) * half ^ 12),
        ((26603 : Dyadic) * half ^ 17)⟩,
       ⟨((-15319 : Dyadic) * half ^ 16),
        ((-24143 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((25373 : Dyadic) * half ^ 16),
        ((21095 : Dyadic) * half ^ 17)⟩,
       ⟨((-615 : Dyadic) * half ^ 15),
        ((9543 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-8353 : Dyadic) * half ^ 15),
        ((-38281 : Dyadic) * half ^ 17)⟩,
       ⟨((18217 : Dyadic) * half ^ 16),
        ((-63843 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word30Step22 :
    word30Chunk22.foldl (fun acc a => a.applyPacked acc)
      word30State22 = word30State23 := by decide +kernel

private def word30Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word30State24 : PackedMat2 :=
    ⟨⟨⟨((35333 : Dyadic) * half ^ 16),
        ((-3201 : Dyadic) * half ^ 14)⟩,
       ⟨((-2747 : Dyadic) * half ^ 16),
        ((-20299 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((11623 : Dyadic) * half ^ 14),
        ((4273 : Dyadic) * half ^ 15)⟩,
       ⟨((-2793 : Dyadic) * half ^ 16),
        ((-19479 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-2793 : Dyadic) * half ^ 16),
        ((-19479 : Dyadic) * half ^ 17)⟩,
       ⟨((11623 : Dyadic) * half ^ 14),
        ((4273 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((2747 : Dyadic) * half ^ 16),
        ((20299 : Dyadic) * half ^ 17)⟩,
       ⟨((-35333 : Dyadic) * half ^ 16),
        ((3201 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word30Step23 :
    word30Chunk23.foldl (fun acc a => a.applyPacked acc)
      word30State23 = word30State24 := by decide +kernel

private def word30Chunk24 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word30State25 : PackedMat2 :=
    ⟨⟨⟨((-9151 : Dyadic) * half ^ 18),
        ((70125 : Dyadic) * half ^ 17)⟩,
       ⟨((32455 : Dyadic) * half ^ 18),
        ((-74801 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((45079 : Dyadic) * half ^ 18),
        ((74383 : Dyadic) * half ^ 18)⟩,
       ⟨((8119 : Dyadic) * half ^ 18),
        ((11023 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-45079 : Dyadic) * half ^ 18),
        ((-74383 : Dyadic) * half ^ 18)⟩,
       ⟨((8119 : Dyadic) * half ^ 18),
        ((11023 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-9151 : Dyadic) * half ^ 18),
        ((70125 : Dyadic) * half ^ 17)⟩,
       ⟨((-32455 : Dyadic) * half ^ 18),
        ((74801 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word30Step24 :
    word30Chunk24.foldl (fun acc a => a.applyPacked acc)
      word30State24 = word30State25 := by decide +kernel

private def word30Chunk25 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word30State26 : PackedMat2 :=
    ⟨⟨⟨((-29317 : Dyadic) * half ^ 19),
        ((-121183 : Dyadic) * half ^ 19)⟩,
       ⟨((76309 : Dyadic) * half ^ 19),
        ((-52847 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-89793 : Dyadic) * half ^ 19),
        ((61095 : Dyadic) * half ^ 17)⟩,
       ⟨((142895 : Dyadic) * half ^ 19),
        ((185145 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((429525 : Dyadic) * half ^ 19),
        ((26551 : Dyadic) * half ^ 19)⟩,
       ⟨((59235 : Dyadic) * half ^ 19),
        ((-14543 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((226877 : Dyadic) * half ^ 19),
        ((-2937 : Dyadic) * half ^ 16)⟩,
       ⟨((15489 : Dyadic) * half ^ 19),
        ((52813 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word30Step25 :
    word30Chunk25.foldl (fun acc a => a.applyPacked acc)
      word30State25 = word30State26 := by decide +kernel

private def word30Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word30State27 : PackedMat2 :=
    ⟨⟨⟨((325397 : Dyadic) * half ^ 20),
        ((20451 : Dyadic) * half ^ 18)⟩,
       ⟨((-167211 : Dyadic) * half ^ 20),
        ((1303 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-17161 : Dyadic) * half ^ 20),
        ((102255 : Dyadic) * half ^ 20)⟩,
       ⟨((964245 : Dyadic) * half ^ 20),
        ((-3195 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-76695 : Dyadic) * half ^ 20),
        ((-236771 : Dyadic) * half ^ 19)⟩,
       ⟨((-127815 : Dyadic) * half ^ 20),
        ((490703 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((83107 : Dyadic) * half ^ 20),
        ((79093 : Dyadic) * half ^ 20)⟩,
       ⟨((80501 : Dyadic) * half ^ 20),
        ((7697 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word30Step26 :
    word30Chunk26.foldl (fun acc a => a.applyPacked acc)
      word30State26 = word30State27 := by decide +kernel

private def word30Chunk27 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word30State28 : PackedMat2 :=
    ⟨⟨⟨((86995 : Dyadic) * half ^ 19),
        ((221839 : Dyadic) * half ^ 21)⟩,
       ⟨((161531 : Dyadic) * half ^ 18),
        ((-110967 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-217169 : Dyadic) * half ^ 20),
        ((90203 : Dyadic) * half ^ 21)⟩,
       ⟨((49465 : Dyadic) * half ^ 20),
        ((1065197 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-217169 : Dyadic) * half ^ 20),
        ((90203 : Dyadic) * half ^ 21)⟩,
       ⟨((-49465 : Dyadic) * half ^ 20),
        ((-1065197 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-86995 : Dyadic) * half ^ 19),
        ((-221839 : Dyadic) * half ^ 21)⟩,
       ⟨((161531 : Dyadic) * half ^ 18),
        ((-110967 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word30Step27 :
    word30Chunk27.foldl (fun acc a => a.applyPacked acc)
      word30State27 = word30State28 := by decide +kernel

private def word30Chunk28 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word30State29 : PackedMat2 :=
    ⟨⟨⟨((-199529 : Dyadic) * half ^ 21),
        ((1062717 : Dyadic) * half ^ 22)⟩,
       ⟨((87897 : Dyadic) * half ^ 18),
        ((1648203 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((7579 : Dyadic) * half ^ 15),
        ((-920859 : Dyadic) * half ^ 22)⟩,
       ⟨((-326331 : Dyadic) * half ^ 21),
        ((1533001 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-326331 : Dyadic) * half ^ 21),
        ((1533001 : Dyadic) * half ^ 22)⟩,
       ⟨((7579 : Dyadic) * half ^ 15),
        ((-920859 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-87897 : Dyadic) * half ^ 18),
        ((-1648203 : Dyadic) * half ^ 22)⟩,
       ⟨((199529 : Dyadic) * half ^ 21),
        ((-1062717 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word30Step28 :
    word30Chunk28.foldl (fun acc a => a.applyPacked acc)
      word30State28 = word30State29 := by decide +kernel

private def word30Chunk29 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word30State30 : PackedMat2 :=
    ⟨⟨⟨((-9579 : Dyadic) * half ^ 21),
        ((-270681 : Dyadic) * half ^ 23)⟩,
       ⟨((2283435 : Dyadic) * half ^ 22),
        ((-145013 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2989993 : Dyadic) * half ^ 22),
        ((-614847 : Dyadic) * half ^ 23)⟩,
       ⟨((-320029 : Dyadic) * half ^ 21),
        ((2362983 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1488915 : Dyadic) * half ^ 22),
        ((-2349935 : Dyadic) * half ^ 23)⟩,
       ⟨((-218517 : Dyadic) * half ^ 20),
        ((3630051 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((31417 : Dyadic) * half ^ 21),
        ((2302593 : Dyadic) * half ^ 23)⟩,
       ⟨((-207847 : Dyadic) * half ^ 22),
        ((2264277 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word30Step29 :
    word30Chunk29.foldl (fun acc a => a.applyPacked acc)
      word30State29 = word30State30 := by decide +kernel

private def word30Chunk30 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word30State31 : PackedMat2 :=
    ⟨⟨⟨((-5544109 : Dyadic) * half ^ 23),
        ((-254075 : Dyadic) * half ^ 23)⟩,
       ⟨((475887 : Dyadic) * half ^ 23),
        ((966603 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((44369 : Dyadic) * half ^ 23),
        ((-252259 : Dyadic) * half ^ 19)⟩,
       ⟨((1656425 : Dyadic) * half ^ 23),
        ((-254997 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1656425 : Dyadic) * half ^ 23),
        ((-254997 : Dyadic) * half ^ 21)⟩,
       ⟨((44369 : Dyadic) * half ^ 23),
        ((-252259 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-475887 : Dyadic) * half ^ 23),
        ((-966603 : Dyadic) * half ^ 23)⟩,
       ⟨((5544109 : Dyadic) * half ^ 23),
        ((254075 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word30Step30 :
    word30Chunk30.foldl (fun acc a => a.applyPacked acc)
      word30State30 = word30State31 := by decide +kernel

private def word30Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word30State32 : PackedMat2 :=
    ⟨⟨⟨((5503969 : Dyadic) * half ^ 24),
        ((-2371257 : Dyadic) * half ^ 23)⟩,
       ⟨((-5263099 : Dyadic) * half ^ 24),
        ((-7790933 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-5192837 : Dyadic) * half ^ 24),
        ((3283501 : Dyadic) * half ^ 24)⟩,
       ⟨((-1124079 : Dyadic) * half ^ 24),
        ((-477921 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1371817 : Dyadic) * half ^ 24),
        ((1579229 : Dyadic) * half ^ 23)⟩,
       ⟨((-5195185 : Dyadic) * half ^ 24),
        ((2034379 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-12533447 : Dyadic) * half ^ 24),
        ((120435 : Dyadic) * half ^ 24)⟩,
       ⟨((3048419 : Dyadic) * half ^ 24),
        ((2691767 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word30Step31 :
    word30Chunk31.foldl (fun acc a => a.applyPacked acc)
      word30State31 = word30State32 := by decide +kernel

private def word30Chunk32 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word30State33 : PackedMat2 :=
    ⟨⟨⟨((-668251 : Dyadic) * half ^ 22),
        ((5691609 : Dyadic) * half ^ 24)⟩,
       ⟨((-7635367 : Dyadic) * half ^ 24),
        ((-105033 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((3238545 : Dyadic) * half ^ 23),
        ((1127445 : Dyadic) * half ^ 23)⟩,
       ⟨((-7260087 : Dyadic) * half ^ 24),
        ((431371 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((3238545 : Dyadic) * half ^ 23),
        ((1127445 : Dyadic) * half ^ 23)⟩,
       ⟨((7260087 : Dyadic) * half ^ 24),
        ((-431371 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((668251 : Dyadic) * half ^ 22),
        ((-5691609 : Dyadic) * half ^ 24)⟩,
       ⟨((-7635367 : Dyadic) * half ^ 24),
        ((-105033 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word30Step32 :
    word30Chunk32.foldl (fun acc a => a.applyPacked acc)
      word30State32 = word30State33 := by decide +kernel

private def word30Chunk33 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word30State34 : PackedMat2 :=
    ⟨⟨⟨((12919063 : Dyadic) * half ^ 24),
        ((4811037 : Dyadic) * half ^ 26)⟩,
       ⟨((14553003 : Dyadic) * half ^ 25),
        ((895023 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((2259923 : Dyadic) * half ^ 25),
        ((-9057757 : Dyadic) * half ^ 26)⟩,
       ⟨((2951917 : Dyadic) * half ^ 23),
        ((-9897265 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-209877 : Dyadic) * half ^ 24),
        ((9547745 : Dyadic) * half ^ 26)⟩,
       ⟨((-9477511 : Dyadic) * half ^ 25),
        ((14067591 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((1958007 : Dyadic) * half ^ 25),
        ((11285123 : Dyadic) * half ^ 26)⟩,
       ⟨((-1426515 : Dyadic) * half ^ 24),
        ((-40391129 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word30Step33 :
    word30Chunk33.foldl (fun acc a => a.applyPacked acc)
      word30State33 = word30State34 := by decide +kernel

private def word30Chunk34 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word30State35 : PackedMat2 :=
    ⟨⟨⟨((14557907 : Dyadic) * half ^ 26),
        ((17379699 : Dyadic) * half ^ 26)⟩,
       ⟨((47910633 : Dyadic) * half ^ 26),
        ((-9823327 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-20983263 : Dyadic) * half ^ 26),
        ((452747 : Dyadic) * half ^ 24)⟩,
       ⟨((16500867 : Dyadic) * half ^ 26),
        ((7745963 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-16500867 : Dyadic) * half ^ 26),
        ((-7745963 : Dyadic) * half ^ 25)⟩,
       ⟨((20983263 : Dyadic) * half ^ 26),
        ((-452747 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((47910633 : Dyadic) * half ^ 26),
        ((-9823327 : Dyadic) * half ^ 26)⟩,
       ⟨((14557907 : Dyadic) * half ^ 26),
        ((17379699 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word30Step34 :
    word30Chunk34.foldl (fun acc a => a.applyPacked acc)
      word30State34 = word30State35 := by decide +kernel

private def word30Chunk35 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word30State36 : PackedMat2 :=
    ⟨⟨⟨((-26832173 : Dyadic) * half ^ 27),
        ((5639169 : Dyadic) * half ^ 27)⟩,
       ⟨((-22391661 : Dyadic) * half ^ 27),
        ((33765765 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-40081917 : Dyadic) * half ^ 27),
        ((-9899413 : Dyadic) * half ^ 26)⟩,
       ⟨((17556961 : Dyadic) * half ^ 27),
        ((49546125 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-40081917 : Dyadic) * half ^ 27),
        ((-9899413 : Dyadic) * half ^ 26)⟩,
       ⟨((-17556961 : Dyadic) * half ^ 27),
        ((-49546125 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((26832173 : Dyadic) * half ^ 27),
        ((-5639169 : Dyadic) * half ^ 27)⟩,
       ⟨((-22391661 : Dyadic) * half ^ 27),
        ((33765765 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word30Step35 :
    word30Chunk35.foldl (fun acc a => a.applyPacked acc)
      word30State35 = word30State36 := by decide +kernel

private def word30Chunk36 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word30State37 : PackedMat2 :=
    ⟨⟨⟨((18437979 : Dyadic) * half ^ 26),
        ((-74564877 : Dyadic) * half ^ 28)⟩,
       ⟨((15723481 : Dyadic) * half ^ 25),
        ((32793633 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-41993393 : Dyadic) * half ^ 27),
        ((-83988873 : Dyadic) * half ^ 28)⟩,
       ⟨((40700997 : Dyadic) * half ^ 27),
        ((-69773395 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((7107739 : Dyadic) * half ^ 27),
        ((41347195 : Dyadic) * half ^ 27)⟩,
       ⟨((-38440567 : Dyadic) * half ^ 26),
        ((-323099 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-53679255 : Dyadic) * half ^ 27),
        ((-13008983 : Dyadic) * half ^ 27)⟩,
       ⟨((10442811 : Dyadic) * half ^ 26),
        ((-49884941 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word30Step36 :
    word30Chunk36.foldl (fun acc a => a.applyPacked acc)
      word30State36 = word30State37 := by decide +kernel

private def word30Chunk37 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word30State38 : PackedMat2 :=
    ⟨⟨⟨((-65175531 : Dyadic) * half ^ 27),
        ((123652673 : Dyadic) * half ^ 29)⟩,
       ⟨((-7211543 : Dyadic) * half ^ 28),
        ((49930575 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-178369125 : Dyadic) * half ^ 28),
        ((-40231357 : Dyadic) * half ^ 29)⟩,
       ⟨((-45440583 : Dyadic) * half ^ 27),
        ((-102356761 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((45440583 : Dyadic) * half ^ 27),
        ((102356761 : Dyadic) * half ^ 29)⟩,
       ⟨((178369125 : Dyadic) * half ^ 28),
        ((40231357 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-7211543 : Dyadic) * half ^ 28),
        ((49930575 : Dyadic) * half ^ 29)⟩,
       ⟨((-65175531 : Dyadic) * half ^ 27),
        ((123652673 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word30Step37 :
    word30Chunk37.foldl (fun acc a => a.applyPacked acc)
      word30State37 = word30State38 := by decide +kernel

private def word30Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word30State39 : PackedMat2 :=
    ⟨⟨⟨((61559819 : Dyadic) * half ^ 28),
        ((168690433 : Dyadic) * half ^ 30)⟩,
       ⟨((258549813 : Dyadic) * half ^ 29),
        ((249344603 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-164123829 : Dyadic) * half ^ 29),
        ((222306707 : Dyadic) * half ^ 30)⟩,
       ⟨((55338251 : Dyadic) * half ^ 28),
        ((-440484445 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-41424447 : Dyadic) * half ^ 26),
        ((274800331 : Dyadic) * half ^ 30)⟩,
       ⟨((-109088869 : Dyadic) * half ^ 29),
        ((-53447327 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-40327085 : Dyadic) * half ^ 29),
        ((-135430175 : Dyadic) * half ^ 30)⟩,
       ⟨((-104508759 : Dyadic) * half ^ 28),
        ((-381669451 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word30Step38 :
    word30Chunk38.foldl (fun acc a => a.applyPacked acc)
      word30State38 = word30State39 := by decide +kernel

private def word30Chunk39 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word30State40 : PackedMat2 :=
    ⟨⟨⟨((45669053 : Dyadic) * half ^ 28),
        ((22153913 : Dyadic) * half ^ 27)⟩,
       ⟨((176955 : Dyadic) * half ^ 21),
        ((414132771 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-87435841 : Dyadic) * half ^ 29),
        ((247753319 : Dyadic) * half ^ 29)⟩,
       ⟨((-106292497 : Dyadic) * half ^ 28),
        ((-39403791 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-456102847 : Dyadic) * half ^ 30),
        ((300020835 : Dyadic) * half ^ 30)⟩,
       ⟨((-534910429 : Dyadic) * half ^ 30),
        ((-125149153 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((591364075 : Dyadic) * half ^ 30),
        ((68319293 : Dyadic) * half ^ 29)⟩,
       ⟨((-236901467 : Dyadic) * half ^ 30),
        ((23018813 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word30Step39 :
    word30Chunk39.foldl (fun acc a => a.applyPacked acc)
      word30State39 = word30State40 := by decide +kernel

private def word30Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word30State41 : PackedMat2 :=
    ⟨⟨⟨((-192241199 : Dyadic) * half ^ 31),
        ((17141069 : Dyadic) * half ^ 29)⟩,
       ⟨((476031325 : Dyadic) * half ^ 31),
        ((142683111 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((2007547339 : Dyadic) * half ^ 31),
        ((1170695 : Dyadic) * half ^ 31)⟩,
       ⟨((-490580731 : Dyadic) * half ^ 31),
        ((29093569 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((2007547339 : Dyadic) * half ^ 31),
        ((1170695 : Dyadic) * half ^ 31)⟩,
       ⟨((490580731 : Dyadic) * half ^ 31),
        ((-29093569 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((192241199 : Dyadic) * half ^ 31),
        ((-17141069 : Dyadic) * half ^ 29)⟩,
       ⟨((476031325 : Dyadic) * half ^ 31),
        ((142683111 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word30Step40 :
    word30Chunk40.foldl (fun acc a => a.applyPacked acc)
      word30State40 = word30State41 := by decide +kernel

private def word30Chunk41 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word30State42 : PackedMat2 :=
    ⟨⟨⟨((1366991653 : Dyadic) * half ^ 32),
        ((786131607 : Dyadic) * half ^ 31)⟩,
       ⟨((-587360623 : Dyadic) * half ^ 32),
        ((1376520733 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((696433627 : Dyadic) * half ^ 32),
        ((295347805 : Dyadic) * half ^ 32)⟩,
       ⟨((-889196331 : Dyadic) * half ^ 32),
        ((869575539 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2034498883 : Dyadic) * half ^ 32),
        ((12047669 : Dyadic) * half ^ 29)⟩,
       ⟨((1443803273 : Dyadic) * half ^ 32),
        ((-792814979 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((2948783947 : Dyadic) * half ^ 32),
        ((389815515 : Dyadic) * half ^ 32)⟩,
       ⟨((195742481 : Dyadic) * half ^ 32),
        ((488588069 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word30Step41 :
    word30Chunk41.foldl (fun acc a => a.applyPacked acc)
      word30State41 = word30State42 := by decide +kernel

private def word30Chunk42 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word30State43 : PackedMat2 :=
    ⟨⟨⟨((3468817553 : Dyadic) * half ^ 32),
        ((122294161 : Dyadic) * half ^ 31)⟩,
       ⟨((-214978681 : Dyadic) * half ^ 31),
        ((691105697 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((335672447 : Dyadic) * half ^ 32),
        ((-482500035 : Dyadic) * half ^ 31)⟩,
       ⟨((131912261 : Dyadic) * half ^ 30),
        ((132253883 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1097253953 : Dyadic) * half ^ 32),
        ((-191976597 : Dyadic) * half ^ 33)⟩,
       ⟨((832746187 : Dyadic) * half ^ 32),
        ((-863321491 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((35550721 : Dyadic) * half ^ 27),
        ((-3898774915 : Dyadic) * half ^ 33)⟩,
       ⟨((406699929 : Dyadic) * half ^ 30),
        ((3038860191 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word30Step42 :
    word30Chunk42.foldl (fun acc a => a.applyPacked acc)
      word30State42 = word30State43 := by decide +kernel

private def word30Chunk43 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word30State44 : PackedMat2 :=
    ⟨⟨⟨((-93335911 : Dyadic) * half ^ 29),
        ((1367706741 : Dyadic) * half ^ 34)⟩,
       ⟨((-550147565 : Dyadic) * half ^ 32),
        ((2118216137 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-326988483 : Dyadic) * half ^ 33),
        ((-10354787415 : Dyadic) * half ^ 34)⟩,
       ⟨((190611881 : Dyadic) * half ^ 33),
        ((5179452301 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((326988483 : Dyadic) * half ^ 33),
        ((10354787415 : Dyadic) * half ^ 34)⟩,
       ⟨((190611881 : Dyadic) * half ^ 33),
        ((5179452301 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-93335911 : Dyadic) * half ^ 29),
        ((1367706741 : Dyadic) * half ^ 34)⟩,
       ⟨((550147565 : Dyadic) * half ^ 32),
        ((-2118216137 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word30Step43 :
    word30Chunk43.foldl (fun acc a => a.applyPacked acc)
      word30State43 = word30State44 := by decide +kernel

private def word30Chunk44 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word30State45 : PackedMat2 :=
    ⟨⟨⟨((1263917357 : Dyadic) * half ^ 32),
        ((-4968588687 : Dyadic) * half ^ 35)⟩,
       ⟨((8391961419 : Dyadic) * half ^ 34),
        ((-315283155 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-8802437857 : Dyadic) * half ^ 34),
        ((-8427098973 : Dyadic) * half ^ 35)⟩,
       ⟨((139912785 : Dyadic) * half ^ 29),
        ((-10366643099 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-139912785 : Dyadic) * half ^ 29),
        ((10366643099 : Dyadic) * half ^ 35)⟩,
       ⟨((8802437857 : Dyadic) * half ^ 34),
        ((8427098973 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((8391961419 : Dyadic) * half ^ 34),
        ((-315283155 : Dyadic) * half ^ 35)⟩,
       ⟨((1263917357 : Dyadic) * half ^ 32),
        ((-4968588687 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word30Step44 :
    word30Chunk44.foldl (fun acc a => a.applyPacked acc)
      word30State44 = word30State45 := by decide +kernel

private def word30Chunk45 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word30State46 : PackedMat2 :=
    ⟨⟨⟨((7598582491 : Dyadic) * half ^ 34),
        ((-19393882401 : Dyadic) * half ^ 36)⟩,
       ⟨((19434095663 : Dyadic) * half ^ 35),
        ((19540216725 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((11913533793 : Dyadic) * half ^ 35),
        ((-4787762667 : Dyadic) * half ^ 36)⟩,
       ⟨((-2184051129 : Dyadic) * half ^ 34),
        ((6404437589 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((174878129 : Dyadic) * half ^ 30),
        ((-16281636051 : Dyadic) * half ^ 36)⟩,
       ⟨((808337461 : Dyadic) * half ^ 35),
        ((7545431535 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-19467049563 : Dyadic) * half ^ 35),
        ((-4236930681 : Dyadic) * half ^ 36)⟩,
       ⟨((-36583581 : Dyadic) * half ^ 34),
        ((-34631260645 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word30Step45 :
    word30Chunk45.foldl (fun acc a => a.applyPacked acc)
      word30State45 = word30State46 := by decide +kernel

private def word30Chunk46 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word30State47 : PackedMat2 :=
    ⟨⟨⟨((-17229937903 : Dyadic) * half ^ 35),
        ((2224837825 : Dyadic) * half ^ 36)⟩,
       ⟨((11411923957 : Dyadic) * half ^ 35),
        ((3032758949 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((9507217627 : Dyadic) * half ^ 35),
        ((18481423361 : Dyadic) * half ^ 36)⟩,
       ⟨((8378784091 : Dyadic) * half ^ 34),
        ((-2057365599 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-8378784091 : Dyadic) * half ^ 34),
        ((2057365599 : Dyadic) * half ^ 33)⟩,
       ⟨((-9507217627 : Dyadic) * half ^ 35),
        ((-18481423361 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((11411923957 : Dyadic) * half ^ 35),
        ((3032758949 : Dyadic) * half ^ 34)⟩,
       ⟨((-17229937903 : Dyadic) * half ^ 35),
        ((2224837825 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word30Step46 :
    word30Chunk46.foldl (fun acc a => a.applyPacked acc)
      word30State46 = word30State47 := by decide +kernel

private def word30Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word30State48 : PackedMat2 :=
    ⟨⟨⟨((-6944703901 : Dyadic) * half ^ 35),
        ((52789060941 : Dyadic) * half ^ 37)⟩,
       ⟨((3585715433 : Dyadic) * half ^ 35),
        ((-7302251827 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((18547969435 : Dyadic) * half ^ 36),
        ((-4190186327 : Dyadic) * half ^ 37)⟩,
       ⟨((50592765201 : Dyadic) * half ^ 36),
        ((17063622309 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-5313452159 : Dyadic) * half ^ 35),
        ((-16022397883 : Dyadic) * half ^ 36)⟩,
       ⟨((-6436717991 : Dyadic) * half ^ 36),
        ((-17285183659 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-469463381 : Dyadic) * half ^ 30),
        ((5265209667 : Dyadic) * half ^ 35)⟩,
       ⟨((22743404557 : Dyadic) * half ^ 36),
        ((-839747117 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word30Step47 :
    word30Chunk47.foldl (fun acc a => a.applyPacked acc)
      word30State47 = word30State48 := by decide +kernel

private def word30Chunk48 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word30State49 : PackedMat2 :=
    ⟨⟨⟨((56244534393 : Dyadic) * half ^ 37),
        ((11568231989 : Dyadic) * half ^ 38)⟩,
       ⟨((-7377470819 : Dyadic) * half ^ 36),
        ((136272657309 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-3092161893 : Dyadic) * half ^ 34),
        ((-1028522107 : Dyadic) * half ^ 38)⟩,
       ⟨((12868187187 : Dyadic) * half ^ 37),
        ((103713321011 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((12868187187 : Dyadic) * half ^ 37),
        ((103713321011 : Dyadic) * half ^ 38)⟩,
       ⟨((-3092161893 : Dyadic) * half ^ 34),
        ((-1028522107 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((7377470819 : Dyadic) * half ^ 36),
        ((-136272657309 : Dyadic) * half ^ 38)⟩,
       ⟨((-56244534393 : Dyadic) * half ^ 37),
        ((-11568231989 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word30Step48 :
    word30Chunk48.foldl (fun acc a => a.applyPacked acc)
      word30State48 = word30State49 := by decide +kernel

private def word30Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word30State50 : PackedMat2 :=
    ⟨⟨⟨((1681873305 : Dyadic) * half ^ 35),
        ((-63748454767 : Dyadic) * half ^ 38)⟩,
       ⟨((108627243423 : Dyadic) * half ^ 37),
        ((-4228282295 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-7162912733 : Dyadic) * half ^ 36),
        ((-8457626995 : Dyadic) * half ^ 38)⟩,
       ⟨((33805140065 : Dyadic) * half ^ 36),
        ((1133627633 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-9680415133 : Dyadic) * half ^ 38),
        ((-6660556833 : Dyadic) * half ^ 35)⟩,
       ⟨((26595669123 : Dyadic) * half ^ 38),
        ((20484026399 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-72205019357 : Dyadic) * half ^ 38),
        ((115354736643 : Dyadic) * half ^ 38)⟩,
       ⟨((-55291890177 : Dyadic) * half ^ 38),
        ((-101899750203 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word30Step49 :
    word30Chunk49.foldl (fun acc a => a.applyPacked acc)
      word30State49 = word30State50 := by decide +kernel

private def word30Chunk50 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word30State51 : PackedMat2 :=
    ⟨⟨⟨((1757092297 : Dyadic) * half ^ 36),
        ((-278922322457 : Dyadic) * half ^ 39)⟩,
       ⟨((9960068445 : Dyadic) * half ^ 38),
        ((31448790451 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((7048072349 : Dyadic) * half ^ 36),
        ((188857852591 : Dyadic) * half ^ 39)⟩,
       ⟨((17448217575 : Dyadic) * half ^ 37),
        ((-66151378783 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((17448217575 : Dyadic) * half ^ 37),
        ((-66151378783 : Dyadic) * half ^ 38)⟩,
       ⟨((7048072349 : Dyadic) * half ^ 36),
        ((188857852591 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-9960068445 : Dyadic) * half ^ 38),
        ((-31448790451 : Dyadic) * half ^ 37)⟩,
       ⟨((-1757092297 : Dyadic) * half ^ 36),
        ((278922322457 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word30Step50 :
    word30Chunk50.foldl (fun acc a => a.applyPacked acc)
      word30State50 = word30State51 := by decide +kernel

private def word30Chunk51 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word30State52 : PackedMat2 :=
    ⟨⟨⟨((13561056303 : Dyadic) * half ^ 38),
        ((-547857337227 : Dyadic) * half ^ 40)⟩,
       ⟨((-159041271807 : Dyadic) * half ^ 38),
        ((-2735149265 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-69620469255 : Dyadic) * half ^ 39),
        ((-136164756779 : Dyadic) * half ^ 40)⟩,
       ⟨((-16842070347 : Dyadic) * half ^ 39),
        ((-267733764381 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-65784503801 : Dyadic) * half ^ 39),
        ((13194599727 : Dyadic) * half ^ 38)⟩,
       ⟨((-50487315145 : Dyadic) * half ^ 37),
        ((-43231269801 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-272561093981 : Dyadic) * half ^ 39),
        ((86301164055 : Dyadic) * half ^ 38)⟩,
       ⟨((137648121623 : Dyadic) * half ^ 38),
        ((9092513469 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word30Step51 :
    word30Chunk51.foldl (fun acc a => a.applyPacked acc)
      word30State51 = word30State52 := by decide +kernel

private def word30Chunk52 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word30State53 : PackedMat2 :=
    ⟨⟨⟨((110456402959 : Dyadic) * half ^ 40),
        ((-317228697361 : Dyadic) * half ^ 41)⟩,
       ⟨((-779184606667 : Dyadic) * half ^ 40),
        ((-386314252961 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-53127713695 : Dyadic) * half ^ 39),
        ((-10751882263 : Dyadic) * half ^ 41)⟩,
       ⟨((159187639093 : Dyadic) * half ^ 39),
        ((-838986700803 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-53127713695 : Dyadic) * half ^ 39),
        ((-10751882263 : Dyadic) * half ^ 41)⟩,
       ⟨((-159187639093 : Dyadic) * half ^ 39),
        ((838986700803 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-110456402959 : Dyadic) * half ^ 40),
        ((317228697361 : Dyadic) * half ^ 41)⟩,
       ⟨((-779184606667 : Dyadic) * half ^ 40),
        ((-386314252961 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word30Step52 :
    word30Chunk52.foldl (fun acc a => a.applyPacked acc)
      word30State52 = word30State53 := by decide +kernel

private def word30Chunk53 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word30State54 : PackedMat2 :=
    ⟨⟨⟨((91621436759 : Dyadic) * half ^ 39),
        ((-3928530555 : Dyadic) * half ^ 38)⟩,
       ⟨((-637883273895 : Dyadic) * half ^ 40),
        ((352347362599 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((566170624305 : Dyadic) * half ^ 40),
        ((131635441191 : Dyadic) * half ^ 39)⟩,
       ⟨((486903879829 : Dyadic) * half ^ 40),
        ((-138830252655 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((387711512109 : Dyadic) * half ^ 41),
        ((526537252067 : Dyadic) * half ^ 40)⟩,
       ⟨((665372017419 : Dyadic) * half ^ 41),
        ((19816686119 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-320919118159 : Dyadic) * half ^ 41),
        ((454640400377 : Dyadic) * half ^ 41)⟩,
       ⟨((383775607039 : Dyadic) * half ^ 41),
        ((-821126147413 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word30Step53 :
    word30Chunk53.foldl (fun acc a => a.applyPacked acc)
      word30State53 = word30State54 := by decide +kernel

private def word30Chunk54 : List Letter := [.h, .s, .t, .h]
private def word30State55 : PackedMat2 :=
    ⟨⟨⟨((391404847399 : Dyadic) * half ^ 40),
        ((2002828424835 : Dyadic) * half ^ 42)⟩,
       ⟨((-491994474267 : Dyadic) * half ^ 40),
        ((1391570507143 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((28612435653 : Dyadic) * half ^ 41),
        ((-40464094553 : Dyadic) * half ^ 42)⟩,
       ⟨((373594418163 : Dyadic) * half ^ 41),
        ((-528342292993 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-28612435653 : Dyadic) * half ^ 41),
        ((40464094553 : Dyadic) * half ^ 42)⟩,
       ⟨((373594418163 : Dyadic) * half ^ 41),
        ((-528342292993 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((391404847399 : Dyadic) * half ^ 40),
        ((2002828424835 : Dyadic) * half ^ 42)⟩,
       ⟨((491994474267 : Dyadic) * half ^ 40),
        ((-1391570507143 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word30Step54 :
    word30Chunk54.foldl (fun acc a => a.applyPacked acc)
      word30State54 = word30State55 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word30_check : check word30 30 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word30 = word30State55.toMatrix := by
    unfold evalRingPacked
    change ((
      word30Chunk0 ++ word30Chunk1 ++ word30Chunk2 ++ word30Chunk3 ++
      word30Chunk4 ++ word30Chunk5 ++ word30Chunk6 ++ word30Chunk7 ++
      word30Chunk8 ++ word30Chunk9 ++ word30Chunk10 ++ word30Chunk11 ++
      word30Chunk12 ++ word30Chunk13 ++ word30Chunk14 ++ word30Chunk15 ++
      word30Chunk16 ++ word30Chunk17 ++ word30Chunk18 ++ word30Chunk19 ++
      word30Chunk20 ++ word30Chunk21 ++ word30Chunk22 ++ word30Chunk23 ++
      word30Chunk24 ++ word30Chunk25 ++ word30Chunk26 ++ word30Chunk27 ++
      word30Chunk28 ++ word30Chunk29 ++ word30Chunk30 ++ word30Chunk31 ++
      word30Chunk32 ++ word30Chunk33 ++ word30Chunk34 ++ word30Chunk35 ++
      word30Chunk36 ++ word30Chunk37 ++ word30Chunk38 ++ word30Chunk39 ++
      word30Chunk40 ++ word30Chunk41 ++ word30Chunk42 ++ word30Chunk43 ++
      word30Chunk44 ++ word30Chunk45 ++ word30Chunk46 ++ word30Chunk47 ++
      word30Chunk48 ++ word30Chunk49 ++ word30Chunk50 ++ word30Chunk51 ++
      word30Chunk52 ++ word30Chunk53 ++ word30Chunk54
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word30Step0, word30Step1, word30Step2, word30Step3, word30Step4,
      word30Step5, word30Step6, word30Step7, word30Step8, word30Step9,
      word30Step10, word30Step11, word30Step12, word30Step13, word30Step14,
      word30Step15, word30Step16, word30Step17, word30Step18, word30Step19,
      word30Step20, word30Step21, word30Step22, word30Step23, word30Step24,
      word30Step25, word30Step26, word30Step27, word30Step28, word30Step29,
      word30Step30, word30Step31, word30Step32, word30Step33, word30Step34,
      word30Step35, word30Step36, word30Step37, word30Step38, word30Step39,
      word30Step40, word30Step41, word30Step42, word30Step43, word30Step44,
      word30Step45, word30Step46, word30Step47, word30Step48, word30Step49,
      word30Step50, word30Step51, word30Step52, word30Step53, word30Step54]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
