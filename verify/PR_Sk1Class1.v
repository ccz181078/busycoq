(* Classification: Sk1-like class 1.
   Consolidated from busycoq PR #21, #23, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dahoas.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat PeanoNat String List.

Module TM1.
Import BusyCoq.Individual62.

Import Lia ZifyNat PeanoNat String List.

Import ListNotations.

Open Scope list.

Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0LC0RA_1LA1LC_1RE0LF_0RA1RF_1LB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma tr_init_18 :
  c0 -->* (0inf {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf)).
Proof.
  change (0inf {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf))
    with ((0inf <* []) {{A}}> ([1; 1; 0; 1; 0; 1; 0] *> 0inf)).
  solve_init.
Qed.

Lemma tr_L0_A (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (0 >> 0 >> 1 >> 0 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L0_B (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X).
Proof. es. Qed.

Lemma tr_L10_A (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L10_B (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L10_bot10 (B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 0inf) -->+
  (0 >> 0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 0inf).
Proof. es. Qed.

Lemma tr_L1010_A (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L1010_B (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L1010_bot10 (B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf) -->+
  (0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 0inf).
Proof. es. Qed.

Lemma tr_R11_emp (X : side) :
  0inf {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0inf) {{A}}> (0 >> X).
Proof. es. Qed.

Lemma tr_R11_01 (X : side) :
  (0 >> 1 >> 0inf) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0inf) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_0101 (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_001 (X B_r : side) :
  (0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 0 >> 1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_0011 (X B_r : side) :
  (0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_00001 (X B_r : side) :
  (0 >> 0 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X).
Proof. es. Qed.

Lemma tr_R11_1_B (X B_r : side) :
  (1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_L0_BB (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (0 >> X).
Proof.
  eapply progress_trans; [apply (tr_L0_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L0_B X (0 >> 1 >> 0 >> 1 >> B_r)).
Qed.

Lemma tr_L10_BB (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_L10_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L10_B X (0 >> 0 >> 1 >> 1 >> B_r)).
Qed.

Lemma tr_L1010_BB (X B_r : side) :
  (0 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_L1010_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L1010_B X (0 >> 0 >> 1 >> 1 >> B_r)).
Qed.

Lemma tr_R11_0011_emp (X : side) :
  (0 >> 0 >> 1 >> 1 >> 0inf) {{A}}> (1 >> 1 >> X) -->+
  (0 >> 1 >> 0inf) {{A}}> (1 >> 0 >> X).
Proof. es. Qed.

Lemma tr_R11_0101_pair (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) {{A}}> (1 >> 1 >> X) -->+
  B_r {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_R11_0101 X (0 >> 1 >> 0 >> 1 >> B_r)) |].
  apply (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) B_r).
Qed.

Lemma tr_R11_01_B (X : side) :
  (0 >> 1 >> 0inf) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0inf) {{A}}> (1 >> 0 >> 1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_R11_01 (1 >> 0 >> 1 >> 0 >> X)) |].
  apply (tr_L1010_B X 0inf).
Qed.

Lemma tr_R11_01011_B (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> 1 >> B_r) {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) -->+
  (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B_r) {{A}}> (1 >> 0 >> X).
Proof.
  eapply progress_trans; [apply (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) (1 >> B_r)) |].
  eapply progress_trans; [apply (tr_R11_1_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L10_B X (0 >> 0 >> 1 >> B_r)).
Qed.

Inductive StackL : nat -> side -> Prop :=
  | bot10 : StackL O (1 >> 0 >> 0inf)
  | pushA {a : nat} {X : side} :
      StackL a X -> StackL (S a) (0 >> 1 >> 0 >> X)
  | pushBB {a : nat} {X : side} :
      StackL a X -> StackL a (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X).

Inductive StackR : nat -> side -> Prop :=
  | SR_emp {a : nat} : StackR (S a) 0inf
  | SR_c0011_emp {a : nat} : StackR a (0 >> 0 >> 1 >> 1 >> 0inf)
  | SR_c001 {a : nat} {B : side} :
      StackR (S a) B -> StackR a (0 >> 0 >> 1 >> B)
  | SR_c0011_001 {a : nat} {B : side} :
      StackR (S a) B -> StackR a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B)
  | SR_c0011_0011 {a : nat} {B : side} :
      StackR a B -> StackR a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B)
  | SR_c00001 {a : nat} {B : side} :
      StackR a B -> StackR (S a) (0 >> 0 >> 0 >> 0 >> 1 >> B)
  | SR_c000011 {a : nat} {B : side} :
      StackR a B -> StackR (S a) (0 >> 0 >> 0 >> 0 >> 1 >> 1 >> B).

Lemma StackR_weaken {a : nat} {B : side} (h : StackR a B) : StackR (S a) B.
Proof.
  induction h.
  - exact SR_emp.
  - exact SR_c0011_emp.
  - exact (SR_c001 IHh).
  - exact (SR_c0011_001 IHh).
  - exact (SR_c0011_0011 IHh).
  - exact (SR_c00001 IHh).
  - exact (SR_c000011 IHh).
Qed.

Inductive StackR1010 : nat -> side -> Prop :=
  | SR1010_emp {a : nat} : StackR1010 (S a) 0inf
  | SR1010_c0011_emp {a : nat} : StackR1010 (S a) (0 >> 0 >> 1 >> 1 >> 0inf)
  | SR1010_c001 {a : nat} {B : side} :
      StackR1010 (S a) B -> StackR1010 a (0 >> 0 >> 1 >> B)
  | SR1010_c0011_0011 {a : nat} {B : side} :
      StackR1010 a B -> StackR1010 a (0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B).

Lemma StackR1010_toStackR {a : nat} {B : side} (h : StackR1010 a B) : StackR a B.
Proof.
  induction h.
  - exact SR_emp.
  - exact SR_c0011_emp.
  - exact (SR_c001 IHh).
  - exact (SR_c0011_0011 IHh).
Qed.

Lemma StackR1010_push0011 {a : nat} {B : side} (h : StackR1010 a B) :
  StackR a (0 >> 0 >> 1 >> 1 >> B).
Proof.
  induction h.
  - exact SR_c0011_emp.
  - exact (SR_c0011_0011 SR_emp).
  - exact (SR_c0011_001 (StackR1010_toStackR h)).
  - exact (SR_c0011_0011 IHh).
Qed.

Inductive PopTarget : nat -> side -> Prop :=
  | PT_emp {a : nat} : PopTarget a (0 >> 1 >> 0inf)
  | PT_c0101 {a : nat} {B_0 : side} :
      StackR a B_0 -> PopTarget a (0 >> 1 >> 0 >> 1 >> B_0)
  | PT_c01011 {a : nat} {B_0 : side} :
      StackR a B_0 -> PopTarget a (0 >> 1 >> 0 >> 1 >> 1 >> B_0).

Inductive R0101 : nat -> side -> Prop :=
  | R0101_base {a : nat} {B : side} : PopTarget a B -> R0101 a B
  | R0101_step {a : nat} {B : side} :
      R0101 a B -> R0101 a (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B).

Inductive Inv : Q * tape -> Prop :=
  | Mode_L0 {a : nat} {X B : side} :
      StackL (S a) X -> R0101 a B ->
      Inv ((0 >> 1 >> B) {{A}}> (0 >> X))
  | Mode_L10 {a : nat} {X B : side} :
      StackL a X -> StackR (S (S a)) B ->
      Inv ((0 >> 1 >> B) {{A}}> (1 >> 0 >> X))
  | Mode_L1010 {a : nat} {X B : side} :
      StackL a X -> StackR1010 (S a) B ->
      Inv ((0 >> 1 >> B) {{A}}> (1 >> 0 >> 1 >> 0 >> X))
  | Mode_R11 {a : nat} {X B : side} :
      StackL a X -> StackR a B ->
      Inv (B {{A}}> (1 >> 1 >> X))
  | Mode_R11_pop {a : nat} {X B : side} :
      StackL a X -> R0101 a B ->
      Inv (B {{A}}> (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X)).

Lemma step_Inv : forall c : Q * tape, Inv c -> exists c' : Q * tape, Inv c' /\ c -->+ c'.
Proof.
  intros c hc.
  destruct hc as [a X B hX hB | a X B hX hB | a X B hX hB | a X B hX hB | a X B hX hB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11_pop hX' hB) | apply tr_L0_A].
    + eexists. split; [exact (Mode_L0 hX' (R0101_step hB)) | apply tr_L0_BB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11 bot10 (SR_c001 (SR_c001 hB))) | apply tr_L10_bot10].
    + eexists. split; [exact (Mode_L10 hX' (SR_c001 hB)) | apply tr_L10_A].
    + eexists. split; [exact (Mode_L10 hX' (SR_c0011_0011 hB)) | apply tr_L10_BB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11 bot10 (SR_c001 (StackR1010_push0011 hB))) | apply tr_L1010_bot10].
    + eexists. split; [exact (Mode_L1010 hX' (SR1010_c001 hB)) | apply tr_L1010_A].
    + eexists. split; [exact (Mode_L1010 hX' (SR1010_c0011_0011 hB)) | apply tr_L1010_BB].
  - inverts hB as hB'.
    + eexists. split; [exact (Mode_L0 hX (R0101_base PT_emp)) | apply tr_R11_emp].
    + eexists. split; [exact (Mode_L10 hX SR_emp) | apply tr_R11_0011_emp].
    + eexists. split; [exact (Mode_R11 (pushA hX) hB') | apply tr_R11_001].
    + eexists. split; [exact (Mode_L10 hX (SR_c00001 hB')) | apply tr_R11_0011].
    + eexists. split; [exact (Mode_L10 hX (SR_c000011 (StackR_weaken hB'))) | apply tr_R11_0011].
    + eexists. split; [exact (Mode_L0 hX (R0101_base (PT_c0101 hB'))) | apply tr_R11_00001].
    + eexists. split; [exact (Mode_L0 hX (R0101_base (PT_c01011 hB'))) | apply tr_R11_00001].
  - inverts hB as hB'.
    + inverts hB' as hT.
      * eexists. split; [exact (Mode_L1010 hX SR1010_c0011_emp) | apply tr_R11_01_B].
      * eexists. split; [exact (Mode_R11 (pushBB hX) hT) | apply tr_R11_0101].
      * eexists. split;
          [exact (Mode_L10 hX (SR_c0011_001 (StackR_weaken (StackR_weaken (StackR_weaken hT)))))
          | apply tr_R11_01011_B].
    + eexists. split; [exact (Mode_R11_pop (pushBB hX) hB') | apply tr_R11_0101_pair].
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact tr_init_18.
  - apply progress_nonhalt with (P := Inv).
    + exact step_Inv.
    + exact (Mode_R11 (pushA bot10) SR_emp).
Qed.

End TM1.
Print Assumptions TM1.nonhalt.



Module TM2.
Import BusyCoq.Individual62.

Import Lia ZifyNat PeanoNat String List.

Import ListNotations.

Open Scope list.

Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB---_0RC0LD_1RD1RC_1LB0LE_1LF0RA_0LD1LA").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma tr_init_19 :
  c0 -->* ((1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf) <{{D}} (0 >> 1 >> 0inf)).
Proof.
  change ((1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf) <{{D}} (0 >> 1 >> 0inf))
    with ((0inf <* [1; 0; 1; 0; 1; 0]) <{{D}} ([0; 1] *> 0inf)).
  solve_init.
Qed.

Lemma tr_L0_A (X B_r : side) :
  (0 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} B_r.
Proof. es. Qed.

Lemma tr_L0_B (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (0 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L10_A (X B_r : side) :
  (1 >> 0 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L10_B (X B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L10_bot10 (B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 0inf) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 1 >> 1 >> 0 >> 0inf) <{{D}} (0 >> 0 >> 1 >> 0 >> 0 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L1010_A (X B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L1010_B (X B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L1010_bot10 (B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0inf) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 1 >> 1 >> 0 >> 0inf) <{{D}} (0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_R11_emp (X : side) :
  (1 >> 1 >> X) <{{D}} 0inf -->+
  (0 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> 0inf).
Proof. es. Qed.

Lemma tr_R11_01 (X : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 1 >> 0inf) -->+
  (1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0inf).
Proof. es. Qed.

Lemma tr_R11_0101 (X B_r : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> B_r) -->+
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} B_r.
Proof. es. Qed.

Lemma tr_R11_001 (X B_r : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 0 >> 1 >> B_r) -->+
  (1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} B_r.
Proof. es. Qed.

Lemma tr_R11_0011 (X B_r : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 0 >> 1 >> 1 >> B_r) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> B_r).
Proof. es. Qed.

Lemma tr_R11_00001 (X B_r : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 0 >> 0 >> 0 >> 1 >> B_r) -->+
  (0 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_R11_1_B (X B_r : side) :
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (1 >> B_r) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> B_r).
Proof. es. Qed.

Lemma tr_L0_BB (X B_r : side) :
  (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (0 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r).
Proof.
  eapply progress_trans; [apply (tr_L0_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L0_B X (0 >> 1 >> 0 >> 1 >> B_r)).
Qed.

Lemma tr_L10_BB (X B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r).
Proof.
  eapply progress_trans; [apply (tr_L10_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L10_B X (0 >> 0 >> 1 >> 1 >> B_r)).
Qed.

Lemma tr_L1010_BB (X B_r : side) :
  (1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B_r) -->+
  (1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> B_r).
Proof.
  eapply progress_trans; [apply (tr_L1010_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L1010_B X (0 >> 0 >> 1 >> 1 >> B_r)).
Qed.

Lemma tr_R11_0011_emp (X : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 0 >> 1 >> 1 >> 0inf) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0inf).
Proof. es. Qed.

Lemma tr_R11_0101_pair (X B_r : side) :
  (1 >> 1 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> B_r) -->+
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} B_r.
Proof.
  eapply progress_trans; [apply (tr_R11_0101 X (0 >> 1 >> 0 >> 1 >> B_r)) |].
  apply (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) B_r).
Qed.

Lemma tr_R11_01_B (X : side) :
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0inf) -->+
  (1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0inf).
Proof.
  eapply progress_trans; [apply (tr_R11_01 (1 >> 0 >> 1 >> 0 >> X)) |].
  apply (tr_L1010_B X 0inf).
Qed.

Lemma tr_R11_01011_B (X B_r : side) :
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 1 >> 1 >> B_r) -->+
  (1 >> 0 >> X) <{{D}} (0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> B_r).
Proof.
  eapply progress_trans; [apply (tr_R11_0101 (1 >> 0 >> 1 >> 0 >> X) (1 >> B_r)) |].
  eapply progress_trans; [apply (tr_R11_1_B (1 >> 0 >> 1 >> 0 >> X) B_r) |].
  apply (tr_L10_B X (0 >> 0 >> 1 >> B_r)).
Qed.

Notation StackL := TM1.StackL.

Notation bot10 := TM1.bot10.

Notation pushA := TM1.pushA.

Notation pushBB := TM1.pushBB.

Notation StackR := TM1.StackR.

Notation SR_emp := TM1.SR_emp.

Notation SR_c0011_emp := TM1.SR_c0011_emp.

Notation SR_c001 := TM1.SR_c001.

Notation SR_c0011_001 := TM1.SR_c0011_001.

Notation SR_c0011_0011 := TM1.SR_c0011_0011.

Notation SR_c00001 := TM1.SR_c00001.

Notation SR_c000011 := TM1.SR_c000011.

Notation StackR_weaken := TM1.StackR_weaken.

Notation StackR1010 := TM1.StackR1010.

Notation SR1010_emp := TM1.SR1010_emp.

Notation SR1010_c0011_emp := TM1.SR1010_c0011_emp.

Notation SR1010_c001 := TM1.SR1010_c001.

Notation SR1010_c0011_0011 := TM1.SR1010_c0011_0011.

Notation StackR1010_toStackR := TM1.StackR1010_toStackR.

Notation StackR1010_push0011 := TM1.StackR1010_push0011.

Notation PopTarget := TM1.PopTarget.

Notation PT_emp := TM1.PT_emp.

Notation PT_c0101 := TM1.PT_c0101.

Notation PT_c01011 := TM1.PT_c01011.

Notation R0101 := TM1.R0101.

Notation R0101_base := TM1.R0101_base.

Notation R0101_step := TM1.R0101_step.

Inductive Inv : Q * tape -> Prop :=
  | Mode_L0 {a : nat} {X B : side} :
      StackL (S a) X -> R0101 a B ->
      Inv ((0 >> X) <{{D}} (0 >> 1 >> B))
  | Mode_L10 {a : nat} {X B : side} :
      StackL a X -> StackR (S (S a)) B ->
      Inv ((1 >> 0 >> X) <{{D}} (0 >> 1 >> B))
  | Mode_L1010 {a : nat} {X B : side} :
      StackL a X -> StackR1010 (S a) B ->
      Inv ((1 >> 0 >> 1 >> 0 >> X) <{{D}} (0 >> 1 >> B))
  | Mode_R11 {a : nat} {X B : side} :
      StackL a X -> StackR a B ->
      Inv ((1 >> 1 >> X) <{{D}} B)
  | Mode_R11_pop {a : nat} {X B : side} :
      StackL a X -> R0101 a B ->
      Inv ((1 >> 1 >> 1 >> 0 >> 1 >> 0 >> X) <{{D}} B).

Lemma step_Inv : forall c : Q * tape, Inv c -> exists c' : Q * tape, Inv c' /\ c -->+ c'.
Proof.
  intros c hc.
  destruct hc as [a X B hX hB | a X B hX hB | a X B hX hB | a X B hX hB | a X B hX hB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11_pop hX' hB) | apply tr_L0_A].
    + eexists. split; [exact (Mode_L0 hX' (R0101_step hB)) | apply tr_L0_BB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11 bot10 (SR_c001 (SR_c001 hB))) | apply tr_L10_bot10].
    + eexists. split; [exact (Mode_L10 hX' (SR_c001 hB)) | apply tr_L10_A].
    + eexists. split; [exact (Mode_L10 hX' (SR_c0011_0011 hB)) | apply tr_L10_BB].
  - inverts hX as hX'.
    + eexists. split; [exact (Mode_R11 bot10 (SR_c001 (StackR1010_push0011 hB))) | apply tr_L1010_bot10].
    + eexists. split; [exact (Mode_L1010 hX' (SR1010_c001 hB)) | apply tr_L1010_A].
    + eexists. split; [exact (Mode_L1010 hX' (SR1010_c0011_0011 hB)) | apply tr_L1010_BB].
  - inverts hB as hB'.
    + eexists. split; [exact (Mode_L0 hX (R0101_base PT_emp)) | apply tr_R11_emp].
    + eexists. split; [exact (Mode_L10 hX SR_emp) | apply tr_R11_0011_emp].
    + eexists. split; [exact (Mode_R11 (pushA hX) hB') | apply tr_R11_001].
    + eexists. split; [exact (Mode_L10 hX (SR_c00001 hB')) | apply tr_R11_0011].
    + eexists. split; [exact (Mode_L10 hX (SR_c000011 (StackR_weaken hB'))) | apply tr_R11_0011].
    + eexists. split; [exact (Mode_L0 hX (R0101_base (PT_c0101 hB'))) | apply tr_R11_00001].
    + eexists. split; [exact (Mode_L0 hX (R0101_base (PT_c01011 hB'))) | apply tr_R11_00001].
  - inverts hB as hB'.
    + inverts hB' as hT.
      * eexists. split; [exact (Mode_L1010 hX SR1010_c0011_emp) | apply tr_R11_01_B].
      * eexists. split; [exact (Mode_R11 (pushBB hX) hT) | apply tr_R11_0101].
      * eexists. split;
          [exact (Mode_L10 hX (SR_c0011_001 (StackR_weaken (StackR_weaken (StackR_weaken hT)))))
          | apply tr_R11_01011_B].
    + eexists. split; [exact (Mode_R11_pop (pushBB hX) hB') | apply tr_R11_0101_pair].
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact tr_init_19.
  - apply progress_nonhalt with (P := Inv).
    + exact step_Inv.
    + exact (Mode_L1010 bot10 SR1010_emp).
Qed.

End TM2.
Print Assumptions TM2.nonhalt.

From Coq Require Import String Bool Lists.List Lia PeanoNat.

Module TM3.
Import BusyCoq.Individual62.

Import String Bool List Lia PeanoNat.

Import ListNotations.

Open Scope list.

Open Scope sym.

Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB0RB_1RC1LC_0LD1RA_1LF1LE_0LA1LC_1LB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma pe_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma ep_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Fixpoint encRight (R : list bool) : side :=
  match R with
  | [] => 0inf%sym
  | false :: R' => 1%sym >> 0%sym >> encRight R'
  | true :: R' => 1%sym >> 1%sym >> 0%sym >> encRight R'
  end.

Definition cfg_B (tl : side) (R : list bool) : Q * tape :=
  B;; (0%sym >> tl) {{0%sym}} (encRight R).

Definition cfg_C (tl : side) (R : list bool) : Q * tape :=
  C;; tl {{0%sym}} (encRight R).

Definition T2 (tl : side) : side := 1%sym >> 1%sym >> 0%sym >> tl.

Definition T3 (tl : side) : side := 1%sym >> 1%sym >> 1%sym >> 0%sym >> tl.

Definition T4 (tl : side) : side := 1%sym >> 1%sym >> 1%sym >> 1%sym >> 0%sym >> tl.

Definition T6 (tl : side) : side :=
  1%sym >> 1%sym >> 1%sym >> 1%sym >> 1%sym >> 1%sym >> 0%sym >> tl.

Definition T12 (tl : side) : side := 1%sym >> 0%sym >> 1%sym >> 1%sym >> 0%sym >> tl.

Definition T322 (tl : side) : side :=
  1%sym >> 1%sym >> 1%sym >> 0%sym >> 0%sym >> 1%sym >> 1%sym >> 0%sym >> tl.

Lemma rule_B_nil (tl : side) :
  cfg_B tl [] -->+ cfg_C (1%sym >> 0%sym >> tl) [].
Proof. unfold cfg_B, cfg_C; simpl; start_progress. Qed.

Lemma rule_B_true (tl : side) (R : list bool) :
  cfg_B tl (true :: R) -->+ cfg_B (T2 tl) R.
Proof. unfold cfg_B, T2; simpl; start_progress. Qed.

Lemma rule_B_false_nil (tl : side) :
  cfg_B tl [false] -->+ cfg_C (T4 tl) [].
Proof. unfold cfg_B, cfg_C, T4; simpl; start_progress. Qed.

Lemma rule_B_false_false (tl : side) (R : list bool) :
  cfg_B tl (false :: false :: R) -->+ cfg_B (T3 tl) R.
Proof. unfold cfg_B, T3; simpl; start_progress. Qed.

Lemma rule_B_false_true (tl : side) (R : list bool) :
  cfg_B tl (false :: true :: R) -->+ cfg_C (T3 tl) (false :: R).
Proof. unfold cfg_B, cfg_C, T3; simpl; start_progress. Qed.

Lemma rule_C_110 (tl : side) (R : list bool) :
  cfg_C (T2 tl) R -->+ cfg_C tl (true :: R).
Proof. unfold cfg_C, T2; simpl; start_progress. Qed.

Lemma rule_C_111 (tl : side) (R : list bool) :
  cfg_C (1%sym >> 1%sym >> 1%sym >> tl) R -->+ cfg_C (1%sym >> tl) (false :: R).
Proof. unfold cfg_C; simpl; start_progress. Qed.

Lemma rule_C_101 (tl : side) (R : list bool) :
  cfg_C (1%sym >> 0%sym >> 1%sym >> tl) R -->+ cfg_B tl (false :: R).
Proof. unfold cfg_C, cfg_B; simpl; start_progress. Qed.

Lemma rule_C_100_false (tl : side) (R : list bool) :
  cfg_C (1%sym >> 0%sym >> 0%sym >> tl) (false :: R) -->+
    cfg_B (1%sym >> 1%sym >> 1%sym >> 1%sym >> tl) R.
Proof. unfold cfg_C, cfg_B; simpl; start_progress. Qed.

Lemma rule_C_41 (tl : side) (R : list bool) :
  cfg_C (T4 tl) R -->+ cfg_C (T2 tl) (false :: R).
Proof. exact (rule_C_111 (1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_61 (tl : side) (R : list bool) :
  cfg_C (T6 tl) R -->+ cfg_C (T4 tl) (false :: R).
Proof. exact (rule_C_111 (1%sym >> 1%sym >> 1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_32 (tl : side) (R : list bool) :
  cfg_C (1%sym >> 1%sym >> 1%sym >> 0%sym >> 0%sym >> tl) R -->+
    cfg_B (1%sym >> 1%sym >> 1%sym >> 1%sym >> tl) R.
Proof.
  exact (ptrans (rule_C_111 (0%sym >> 0%sym >> tl) R) (rule_C_100_false tl R)).
Qed.

Lemma rule_C_31_1 (tl : side) (R : list bool) :
  cfg_C (T3 (1%sym >> tl)) R -->+ cfg_B (T3 tl) R.
Proof.
  exact (ptrans (rule_C_111 (0%sym >> 1%sym >> tl) R)
    (ptrans (rule_C_101 tl (false :: R)) (rule_B_false_false tl R))).
Qed.

Lemma rule_B_nil_1 (tl : side) :
  cfg_B (1%sym >> tl) [] -->+ cfg_C (T4 tl) [].
Proof.
  exact (ptrans (rule_B_nil (1%sym >> tl))
    (ptrans (rule_C_101 tl []) (rule_B_false_nil tl))).
Qed.

Lemma rule_B_carry_true (tl : side) (R : list bool) :
  cfg_B (1%sym >> tl) (false :: true :: R) -->+ cfg_B (T3 tl) (false :: R).
Proof.
  exact (ptrans (rule_B_false_true (1%sym >> tl) R) (rule_C_31_1 tl (false :: R))).
Qed.

Lemma rule_C_3_22 (tl : side) (R : list bool) :
  cfg_C (T3 (T2 (T2 tl))) R -->+ cfg_B (T3 (T12 tl)) R.
Proof. exact (rule_C_31_1 (1%sym >> 0%sym >> T2 tl) R). Qed.

Lemma rule_C_3_12 (tl : side) (R : list bool) :
  cfg_C (T3 (T12 tl)) R -->+ cfg_B (T322 tl) R.
Proof. exact (rule_C_31_1 (0%sym >> 1%sym >> 1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_322 (tl : side) (R : list bool) :
  cfg_C (T322 tl) R -->+ cfg_B (T6 tl) R.
Proof. exact (rule_C_32 (1%sym >> 1%sym >> 0%sym >> tl) R). Qed.

Lemma rule_C_6 (tl : side) (R : list bool) :
  cfg_C (T6 tl) R -->+ cfg_C tl (true :: false :: false :: R).
Proof.
  exact (ptrans (rule_C_61 tl R)
    (ptrans (rule_C_41 tl (false :: R)) (rule_C_110 tl (false :: false :: R)))).
Qed.

Lemma rule_C_default (R : list bool) :
  cfg_C 0inf%sym R -->+ cfg_B 0inf%sym (true :: R).
Proof.
  unfold cfg_C, cfg_B; simpl; rewrite <- const_unfold; start_progress.
Qed.

Lemma rule_B_norm_exit (tl : side) :
  cfg_B (T2 (T2 tl)) [false] -->+ cfg_C tl [true; true; true; false].
Proof.
  exact (ptrans (rule_B_false_nil (T2 (T2 tl)))
    (ptrans (rule_C_41 (T2 (T2 tl)) [])
      (ptrans (rule_C_110 (T2 (T2 tl)) [false])
        (ptrans (rule_C_110 (T2 tl) [true; false])
          (rule_C_110 tl [true; true; false]))))).
Qed.

Lemma rule_B_carry_exit (tl : side) :
  cfg_B (T3 (T2 (T2 tl))) [false; false] -->+
    cfg_C (T3 (T12 tl)) [true; true; true; false].
Proof.
  exact (ptrans (rule_B_false_false (T3 (T2 (T2 tl))) [])
    (ptrans (rule_B_nil_1 (T2 (T3 (T2 (T2 tl)))))
      (ptrans (rule_C_41 (T2 (T3 (T2 (T2 tl)))) [])
        (ptrans (rule_C_110 (T2 (T3 (T2 (T2 tl)))) [false])
          (ptrans (rule_C_110 (T3 (T2 (T2 tl))) [true; false])
            (ptrans (rule_C_3_22 tl [true; true; false])
              (ptrans (rule_B_true (T3 (T12 tl)) [true; false])
                (ptrans (rule_B_true (T2 (T3 (T12 tl))) [false])
                  (ptrans (rule_B_false_nil (T2 (T2 (T3 (T12 tl)))))
                    (ptrans (rule_C_41 (T2 (T2 (T3 (T12 tl)))) [])
                      (ptrans (rule_C_110 (T2 (T2 (T3 (T12 tl)))) [false])
                        (ptrans (rule_C_110 (T2 (T3 (T12 tl))) [true; false])
                          (rule_C_110 (T3 (T12 tl)) [true; true; false]))))))))))))).
Qed.

Lemma rule_C_3_0 (R : list bool) :
  cfg_C (T3 0inf%sym) R -->+ cfg_B (T4 0inf%sym) R.
Proof.
  unfold T3, T4.
  pose proof (rule_C_32 0inf%sym R) as H.
  repeat rewrite <- const_unfold in *.
  exact H.
Qed.

Lemma rule_C_6_3 (R : list bool) :
  cfg_C (T6 (T2 (T2 (T2 (T3 0inf%sym))))) R -->+
    cfg_B (T3 (T2 (T2 (T2 (T2 (T4 0inf%sym)))))) R.
Proof.
  exact (ptrans (rule_C_6 (T2 (T2 (T2 (T3 0inf%sym)))) R)
    (ptrans (rule_C_110 (T2 (T2 (T3 0inf%sym))) (true :: false :: false :: R))
      (ptrans (rule_C_110 (T2 (T3 0inf%sym)) (true :: true :: false :: false :: R))
        (ptrans (rule_C_110 (T3 0inf%sym) (true :: true :: true :: false :: false :: R))
          (ptrans (rule_C_3_0 (true :: true :: true :: true :: false :: false :: R))
            (ptrans (rule_B_true (T4 0inf%sym) (true :: true :: true :: false :: false :: R))
              (ptrans (rule_B_true (T2 (T4 0inf%sym)) (true :: true :: false :: false :: R))
                (ptrans (rule_B_true (T2 (T2 (T4 0inf%sym))) (true :: false :: false :: R))
                  (ptrans (rule_B_true (T2 (T2 (T2 (T4 0inf%sym)))) (false :: false :: R))
                    (rule_B_false_false (T2 (T2 (T2 (T2 (T4 0inf%sym))))) R)))))))))).
Qed.

Lemma rule_B_carry_3_true (x : side) (R : list bool) :
  cfg_B (T3 x) (false :: true :: R) -->+ cfg_B (T3 (T2 x)) (false :: R).
Proof. exact (rule_B_carry_true (T2 x) R). Qed.

Lemma rule_C_6_4 (R : list bool) :
  cfg_C (T6 (T2 (T2 (T4 0inf%sym)))) R -->+
    cfg_B (T3 (T3 (T2 (T2 (T12 0inf%sym))))) (false :: R).
Proof.
  exact (ptrans (rule_C_6 (T2 (T2 (T4 0inf%sym))) R)
    (ptrans (rule_C_110 (T2 (T4 0inf%sym)) (true :: false :: false :: R))
      (ptrans (rule_C_110 (T4 0inf%sym) (true :: true :: false :: false :: R))
        (ptrans (rule_C_41 0inf%sym (true :: true :: true :: false :: false :: R))
          (ptrans (rule_C_110 0inf%sym (false :: true :: true :: true :: false :: false :: R))
            (ptrans (rule_C_default (true :: false :: true :: true :: true :: false :: false :: R))
              (ptrans (rule_B_true 0inf%sym (true :: false :: true :: true :: true :: false :: false :: R))
                (ptrans (rule_B_true (T2 0inf%sym) (false :: true :: true :: true :: false :: false :: R))
                  (ptrans (rule_B_false_true (T2 (T2 0inf%sym)) (true :: true :: false :: false :: R))
                    (ptrans (rule_C_3_22 0inf%sym (false :: true :: true :: false :: false :: R))
                      (ptrans (rule_B_carry_3_true (T12 0inf%sym) (true :: false :: false :: R))
                        (ptrans (rule_B_carry_3_true (T2 (T12 0inf%sym)) (false :: false :: R))
                          (rule_B_false_false (T3 (T2 (T2 (T12 0inf%sym)))) (false :: R)))))))))))))).
Qed.

Lemma rule_C_12_0 (R : list bool) :
  cfg_C (T12 0inf%sym) R -->+ cfg_B (1%sym >> 0inf%sym) (false :: R).
Proof.
  unfold T12.
  pose proof (rule_C_101 (1%sym >> 0%sym >> 0inf%sym) R) as H.
  repeat rewrite <- const_unfold in *.
  exact H.
Qed.

Lemma rule_B_carry_1_0 (R : list bool) :
  cfg_B (1%sym >> 0inf%sym) (false :: true :: R) -->+ cfg_B (T3 0inf%sym) (false :: R).
Proof. exact (rule_B_carry_true 0inf%sym R). Qed.

Lemma rule_C_6_12 (R : list bool) :
  cfg_C (T6 (T12 0inf%sym)) R -->+
    cfg_B (T3 (T3 0inf%sym)) (false :: R).
Proof.
  exact (ptrans (rule_C_6 (T12 0inf%sym) R)
    (ptrans (rule_C_12_0 (true :: false :: false :: R))
      (ptrans (rule_B_carry_1_0 (false :: false :: R))
        (rule_B_false_false (T3 0inf%sym) (false :: R))))).
Qed.

Fixpoint powT2 (n : nat) (x : side) : side :=
  match n with
  | O => x
  | S n' => T2 (powT2 n' x)
  end.

Fixpoint powTrue (n : nat) (R : list bool) : list bool :=
  match n with
  | O => R
  | S n' => true :: powTrue n' R
  end.

Lemma powT2_comm (n : nat) (x : side) : powT2 n (T2 x) = T2 (powT2 n x).
Proof.
  induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma powTrue_comm (n : nat) (R : list bool) : powTrue n (true :: R) = true :: powTrue n R.
Proof.
  induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma c_pop_T2 (n : nat) (x : side) (R : list bool) :
  cfg_C (powT2 n x) R -->* cfg_C x (powTrue n R).
Proof.
  revert R.
  induction n as [|n IH]; intros R; simpl.
  - apply evstep_refl.
  - rewrite <- powTrue_comm.
    exact (pev (pe_trans (rule_C_110 (powT2 n x) R) (IH (true :: R)))).
Qed.

Lemma b_push_T2 (n : nat) (x : side) (R : list bool) :
  cfg_B x (powTrue n R) -->* cfg_B (powT2 n x) R.
Proof.
  revert x.
  induction n as [|n IH]; intros x; simpl.
  - apply evstep_refl.
  - rewrite <- powT2_comm.
    exact (pev (pe_trans (rule_B_true x (powTrue n R)) (IH (T2 x)))).
Qed.

Lemma b_carry_push_T2 (n : nat) (x : side) (R : list bool) :
  cfg_B (T3 x) (false :: powTrue n R) -->* cfg_B (T3 (powT2 n x)) (false :: R).
Proof.
  revert x.
  induction n as [|n IH]; intros x; simpl.
  - apply evstep_refl.
  - rewrite <- powT2_comm.
    exact (pev (pe_trans (rule_B_carry_3_true x (powTrue n R)) (IH (T2 x)))).
Qed.

Lemma c_pop_T6 (b : nat) (tl : side) (R : list bool) :
  cfg_C (T6 (powT2 b tl)) R -->+ cfg_C tl (powTrue (b + 1) (false :: false :: R)).
Proof.
  replace (b + 1) with (S b) by lia; simpl.
  eapply pe_trans; [apply (rule_C_6 (powT2 b tl) R) |].
  pose proof (c_pop_T2 b tl (true :: false :: false :: R)) as H.
  rewrite powTrue_comm in H.
  exact H.
Qed.

Lemma b_norm_block (m : nat) (x : side) (R : list bool) :
  cfg_B x (powTrue m (false :: false :: R)) -->+ cfg_B (T3 (powT2 m x)) R.
Proof.
  exact (ep_trans (b_push_T2 m x (false :: false :: R)) (rule_B_false_false (powT2 m x) R)).
Qed.

Lemma b_carry_block (m : nat) (x : side) (R : list bool) :
  cfg_B (T3 x) (false :: powTrue m (false :: false :: R)) -->+
    cfg_B (T3 (T3 (powT2 m x))) (false :: R).
Proof.
  exact (ep_trans (b_carry_push_T2 m x (false :: false :: R))
    (rule_B_false_false (T3 (powT2 m x)) (false :: R))).
Qed.

Lemma b_norm_end (a : nat) (x : side) :
  cfg_B x (powTrue a [true; true; true; false]) -->+
    cfg_C (powT2 (a + 1) x) [true; true; true; false].
Proof.
  replace (a + 1) with (S a) by lia; simpl.
  exact (ep_trans (b_push_T2 a x [true; true; true; false])
    (ptrans (rule_B_true (powT2 a x) [true; true; false])
      (ptrans (rule_B_true (T2 (powT2 a x)) [true; false])
        (ptrans (rule_B_true (T2 (T2 (powT2 a x))) [false])
          (rule_B_norm_exit (T2 (powT2 a x))))))).
Qed.

Lemma b_carry_end (a : nat) (x : side) :
  cfg_B (T3 x) (false :: powTrue a [true; true; true; false]) -->+
    cfg_C (T3 (T12 (powT2 (a + 1) x))) [true; true; true; false].
Proof.
  replace (a + 1) with (S a) by lia; simpl.
  exact (ep_trans (b_carry_push_T2 a x [true; true; true; false])
    (ptrans (rule_B_carry_3_true (powT2 a x) [true; true; false])
      (ptrans (rule_B_carry_3_true (T2 (powT2 a x)) [true; false])
        (ptrans (rule_B_carry_3_true (T2 (T2 (powT2 a x))) [false])
          (rule_B_carry_exit (T2 (powT2 a x))))))).
Qed.

Definition StepNorm (s1 s2 : side) : Prop :=
  forall R : list bool, cfg_C s1 R -->+ cfg_B s2 R.

Definition StepCarry (s1 s2 : side) : Prop :=
  forall R : list bool, cfg_C s1 R -->+ cfg_B (T3 s2) (false :: R).

Inductive NormSteps : nat -> side -> side -> Prop :=
| NormSteps_zero (s : side) : NormSteps 0 s s
| NormSteps_succ {n : nat} {s1 s2 s3 : side} :
    StepNorm s1 s2 -> NormSteps n s2 s3 -> NormSteps (S n) s1 s3.

Definition CarryRun (n : nat) (s1 s2 : side) : Prop :=
  exists mid : side, NormSteps n s1 mid /\ StepCarry mid s2.

Lemma NormSteps_trans {m n : nat} {s1 s2 s3 : side}
    (H1 : NormSteps m s1 s2) (H2 : NormSteps n s2 s3) : NormSteps (m + n) s1 s3.
Proof.
  induction H1; simpl; [exact H2 | eapply NormSteps_succ; eauto].
Qed.

Lemma CarryRun_prepend {m n : nat} {s1 s2 s3 : side}
    (H1 : NormSteps m s1 s2) (H2 : CarryRun n s2 s3) : CarryRun (m + n) s1 s3.
Proof.
  destruct H2 as [mid [Hm Hc]].
  exists mid; split; [exact (NormSteps_trans H1 Hm) | exact Hc].
Qed.

Lemma stepNorm_3_22 (b : nat) (s : side) :
  StepNorm (T3 (powT2 (b + 2) s)) (T3 (T12 (powT2 b s))).
Proof.
  replace (b + 2) with (S (S b)) by lia; simpl.
  intro R; exact (rule_C_3_22 (powT2 b s) R).
Qed.

Lemma stepNorm_3_12 (s : side) : StepNorm (T3 (T12 s)) (T322 s).
Proof. intro R; exact (rule_C_3_12 s R). Qed.

Lemma stepNorm_322 (s : side) : StepNorm (T322 s) (T6 s).
Proof. intro R; exact (rule_C_322 s R). Qed.

Lemma stepNorm_T6 {s1 s2 : side} (b : nat) (H : StepNorm s1 s2) :
  StepNorm (T6 (powT2 b s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  intro R.
  exact (ptrans (c_pop_T6 b s1 R)
    (ptrans (H (powTrue (b + 1) (false :: false :: R))) (b_norm_block (b + 1) s2 R))).
Qed.

Lemma stepCarry_T6 {s1 s2 : side} (b : nat) (H : StepCarry s1 s2) :
  StepCarry (T6 (powT2 b s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  intro R.
  exact (ptrans (c_pop_T6 b s1 R)
    (ptrans (H (powTrue (b + 1) (false :: false :: R))) (b_carry_block (b + 1) s2 R))).
Qed.

Lemma normSteps_cycle_T3_12 {s1 s2 : side} (b : nat) (H : StepNorm s1 s2) :
  NormSteps 3 (T3 (T12 (powT2 b s1))) (T3 (powT2 (b + 1) s2)).
Proof.
  exact (NormSteps_succ (stepNorm_3_12 _)
    (NormSteps_succ (stepNorm_322 _)
      (NormSteps_succ (stepNorm_T6 b H) (NormSteps_zero _)))).
Qed.

Lemma normSteps_cycle_T3 {s1 s2 : side} (b : nat) (H : StepNorm s1 s2) :
  NormSteps 4 (T3 (powT2 (b + 2) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  exact (NormSteps_succ (stepNorm_3_22 b s1) (normSteps_cycle_T3_12 b H)).
Qed.

Lemma carryRun_cycle_T3_12 {s1 s2 : side} (b : nat) (H : StepCarry s1 s2) :
  CarryRun 2 (T3 (T12 (powT2 b s1))) (T3 (powT2 (b + 1) s2)).
Proof.
  exists (T6 (powT2 b s1)).
  split.
  - exact (NormSteps_succ (stepNorm_3_12 _) (NormSteps_succ (stepNorm_322 _) (NormSteps_zero _))).
  - exact (stepCarry_T6 b H).
Qed.

Lemma carryRun_cycle_T3 {s1 s2 : side} (b : nat) (H : StepCarry s1 s2) :
  CarryRun 3 (T3 (powT2 (b + 2) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  destruct (carryRun_cycle_T3_12 b H) as [mid [Hm Hc]].
  exists mid; split; [exact (NormSteps_succ (stepNorm_3_22 b s1) Hm) | exact Hc].
Qed.

Lemma lift_NormSteps {n : nat} {s1 s2 : side} (H : NormSteps n s1 s2) :
  forall b : nat,
    NormSteps (4 * n) (T3 (powT2 (b + n + 1) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  induction H as [s | m s1 s2 s3 Hstep Hrest IH]; intro b.
  - replace (4 * 0) with 0 by lia.
    replace (b + 0 + 1) with (b + 1) by lia.
    apply NormSteps_zero.
  - assert (H1 : NormSteps 4 (T3 (powT2 (b + S m + 1) s1)) (T3 (powT2 (b + m + 1) s2))).
    { replace (b + S m + 1) with ((b + m) + 2) by lia.
      replace (b + m + 1) with ((b + m) + 1) by lia.
      exact (normSteps_cycle_T3 (b + m) Hstep). }
    pose proof (NormSteps_trans H1 (IH b)) as H2.
    replace (4 + 4 * m) with (4 * S m) in H2 by lia.
    exact H2.
Qed.

Lemma lift_NormSteps_T3_12 {n : nat} {s1 s2 s3 : side}
    (H1 : StepNorm s1 s2) (H2 : NormSteps n s2 s3) (b : nat) :
  NormSteps (4 * n + 3) (T3 (T12 (powT2 (b + n) s1))) (T3 (powT2 (b + 1) s3)).
Proof.
  pose proof (normSteps_cycle_T3_12 (b + n) H1) as Ha.
  replace ((b + n) + 1) with (b + n + 1) in Ha by lia.
  pose proof (lift_NormSteps H2 b) as Hb.
  pose proof (NormSteps_trans Ha Hb) as Hc.
  replace (3 + 4 * n) with (4 * n + 3) in Hc by lia.
  exact Hc.
Qed.

Lemma lift_CarryRun {n : nat} {s1 s2 : side} (H : CarryRun n s1 s2) (b : nat) :
  CarryRun (4 * n + 3) (T3 (powT2 (b + n + 2) s1)) (T3 (powT2 (b + 1) s2)).
Proof.
  destruct H as [mid [Hm Hc]].
  assert (H1 : NormSteps (4 * n) (T3 (powT2 (b + n + 2) s1)) (T3 (powT2 (b + 2) mid))).
  { replace (b + n + 2) with ((b + 1) + n + 1) by lia.
    replace (b + 2) with ((b + 1) + 1) by lia.
    exact (lift_NormSteps Hm (b + 1)). }
  exact (CarryRun_prepend H1 (carryRun_cycle_T3 b Hc)).
Qed.

Lemma lift_CarryRun_T3_12 {n : nat} {s1 s2 : side} (H : CarryRun n s1 s2) (b : nat) :
  CarryRun (4 * n + 2) (T3 (T12 (powT2 (b + n) s1))) (T3 (powT2 (b + 1) s2)).
Proof.
  destruct H as [mid [Hm Hc]].
  inversion Hm as [s Heq1 Heq2 Heq3 | m s_a s_next s_b Hstep Hrest Heq1 Heq2 Heq3]; subst.
  - replace (4 * 0 + 2) with 2 by lia.
    replace (b + 0) with b by lia.
    exact (carryRun_cycle_T3_12 b Hc).
  - assert (H1 : NormSteps 3 (T3 (T12 (powT2 (b + S m) s1))) (T3 (powT2 (b + m + 2) s_next))).
    { replace (b + S m) with ((b + m) + 1) by lia.
      replace (b + m + 2) with (((b + m) + 1) + 1) by lia.
      exact (normSteps_cycle_T3_12 ((b + m) + 1) Hstep). }
    assert (Hcr : CarryRun m s_next s2) by (exists mid; split; assumption).
    pose proof (lift_CarryRun Hcr b) as H2.
    pose proof (CarryRun_prepend H1 H2) as H3.
    replace (3 + (4 * m + 3)) with (4 * S m + 2) in H3 by lia.
    exact H3.
Qed.

Lemma run_StepNorm {s1 s2 : side} (H : StepNorm s1 s2) (a : nat) :
  cfg_C (powT2 a s1) [true; true; true; false] -->+
    cfg_C (powT2 (a + 1) s2) [true; true; true; false].
Proof.
  exact (ep_trans (c_pop_T2 a s1 [true; true; true; false])
    (ptrans (H (powTrue a [true; true; true; false])) (b_norm_end a s2))).
Qed.

Lemma run_NormSteps {n : nat} {s1 s2 : side} (H : NormSteps n s1 s2) :
  forall a : nat,
    cfg_C (powT2 a s1) [true; true; true; false] -->*
      cfg_C (powT2 (a + n) s2) [true; true; true; false].
Proof.
  induction H as [s | m s1 s2 s3 Hstep Hrest IH]; intro a.
  - replace (a + 0) with a by lia.
    apply evstep_refl.
  - pose proof (pev (run_StepNorm Hstep a)) as H1.
    pose proof (IH (a + 1)) as H2.
    replace (a + 1 + m) with (a + S m) in H2 by lia.
    exact (etrans H1 H2).
Qed.

Lemma run_StepCarry {s1 s2 : side} (H : StepCarry s1 s2) (a : nat) :
  cfg_C (powT2 a s1) [true; true; true; false] -->+
    cfg_C (T3 (T12 (powT2 (a + 1) s2))) [true; true; true; false].
Proof.
  exact (ep_trans (c_pop_T2 a s1 [true; true; true; false])
    (ptrans (H (powTrue a [true; true; true; false])) (b_carry_end a s2))).
Qed.

Lemma run_CarryRun {n : nat} {s1 s2 : side} (H : CarryRun n s1 s2) (a : nat) :
  cfg_C (powT2 a s1) [true; true; true; false] -->+
    cfg_C (T3 (T12 (powT2 (a + n + 1) s2))) [true; true; true; false].
Proof.
  destruct H as [mid [Hm Hc]].
  exact (ep_trans (run_NormSteps Hm a) (run_StepCarry Hc (a + n))).
Qed.

Fixpoint N (k : nat) : nat :=
  match k with
  | O => 0
  | S k' => 4 * N k' + 3
  end.

Fixpoint ChainA (k : nat) : side :=
  match k with
  | O => T3 (powT2 2 (T12 0inf%sym))
  | S k' => T3 (powT2 (2 * N (S k') + 3) (ChainA k'))
  end.

Fixpoint ChainB (k : nat) : side :=
  match k with
  | O => T3 0inf%sym
  | S k' => T3 (powT2 (N (S k') + 2) (ChainB k'))
  end.

Fixpoint ChainC (k : nat) : side :=
  match k with
  | O => T3 (powT2 4 (T4 0inf%sym))
  | S k' => T3 (powT2 (3 * N (S k') + 4) (ChainC k'))
  end.

Definition TopA (k : nat) : side := T3 (T12 (powT2 (2 * N (S k) + 1) (ChainA k))).

Definition TopB (k : nat) : side := T3 (T12 (powT2 (N (S (S k))) (ChainB (S k)))).

Definition State (k : nat) : Q * tape :=
  cfg_C (powT2 (N (S k)) (ChainC k)) [true; true; true; false].

Lemma carryRun_base12 : CarryRun 2 (T3 (T12 (T12 0inf%sym))) (T3 0inf%sym).
Proof.
  exists (T6 (T12 0inf%sym)).
  split.
  - exact (NormSteps_succ (stepNorm_3_12 _) (NormSteps_succ (stepNorm_322 _) (NormSteps_zero _))).
  - exact (fun R => rule_C_6_12 R).
Qed.

Lemma normSteps_base3 : NormSteps 3 (T3 (T12 (powT2 3 (T3 0inf%sym)))) (ChainC 0).
Proof.
  exact (NormSteps_succ (stepNorm_3_12 _)
    (NormSteps_succ (stepNorm_322 _)
      (NormSteps_succ (fun R => rule_C_6_3 R) (NormSteps_zero _)))).
Qed.

Lemma carryRun_base4 : CarryRun 3 (ChainC 0) (ChainA 0).
Proof.
  exists (T6 (powT2 2 (T4 0inf%sym))).
  split.
  - exact (NormSteps_succ (stepNorm_3_22 2 (T4 0inf%sym))
      (NormSteps_succ (stepNorm_3_12 _)
        (NormSteps_succ (stepNorm_322 _) (NormSteps_zero _)))).
  - exact (fun R => rule_C_6_4 R).
Qed.

Lemma phase1_chain (k : nat) : CarryRun (N (S k)) (ChainA k) (ChainB k).
Proof.
  induction k as [|k IH].
  - destruct carryRun_base12 as [mid [Hm Hc]].
    exists mid; split; [| exact Hc].
    exact (NormSteps_succ (stepNorm_3_22 0 (T12 0inf%sym)) Hm).
  - pose proof (lift_CarryRun IH (N (S k) + 1)) as H.
    change (4 * N (S k) + 3) with (N (S (S k))) in H.
    replace ((N (S k) + 1) + N (S k) + 2) with (2 * N (S k) + 3) in H by lia.
    replace ((N (S k) + 1) + 1) with (N (S k) + 2) in H by lia.
    exact H.
Qed.

Lemma phase1_top (k : nat) : CarryRun (4 * N (S k) + 2) (TopA k) (ChainB (S k)).
Proof.
  unfold TopA.
  pose proof (lift_CarryRun_T3_12 (phase1_chain k) (N (S k) + 1)) as H.
  replace ((N (S k) + 1) + N (S k)) with (2 * N (S k) + 1) in H by lia.
  replace ((N (S k) + 1) + 1) with (N (S k) + 2) in H by lia.
  exact H.
Qed.

Lemma phase2_chain (k : nat) : NormSteps (N (S k) + 1) (ChainB (S k)) (ChainC k).
Proof.
  induction k as [|k IH].
  - change (N 1 + 1) with 4.
    change (ChainB 1) with (T3 (powT2 5 (T3 0inf%sym))).
    exact (NormSteps_succ (stepNorm_3_22 3 (T3 0inf%sym)) normSteps_base3).
  - pose proof (lift_NormSteps IH (3 * N (S k) + 3)) as H.
    assert (Heq1 : 4 * (N (S k) + 1) = N (S (S k)) + 1) by (simpl; lia).
    assert (Heq2 : (3 * N (S k) + 3) + (N (S k) + 1) + 1 = N (S (S k)) + 2) by (simpl; lia).
    assert (Heq3 : (3 * N (S k) + 3) + 1 = 3 * N (S k) + 4) by lia.
    rewrite Heq1, Heq2, Heq3 in H.
    exact H.
Qed.

Lemma phase2_top (k : nat) : NormSteps (N (S (S k))) (TopB k) (ChainC (S k)).
Proof.
  unfold TopB.
  pose proof (phase2_chain k) as Hchain.
  remember (N (S k)) as n_sk eqn:En.
  replace (n_sk + 1) with (S n_sk) in Hchain by lia.
  inversion Hchain as [| m s1 s_mid s3 Hstep Hrest Heq1 Heq2 Heq3]; subst.
  pose proof (lift_NormSteps_T3_12 Hstep Hrest (3 * N (S k) + 3)) as H.
  replace (4 * N (S k) + 3) with (N (S (S k))) in H by (simpl; lia).
  replace ((3 * N (S k) + 3) + N (S k)) with (N (S (S k))) in H by (simpl; lia).
  replace ((3 * N (S k) + 3) + 1) with (3 * N (S k) + 4) in H by lia.
  exact H.
Qed.

Lemma phase3_chain (k : nat) : CarryRun (N (S k)) (ChainC k) (ChainA k).
Proof.
  induction k as [|k IH].
  - exact carryRun_base4.
  - pose proof (lift_CarryRun IH (2 * N (S k) + 2)) as H.
    change (4 * N (S k) + 3) with (N (S (S k))) in H.
    replace ((2 * N (S k) + 2) + N (S k) + 2) with (3 * N (S k) + 4) in H by lia.
    replace ((2 * N (S k) + 2) + 1) with (2 * N (S k) + 3) in H by lia.
    exact H.
Qed.

Lemma state_step (k : nat) : State k -->+ State (S k).
Proof.
  unfold State.
  pose proof (run_CarryRun (phase3_chain k) (N (S k))) as H3.
  replace (N (S k) + N (S k) + 1) with (2 * N (S k) + 1) in H3 by lia.
  fold (TopA k) in H3.
  pose proof (run_CarryRun (phase1_top k) 0) as H1.
  assert (Heq1 : 0 + (4 * N (S k) + 2) + 1 = N (S (S k))) by (simpl; lia).
  rewrite Heq1 in H1.
  fold (TopB k) in H1.
  pose proof (run_NormSteps (phase2_top k) 0) as H2.
  replace (0 + N (S (S k))) with (N (S (S k))) in H2 by lia.
  exact (ptrans H3 (pe_trans H1 H2)).
Qed.

Lemma init_step5 : c0 -->+ cfg_C 0inf%sym [true].
Proof. unfold c0, tape0, cfg_C; simpl; start_progress. Qed.

Lemma start_to_step127 :
  cfg_C 0inf%sym [true] -->+ cfg_C (T4 0inf%sym) [true; true; true; false].
Proof.
  exact (ptrans (rule_C_default [true])
    (ptrans (rule_B_true 0inf%sym [true])
      (ptrans (rule_B_true (T2 0inf%sym) [])
        (ptrans (rule_B_nil_1 (1%sym >> 0%sym >> T2 0inf%sym))
          (ptrans (rule_C_41 (T12 0inf%sym) [])
            (ptrans (rule_C_110 (T12 0inf%sym) [false])
              (ptrans (rule_C_12_0 [true; false])
                (ptrans (rule_B_carry_1_0 [false])
                  (ptrans (rule_B_false_false (T3 0inf%sym) [])
                    (ptrans (rule_B_nil_1 (1%sym >> 1%sym >> 0%sym >> T3 0inf%sym))
                      (ptrans (rule_C_41 (T2 (T3 0inf%sym)) [])
                        (ptrans (rule_C_110 (T2 (T3 0inf%sym)) [false])
                          (ptrans (rule_C_110 (T3 0inf%sym) [true; false])
                            (ptrans (rule_C_3_0 [true; true; false])
                              (ptrans (rule_B_true (T4 0inf%sym) [true; false])
                                (ptrans (rule_B_true (T2 (T4 0inf%sym)) [false])
                                  (rule_B_norm_exit (T4 0inf%sym)))))))))))))))))).
Qed.

Lemma step127_to_start :
  cfg_C (T4 0inf%sym) [true; true; true; false] -->+
    cfg_C (T3 (T12 (T12 0inf%sym))) [true; true; true; false].
Proof.
  exact (ptrans (rule_C_41 0inf%sym [true; true; true; false])
    (ptrans (rule_C_110 0inf%sym [false; true; true; true; false])
      (ptrans (rule_C_default [true; false; true; true; true; false])
        (ptrans (rule_B_true 0inf%sym [true; false; true; true; true; false])
          (ptrans (rule_B_true (T2 0inf%sym) [false; true; true; true; false])
            (ptrans (rule_B_false_true (T2 (T2 0inf%sym)) [true; true; false])
              (ptrans (rule_C_3_22 0inf%sym [false; true; true; false])
                (ptrans (rule_B_carry_3_true (T12 0inf%sym) [true; false])
                  (ptrans (rule_B_carry_3_true (T2 (T12 0inf%sym)) [false])
                    (rule_B_carry_exit (T12 0inf%sym))))))))))).
Qed.

Lemma init_to_start :
  c0 -->+ cfg_C (T3 (T12 (T12 0inf%sym))) [true; true; true; false].
Proof.
  exact (ptrans init_step5 (ptrans start_to_step127 step127_to_start)).
Qed.

Lemma init_to_state0 : c0 -->+ State 0.
Proof.
  pose proof init_to_start as H0.
  pose proof (run_CarryRun carryRun_base12 0) as H1.
  pose proof (run_NormSteps normSteps_base3 0) as H2.
  exact (ptrans H0 (pe_trans H1 H2)).
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := State 0).
  - exact (pev init_to_state0).
  - eapply progress_nonhalt_simple with (C := State) (i0 := 0).
    intro k; exists (S k); exact (state_step k).
Qed.

End TM3.
Print Assumptions TM3.nonhalt.



Module TM4.
Import BusyCoq.Individual62.

Import Lia ZifyNat PeanoNat String List.

Import ListNotations.

Open Scope list.

Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope nat_scope.

Lemma rule_E_b (l r : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 0; 0; 1]%sym *> r) -->+
  (1%sym >> l) {{C}}> ([0; 0; 0; 1; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_E_aa (l r : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 1; 0; 1]%sym *> r) -->+
  (1%sym >> ([1; 1; 0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_E_ab (l r : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 1; 0; 0; 0; 1]%sym *> r) -->+
  (1%sym >> ([0; 1; 1; 1; 0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_C_a (l r : side) :
  (1%sym >> ([0; 1]%sym *> l)) {{C}}> ([0; 0]%sym *> r) -->+
  (1%sym >> l) {{C}}> ([0; 0; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_C_b (l r : side) :
  (1%sym >> ([1; 1; 0; 1]%sym *> l)) {{C}}> ([0; 0]%sym *> r) -->+
  (1%sym >> l) {{C}}> ([0; 0; 0; 0; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_C_nil (r : side) :
  (1%sym >> 0inf%sym) {{C}}> ([0; 0]%sym *> r) -->+
  (1%sym >> ([0; 1]%sym *> 0inf%sym)) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_E_end (l : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) -->+
  l {{E}}> ([1; 0; 0; 0; 1; 0; 0; 1]%sym *> 0inf%sym).
Proof. start_progress. Qed.

Lemma rule_EL_a (l r : side) :
  ([0; 1]%sym *> l) {{E}}> (1%sym >> r) -->+
  l {{E}}> ([1; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_EL_b (l r : side) :
  ([1; 1; 0; 1]%sym *> l) {{E}}> (1%sym >> r) -->+
  l {{E}}> ([1; 0; 0; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_EL_nil (r : side) :
  0inf%sym {{E}}> (1%sym >> r) -->+
  (1%sym >> 0inf%sym) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Notation T0 := ([0; 0; 0; 1]%sym).

Notation T1 := ([0; 1; 0; 1]%sym).

Notation T2 := ([0; 1; 0; 0; 0; 1]%sym).

Definition RoundC (r r' : side) : Prop :=
  forall l : side,
    (1%sym >> l) {{E}}> ([0; 1]%sym *> r) -->+
    (1%sym >> l) {{C}}> ([0; 0]%sym *> r').

Definition RoundA (r r_out : side) : Prop :=
  forall l : side,
    (1%sym >> ([0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r) -->+
    (1%sym >> l) {{C}}> ([0; 0]%sym *> r_out).

Lemma roundC_to_roundA {r r' : side} (H : RoundC r r') :
  RoundA r ([0; 1]%sym *> r').
Proof.
  intro l.
  eapply progress_trans; [exact (H ([0; 1]%sym *> l)) |].
  exact (rule_C_a l r').
Qed.

Lemma roundC_T0 (u : side) :
  RoundC (T0 *> u) (T1 *> u).
Proof.
  intro l. exact (rule_E_b l u).
Qed.

Lemma roundA_T0 (u : side) :
  RoundA (T0 *> u) (T1 *> ([0; 1]%sym *> u)).
Proof.
  exact (roundC_to_roundA (roundC_T0 u)).
Qed.

Lemma roundC_T1 {u u' : side} (H : RoundC u u') :
  RoundC (T1 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_aa l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_C_b l u').
Qed.

Lemma roundA_T1 {u u' : side} (H : RoundC u u') :
  RoundA (T1 *> u) (T2 *> u').
Proof.
  exact (roundC_to_roundA (roundC_T1 H)).
Qed.

Lemma roundC_T2 {u u' : side} (H : RoundA u u') :
  RoundC (T2 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_ab l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_C_b l u').
Qed.

Lemma roundA_T2 {u u' : side} (H : RoundA u u') :
  RoundA (T2 *> u) (T2 *> u').
Proof.
  exact (roundC_to_roundA (roundC_T2 H)).
Qed.

Definition RoundE (r r' : side) : Prop :=
  forall l : side,
    (1%sym >> l) {{E}}> ([0; 1]%sym *> r) -->+
    l {{E}}> (1%sym >> r').

Definition RoundEA (r r_out : side) : Prop :=
  forall l : side,
    (1%sym >> ([0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r) -->+
    l {{E}}> (1%sym >> r_out).

Lemma roundE_to_roundEA {r r' : side} (H : RoundE r r') :
  RoundEA r ([0; 1]%sym *> r').
Proof.
  intro l.
  eapply progress_trans; [exact (H ([0; 1]%sym *> l)) |].
  exact (rule_EL_a l r').
Qed.

Lemma roundE_end :
  RoundE ([0; 1; 0; 0; 1]%sym *> 0inf%sym) ([0; 0; 0; 1; 0; 0; 1]%sym *> 0inf%sym).
Proof.
  intro l. exact (rule_E_end l).
Qed.

Lemma roundE_T1 {u u' : side} (H : RoundE u u') :
  RoundE (T1 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_aa l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_EL_b l u').
Qed.

Lemma roundEA_T1 {u u' : side} (H : RoundE u u') :
  RoundEA (T1 *> u) (T2 *> u').
Proof.
  exact (roundE_to_roundEA (roundE_T1 H)).
Qed.

Lemma roundE_T2 {u u' : side} (H : RoundEA u u') :
  RoundE (T2 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_ab l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_EL_b l u').
Qed.

Lemma roundEA_T2 {u u' : side} (H : RoundEA u u') :
  RoundEA (T2 *> u) (T2 *> u').
Proof.
  exact (roundE_to_roundEA (roundE_T2 H)).
Qed.

Definition cfgE0 (r : side) : Q * tape :=
  (1%sym >> ([0; 1]%sym *> 0inf%sym)) {{E}}> ([0; 1]%sym *> r).

Lemma sweep_step {r r_out : side} (H : RoundA r r_out) :
  cfgE0 r -->+ cfgE0 r_out.
Proof.
  eapply progress_trans; [exact (H 0inf%sym) |].
  exact (rule_C_nil r_out).
Qed.

Lemma era_end_step {r r_era r_next : side}
    (H1 : RoundEA r r_era) (H2 : RoundC r_era r_next) :
  cfgE0 r -->+ cfgE0 r_next.
Proof.
  eapply progress_trans; [exact (H1 0inf%sym) |].
  eapply progress_trans; [exact (rule_EL_nil r_era) |].
  eapply progress_trans; [exact (H2 0inf%sym) |].
  exact (rule_C_nil r_next).
Qed.

Definition bot : side := [0; 0; 1]%sym *> 0inf%sym.

Definition bota : side := [0; 1; 0; 0; 1]%sym *> 0inf%sym.

Definition botc : side := [0; 1; 1]%sym *> 0inf%sym.

Lemma roundC_bot : RoundC bot botc.
Proof.
  intro l. unfold bot, botc. start_progress.
Qed.

Lemma roundC_botc : RoundC botc bot.
Proof.
  intro l. unfold bot, botc. start_progress.
Qed.

Inductive StepsA : nat -> side -> side -> Prop :=
  | StepsA_O (u : side) : StepsA 0 u u
  | StepsA_S (n : nat) (u v w : side) :
      RoundA u v -> StepsA n v w -> StepsA (S n) u w.

Lemma stepsA_trans {a b : nat} {u v w : side}
    (H1 : StepsA a u v) (H2 : StepsA b v w) :
  StepsA (a + b) u w.
Proof.
  induction H1 as [u | n u u1 v H _ IH].
  - exact H2.
  - cbn [Nat.add]. eapply StepsA_S; [exact H | exact (IH H2)].
Qed.

Lemma stepsA_T2 {n : nat} {u w : side} (H : StepsA n u w) :
  StepsA n (T2 *> u) (T2 *> w).
Proof.
  induction H as [u | n u v w H1 _ IH].
  - apply StepsA_O.
  - eapply StepsA_S; [exact (roundA_T2 H1) | exact IH].
Qed.

Definition B3 (r : side) : side :=
  T2 *> (T2 *> (T2 *> r)).

Fixpoint powB3 (m : nat) (r : side) : side :=
  match m with
  | 0 => r
  | S m' => B3 (powB3 m' r)
  end.

Lemma powB3_B3 (m : nat) (r : side) :
  powB3 m (B3 r) = B3 (powB3 m r).
Proof.
  induction m as [| m IH]; cbn [powB3].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma powB3_T2 (m : nat) (r : side) :
  powB3 m (T2 *> r) = T2 *> powB3 m r.
Proof.
  induction m as [| m IH]; cbn [powB3].
  - reflexivity.
  - unfold B3 at 1. rewrite IH. reflexivity.
Qed.

Lemma roundA_B3 {u u' : side} (H : RoundA u u') :
  RoundA (B3 u) (B3 u').
Proof.
  exact (roundA_T2 (roundA_T2 (roundA_T2 H))).
Qed.

Lemma roundA_powB3 (m : nat) {u u' : side} (H : RoundA u u') :
  RoundA (powB3 m u) (powB3 m u').
Proof.
  induction m as [| m IH]; cbn [powB3].
  - exact H.
  - exact (roundA_B3 IH).
Qed.

Lemma roundEA_B3 {u u' : side} (H : RoundEA u u') :
  RoundEA (B3 u) (B3 u').
Proof.
  exact (roundEA_T2 (roundEA_T2 (roundEA_T2 H))).
Qed.

Lemma roundEA_powB3 (m : nat) {u u' : side} (H : RoundEA u u') :
  RoundEA (powB3 m u) (powB3 m u').
Proof.
  induction m as [| m IH]; cbn [powB3].
  - exact H.
  - exact (roundEA_B3 IH).
Qed.

Lemma stepsA_B3 {n : nat} {u w : side} (H : StepsA n u w) :
  StepsA n (B3 u) (B3 w).
Proof.
  exact (stepsA_T2 (stepsA_T2 (stepsA_T2 H))).
Qed.

Lemma stepsA_powB3 (m : nat) {n : nat} {u w : side} (H : StepsA n u w) :
  StepsA n (powB3 m u) (powB3 m w).
Proof.
  induction m as [| m IH]; cbn [powB3].
  - exact H.
  - exact (stepsA_B3 IH).
Qed.

Lemma step6_022 {v v_C : side} (HC : RoundC v v_C) :
  StepsA 6 (T0 *> (T2 *> (T2 *> v))) (B3 (T0 *> (T2 *> v_C))).
Proof.
  eapply StepsA_S; [exact (roundA_T0 (T2 *> (T2 *> v))) |].
  eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> v)))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T0 (T1 *> (T2 *> v)))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 v))))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> v))))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 HC))))) |].
  apply StepsA_O.
Qed.

Lemma finish8_22 {v v_C : side} (HC : RoundC v v_C) :
  StepsA 8 (T0 *> (T2 *> (T2 *> v))) (B3 (T2 *> (T0 *> (T1 *> v_C)))).
Proof.
  assert (H2 : StepsA 2 (T0 *> (T2 *> v_C)) (T2 *> (T0 *> (T1 *> v_C)))).
  { eapply StepsA_S; [exact (roundA_T0 (T2 *> v_C)) |].
    eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T0 v_C))) |].
    apply StepsA_O. }
  exact (stepsA_trans (step6_022 HC) (stepsA_B3 H2)).
Qed.

Lemma cross_B3 {u u1 u2 u3 : side}
    (H1 : RoundA u u1) (H2 : RoundA u1 u2) (H3 : RoundA u2 u3) :
  StepsA 12 (T0 *> B3 u) (B3 (B3 (T0 *> u3))).
Proof.
  assert (H4 : StepsA 4 (T0 *> (T1 *> (T0 *> u1))) (T2 *> (T2 *> (T0 *> u3)))).
  { eapply StepsA_S; [exact (roundA_T0 (T1 *> (T0 *> u1))) |].
    eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T2 H2))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T0 (T0 *> u2))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T1 (roundC_T2 H3))) |].
    apply StepsA_O. }
  exact (stepsA_trans (finish8_22 (roundC_T2 H1)) (stepsA_B3 (stepsA_T2 H4))).
Qed.

Lemma cross_powB3 (m : nat) : forall {u w : side},
  StepsA (3 * m) u w ->
  StepsA (12 * m) (T0 *> powB3 m u) (powB3 (2 * m) (T0 *> w)).
Proof.
  induction m as [| m IH]; intros u w H.
  - cbn in H |- *.
    inverts H.
    apply StepsA_O.
  - replace (3 * S m) with (S (S (S (3 * m)))) in H by lia.
    inverts H as H1 H_1.
    inverts H_1 as H2 H_2.
    inverts H_2 as H3 Hrest.
    pose proof (cross_B3 (roundA_powB3 m H1) (roundA_powB3 m H2) (roundA_powB3 m H3)) as Hc.
    pose proof (stepsA_B3 (stepsA_B3 (IH _ _ Hrest))) as Hrec.
    pose proof (stepsA_trans Hc Hrec) as Htot.
    replace (12 * S m) with (12 + 12 * m) by lia.
    replace (2 * S m) with (S (S (2 * m))) by lia.
    cbn [powB3].
    exact Htot.
Qed.

Definition fEra (k : nat) (u : side) : side :=
  T2 *> powB3 (k + 1) (T1 *> (T1 *> u)).

Inductive StepEra (k : nat) (u w : side) : Prop :=
  | StepEra_mk (u_E w_0 w_last v_C : side) :
      RoundE u u_E ->
      RoundC ([0; 1]%sym *> u_E) w_0 ->
      StepsA (3 * k + 2) w_0 w_last ->
      RoundC w_last v_C ->
      w = [0; 1]%sym *> v_C ->
      StepEra k u w.

Lemma stepEra_next {k : nat} {u w : side} (H : StepEra k u w) :
  StepEra (2 * (2 * k + 2) + 2) (fEra k u) (fEra (2 * k + 2) w).
Proof.
  destruct H as [u_E w_0 w_last v_C HE HC0 HA HClast Hw].
  eapply StepEra_mk with
    (u_E := T0 *> powB3 (k + 1) (T2 *> (T0 *> u_E)))
    (w_0 := T0 *> powB3 (k + 1) (T2 *> (T1 *> ([0; 1]%sym *> u_E))))
    (w_last := T2 *> powB3 ((2 * k + 2) + 1) (T0 *> (T1 *> v_C)))
    (v_C := T0 *> powB3 ((2 * k + 2) + 1) (T1 *> (T1 *> w))).
  - exact (roundE_T2 (roundEA_powB3 (k + 1) (roundEA_T1 (roundE_T1 HE)))).
  - exact (roundC_T2 (roundA_powB3 (k + 1) (roundA_T2 (roundA_T0 u_E)))).
  - assert (H3 : StepsA (3 * (k + 1)) (T2 *> (T1 *> ([0; 1]%sym *> u_E))) (T2 *> (T2 *> w_last))).
    { replace (3 * (k + 1)) with (S (3 * k + 2)) by lia.
      apply stepsA_T2.
      eapply StepsA_S; [exact (roundA_T1 HC0) | exact (stepsA_T2 HA)]. }
    pose proof (cross_powB3 (k + 1) H3) as Hcross.
    pose proof (stepsA_powB3 (2 * (k + 1)) (finish8_22 HClast)) as Hfin.
    pose proof (stepsA_trans Hcross Hfin) as Htot.
    assert (Heq_t : powB3 (2 * (k + 1)) (B3 (T2 *> (T0 *> (T1 *> v_C)))) =
                    T2 *> powB3 ((2 * k + 2) + 1) (T0 *> (T1 *> v_C))).
    { rewrite powB3_B3.
      change (B3 (powB3 (2 * (k + 1)) (T2 *> (T0 *> (T1 *> v_C)))))
        with (powB3 (S (2 * (k + 1))) (T2 *> (T0 *> (T1 *> v_C)))).
      replace (S (2 * (k + 1))) with ((2 * k + 2) + 1) by lia.
      apply powB3_T2. }
    rewrite Heq_t in Htot.
    replace (12 * (k + 1) + 8) with (3 * (2 * (2 * k + 2) + 2) + 2) in Htot by lia.
    exact Htot.
  - rewrite Hw.
    exact (roundC_T2 (roundA_powB3 ((2 * k + 2) + 1) (roundA_T0 (T1 *> v_C)))).
  - reflexivity.
Qed.

Definition u_m2 : side :=
  T2 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))).

Definition u_m1 : side :=
  T2 *> (T2 *> (T2 *> (T2 *> (T1 *> (T2 *> (T1 *> (T2 *> (T2 *> (T1 *> bota))))))))).

Lemma stepEra_m2 : StepEra 2 u_m2 u_m1.
Proof.
  eapply StepEra_mk with
    (u_E := T0 *> (T2 *> (T0 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))
    (w_0 := T0 *> (T2 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))
    (w_last := T2 *> (T2 *> (T2 *> (T2 *> (T0 *> (T0 *> (T1 *> (T2 *> (T2 *> (T1 *> bota))))))))))
    (v_C := T0 *> (T2 *> (T2 *> (T2 *> (T1 *> (T2 *> (T1 *> (T2 *> (T2 *> (T1 *> bota)))))))))).
  - exact (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))).
  - exact (roundC_T2 (roundA_T2 (roundA_T0 (T2 *> (T2 *> (T2 *> (T0 *> bot))))))).
  - cbn [Nat.mul Nat.add].
    eapply StepsA_S; [exact (roundA_T0 (T2 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot)))))))) |].
    eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T0 (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T0 (T1 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T0 *> (T0 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T0 (T0 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T1 *> bota)))))))))) |].
    apply StepsA_O.
  - exact (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T2 *> (T2 *> (T1 *> bota)))))))))).
  - reflexivity.
Qed.

Lemma stepEra_m1 : StepEra 6 u_m1 (fEra 2 u_m2).
Proof.
  eapply StepEra_mk with
    (u_E := T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> (T2 *> (T0 *> (T2 *> (T2 *> (T0 *> bot)))))))))))
    (w_0 := T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))))))
    (w_last := T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> (T1 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))))
    (v_C := T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> (T1 *> (T2 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))).
  - exact (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))))))).
  - exact (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))))).
  - pose proof (cross_B3
      (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))
      (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))
      (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) as Hc12.
    pose proof (stepsA_B3 (stepsA_B3 (finish8_22 (roundC_T2 (roundA_T0 (T0 *> (T2 *> (T2 *> (T1 *> bota))))))))) as Hf8.
    exact (stepsA_trans Hc12 Hf8).
  - exact (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))).
  - reflexivity.
Qed.

Lemma stepsA_run {n : nat} {v w : side} (H2 : StepsA n v w) :
  forall {u : side}, cfgE0 u -->+ cfgE0 v -> cfgE0 u -->+ cfgE0 w.
Proof.
  induction H2 as [v | n v v1 w Ha _ IH]; intros u H1.
  - exact H1.
  - apply IH. eapply progress_trans; [exact H1 | exact (sweep_step Ha)].
Qed.

Lemma stepEra_run {k : nat} {u w : side} (H : StepEra k u w) :
  cfgE0 u -->+ cfgE0 w.
Proof.
  destruct H as [u_E w_0 w_last v_C HE HC0 HA HClast Hw].
  rewrite Hw.
  assert (H0 : cfgE0 u -->+ cfgE0 w_0) by exact (era_end_step (roundE_to_roundEA HE) HC0).
  assert (H1 : cfgE0 u -->+ cfgE0 w_last) by exact (stepsA_run HA H0).
  eapply progress_trans; [exact H1 | exact (sweep_step (roundC_to_roundA HClast))].
Qed.

Lemma init_to_botc : c0 -->* cfgE0 botc.
Proof.
  unfold cfgE0, botc.
  change ((1%sym >> ([0; 1]%sym *> 0inf%sym)) {{E}}> ([0; 1]%sym *> ([0; 1; 1]%sym *> 0inf%sym)))
    with ((0inf%sym <* [1; 0; 1]%sym) {{E}}> ([0; 1; 0; 1; 1]%sym *> 0inf%sym)).
  solve_init.
Qed.

Lemma botc_to_u0 : cfgE0 botc -->+ cfgE0 (fEra 2 u_m2).
Proof.
  eapply progress_trans; [exact (sweep_step (roundC_to_roundA roundC_botc)) |].
  eapply progress_trans; [exact (era_end_step (roundE_to_roundEA roundE_end) (roundC_T2 (roundC_to_roundA roundC_bot))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 ([0; 1]%sym *> botc))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 roundC_botc))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 bot))) |].
  eapply progress_trans; [exact (era_end_step (roundEA_T2 (roundEA_T1 roundE_end)) (roundC_T2 (roundA_T2 (roundA_T0 bot)))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 (T2 *> (T1 *> bota)))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T1 *> bota))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 (T1 *> (T1 *> bota))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T1 roundC_bot)))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T0 *> botc)))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T0 botc)))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> ([0; 1]%sym *> botc))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 roundC_botc))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> bot))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundC_to_roundA roundC_bot)))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 ([0; 1]%sym *> botc)))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 roundC_botc)))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot)))))))) |].
  eapply progress_trans; [exact (era_end_step (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end))))))) (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 (T1 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))) |].
  eapply progress_trans; [exact (era_end_step (roundEA_T2 (roundEA_T2 (roundEA_T1 (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))))))) (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 (T2 *> (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 (T1 *> (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T0 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T0 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T0 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T0 (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T1 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))))) |].
  exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))))).
Qed.

Definition Hub (s : nat * side * side) : Q * tape :=
  let '(k, u, w) := s in cfgE0 u.

Definition InvP (s : nat * side * side) : Prop :=
  let '(k, u, w) := s in StepEra k u w /\ StepEra (2 * k + 2) w (fEra k u).

Lemma start : c0 -->* Hub (14, fEra 2 u_m2, fEra 6 u_m1).
Proof.
  unfold Hub.
  eapply evstep_trans; [exact init_to_botc |].
  apply progress_evstep.
  exact botc_to_u0.
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := Hub (14, fEra 2 u_m2, fEra 6 u_m1)).
  - exact start.
  - eapply progress_nonhalt_cond with
      (C := Hub) (P := InvP) (i0 := (14, fEra 2 u_m2, fEra 6 u_m1)).
    + intros [[k u] w] [H1 H2].
      exists (2 * k + 2, w, fEra k u).
      split.
      * exact (stepEra_run H1).
      * split; [exact H2 | exact (stepEra_next H1)].
    + split; [exact (stepEra_next stepEra_m2) | exact (stepEra_next stepEra_m1)].
Qed.

End TM4.
Print Assumptions TM4.nonhalt.
