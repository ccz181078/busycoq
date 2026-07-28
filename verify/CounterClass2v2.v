From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import List.
Require Import PeanoNat.
Require Import String.
Require Import Wf_nat.
Import ListNotations.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC0LF_1RD0LC_1RE1RC_1RA1RF_0RD1LB").

Open Scope list.
Open Scope nat_scope.

Ltac flia := repeat (lia || f_equal).

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Fixpoint SkelE (n : nat) : side :=
  match n with
  | O => const S0 <* [S1; S1]
  | S n' =>
      SkelE n' <* [S0] <* [S1]^^(6 + 4 * n')
        <* [S0] <* [S1]^^(6 + 4 * n')
  end.

Definition SkelO (n : nat) : side :=
  SkelE n <* [S0] <* [S1]^^(6 + 4 * n).

Definition Pside (i : side) (r : nat) : side :=
  i <* [S1]^^r.

Definition Bside (i : side) (j b : nat) : side :=
  i <* [S1]^^(4 * j) <* [S0] <* [S1]^^b.

Definition Aside (i : side) (q b : nat) : side :=
  i <* [S0] <* [S1]^^(4 * q + 2) <* [S0] <* [S1]^^b.

Definition Pe (n r : nat) : side := Pside (SkelE n) r.
Definition Po (n r : nat) : side := Pside (SkelO n) r.
Definition Be (n j b : nat) : side := Bside (SkelE n) j b.
Definition Bo (n j b : nat) : side := Bside (SkelO n) j b.
Definition Ae (n q b : nat) : side := Aside (SkelE n) q b.
Definition Ao (n q b : nat) : side := Aside (SkelO n) q b.

Definition K0 : side := const S0.
Definition K1 : side := const S0 <* [S1].

Opaque SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Inductive Side : Type :=
| SK0 : Side
| SK1 : Side
| SPe : nat -> nat -> Side
| SPo : nat -> nat -> Side
| SBe : nat -> nat -> nat -> Side
| SBo : nat -> nat -> nat -> Side
| SAe : nat -> nat -> nat -> Side
| SAo : nat -> nat -> nat -> Side.

Definition to_side (h : Side) : side :=
  match h with
  | SK0 => K0
  | SK1 => K1
  | SPe n r => Pe n r
  | SPo n r => Po n r
  | SBe n j b => Be n j b
  | SBo n j b => Bo n j b
  | SAe n q b => Ae n q b
  | SAo n q b => Ao n q b
  end.

Fixpoint skelE_measure (n : nat) : nat :=
  match n with
  | O => 2
  | S n' => skelE_measure n' + (7 + 4 * n') + (7 + 4 * n')
  end.

Definition skelO_measure (n : nat) : nat :=
  skelE_measure n + (7 + 4 * n).

Definition side_measure (h : Side) : nat :=
  match h with
  | SK0 => 0
  | SK1 => 1
  | SPe n r => skelE_measure n + r
  | SPo n r => skelO_measure n + r
  | SBe n j b => skelE_measure n + 4 * j + 1 + b
  | SBo n j b => skelO_measure n + 4 * j + 1 + b
  | SAe n q b => skelE_measure n + 4 * q + 4 + b
  | SAo n q b => skelO_measure n + 4 * q + 4 + b
  end.

Definition class_rank (q : Q) (h : Side) : nat :=
  match q, h with
  | F, SBe _ _ _ => 3
  | F, SBo _ _ _ => 3
  | B, SBe _ _ _ => 2
  | B, SBo _ _ _ => 2
  | C, SBe _ _ _ => 1
  | C, SBo _ _ _ => 1
  | C, SAe _ _ _ => 1
  | C, SAo _ _ _ => 1
  | _, _ => 0
  end.

Definition measure (q : Q) (h : Side) : nat :=
  4 * side_measure h + class_rank q h.

Transparent SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Lemma side_repeat_one_succ l n :
  l <* [S1]^^(S n) = S1 >> (l <* [S1]^^n).
Proof.
  cbn [lpow].
  reflexivity.
Qed.

Lemma K1_step :
  K1 = S1 >> K0.
Proof.
  unfold K1, K0.
  reflexivity.
Qed.

Lemma Pe_succ_step n r :
  Pe n (S r) = S1 >> Pe n r.
Proof.
  unfold Pe, Pside.
  rewrite side_repeat_one_succ.
  reflexivity.
Qed.

Lemma Po_succ_step n r :
  Po n (S r) = S1 >> Po n r.
Proof.
  unfold Po, Pside.
  rewrite side_repeat_one_succ.
  reflexivity.
Qed.

Lemma Be_succ_step n j b :
  Be n j (S b) = S1 >> Be n j b.
Proof.
  unfold Be, Bside.
  rewrite side_repeat_one_succ.
  reflexivity.
Qed.

Lemma Bo_succ_step n j b :
  Bo n j (S b) = S1 >> Bo n j b.
Proof.
  unfold Bo, Bside.
  rewrite side_repeat_one_succ.
  reflexivity.
Qed.

Lemma Ae_succ_step n q b :
  Ae n q (S b) = S1 >> Ae n q b.
Proof.
  unfold Ae, Aside.
  rewrite side_repeat_one_succ.
  reflexivity.
Qed.

Lemma Ao_succ_step n q b :
  Ao n q (S b) = S1 >> Ao n q b.
Proof.
  unfold Ao, Aside.
  rewrite side_repeat_one_succ.
  reflexivity.
Qed.

Lemma Pe_zero_step :
  Pe 0 0 = S1 >> K1.
Proof.
  unfold Pe, Pside, K1, SkelE.
  reflexivity.
Qed.

Lemma Pe_succ_zero_step n :
  Pe (S n) 0 = S1 >> Bo n 0 (5 + 4 * n).
Proof.
  unfold Pe, Pside.
  cbn [SkelE].
  unfold Bo, Bside, SkelO.
  replace (6 + 4 * n) with (S (5 + 4 * n)) by lia.
  cbn [lpow Nat.mul].
  reflexivity.
Qed.

Lemma Po_zero_step n :
  Po n 0 = S1 >> Be n 0 (5 + 4 * n).
Proof.
  unfold Po, Be, Pside, Bside, SkelO.
  replace (6 + 4 * n) with (S (5 + 4 * n)) by lia.
  cbn [lpow Nat.mul].
  reflexivity.
Qed.

Lemma Be_zero_step n j :
  Be n j 0 = S0 >> Pe n (4 * j).
Proof.
  unfold Be, Pe, Bside, Pside.
  reflexivity.
Qed.

Lemma Bo_zero_step n j :
  Bo n j 0 = S0 >> Po n (4 * j).
Proof.
  unfold Bo, Po, Bside, Pside.
  reflexivity.
Qed.

Lemma Ae_zero_step n q :
  Ae n q 0 = S0 >> Be n 0 (4 * q + 2).
Proof.
  unfold Ae, Be, Aside, Bside.
  reflexivity.
Qed.

Lemma Ao_zero_step n q :
  Ao n q 0 = S0 >> Bo n 0 (4 * q + 2).
Proof.
  unfold Ao, Bo, Aside, Bside.
  reflexivity.
Qed.

Opaque SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Lemma to_side_SK1_step :
  to_side SK1 = S1 >> to_side SK0.
Proof.
  cbn [to_side].
  apply K1_step.
Qed.

Lemma to_side_SPe_succ_step n r :
  to_side (SPe n (S r)) = S1 >> to_side (SPe n r).
Proof.
  cbn [to_side].
  apply Pe_succ_step.
Qed.

Lemma to_side_SPo_succ_step n r :
  to_side (SPo n (S r)) = S1 >> to_side (SPo n r).
Proof.
  cbn [to_side].
  apply Po_succ_step.
Qed.

Lemma to_side_SBe_succ_step n j b :
  to_side (SBe n j (S b)) = S1 >> to_side (SBe n j b).
Proof.
  cbn [to_side].
  apply Be_succ_step.
Qed.

Lemma to_side_SBo_succ_step n j b :
  to_side (SBo n j (S b)) = S1 >> to_side (SBo n j b).
Proof.
  cbn [to_side].
  apply Bo_succ_step.
Qed.

Lemma to_side_SAe_succ_step n q b :
  to_side (SAe n q (S b)) = S1 >> to_side (SAe n q b).
Proof.
  cbn [to_side].
  apply Ae_succ_step.
Qed.

Lemma to_side_SAo_succ_step n q b :
  to_side (SAo n q (S b)) = S1 >> to_side (SAo n q b).
Proof.
  cbn [to_side].
  apply Ao_succ_step.
Qed.

Lemma to_side_SPe_zero_step :
  to_side (SPe 0 0) = S1 >> to_side SK1.
Proof.
  cbn [to_side].
  apply Pe_zero_step.
Qed.

Lemma to_side_SPe_succ_zero_step n :
  to_side (SPe (S n) 0) = S1 >> to_side (SBo n 0 (5 + 4 * n)).
Proof.
  cbn [to_side].
  apply Pe_succ_zero_step.
Qed.

Lemma to_side_SPo_zero_step n :
  to_side (SPo n 0) = S1 >> to_side (SBe n 0 (5 + 4 * n)).
Proof.
  cbn [to_side].
  apply Po_zero_step.
Qed.

Lemma to_side_SBe_zero_step n j :
  to_side (SBe n j 0) = S0 >> to_side (SPe n (4 * j)).
Proof.
  cbn [to_side].
  apply Be_zero_step.
Qed.

Lemma to_side_SBo_zero_step n j :
  to_side (SBo n j 0) = S0 >> to_side (SPo n (4 * j)).
Proof.
  cbn [to_side].
  apply Bo_zero_step.
Qed.

Lemma to_side_SAe_zero_step n q :
  to_side (SAe n q 0) = S0 >> to_side (SBe n 0 (4 * q + 2)).
Proof.
  cbn [to_side].
  apply Ae_zero_step.
Qed.

Lemma to_side_SAo_zero_step n q :
  to_side (SAo n q 0) = S0 >> to_side (SBo n 0 (4 * q + 2)).
Proof.
  cbn [to_side].
  apply Ao_zero_step.
Qed.

Ltac expand_one_to_side_in_goal :=
  first
    [ rewrite to_side_SK1_step
    | rewrite to_side_SPe_succ_step
    | rewrite to_side_SPo_succ_step
    | rewrite to_side_SBe_succ_step
    | rewrite to_side_SBo_succ_step
    | rewrite to_side_SAe_succ_step
    | rewrite to_side_SAo_succ_step
    | rewrite to_side_SPe_zero_step
    | rewrite to_side_SPe_succ_zero_step
    | rewrite to_side_SPo_zero_step
    | rewrite to_side_SBe_zero_step
    | rewrite to_side_SBo_zero_step
    | rewrite to_side_SAe_zero_step
    | rewrite to_side_SAo_zero_step ].

Ltac expand_sideRLs_to_side_once :=
  lazymatch goal with
  | |- sideRLs _ _ (to_side _) (to_side _) =>
      expand_one_to_side_in_goal; expand_one_to_side_in_goal
  | |- sideRLs _ _ (to_side _) _ =>
      expand_one_to_side_in_goal
  | |- sideRLs _ _ _ (to_side _) =>
      expand_one_to_side_in_goal
  end.

Lemma sideRLs_change_ends tm h a a' b b' :
  a = a' ->
  b = b' ->
  sideRLs tm h a' b' ->
  sideRLs tm h a b.
Proof.
  intros -> -> H.
  exact H.
Qed.

Ltac unfold_to_side_one_step :=
  expand_one_to_side_in_goal.

Ltac normalize_sideRLs_ends :=
  lazymatch goal with
  | |- sideRLs ?tm ?h ?a ?b =>
      eapply (sideRLs_change_ends tm h a _ b _);
      [ unfold_to_side_one_step; reflexivity
      | unfold_to_side_one_step; reflexivity
      | ]
  end.

Ltac split_sideRLs_concat :=
  repeat rewrite Str_cons_def;
  eapply segRLs_sideRLs_concat;
  [ shelve | ].

Ltac normalize_split_sideRLs_concat :=
  normalize_sideRLs_ends;
  split_sideRLs_concat.

Opaque SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Transparent SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Lemma sideRLs_D_Bo0_1 :
  sideRLs (flip tm) [((F, []), (A, []))] (to_side (SBo 0 0 1)) (to_side (SPo 0 3)).
Proof.
  cbn [to_side].
  unfold Bo, Po, Bside, Pside, SkelO, SkelE.
  cbn.
  esc.
Qed.

Lemma sideRLs_D_Bo0_5 :
  sideRLs (flip tm) [((F, []), (F, []))] (to_side (SBo 0 0 5)) (to_side (SPe 1 0)).
Proof.
  cbn [to_side].
  unfold Bo, Pe, Bside, Pside, SkelO, SkelE.
  cbn.
  esc.
Qed.

Lemma sideRLs_E_keep_1 r :
  sideRLs (flip tm) [((D, []), (C, []))] (S1 >> r) (S1 >> r).
Proof.
  esx.
Qed.

Lemma sideRLs_F_0_to_1 r :
  sideRLs (flip tm) [((C, []), (D, []))] (S0 >> r) (S1 >> r).
Proof.
  esx.
Qed.

Opaque SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Inductive ClosedCall : Q -> Side -> Q -> Side -> Prop :=
| CC_B_Ao_zero n q :
    q <= n ->
    ClosedCall B (SAo n q 0) C (SAe n q (7 + 4 * n))
| CC_B_Ae_succ_zero n q :
    q <= n ->
    ClosedCall B (SAe (n + 1) q 0) C (SAo n q (7 + 4 * n))
| CC_B_Ae_succ_diag_zero n :
    ClosedCall B (SAe (n + 1) (n + 1) 0) C (SBe (n + 1) 0 (7 + 4 * n))
| CC_B_Ae_tail2 n q :
    q <= n ->
    ClosedCall B (SAe n q 2) E (SBe n 0 (4 * q + 5))
| CC_B_Ao_tail2 n q :
    q <= n ->
    ClosedCall B (SAo n q 2) E (SBo n 0 (4 * q + 5))
| CC_B_Ae_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 3 ->
    ClosedCall B (SAe n q (2 * k + 4)) D (SAe n (q + 1) (2 * k))
| CC_B_Ao_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 5 ->
    ClosedCall B (SAo n q (2 * k + 4)) D (SAo n (q + 1) (2 * k))
| CC_B_Ae_long_diag_low n k :
    k <= 2 * n + 2 ->
    ClosedCall B (SAe n n (2 * k + 4)) D (SBo n 0 (2 * k))
| CC_B_Ae_long_diag_high n s :
    s <= 2 * n ->
    ClosedCall B (SAe n n (2 * (2 * n + 3 + s) + 4)) D (SPe (n + 1) (2 * s))
| CC_B_Ao_long_diag_low n k :
    k <= 2 * n + 4 ->
    ClosedCall B (SAo n n (2 * k + 4)) D (SBe (n + 1) 0 (2 * k))
| CC_B_Ao_long_diag_high n s :
    s <= 2 * n ->
    ClosedCall B (SAo n n (2 * (2 * n + 5 + s) + 4)) D (SPo (n + 1) (2 * s))

| CC_B_Be0_0_succ n :
    ClosedCall B (SBe (n + 1) 0 0) C (SPe (n + 1) 1)
| CC_B_Bo_succ0_0 n :
    ClosedCall B (SBo (n + 1) 0 0) C (SBe (n + 1) 1 (7 + 4 * n))
| CC_B_Be0_1 n :
    ClosedCall B (SBe n 0 1) E (SBe n 0 1)
| CC_B_Bo0_1 n :
    ClosedCall B (SBo n 0 1) E (SBo n 0 1)
| CC_B_Be0_2_succ n :
    ClosedCall B (SBe (n + 1) 0 2) E (SPe (n + 1) 3)
| CC_B_Bo0_2 n :
    ClosedCall B (SBo (n + 1) 0 2) E (SPo (n + 1) 3)
| CC_B_Be0_odd_tail n k :
    k <= 2 * n + 1 ->
    ClosedCall B (SBe n 0 (2 * k + 3)) D (SAe n 0 (2 * k))
| CC_B_Bo0_odd_tail n k :
    k <= 2 * n + 1 ->
    ClosedCall B (SBo n 0 (2 * k + 3)) D (SAo n 0 (2 * k))
| CC_B_Be0_even_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall B (SBe (n + 1) 0 (2 * k + 4)) D (SBe (n + 1) 1 (2 * k))
| CC_B_Bo0_even_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall B (SBo (n + 1) 0 (2 * k + 4)) D (SBo (n + 1) 1 (2 * k))

| CC_B_Be_succ_pos_zero n j :
    1 <= j ->
    j < n + 1 ->
    ClosedCall B (SBe (n + 1) j 0) C (SBo n j (7 + 4 * n))
| CC_B_Be_diag_zero n :
    ClosedCall B (SBe n n 0) C (SBe n 0 (4 * n + 1))
| CC_B_Be_pos_tail2 n j :
    1 <= j ->
    j < n ->
    ClosedCall B (SBe n j 2) E (SPe n (4 * j + 3))
| CC_B_Be_diag_tail2 n :
    ClosedCall B (SBe n n 2) C (SBe n 0 (4 * n + 3))
| CC_B_Be_diag_tail4 n :
    ClosedCall B (SBe n n 4) E (SBe n 0 (4 * n + 5))
| CC_B_Be_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n + 1 ->
    ClosedCall B (SBe n j (2 * k + 4)) D (SBe n (j + 1) (2 * k))
| CC_B_Be_diag_long_low n k :
    k <= 2 * n ->
    ClosedCall B (SBe n n (2 * k + 6)) D (SBo n 0 (2 * k))
| CC_B_Bo_succ_pos_zero n j :
    1 <= j ->
    j < n + 1 ->
    ClosedCall B (SBo (n + 1) j 0) C (SBe (n + 1) (j + 1) (7 + 4 * n))
| CC_B_Bo_diag_zero n :
    ClosedCall B (SBo n n 0) C (SBo n 0 (4 * n + 1))
| CC_B_Bo_pos_tail2 n j :
    1 <= j ->
    j < n ->
    ClosedCall B (SBo n j 2) E (SPo n (4 * j + 3))
| CC_B_Bo_diag_tail2 n :
    ClosedCall B (SBo n n 2) C (SAe n n (7 + 4 * n))
| CC_B_Bo_diag_tail4 n :
    ClosedCall B (SBo n n 4) E (SBo n 0 (4 * n + 5))
| CC_B_Bo_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n + 3 ->
    ClosedCall B (SBo n j (2 * k + 4)) D (SBo n (j + 1) (2 * k))
| CC_B_Bo_diag_long_low n k :
    k <= 2 * n + 2 ->
    ClosedCall B (SBo n n (2 * k + 6)) D (SBe (n + 1) 0 (2 * k))

| CC_B_Pe_succ_even n k :
    k <= 2 ->
    ClosedCall B (SPe (n + 2) (2 * k)) D (SBo (n + 1) 1 (6 + 4 * n + 2 * k))
| CC_B_Pe_odd n k :
    k <= 2 * n + 3 ->
    ClosedCall B (SPe (n + 1) (2 * k + 1)) D (SAo n 0 (4 + 4 * n + 2 * k))
| CC_B_Po_even n k :
    k = 0 ->
    ClosedCall B (SPo (n + 1) (2 * k)) D (SBe (n + 1) 1 (6 + 4 * n + 2 * k))
| CC_B_Po_odd n k :
    k <= 2 * n + 1 ->
    ClosedCall B (SPo n (2 * k + 1)) D (SAe n 0 (4 + 4 * n + 2 * k))

| CC_F_Ae_1 n q :
    q <= n ->
    ClosedCall F (SAe n q 1) D (SBe n 0 (4 * q + 4))
| CC_F_Ao_1 n q :
    q <= n ->
    ClosedCall F (SAo n q 1) D (SBo n 0 (4 * q + 4))
| CC_F_Ae_3_nonmax n q :
    q < n ->
    ClosedCall F (SAe n q 3) F (SBe n 0 (4 * q + 6))
| CC_F_Ae_3_diag n :
    ClosedCall F (SAe n n 3) F (SPo n 0)
| CC_F_Ao_3_nonmax n q :
    q < n ->
    ClosedCall F (SAo n q 3) F (SBo n 0 (4 * q + 6))
| CC_F_Ao_3_diag n :
    ClosedCall F (SAo n n 3) F (SPe (n + 1) 0)
| CC_F_Ae_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 2 ->
    ClosedCall F (SAe n q (2 * k + 5)) C (SAe n (q + 1) (2 * k + 1))
| CC_F_Ao_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 4 ->
    ClosedCall F (SAo n q (2 * k + 5)) C (SAo n (q + 1) (2 * k + 1))
| CC_F_Ae_long_diag_low n k :
    k <= 2 * n + 2 ->
    ClosedCall F (SAe n n (2 * k + 5)) C (SBo n 0 (2 * k + 1))
| CC_F_Ae_long_diag_high n s :
    s < 2 * n ->
    ClosedCall F (SAe n n (2 * (2 * n + 3 + s) + 5)) C (SPe (n + 1) (2 * s + 1))
| CC_F_Ao_long_diag_low n k :
    k <= 2 * n + 4 ->
    ClosedCall F (SAo n n (2 * k + 5)) C (SBe (n + 1) 0 (2 * k + 1))
| CC_F_Ao_long_diag_high n s :
    s < 2 * n ->
    ClosedCall F (SAo n n (2 * (2 * n + 5 + s) + 5)) C (SPo (n + 1) (2 * s + 1))

| CC_F_Be0_0 n :
    ClosedCall F (SBe n 0 0) D (SBe n 0 0)
| CC_F_Bo0_0 n :
    ClosedCall F (SBo n 0 0) D (SBo n 0 0)
| CC_F_Be0_1 n :
    ClosedCall F (SBe (n + 1) 0 1) D (SPe (n + 1) 2)
| CC_F_Bo0_1 n :
    ClosedCall F (SBo (n + 1) 0 1) D (SPo (n + 1) 2)
| CC_F_Be0_2 n :
    ClosedCall F (SBe n 0 2) F (SBe n 0 2)
| CC_F_Bo0_2 n :
    ClosedCall F (SBo n 0 2) F (SBo n 0 2)
| CC_F_Be0_3 n :
    ClosedCall F (SBe (n + 1) 0 3) F (SPe (n + 1) 4)
| CC_F_Bo0_3 n :
    ClosedCall F (SBo (n + 1) 0 3) F (SPo (n + 1) 4)
| CC_F_Be0_even_tail n k :
    k <= 2 * n ->
    ClosedCall F (SBe n 0 (2 * k + 4)) C (SAe n 0 (2 * k + 1))
| CC_F_Bo0_even_tail n k :
    k <= 2 * n ->
    ClosedCall F (SBo n 0 (2 * k + 4)) C (SAo n 0 (2 * k + 1))
| CC_F_Be0_odd_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall F (SBe (n + 1) 0 (2 * k + 5)) C (SBe (n + 1) 1 (2 * k + 1))
| CC_F_Bo0_odd_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall F (SBo (n + 1) 0 (2 * k + 5)) C (SBo (n + 1) 1 (2 * k + 1))

| CC_F_Be_pos_1 n j :
    1 <= j ->
    j < n ->
    ClosedCall F (SBe n j 1) D (SPe n (4 * j + 2))
| CC_F_Be_succ_diag_1 n :
    ClosedCall F (SBe (n + 1) (n + 1) 1) A (SAo n n (10 + 4 * n))
| CC_F_Be_pos_3 n j :
    1 <= j ->
    j < n ->
    ClosedCall F (SBe n j 3) F (SPe n (4 * j + 4))
| CC_F_Be_diag_3 n :
    ClosedCall F (SBe n n 3) D (SBe n 0 (4 * n + 4))
| CC_F_Be_diag_5 n :
    ClosedCall F (SBe n n 5) F (SPo n 0)
| CC_F_Be_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n ->
    ClosedCall F (SBe n j (2 * k + 5)) C (SBe n (j + 1) (2 * k + 1))
| CC_F_Be_diag_long_low n k :
    k < 2 * n ->
    ClosedCall F (SBe n n (2 * k + 7)) C (SBo n 0 (2 * k + 1))
| CC_F_Bo_pos_1 n j :
    1 <= j ->
    j < n ->
    ClosedCall F (SBo n j 1) D (SPo n (4 * j + 2))
| CC_F_Bo_succ_diag_1 n :
    ClosedCall F (SBo (n + 1) (n + 1) 1) A (SAe (n + 1) n (10 + 4 * (n + 1)))
| CC_F_Bo_pos_3 n j :
    1 <= j ->
    j < n ->
    ClosedCall F (SBo n j 3) F (SPo n (4 * j + 4))
| CC_F_Bo_diag_3 n :
    ClosedCall F (SBo n n 3) D (SBo n 0 (4 * n + 4))
| CC_F_Bo_diag_5 n :
    ClosedCall F (SBo n n 5) F (SPe (n + 1) 0)
| CC_F_Bo_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n + 2 ->
    ClosedCall F (SBo n j (2 * k + 5)) C (SBo n (j + 1) (2 * k + 1))
| CC_F_Bo_diag_long_low n k :
    k <= 2 * n + 1 ->
    ClosedCall F (SBo n n (2 * k + 7)) C (SBe (n + 1) 0 (2 * k + 1))

| CC_F_Pe_even n k :
    k <= 2 * n + 3 ->
    ClosedCall F (SPe (n + 1) (2 * k)) C (SAo n 0 (3 + 4 * n + 2 * k))
| CC_F_Pe_succ_odd n k :
    k <= 1 ->
    ClosedCall F (SPe (n + 2) (2 * k + 1)) C (SBo (n + 1) 1 (7 + 4 * n + 2 * k))
| CC_F_Po_even n k :
    k <= 2 * n + 1 ->
    ClosedCall F (SPo n (2 * k)) C (SAe n 0 (3 + 4 * n + 2 * k))

| CC_C_Ae_0 n q :
    q <= n ->
    ClosedCall C (SAe n q 0) D (SBe n 0 (4 * q + 3))
| CC_C_Ao_0 n q :
    q <= n ->
    ClosedCall C (SAo n q 0) D (SBo n 0 (4 * q + 3))
| CC_C_Ae_1 n q :
    q <= n ->
    ClosedCall C (SAe n q 1) E (SBe n 0 (4 * q + 4))
| CC_C_Ao_1 n q :
    q <= n ->
    ClosedCall C (SAo n q 1) E (SBo n 0 (4 * q + 4))
| CC_C_Ae_2 n q :
    q <= n ->
    ClosedCall C (SAe n q 2) A (SBe n 0 (4 * q + 5))
| CC_C_Ao_2 n q :
    q <= n ->
    ClosedCall C (SAo n q 2) A (SBo n 0 (4 * q + 5))
| CC_C_Ae_special n q :
    q <= n ->
    ClosedCall C (SAe n q (7 + 4 * n)) C (SBo n 0 (4 * q + 3))
| CC_C_Ao_special n q :
    q <= n ->
    ClosedCall C (SAo n q (7 + 4 * n)) C (SBe (n + 1) 0 (4 * q + 3))
| CC_C_Ae_tail_0 n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAe n q (4 * m + 4)) D (SAe n m (4 * q + 4))
| CC_C_Ao_tail_0 n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAo n q (4 * m + 4)) D (SAo n m (4 * q + 4))
| CC_C_Ae_tail_1 n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAe n q (4 * m + 5)) E (SAe n m (4 * q + 5))
| CC_C_Ao_tail_1 n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAo n q (4 * m + 5)) E (SAo n m (4 * q + 5))
| CC_C_Ae_tail_2 n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAe n q (4 * m + 6)) A (SAe n m (4 * q + 6))
| CC_C_Ao_tail_2 n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAo n q (4 * m + 6)) A (SAo n m (4 * q + 6))
| CC_C_Ae_tail_3_low n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAe n q (4 * m + 3)) C (SAe n m (4 * q + 3))
| CC_C_Ao_tail_3_low n q m :
    q <= n ->
    m <= n ->
    ClosedCall C (SAo n q (4 * m + 3)) C (SAo n m (4 * q + 3))

| CC_C_Be_small0 n j :
    ClosedCall C (SBe n j 0) D (SPe n (4 * j + 1))
| CC_C_Bo_small0 n j :
    ClosedCall C (SBo n j 0) D (SPo n (4 * j + 1))
| CC_C_Be_small1 n j :
    ClosedCall C (SBe n j 1) E (SPe n (4 * j + 2))
| CC_C_Bo_small1 n j :
    ClosedCall C (SBo n j 1) E (SPo n (4 * j + 2))
| CC_C_Be_small2 n j :
    ClosedCall C (SBe n j 2) A (SPe n (4 * j + 3))
| CC_C_Bo_small2 n j :
    ClosedCall C (SBo n j 2) A (SPo n (4 * j + 3))
| CC_C_Be_A_range_3 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBe (n + 1) j (4 * m + 3)) C (SAo n m (7 + 4 * n + 4 * j))
| CC_C_Be_A_range_4 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBe (n + 1) j (4 * m + 4)) D (SAo n m (8 + 4 * n + 4 * j))
| CC_C_Be_A_range_5 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBe (n + 1) j (4 * m + 5)) E (SAo n m (9 + 4 * n + 4 * j))
| CC_C_Be_A_range_6 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBe (n + 1) j (4 * m + 6)) A (SAo n m (10 + 4 * n + 4 * j))
| CC_C_Bo_A_range_3 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBo n j (4 * m + 3)) C (SAe n m (7 + 4 * n + 4 * j))
| CC_C_Bo_A_range_4 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBo n j (4 * m + 4)) D (SAe n m (8 + 4 * n + 4 * j))
| CC_C_Bo_A_range_5 n j m :
    j <= n ->
    m <= n ->
    ClosedCall C (SBo n j (4 * m + 5)) E (SAe n m (9 + 4 * n + 4 * j))
| CC_C_Bo_A_range_6 n j m :
    j <= n ->
    m <= n ->
    (m < n \/ 1 <= j) ->
    ClosedCall C (SBo n j (4 * m + 6)) A (SAe n m (10 + 4 * n + 4 * j))

| CC_C_Be_past_3_j0 n s :
    s = 0 ->
    ClosedCall C (SBe (n + 1) 0 (4 * (n + 1 + s) + 3)) C (SBe (n + 1) 0 (7 + 4 * n))
| CC_C_Be_past_3_jpos n j s :
    j + 1 <= n ->
    s = 0 ->
    ClosedCall C (SBe (n + 1) (j + 1) (4 * (n + 1 + s) + 3)) C (SPo (n + 1) (4 * j + 1))
| CC_C_Be_past_4_j0 n s :
    s = 0 ->
    ClosedCall C (SBe (n + 1) 0 (4 * (n + 1 + s) + 4)) D (SBe (n + 1) 0 (8 + 4 * n))
| CC_C_Be_past_5_j0 n s :
    s = 0 ->
    ClosedCall C (SBe (n + 1) 0 (4 * (n + 1 + s) + 5)) E (SBe (n + 1) 0 (9 + 4 * n))
| CC_C_Bo_past_3_jpos n j s :
    j + 1 <= n ->
    s = 0 ->
    ClosedCall C (SBo n (j + 1) (4 * (n + 1 + s) + 3)) C (SPe (n + 1) (4 * j + 5))

| CC_C_Pe_succ_0 n :
    ClosedCall C (SPe (n + 1) 0) A (SAe n n (10 + 4 * n))
| CC_C_Po_0 n :
    ClosedCall C (SPo n 0) A (SPo n 0)
| CC_C_Pe_1 n :
    1 <= n ->
    ClosedCall C (SPe n 1) C (SPe n 1)
| CC_C_Pe_2 n :
    1 <= n ->
    ClosedCall C (SPe n 2) D (SPe n 2)
| CC_C_Pe_3 n :
    1 <= n ->
    ClosedCall C (SPe n 3) E (SPe n 3)
| CC_C_Pe_4 n :
    1 <= n ->
    ClosedCall C (SPe n 4) A (SPe n 4)
| CC_C_Pe_large_1 n m :
    m < n ->
    ClosedCall C (SPe (n + 1) (4 * m + 5)) C (SBo n (m + 1) (7 + 4 * n))
| CC_C_Pe_large_2 n m :
    m < n ->
    ClosedCall C (SPe (n + 1) (4 * m + 6)) D (SBo n (m + 1) (8 + 4 * n))
| CC_C_Pe_large_3 n m :
    m < n ->
    ClosedCall C (SPe (n + 1) (4 * m + 7)) E (SBo n (m + 1) (9 + 4 * n))
| CC_C_Pe_large_4 n m :
    m < n ->
    ClosedCall C (SPe (n + 1) (4 * m + 8)) A (SBo n (m + 1) (10 + 4 * n))
| CC_C_Po_pos_1 n m :
    m <= n ->
    ClosedCall C (SPo (n + 1) (4 * m + 1)) C (SBe (n + 1) (m + 1) (7 + 4 * n))
| CC_C_Po_pos_2 n m :
    m <= n ->
    ClosedCall C (SPo (n + 1) (4 * m + 2)) D (SBe (n + 1) (m + 1) (8 + 4 * n))
| CC_C_Po_pos_3 n m :
    m <= n ->
    ClosedCall C (SPo (n + 1) (4 * m + 3)) E (SBe (n + 1) (m + 1) (9 + 4 * n))
| CC_C_Po_pos_4 n m :
    m <= n ->
    ClosedCall C (SPo (n + 1) (4 * m + 4)) A (SBe (n + 1) (m + 1) (10 + 4 * n))
| CC_C_Be_top_3 n m :
    m <= n ->
    ClosedCall C (SBe (n + 1) (n + 1) (4 * m + 3)) C (SAo n m (11 + 8 * n))
| CC_C_Be_top_4 n m :
    m <= n ->
    ClosedCall C (SBe (n + 1) (n + 1) (4 * m + 4)) D (SAo n m (12 + 8 * n))
| CC_C_Be_top_5 n m :
    m <= n ->
    ClosedCall C (SBe (n + 1) (n + 1) (4 * m + 5)) E (SAo n m (13 + 8 * n))
| CC_C_Be_top_6 n m :
    m <= n ->
    ClosedCall C (SBe (n + 1) (n + 1) (4 * m + 6)) A (SAo n m (14 + 8 * n))
| CC_C_Be_top_past_3 n :
    ClosedCall C (SBe (n + 1) (n + 1) (4 * n + 7)) C (SPo (n + 1) (4 * n + 1))

.

Ltac measure_decr :=
  unfold measure, side_measure, class_rank, skelO_measure;
  repeat rewrite Nat.add_1_r;
  cbn [skelE_measure skelO_measure];
  flia.

Ltac rec_closed IH :=
  lazymatch goal with
  | |- sideRLs _ [((?q0, []), (?q1, []))] (to_side ?s0) (to_side ?s1) =>
      eapply (IH (measure q0 s0));
      [ measure_decr
      | reflexivity
      | eauto using ClosedCall; flia ]
  end.

Ltac ih_by IH q s tac :=
  refine (IH (measure q s) _ q s _ _ _ _);
  [ measure_decr | flia | tac ].

Definition closed_call_sound (q q' : Q) (h h' : Side) : Prop :=
  forall r, to_side h <{{q}} r -[ tm ]->* to_side h' {{q'}}> r.

Theorem ClosedCall_sideRLs q s q' s' :
  ClosedCall q s q' s' ->
  sideRLs (flip tm) [((q, []), (q', []))] (to_side s) (to_side s').
Proof.
  enough
    (Hind : forall m q0 s0 q1 s1,
      measure q0 s0 = m ->
      ClosedCall q0 s0 q1 s1 ->
      sideRLs (flip tm) [((q0, []), (q1, []))] (to_side s0) (to_side s1)).
  { intro Hcall.
    eapply Hind.
    - reflexivity.
    - exact Hcall.
  }
  intro m.
  induction m as [m IH] using lt_wf_ind.
  intros q0 s0 q1 s1 Hm Hcall.
  subst m.
  inversion Hcall; subst.
  - replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        destruct q2 as [| q0].
        { eapply sideRLs_trans.
          { eapply (IH (measure C (SBo n 0 2))).
            { unfold measure, side_measure, class_rank, skelO_measure.
              cbn [skelE_measure skelO_measure].
              flia. }
            { reflexivity. }
            { apply CC_C_Bo_small2. } }
          eapply (IH (measure B (SPo n 3))).
          { unfold measure, side_measure, class_rank, skelO_measure.
            cbn [skelE_measure skelO_measure].
            flia. }
          { flia. }
          { applys_eq (CC_B_Po_odd n 1); flia. } }
        { eapply sideRLs_trans.
          { eapply (IH (measure C (SBo n 0 (4 * q0 + 6)))).
            { unfold measure, side_measure, class_rank, skelO_measure.
              cbn [skelE_measure skelO_measure].
              flia. }
            { flia. }
            { applys_eq (CC_C_Bo_A_range_6 n 0 q0); flia. } }
          eapply (IH (measure B (SAe n q0 (10 + 4 * n)))).
          { unfold measure, side_measure, class_rank, skelO_measure.
            cbn [skelE_measure skelO_measure].
            flia. }
          { flia. }
          { applys_eq (CC_B_Ae_long_nonmax n q0 (2 * n + 3)); flia. } }
      }
      Unshelve.
      all: esc.
  - replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      destruct q2 as [| qn].
      { eapply sideRLs_trans.
        { ih_by IH C (SBe (n + 1) 0 (4 * 0 + 2))
            ltac:(apply CC_C_Be_small2). }
        ih_by IH B (SPe (n + 1) (4 * 0 + 3))
          ltac:(applys_eq (CC_B_Pe_odd n 1); flia). }
      { eapply sideRLs_trans.
        { ih_by IH C (SBe (n + 1) 0 (4 * S qn + 2))
            ltac:(applys_eq (CC_C_Be_A_range_6 n 0 qn); flia). }
        eapply (IH (measure B (SAo n qn (10 + 4 * n)))).
        { measure_decr. }
        { flia. }
        { applys_eq (CC_B_Ao_long_nonmax n qn (2 * n + 3)); flia. } }
    }
    Unshelve.
    all: esc.
  - replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SBe (n + 1) 0 (4 * (n + 1) + 2))
          ltac:(applys_eq (CC_C_Be_A_range_6 n 0 n); flia). }
      ih_by IH B (SAo n n (10 + 4 * n + 4 * 0))
        ltac:(applys_eq (CC_B_Ao_long_diag_low n (2 * n + 3)); flia).
    }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAe n q2 1) ltac:(apply CC_F_Ae_1; flia). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAo n q2 1) ltac:(apply CC_F_Ao_1; flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAe_succ_step.
      rewrite to_side_SAe_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SAe n q2 3)
          ltac:(applys_eq (CC_F_Ae_3_nonmax n q2); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SAe n q2 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Ae_long_nonmax n q2 k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAo_succ_step.
      rewrite to_side_SAo_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SAo n q2 3)
          ltac:(applys_eq (CC_F_Ao_3_nonmax n q2); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SAo n q2 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Ao_long_nonmax n q2 k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAe_succ_step.
      rewrite to_side_SBo_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SAe n n 3) ltac:(apply CC_F_Ae_3_diag). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SAe n n (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Ae_long_diag_low n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * (2 * n + 3 + s2) + 4) with
      (S (2 * (2 * n + 3 + s2) + 3)) by flia.
    rewrite to_side_SAe_succ_step.
    destruct s2 as [| s0].
    { replace (n + 1) with (S n) by flia.
      rewrite to_side_SPe_succ_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SAe n n (2 * (2 * n + 3 + 0) + 3))
          ltac:(applys_eq (CC_F_Ae_long_diag_low n (2 * n + 2)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S s0) with (S (2 * s0 + 1)) by flia.
      rewrite to_side_SPe_succ_step.
      split_sideRLs_concat.
      { ih_by IH F (SAe n n (2 * (2 * n + 3 + S s0) + 3))
          ltac:(applys_eq (CC_F_Ae_long_diag_high n s0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAo_succ_step.
      rewrite to_side_SBe_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SAo n n 3) ltac:(apply CC_F_Ao_3_diag). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SAo n n (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Ao_long_diag_low n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * (2 * n + 5 + s2) + 4) with
      (S (2 * (2 * n + 5 + s2) + 3)) by flia.
    rewrite to_side_SAo_succ_step.
    destruct s2 as [| s0].
    { rewrite to_side_SPo_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SAo n n (2 * (2 * n + 5 + 0) + 3))
          ltac:(applys_eq (CC_F_Ao_long_diag_low n (2 * n + 4)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S s0) with (S (2 * s0 + 1)) by flia.
      rewrite to_side_SPo_succ_step.
      split_sideRLs_concat.
      { ih_by IH F (SAo n n (2 * (2 * n + 5 + S s0) + 3))
          ltac:(applys_eq (CC_F_Ao_long_diag_high n s0); flia). }
      Unshelve.
      all: esc. }
  - rewrite to_side_SBe_zero_step.
    replace 1 with (S 0) by flia.
    rewrite to_side_SPe_succ_step.
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SPe (n + 1) 0) ltac:(apply CC_C_Pe_succ_0). }
      ih_by IH B (SAe n n (10 + 4 * n))
        ltac:(applys_eq (CC_B_Ae_long_diag_high n 0); flia).
    }
    Unshelve.
    all: esc.
  - rewrite to_side_SBo_zero_step.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SPo (n + 1) 0) ltac:(apply CC_C_Po_0). }
      ih_by IH B (SPo (n + 1) 0)
        ltac:(applys_eq (CC_B_Po_even n 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    { ih_by IH F (SBe n 0 0) ltac:(apply CC_F_Be0_0). }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    rewrite to_side_SBo_succ_step.
    split_sideRLs_concat.
    { ih_by IH F (SBo n 0 0) ltac:(apply CC_F_Bo0_0). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace 3 with (S 2) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) 0 1) ltac:(apply CC_F_Be0_1). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace 3 with (S 2) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo (n + 1) 0 1) ltac:(apply CC_F_Bo0_1). }
    Unshelve.
    all: esc.
  - replace (2 * k + 3) with (S (2 * k + 2)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SBe_succ_step.
      rewrite to_side_SAe_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SBe n 0 2) ltac:(apply CC_F_Be0_2). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SBe n 0 (S (2 * k0 + 1) + 2))
          ltac:(applys_eq (CC_F_Be0_even_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 3) with (S (2 * k + 2)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SBo_succ_step.
      rewrite to_side_SAo_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SBo n 0 2) ltac:(apply CC_F_Bo0_2). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SBo n 0 (S (2 * k0 + 1) + 2))
          ltac:(applys_eq (CC_F_Bo0_even_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite to_side_SBe_succ_step.
    destruct k as [| k0].
    { rewrite to_side_SBe_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SBe (n + 1) 0 3) ltac:(apply CC_F_Be0_3). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite to_side_SBe_succ_step.
      split_sideRLs_concat.
      { ih_by IH F (SBe (n + 1) 0 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Be0_odd_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite to_side_SBo_succ_step.
    destruct k as [| k0].
    { rewrite to_side_SBo_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SBo (n + 1) 0 3) ltac:(apply CC_F_Bo0_3). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite to_side_SBo_succ_step.
      split_sideRLs_concat.
      { ih_by IH F (SBo (n + 1) 0 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Bo0_odd_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - rewrite to_side_SBe_zero_step.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    rewrite to_side_SBo_succ_step.
    split_sideRLs_concat.
    {
      destruct j as [| [| j0]].
      { exfalso; flia. }
      { destruct n as [| n0].
        { exfalso; flia. }
        eapply sideRLs_trans.
        { ih_by IH C (SPe (S n0 + 1) 4)
            ltac:(applys_eq (CC_C_Pe_4 (S n0 + 1)); flia). }
        ih_by IH B (SPe (S n0 + 1) 4)
          ltac:(applys_eq (CC_B_Pe_succ_even n0 2); flia). }
      { eapply sideRLs_trans.
        { ih_by IH C (SPe (n + 1) (4 * S (S j0)))
            ltac:(applys_eq (CC_C_Pe_large_4 n j0); flia). }
        ih_by IH B (SBo n (j0 + 1) (10 + 4 * n))
          ltac:(applys_eq (CC_B_Bo_pos_long n (j0 + 1) (2 * n + 3)); flia). }
    }
    Unshelve.
    all: esc.
  - destruct n as [| [| n0]].
    { unfold to_side.
      cbn.
      esc. }
    { unfold to_side.
      cbn.
      eapply sideRLs_c_spec with (T:=10^6);
      [ vm_compute; reflexivity | st; reflexivity ]. }
    { rewrite to_side_SBe_zero_step.
      replace (4 * S (S n0) + 1) with (S (4 * S (S n0))) by flia.
      rewrite to_side_SBe_succ_step.
      split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SPe (S (S n0)) (4 * S (S n0)))
            ltac:(applys_eq (CC_C_Pe_large_4 (n0 + 1) n0); flia). }
        ih_by IH B (SBo (n0 + 1) (n0 + 1) (10 + 4 * (n0 + 1)))
          ltac:(applys_eq (CC_B_Bo_diag_long_low (n0 + 1) (2 * (n0 + 1) + 2)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe n j 1)
        ltac:(apply CC_F_Be_pos_1; flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side.
      cbn.
      esc. }
    { replace 2 with (S 1) by flia.
      replace (4 * S n0 + 3) with (S (4 * S n0 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBe (S n0) (S n0) 1)
            ltac:(applys_eq (CC_F_Be_succ_diag_1 n0); flia). }
        ih_by IH B (SAo n0 n0 (10 + 4 * n0))
          ltac:(applys_eq (CC_B_Ao_long_diag_low n0 (2 * n0 + 3)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 4 with (S 3) by flia.
    replace (4 * n + 5) with (S (4 * n + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe n n 3) ltac:(apply CC_F_Be_diag_3). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite (to_side_SBe_succ_step n j (2 * k + 3)).
    destruct k as [| k0].
    { rewrite to_side_SBe_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SBe n j 3)
          ltac:(applys_eq (CC_F_Be_pos_3 n j); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite (to_side_SBe_succ_step n (j + 1) (2 * k0 + 1)).
      split_sideRLs_concat.
      { ih_by IH F (SBe n j (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Be_pos_long n j k0); flia). }
      Unshelve.
      all: esc. }
  - destruct k as [| k0].
    { replace (2 * 0 + 6) with (S 5) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SBe n n 5) ltac:(apply CC_F_Be_diag_5). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0 + 6) with (S (2 * k0 + 7)) by flia.
      replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SBe n n (2 * k0 + 7))
          ltac:(applys_eq (CC_F_Be_diag_long_low n k0); flia). }
      Unshelve.
      all: esc. }
  - rewrite to_side_SBo_zero_step.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SPo (n + 1) (4 * j))
          ltac:(applys_eq (CC_C_Po_pos_4 n (j - 1)); flia). }
      ih_by IH B (SBe (n + 1) (j - 1 + 1) (10 + 4 * n))
        ltac:(applys_eq (CC_B_Be_pos_long (n + 1) j (2 * n + 3)); flia).
    }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side.
      cbn.
      esc. }
    { rewrite to_side_SBo_zero_step.
      replace (4 * S n0 + 1) with (S (4 * S n0)) by flia.
      rewrite to_side_SBo_succ_step.
      split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SPo (S n0) (4 * S n0))
            ltac:(applys_eq (CC_C_Po_pos_4 n0 n0); flia). }
        ih_by IH B (SBe (n0 + 1) (n0 + 1) (10 + 4 * n0))
          ltac:(applys_eq (CC_B_Be_diag_long_low (S n0) (2 * S n0)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n j 1)
        ltac:(apply CC_F_Bo_pos_1; flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { replace 2 with (S 1) by flia.
      replace (7 + 4 * 0) with (S 6) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { apply sideRLs_D_Bo0_1. }
        ih_by IH B (SPo 0 3) ltac:(applys_eq (CC_B_Po_odd 0 1); flia).
      }
      Unshelve.
      all: esc. }
    { replace 2 with (S 1) by flia.
      replace (7 + 4 * S n0) with (S (6 + 4 * S n0)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBo (S n0) (S n0) 1)
            ltac:(applys_eq (CC_F_Bo_succ_diag_1 n0); flia). }
        ih_by IH B (SAe (n0 + 1) n0 (10 + 4 * (n0 + 1)))
          ltac:(applys_eq (CC_B_Ae_long_nonmax (S n0) n0 (2 * n0 + 5)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 4 with (S 3) by flia.
    replace (4 * n + 5) with (S (4 * n + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n n 3) ltac:(apply CC_F_Bo_diag_3). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite (to_side_SBo_succ_step n j (2 * k + 3)).
    destruct k as [| k0].
    { rewrite to_side_SBo_zero_step.
      split_sideRLs_concat.
      { ih_by IH F (SBo n j 3)
          ltac:(applys_eq (CC_F_Bo_pos_3 n j); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite (to_side_SBo_succ_step n (j + 1) (2 * k0 + 1)).
      split_sideRLs_concat.
      { ih_by IH F (SBo n j (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_F_Bo_pos_long n j k0); flia). }
      Unshelve.
      all: esc. }
  - destruct k as [| k0].
    { replace (2 * 0 + 6) with (S 5) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SBo n n 5) ltac:(apply CC_F_Bo_diag_5). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0 + 6) with (S (2 * k0 + 7)) by flia.
      replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SBo n n (2 * k0 + 7))
          ltac:(applys_eq (CC_F_Bo_diag_long_low n k0); flia). }
      Unshelve.
      all: esc. }
  - destruct k as [| k0].
    { replace (n + 2) with (S (n + 1)) by flia.
      replace (6 + 4 * n + 2 * 0) with (S (5 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      { eapply (IH (measure F (SBo (n + 1) 0 (5 + 4 * (n + 1))))).
        { replace (n + 2) with (S (n + 1)) by flia; measure_decr. }
        { flia. }
        { applys_eq (CC_F_Bo0_odd_tail n (2 * n + 2)); flia. } }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      replace (6 + 4 * n + S (2 * k0 + 1)) with (S (7 + 4 * n + 2 * k0)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH F (SPe (n + 2) (2 * k0 + 1))
          ltac:(applys_eq (CC_F_Pe_succ_odd n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 1) with (S (2 * k)) by flia.
    replace (4 + 4 * n + 2 * k) with (S (3 + 4 * n + 2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPe (n + 1) (2 * k))
        ltac:(applys_eq (CC_F_Pe_even n k); flia). }
    Unshelve.
    all: esc.
  - replace (n + 1) with (S n) by flia.
    replace (6 + 4 * n) with (S (5 + 4 * n)) by flia.
    rewrite to_side_SPo_zero_step.
    replace (S (5 + 4 * n) + 2 * 0) with (S (5 + 4 * n)) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    { ih_by IH F (SBe (S n) 0 (5 + 4 * S n))
        ltac:(applys_eq (CC_F_Be0_odd_tail n (2 * n + 2)); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 1) with (S (2 * k)) by flia.
    replace (4 + 4 * n + 2 * k) with (S (3 + 4 * n + 2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPo n (2 * k))
        ltac:(applys_eq (CC_F_Po_even n k); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { destruct q2 as [| q0].
      { unfold to_side.
        cbn.
        esc. }
      { exfalso; flia. } }
    replace 1 with (S 0) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    {
      destruct (Nat.eq_dec q2 (S n0)) as [Hq | Hq].
      { subst q2.
        eapply sideRLs_trans.
        { ih_by IH B (SAe (S n0) (S n0) 0)
            ltac:(applys_eq (CC_B_Ae_succ_diag_zero n0); flia). }
        ih_by IH C (SBe (n0 + 1) 0 (7 + 4 * n0))
          ltac:(applys_eq (CC_C_Be_past_3_j0 n0 0); flia). }
      { eapply sideRLs_trans.
        { ih_by IH B (SAe (S n0) q2 0)
            ltac:(applys_eq (CC_B_Ae_succ_zero n0 q2); flia). }
        ih_by IH C (SAo n0 q2 (7 + 4 * n0))
          ltac:(applys_eq (CC_C_Ao_special n0 q2); flia). }
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SAo n q2 0)
          ltac:(applys_eq (CC_B_Ao_zero n q2); flia). }
      ih_by IH C (SAe n q2 (7 + 4 * n))
        ltac:(applys_eq (CC_C_Ae_special n q2); flia).
    }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAe n q2 2)
        ltac:(apply CC_B_Ae_tail2; flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAe n n 2)
        ltac:(applys_eq (CC_B_Ae_tail2 n n); flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAo n q2 2)
        ltac:(apply CC_B_Ao_tail2; flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SAo_succ_step n n 2).
    replace (n + 1) with (S n) by flia.
    rewrite to_side_SPe_succ_zero_step.
    split_sideRLs_concat.
    { ih_by IH B (SAo n n 2)
        ltac:(applys_eq (CC_B_Ao_tail2 n n); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAe n q2 (2 * k + 4))
        ltac:(applys_eq (CC_B_Ae_long_nonmax n q2 k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAo n q2 (2 * k + 4))
        ltac:(applys_eq (CC_B_Ao_long_nonmax n q2 k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAe n n (2 * k + 4))
        ltac:(applys_eq (CC_B_Ae_long_diag_low n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * (2 * n + 3 + s2) + 5) with (S (2 * (2 * n + 3 + s2) + 4)) by flia.
    replace (2 * s2 + 1) with (S (2 * s2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAe n n (2 * (2 * n + 3 + s2) + 4))
        ltac:(applys_eq (CC_B_Ae_long_diag_high n s2); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAo n n (2 * k + 4))
        ltac:(applys_eq (CC_B_Ao_long_diag_low n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * (2 * n + 5 + s2) + 5) with (S (2 * (2 * n + 5 + s2) + 4)) by flia.
    replace (2 * s2 + 1) with (S (2 * s2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SAo n n (2 * (2 * n + 5 + s2) + 4))
        ltac:(applys_eq (CC_B_Ao_long_diag_high n s2); flia). }
    Unshelve.
    all: esc.
  - unfold to_side.
    cbn.
    esx.
  - unfold to_side.
    cbn.
    esx.
  - replace 1 with (S 0) by flia.
    rewrite (to_side_SBe_succ_step (n + 1) 0 0).
    replace 2 with (S 1) by flia.
    rewrite (to_side_SPe_succ_step (n + 1) 1).
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBe (n + 1) 0 0)
          ltac:(applys_eq (CC_B_Be0_0_succ n); flia). }
      ih_by IH C (SPe (n + 1) 1)
        ltac:(applys_eq (CC_C_Pe_1 (n + 1)); flia).
    }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side. cbn. esc. }
    replace 1 with (S 0) by flia.
    rewrite (to_side_SBo_succ_step (S n0 + 1) 0 0).
    replace 2 with (S 1) by flia.
    rewrite (to_side_SPo_succ_step (S n0 + 1) 1).
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBo (S n0 + 1) 0 0)
          ltac:(applys_eq (CC_B_Bo_succ0_0 (S n0)); flia). }
      ih_by IH C (SBe (S n0 + 1) 1 (7 + 4 * S n0))
        ltac:(applys_eq (CC_C_Be_past_3_jpos (S n0) 0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    rewrite (to_side_SBe_succ_step n 0 1).
    split_sideRLs_concat.
    { ih_by IH B (SBe n 0 1)
        ltac:(apply CC_B_Be0_1). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    rewrite (to_side_SBo_succ_step n 0 1).
    split_sideRLs_concat.
    { ih_by IH B (SBo n 0 1)
        ltac:(apply CC_B_Bo0_1). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SBe_succ_step (n + 1) 0 2).
    replace 4 with (S 3) by flia.
    rewrite (to_side_SPe_succ_step (n + 1) 3).
    split_sideRLs_concat.
    { ih_by IH B (SBe (n + 1) 0 2)
        ltac:(apply CC_B_Be0_2_succ). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SBo_succ_step (n + 1) 0 2).
    replace 4 with (S 3) by flia.
    rewrite (to_side_SPo_succ_step (n + 1) 3).
    split_sideRLs_concat.
    { ih_by IH B (SBo (n + 1) 0 2)
        ltac:(apply CC_B_Bo0_2). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBe n 0 (2 * k + 3))
        ltac:(applys_eq (CC_B_Be0_odd_tail n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBo n 0 (2 * k + 3))
        ltac:(applys_eq (CC_B_Bo0_odd_tail n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBe (n + 1) 0 (2 * k + 4))
        ltac:(applys_eq (CC_B_Be0_even_tail n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBo (n + 1) 0 (2 * k + 4))
        ltac:(applys_eq (CC_B_Bo0_even_tail n k); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { exfalso; flia. }
    destruct j as [| j0].
    { exfalso; flia. }
    replace 1 with (S 0) by flia.
    replace (4 * S j0 + 2) with (S (4 * j0 + 5)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
    { ih_by IH B (SBe (S n0) (S j0) 0)
          ltac:(applys_eq (CC_B_Be_succ_pos_zero n0 (S j0)); flia). }
      ih_by IH C (SBo n0 (S j0) (7 + 4 * n0))
        ltac:(applys_eq (CC_C_Bo_past_3_jpos n0 j0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    replace (n + 1) with (S n) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBe (S n) (S n) 0)
          ltac:(applys_eq (CC_B_Be_diag_zero (S n)); flia). }
      ih_by IH C (SBe (S n) 0 (4 * S n + 1))
        ltac:(applys_eq (CC_C_Be_A_range_5 n 0 n); flia).
    }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * j + 4) with (S (4 * j + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBe n j 2)
        ltac:(apply CC_B_Be_pos_tail2; flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side.
      cbn.
      esc. }
    replace 3 with (S 2) by flia.
    replace (4 * S n0 + 4) with (S (4 * S n0 + 3)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBe (S n0) (S n0) 2)
          ltac:(applys_eq (CC_B_Be_diag_tail2 (S n0)); flia). }
      ih_by IH C (SBe (S n0) 0 (4 * S n0 + 3))
        ltac:(applys_eq (CC_C_Be_past_3_j0 n0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 5 with (S 4) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBe n n 4)
        ltac:(applys_eq (CC_B_Be_diag_tail4 n); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBe n j (2 * k + 4))
        ltac:(applys_eq (CC_B_Be_pos_long n j k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 7) with (S (2 * k + 6)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBe n n (2 * k + 6))
        ltac:(applys_eq (CC_B_Be_diag_long_low n k); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { exfalso; flia. }
    destruct j as [| j0].
    { exfalso; flia. }
    replace 1 with (S 0) by flia.
    replace (4 * S j0 + 2) with (S (4 * j0 + 5)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBo (S n0) (S j0) 0)
          ltac:(applys_eq (CC_B_Bo_succ_pos_zero n0 (S j0)); flia). }
      destruct (Nat.eq_dec (S j0) n0) as [Htop | Hntop].
      { subst n0.
        ih_by IH C (SBe (S j0 + 1) (S j0 + 1) (7 + 4 * S j0))
          ltac:(applys_eq (CC_C_Be_top_past_3 (S j0)); flia). }
      ih_by IH C (SBe (n0 + 1) (S j0 + 1) (7 + 4 * n0))
        ltac:(applys_eq (CC_C_Be_past_3_jpos n0 (S j0) 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (10 + 4 * (n + 1)) with (S (9 + 4 * (n + 1))) by flia.
    replace (n + 1) with (S n) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBo (S n) (S n) 0)
          ltac:(applys_eq (CC_B_Bo_diag_zero (S n)); flia). }
      ih_by IH C (SBo (S n) 0 (4 * S n + 1))
        ltac:(applys_eq (CC_C_Bo_A_range_5 (S n) 0 n); flia).
    }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * j + 4) with (S (4 * j + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBo n j 2)
        ltac:(apply CC_B_Bo_pos_tail2; flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side.
      cbn.
      esc. }
    replace 3 with (S 2) by flia.
    replace (4 * S n0 + 4) with (S (4 * S n0 + 3)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH B (SBo (S n0) (S n0) 2)
          ltac:(applys_eq (CC_B_Bo_diag_tail2 (S n0)); flia). }
      ih_by IH C (SAe (S n0) (S n0) (7 + 4 * S n0))
        ltac:(applys_eq (CC_C_Ae_special (S n0) (S n0)); flia).
    }
    Unshelve.
    all: esc.
  - replace 5 with (S 4) by flia.
    rewrite (to_side_SBo_succ_step n n 4).
    replace (n + 1) with (S n) by flia.
    rewrite to_side_SPe_succ_zero_step.
    split_sideRLs_concat.
    { ih_by IH B (SBo n n 4)
        ltac:(applys_eq (CC_B_Bo_diag_tail4 n); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBo n j (2 * k + 4))
        ltac:(applys_eq (CC_B_Bo_pos_long n j k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 7) with (S (2 * k + 6)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SBo n n (2 * k + 6))
        ltac:(applys_eq (CC_B_Bo_diag_long_low n k); flia). }
    Unshelve.
    all: esc.
  - destruct k as [| k0].
    { replace (n + 1) with (S n) by flia.
      rewrite to_side_SPe_succ_zero_step.
      replace (3 + 4 * n + 2 * 0) with (S (2 + 4 * n)) by flia.
      rewrite (to_side_SAo_succ_step n 0 (2 + 4 * n)).
      split_sideRLs_concat.
      { ih_by IH B (SBo n 0 (5 + 4 * n))
          ltac:(applys_eq (CC_B_Bo0_odd_tail n (2 * n + 1)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      replace (3 + 4 * n + 2 * S k0) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SPe_succ_step (n + 1) (2 * k0 + 1)).
      replace (3 + 4 * n + S (2 * k0 + 1)) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SAo_succ_step n 0 (4 + 4 * n + 2 * k0)).
      split_sideRLs_concat.
      { ih_by IH B (SPe (n + 1) (2 * k0 + 1))
          ltac:(applys_eq (CC_B_Pe_odd n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 1) with (S (2 * k)) by flia.
    replace (7 + 4 * n + 2 * k) with (S (6 + 4 * n + 2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH B (SPe (n + 2) (2 * k))
        ltac:(applys_eq (CC_B_Pe_succ_even n k); flia). }
    Unshelve.
    all: esc.
  - destruct k as [| k0].
    { rewrite to_side_SPo_zero_step.
      replace (3 + 4 * n + 2 * 0) with (S (2 + 4 * n)) by flia.
      rewrite (to_side_SAe_succ_step n 0 (2 + 4 * n)).
      split_sideRLs_concat.
      { ih_by IH B (SBe n 0 (5 + 4 * n))
          ltac:(applys_eq (CC_B_Be0_odd_tail n (2 * n + 1)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      replace (3 + 4 * n + 2 * S k0) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SPo_succ_step n (2 * k0 + 1)).
      replace (3 + 4 * n + S (2 * k0 + 1)) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SAe_succ_step n 0 (4 + 4 * n + 2 * k0)).
      split_sideRLs_concat.
      { ih_by IH B (SPo n (2 * k0 + 1))
          ltac:(applys_eq (CC_B_Po_odd n k0); flia). }
      Unshelve.
      all: esc. }
  - rewrite to_side_SAe_zero_step.
    replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
    rewrite (to_side_SBe_succ_step n 0 (4 * q2 + 2)).
    apply sideRLs_F_0_to_1.
  - rewrite to_side_SAo_zero_step.
    replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
    rewrite (to_side_SBo_succ_step n 0 (4 * q2 + 2)).
    apply sideRLs_F_0_to_1.
  - replace 1 with (S 0) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAe n q2 0) ltac:(applys_eq (CC_C_Ae_0 n q2); flia). }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAo n q2 0) ltac:(applys_eq (CC_C_Ao_0 n q2); flia). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAe n q2 1) ltac:(applys_eq (CC_C_Ae_1 n q2); flia). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAo n q2 1) ltac:(applys_eq (CC_C_Ao_1 n q2); flia). }
    Unshelve.
    all: esc.
  - replace (7 + 4 * n) with (S (4 * n + 6)) by flia.
    replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SAe n q2 (4 * n + 6))
          ltac:(applys_eq (CC_C_Ae_tail_2 n q2 n); flia). }
      ih_by IH B (SAe n n (4 * q2 + 6))
        ltac:(applys_eq (CC_B_Ae_long_diag_low n (2 * q2 + 1)); flia).
    }
    Unshelve.
    all: esc.
  - replace (7 + 4 * n) with (S (4 * n + 6)) by flia.
    replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SAo n q2 (4 * n + 6))
          ltac:(applys_eq (CC_C_Ao_tail_2 n q2 n); flia). }
      ih_by IH B (SAo n n (4 * q2 + 6))
        ltac:(applys_eq (CC_B_Ao_long_diag_low n (2 * q2 + 1)); flia).
    }
    Unshelve.
    all: esc.
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAe n q2 (4 * m + 3))
        ltac:(applys_eq (CC_C_Ae_tail_3_low n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAo n q2 (4 * m + 3))
        ltac:(applys_eq (CC_C_Ao_tail_3_low n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAe n q2 (4 * m + 4))
        ltac:(applys_eq (CC_C_Ae_tail_0 n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAo n q2 (4 * m + 4))
        ltac:(applys_eq (CC_C_Ao_tail_0 n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAe n q2 (4 * m + 5))
        ltac:(applys_eq (CC_C_Ae_tail_1 n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAo n q2 (4 * m + 5))
        ltac:(applys_eq (CC_C_Ao_tail_1 n q2 m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SAe n q2 2)
            ltac:(applys_eq (CC_C_Ae_2 n q2); flia). }
        ih_by IH B (SBe n 0 (4 * q2 + 5))
          ltac:(applys_eq (CC_B_Be0_odd_tail n (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SAe n q2 (4 * m0 + 6))
            ltac:(applys_eq (CC_C_Ae_tail_2 n q2 m0); flia). }
        ih_by IH B (SAe n m0 (4 * q2 + 6))
          ltac:(applys_eq (CC_B_Ae_long_nonmax n m0 (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SAo n q2 2)
            ltac:(applys_eq (CC_C_Ao_2 n q2); flia). }
        ih_by IH B (SBo n 0 (4 * q2 + 5))
          ltac:(applys_eq (CC_B_Bo0_odd_tail n (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SAo n q2 (4 * m0 + 6))
            ltac:(applys_eq (CC_C_Ao_tail_2 n q2 m0); flia). }
        ih_by IH B (SAo n m0 (4 * q2 + 6))
          ltac:(applys_eq (CC_B_Ao_long_nonmax n m0 (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
  - rewrite to_side_SBe_zero_step.
    replace (4 * j + 1) with (S (4 * j)) by flia.
    rewrite (to_side_SPe_succ_step n (4 * j)).
    apply sideRLs_F_0_to_1.
  - rewrite to_side_SBo_zero_step.
    replace (4 * j + 1) with (S (4 * j)) by flia.
    rewrite (to_side_SPo_succ_step n (4 * j)).
    apply sideRLs_F_0_to_1.
  - replace 1 with (S 0) by flia.
    replace (4 * j + 2) with (S (4 * j + 1)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe n j 0) ltac:(apply CC_C_Be_small0). }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (4 * j + 2) with (S (4 * j + 1)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n j 0) ltac:(apply CC_C_Bo_small0). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe n j 1) ltac:(apply CC_C_Be_small1). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n j 1) ltac:(apply CC_C_Bo_small1). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBe (n + 1) j 2) ltac:(apply CC_C_Be_small2). }
        ih_by IH B (SPe (n + 1) (4 * j + 3))
          ltac:(applys_eq (CC_B_Pe_odd n (2 * j + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBe (n + 1) j (4 * m0 + 6))
            ltac:(applys_eq (CC_C_Be_A_range_6 n j m0); flia). }
        ih_by IH B (SAo n m0 (10 + 4 * n + 4 * j))
          ltac:(applys_eq (CC_B_Ao_long_nonmax n m0 (3 + 2 * n + 2 * j)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (8 + 4 * n + 4 * j) with (S (7 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) j (4 * m + 3))
        ltac:(applys_eq (CC_C_Be_A_range_3 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (9 + 4 * n + 4 * j) with (S (8 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) j (4 * m + 4))
        ltac:(applys_eq (CC_C_Be_A_range_4 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (10 + 4 * n + 4 * j) with (S (9 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) j (4 * m + 5))
        ltac:(applys_eq (CC_C_Be_A_range_5 n j m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBo n j 2) ltac:(apply CC_C_Bo_small2). }
        ih_by IH B (SPo n (4 * j + 3))
          ltac:(applys_eq (CC_B_Po_odd n (2 * j + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBo n j (4 * m0 + 6))
            ltac:(applys_eq (CC_C_Bo_A_range_6 n j m0); flia). }
        ih_by IH B (SAe n m0 (10 + 4 * n + 4 * j))
          ltac:(applys_eq (CC_B_Ae_long_nonmax n m0 (3 + 2 * n + 2 * j)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (8 + 4 * n + 4 * j) with (S (7 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n j (4 * m + 3))
        ltac:(applys_eq (CC_C_Bo_A_range_3 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (9 + 4 * n + 4 * j) with (S (8 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n j (4 * m + 4))
        ltac:(applys_eq (CC_C_Bo_A_range_4 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (10 + 4 * n + 4 * j) with (S (9 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n j (4 * m + 5))
        ltac:(applys_eq (CC_C_Bo_A_range_5 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 3) with (S (4 * n + 6)) by flia.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SBe (n + 1) 0 (4 * n + 6))
          ltac:(applys_eq (CC_C_Be_A_range_6 n 0 n); flia). }
      ih_by IH B (SAo n n (10 + 4 * n + 4 * 0))
        ltac:(applys_eq (CC_B_Ao_long_diag_low n (2 * n + 3)); flia).
    }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 3) with (S (4 * n + 6)) by flia.
    replace (4 * j + 1) with (S (4 * j)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SBe (n + 1) (j + 1) (4 * n + 6))
          ltac:(applys_eq (CC_C_Be_A_range_6 n (j + 1) n); flia). }
      ih_by IH B (SAo n n (10 + 4 * n + 4 * (j + 1)))
        ltac:(applys_eq (CC_B_Ao_long_diag_high n (2 * j)); flia).
    }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 4) with (S (4 * (n + 1 + 0) + 3)) by flia.
    replace (8 + 4 * n) with (S (7 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) 0 (4 * (n + 1 + 0) + 3))
        ltac:(applys_eq (CC_C_Be_past_3_j0 n 0); flia). }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 5) with (S (4 * (n + 1 + 0) + 4)) by flia.
    replace (9 + 4 * n) with (S (8 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) 0 (4 * (n + 1 + 0) + 4))
        ltac:(applys_eq (CC_C_Be_past_4_j0 n 0); flia). }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 3) with (S (4 * n + 6)) by flia.
    replace (4 * j + 5) with (S (4 * j + 4)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SBo n (j + 1) (4 * n + 6))
          ltac:(applys_eq (CC_C_Bo_A_range_6 n (j + 1) n); flia). }
      ih_by IH B (SAe n n (10 + 4 * n + 4 * (j + 1)))
        ltac:(applys_eq (CC_B_Ae_long_diag_high n (2 * j + 2)); flia).
    }
    Unshelve.
    all: esc.
  - replace (n + 1) with (S n) by flia.
    rewrite to_side_SPe_succ_zero_step.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    rewrite (to_side_SAe_succ_step n n (9 + 4 * n)).
    split_sideRLs_concat.
    { ih_by IH C (SBo n 0 (5 + 4 * n))
        ltac:(applys_eq (CC_C_Bo_A_range_5 n 0 n); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side. cbn. esc. }
    rewrite to_side_SPo_zero_step.
    split_sideRLs_concat.
    { ih_by IH C (SBe (S n0) 0 (5 + 4 * S n0))
        ltac:(applys_eq (CC_C_Be_past_5_j0 n0 0); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { exfalso; flia. }
    replace 1 with (S 0) by flia.
    rewrite (to_side_SPe_succ_step (S n0) 0).
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SPe (S n0) 0)
          ltac:(applys_eq (CC_C_Pe_succ_0 n0); flia). }
      ih_by IH B (SAe n0 n0 (10 + 4 * n0))
        ltac:(applys_eq (CC_B_Ae_long_diag_high n0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    rewrite (to_side_SPe_succ_step n 1).
    split_sideRLs_concat.
    { ih_by IH C (SPe n 1) ltac:(applys_eq (CC_C_Pe_1 n); flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SPe_succ_step n 2).
    split_sideRLs_concat.
    { ih_by IH C (SPe n 2) ltac:(applys_eq (CC_C_Pe_2 n); flia). }
    Unshelve.
    all: esc.
  - replace 4 with (S 3) by flia.
    rewrite (to_side_SPe_succ_step n 3).
    split_sideRLs_concat.
    { ih_by IH C (SPe n 3) ltac:(applys_eq (CC_C_Pe_3 n); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { destruct n as [| n0].
      { exfalso; flia. }
      replace (4 * 0 + 5) with (S 4) by flia.
      replace (0 + 1) with 1 by flia.
      replace (7 + 4 * S n0) with (S (6 + 4 * S n0)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SPe (S n0 + 1) 4)
            ltac:(applys_eq (CC_C_Pe_4 (S n0 + 1)); flia). }
        ih_by IH B (SPe (S n0 + 1) 4)
          ltac:(applys_eq (CC_B_Pe_succ_even n0 2); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 5) with (S (4 * m0 + 8)) by flia.
      replace (S m0 + 1) with (m0 + 2) by flia.
      replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SPe (n + 1) (4 * m0 + 8))
            ltac:(applys_eq (CC_C_Pe_large_4 n m0); flia). }
        ih_by IH B (SBo n (m0 + 1) (10 + 4 * n))
          ltac:(applys_eq (CC_B_Bo_pos_long n (m0 + 1) (2 * n + 3)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (8 + 4 * n) with (S (7 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPe (n + 1) (4 * m + 5))
        ltac:(applys_eq (CC_C_Pe_large_1 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 7) with (S (4 * m + 6)) by flia.
    replace (9 + 4 * n) with (S (8 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPe (n + 1) (4 * m + 6))
        ltac:(applys_eq (CC_C_Pe_large_2 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 8) with (S (4 * m + 7)) by flia.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPe (n + 1) (4 * m + 7))
        ltac:(applys_eq (CC_C_Pe_large_3 n m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 1) with (S 0) by flia.
      replace (0 + 1) with 1 by flia.
      replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SPo (n + 1) 0)
            ltac:(applys_eq (CC_C_Po_0 (n + 1)); flia). }
        ih_by IH B (SPo (n + 1) 0)
          ltac:(applys_eq (CC_B_Po_even n 0); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 1) with (S (4 * m0 + 4)) by flia.
      replace (S m0 + 1) with (m0 + 2) by flia.
      replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SPo (n + 1) (4 * m0 + 4))
            ltac:(applys_eq (CC_C_Po_pos_4 n m0); flia). }
        ih_by IH B (SBe (n + 1) (m0 + 1) (10 + 4 * n))
          ltac:(applys_eq (CC_B_Be_pos_long (n + 1) (m0 + 1) (2 * n + 3)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 2) with (S (4 * m + 1)) by flia.
    replace (8 + 4 * n) with (S (7 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPo (n + 1) (4 * m + 1))
        ltac:(applys_eq (CC_C_Po_pos_1 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 3) with (S (4 * m + 2)) by flia.
    replace (9 + 4 * n) with (S (8 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPo (n + 1) (4 * m + 2))
        ltac:(applys_eq (CC_C_Po_pos_2 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPo (n + 1) (4 * m + 3))
        ltac:(applys_eq (CC_C_Po_pos_3 n m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (11 + 8 * n) with (S (10 + 8 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBe (n + 1) (n + 1) 2)
            ltac:(apply CC_C_Be_small2). }
        ih_by IH B (SPe (n + 1) (4 * (n + 1) + 3))
          ltac:(applys_eq (CC_B_Pe_odd n (2 * n + 3)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (11 + 8 * n) with (S (10 + 8 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBe (n + 1) (n + 1) (4 * m0 + 6))
            ltac:(applys_eq (CC_C_Be_top_6 n m0); flia). }
        ih_by IH B (SAo n m0 (14 + 8 * n))
          ltac:(applys_eq (CC_B_Ao_long_nonmax n m0 (4 * n + 5)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (12 + 8 * n) with (S (11 + 8 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) (n + 1) (4 * m + 3))
        ltac:(applys_eq (CC_C_Be_top_3 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (13 + 8 * n) with (S (12 + 8 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) (n + 1) (4 * m + 4))
        ltac:(applys_eq (CC_C_Be_top_4 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (14 + 8 * n) with (S (13 + 8 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) (n + 1) (4 * m + 5))
        ltac:(applys_eq (CC_C_Be_top_5 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * n + 7) with (S (4 * n + 6)) by flia.
    replace (4 * n + 1) with (S (4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH C (SBe (n + 1) (n + 1) (4 * n + 6))
          ltac:(applys_eq (CC_C_Be_top_6 n n); flia). }
      ih_by IH B (SAo n n (14 + 8 * n))
        ltac:(applys_eq (CC_B_Ao_long_diag_high n (2 * n)); flia).
    }
    Unshelve.
    all: esc.
Qed.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Transparent SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Definition Bcfg (h : Side) : Q * tape :=
  to_side h {{{ ((A, []), R) }}} const S0.

Lemma init_to_start :
  c0 -->* Bcfg (SBe 1 0 4).
Proof.
  apply without_counter with (n := 318).
  rewrite <- multistep_c_spec.
  unfold Bcfg.
  cbn [to_side].
  unfold Be, Bside, SkelE.
  vm_compute.
  repeat rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma ClosedCall_progress_any q s q' s' r :
  ClosedCall q s q' s' ->
  to_side s {{{ ((q, []), L) }}} r -->+
  to_side s' {{{ ((q', []), R) }}} r.
Proof.
  intro H.
  eapply sideRLs_1L.
  apply ClosedCall_sideRLs.
  exact H.
Qed.

Lemma A_to_B h :
  Bcfg h -->+ to_side h {{{ ((B, []), L) }}} (S1 >> const S0).
Proof.
  unfold Bcfg, tm.
  step1s.
Qed.

Lemma marker_D_to_A l :
  l {{{ ((D, []), R) }}} (S1 >> const S0) -->+
  S1 >> S1 >> S1 >> S1 >> l {{{ ((A, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma marker_D_tail4_Be n j b :
  to_side (SBe n j b) {{{ ((D, []), R) }}} (S1 >> const S0) -->+
  Bcfg (SBe n j (b + 4)).
Proof.
  unfold Bcfg.
  cbn [to_side].
  replace (b + 4) with (S (S (S (S b)))) by lia.
  repeat rewrite Be_succ_step.
  apply marker_D_to_A.
Qed.

Lemma marker_D_tail4_Bo n j b :
  to_side (SBo n j b) {{{ ((D, []), R) }}} (S1 >> const S0) -->+
  Bcfg (SBo n j (b + 4)).
Proof.
  unfold Bcfg.
  cbn [to_side].
  replace (b + 4) with (S (S (S (S b)))) by lia.
  repeat rewrite Bo_succ_step.
  apply marker_D_to_A.
Qed.

Lemma boundary_C0_to_A l :
  l {{{ ((C, []), R) }}} const S0 -->+
  S1 >> S1 >> S1 >> l {{{ ((A, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma boundary_C010_to_A l :
  l {{{ ((C, []), R) }}} (S0 >> S1 >> const S0) -->+
  S1 >> S1 >> S1 >> S1 >> S1 >> l {{{ ((A, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma boundary_E0 l :
  l {{{ ((D, []), R) }}} const S0 -->+
  S1 >> l {{{ ((E, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma boundary_F0 l :
  l {{{ ((C, []), R) }}} const S0 -->+
  S1 >> l {{{ ((D, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma marker1_A l :
  l {{{ ((E, []), R) }}} (S1 >> const S0) -->+
  S1 >> l {{{ ((F, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma marker1_F s s' :
  ClosedCall C s C s' ->
  to_side s {{{ ((C, []), R) }}} (S1 >> const S0) -->+
  to_side s' {{{ ((C, []), R) }}} const S0.
Proof.
  intro HC.
  eapply progress_trans.
  - unfold tm.
    step1s.
  - apply ClosedCall_progress_any.
    exact HC.
Qed.

Lemma boundary_E0_to_A l :
  l {{{ ((D, []), R) }}} const S0 -->+
  S1 >> S1 >> l {{{ ((A, []), R) }}} const S0.
Proof.
  eapply progress_trans.
  - apply boundary_E0.
  - unfold tm.
    step1s.
Qed.

Lemma boundary_F0_to_A l :
  l {{{ ((C, []), R) }}} const S0 -->+
  S1 >> S1 >> S1 >> l {{{ ((A, []), R) }}} const S0.
Proof.
  eapply progress_trans.
  - apply boundary_F0.
  - apply boundary_E0_to_A.
Qed.

Lemma Btail_F_to_A s s' :
  ClosedCall C s C s' ->
  to_side s {{{ ((C, []), R) }}} (S1 >> const S0) -->+
  S1 >> S1 >> S1 >> to_side s' {{{ ((A, []), R) }}} const S0.
Proof.
  intro HC.
  eapply progress_trans.
  - apply marker1_F.
    exact HC.
  - apply boundary_F0_to_A.
Qed.

Lemma boundary_F0_Pe4_to_A n k :
  to_side (SPe n (4 * k)) {{{ ((F, []), R) }}} const S0 -->+
  Bcfg (SBe n k 2).
Proof.
  unfold Bcfg.
  cbn [to_side].
  replace 2 with (S (S 0)) by lia.
  repeat rewrite Be_succ_step.
  rewrite Be_zero_step.
  eapply progress_trans.
  - unfold tm.
    step1s.
  - apply boundary_E0_to_A.
Qed.

Lemma boundary_F0_Po4_to_A n k :
  to_side (SPo n (4 * k)) {{{ ((F, []), R) }}} const S0 -->+
  Bcfg (SBo n k 2).
Proof.
  unfold Bcfg.
  cbn [to_side].
  replace 2 with (S (S 0)) by lia.
  repeat rewrite Bo_succ_step.
  rewrite Bo_zero_step.
  eapply progress_trans.
  - unfold tm.
    step1s.
  - apply boundary_E0_to_A.
Qed.

Lemma Be_diag_tail4_to_Po n :
  S1 >> to_side (SBe n 0 (4 * n + 5)) =
  to_side (SPo n 0).
Proof.
  cbn [to_side].
  replace (4 * n + 5) with (5 + 4 * n) by lia.
  rewrite <- Po_zero_step.
  reflexivity.
Qed.

Lemma Bo_diag_tail2_to_Pe n :
  S1 >> S1 >> S1 >> to_side (SBo n 0 (4 * n + 3)) =
  to_side (SPe (n + 1) 0).
Proof.
  cbn [to_side].
  replace (n + 1) with (S n) by lia.
  rewrite <- Bo_succ_step.
  rewrite <- Bo_succ_step.
  replace (S (S (4 * n + 3))) with (5 + 4 * n) by lia.
  rewrite <- Pe_succ_zero_step.
  reflexivity.
Qed.

Lemma SPe_succ_zero_as_Bo n :
  to_side (SPe (n + 1) 0) = to_side (SBo n 0 (6 + 4 * n)).
Proof.
  cbn [to_side].
  replace (n + 1) with (S n) by lia.
  rewrite Pe_succ_zero_step.
  replace (6 + 4 * n) with (S (5 + 4 * n)) by lia.
  rewrite Bo_succ_step.
  reflexivity.
Qed.

Lemma Bstep2_Bo_pos_tail2 n j :
  1 <= j ->
  j < n ->
  Bcfg (SBo n j 2) -->+
  Bcfg (SBo n (j + 1) 2).
Proof.
  intros Hj Hjn.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Bo_pos_tail2 n j); lia.
    + eapply progress_trans.
      * apply marker1_A.
      * cbn [to_side].
        rewrite <- Po_succ_step.
        replace (S (4 * j + 3)) with (4 * (j + 1)) by lia.
        apply boundary_F0_Po4_to_A.
Qed.

Lemma Bstep2_Bo0_tail2 n :
  Bcfg (SBo (n + 1) 0 2) -->+
  Bcfg (SBo (n + 1) 1 2).
Proof.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_B_Bo0_2.
    + eapply progress_trans.
      * apply marker1_A.
      * cbn [to_side].
        rewrite <- Po_succ_step.
        replace (S 3) with (4 * 1) by lia.
        apply boundary_F0_Po4_to_A.
Qed.

Lemma Bstep2_Be_diag_tail4 n :
  Bcfg (SBe n n 4) -->+
  Bcfg (SBo n 0 2).
Proof.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_B_Be_diag_tail4.
    + eapply progress_trans.
      * apply marker1_A.
      * rewrite Be_diag_tail4_to_Po.
        replace (to_side (SPo n 0)) with (to_side (SPo n (4 * 0))) by (f_equal; lia).
        apply boundary_F0_Po4_to_A.
Qed.

Lemma Bstep2_Bo_diag_tail2 n :
  Bcfg (SBo n n 2) -->+
  Bcfg (SBo n 0 (6 + 4 * n)).
Proof.
  replace (Bcfg (SBo n 0 (6 + 4 * n))) with (Bcfg (SPe (n + 1) 0)).
  - eapply progress_trans.
    + apply A_to_B.
    + eapply progress_trans.
      * apply ClosedCall_progress_any.
        apply CC_B_Bo_diag_tail2.
      * unfold Bcfg.
        rewrite <- Bo_diag_tail2_to_Pe.
        apply Btail_F_to_A.
        applys_eq (CC_C_Ae_special n n); lia.
  - unfold Bcfg.
    rewrite SPe_succ_zero_as_Bo.
    reflexivity.
Qed.

Lemma Bstep2_Be0_even_tail n k :
  k <= 2 * (n + 1) ->
  Bcfg (SBe (n + 1) 0 (2 * k + 4)) -->+
  Bcfg (SBe (n + 1) 1 (2 * k + 4)).
Proof.
  intro Hk.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Be0_even_tail n k); lia.
    + replace (2 * k + 4) with (2 * k + 4) by lia.
      apply marker_D_tail4_Be.
Qed.

Lemma Bstep2_Be_pos_long n j k :
  1 <= j ->
  j < n ->
  k <= 2 * n + 1 ->
  Bcfg (SBe n j (2 * k + 4)) -->+
  Bcfg (SBe n (j + 1) (2 * k + 4)).
Proof.
  intros Hj Hjn Hk.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Be_pos_long n j k); lia.
    + apply marker_D_tail4_Be.
Qed.

Lemma Bstep2_Be_diag_long_low n k :
  k <= 2 * n ->
  Bcfg (SBe n n (2 * k + 6)) -->+
  Bcfg (SBo n 0 (2 * k + 4)).
Proof.
  intro Hk.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Be_diag_long_low n k); lia.
    + apply marker_D_tail4_Bo.
Qed.

Lemma Bstep2_Bo0_even_tail n k :
  k <= 2 * (n + 1) ->
  Bcfg (SBo (n + 1) 0 (2 * k + 4)) -->+
  Bcfg (SBo (n + 1) 1 (2 * k + 4)).
Proof.
  intro Hk.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Bo0_even_tail n k); lia.
    + apply marker_D_tail4_Bo.
Qed.

Lemma Bstep2_Bo0_special n :
  1 <= n ->
  Bcfg (SBo n 0 (4 * n + 6)) -->+
  Bcfg (SBo n 1 (4 * n + 6)).
Proof.
  intro Hn.
  destruct n as [| n0].
  { lia. }
  eapply progress_trans.
  - apply A_to_B.
  - replace (4 * S n0 + 6) with (S (4 * S n0 + 5)) by lia.
    cbn [to_side].
    rewrite Bo_succ_step.
    eapply progress_trans.
    + unfold tm.
      step1s.
    + eapply progress_trans.
      * match goal with
        | |- ?lhs -->+ _ =>
            replace lhs with (to_side (SBo (S n0) 0 (2 * (2 * S n0) + 5))
              {{{ ((F, []), L) }}} (S0 >> S1 >> const S0))
        end.
        2:{
          cbn [to_side to_DH_config].
          unfold Bo, Bside.
          repeat rewrite lpow_add'.
          replace (2 * (2 * S n0) + 5)
            with (S (n0 + S (n0 + S (n0 + S (n0 + 0))) + 5)) by lia.
          cbn [lpow].
          reflexivity.
        }
        apply ClosedCall_progress_any.
        replace (S n0) with (n0 + 1) by lia.
        apply CC_F_Bo0_odd_tail.
        lia.
      * unfold Bcfg.
        replace (n0 + 1) with (S n0) by lia.
        cbn [to_side].
        replace (S (4 * S n0 + 5))
          with (S (S (S (S (S (2 * (2 * S n0) + 1)))))) by lia.
        repeat rewrite Bo_succ_step.
        apply boundary_C010_to_A.
Qed.

Lemma Bstep2_Bo_pos_long n j k :
  1 <= j ->
  j < n ->
  k <= 2 * n + 3 ->
  Bcfg (SBo n j (2 * k + 4)) -->+
  Bcfg (SBo n (j + 1) (2 * k + 4)).
Proof.
  intros Hj Hjn Hk.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Bo_pos_long n j k); lia.
    + apply marker_D_tail4_Bo.
Qed.

Lemma Bstep2_Bo_diag_long_low n k :
  k <= 2 * n + 2 ->
  Bcfg (SBo n n (2 * k + 6)) -->+
  Bcfg (SBe (n + 1) 0 (2 * k + 4)).
Proof.
  intro Hk.
  eapply progress_trans.
  - apply A_to_B.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_B_Bo_diag_long_low n k); lia.
    + apply marker_D_tail4_Be.
Qed.

Definition G2e (n : nat) : nat := 7 + 4 * n.
Definition G2o (n : nat) : nat := 7 + 4 * n.

Definition Bnext2 (h : Side) : Side :=
  match h with
  | SBe n j b =>
      if j <? n then SBe n (j + 1) b
      else if b =? 2 then SBe n 0 (G2e n - 1)
      else SBo n 0 (b - 2)
  | SBo n j b =>
      if j <? n then SBo n (j + 1) b
      else if b =? 2 then SBo n 0 (G2o n - 1)
      else SBe (n + 1) 0 (b - 2)
  | _ => h
  end.

Inductive Pow2 : nat -> Prop :=
| Pow2_1 : Pow2 1
| Pow2_double p : Pow2 p -> Pow2 (2 * p).

Lemma Pow2_even_or_one p :
  Pow2 p -> p = 1 \/ exists k, p = 2 * k.
Proof.
  intro H.
  inversion H; subst.
  - left. reflexivity.
  - right. exists p0. reflexivity.
Qed.

Definition Good2 (h : Side) : Prop :=
  match h with
  | SBe n j b =>
      exists p t,
        Pow2 p /\
        p <= 4 * n /\
        2 * n + t = p /\
        b = 2 * t /\
        j <= n /\
        1 <= t
  | SBo n j b =>
      (exists p t,
        Pow2 p /\
        1 <= n /\
        p <= 2 * (2 * n + 1) /\
        (2 * n + 1) + t = p /\
        b = 2 * t /\
        j <= n /\
        1 <= t) \/
      (Pow2 (2 * n + 2) /\
        1 <= n /\
        b = 4 * n + 6 /\
        j <= n)
  | _ => False
  end.

Lemma Good2_start :
  Good2 (SBe 1 0 4).
Proof.
  cbn [Good2].
  exists 4, 2.
  repeat split; try lia.
  change 4 with (2 * (2 * 1)).
  apply Pow2_double.
  change 2 with (2 * 1).
  apply Pow2_double.
  apply Pow2_1.
Qed.

Lemma Good2_next h :
  Good2 h ->
  Good2 (Bnext2 h).
Proof.
  destruct h as [| | n r | n r | n j b | n j b | n q b | n q b];
    cbn [Good2 Bnext2]; try contradiction.
  - intros (p & t & Hp & Hp_le & Hsum & Hb & Hj & Ht).
    destruct (j <? n) eqn:Hjlt.
    + apply Nat.ltb_lt in Hjlt.
      exists p, t.
      repeat split; try assumption; lia.
    + apply Nat.ltb_ge in Hjlt.
      assert (Hj_eq : j = n) by lia.
      subst j.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        assert (Ht1 : t = 1) by lia.
        subst t.
        destruct (Pow2_even_or_one _ Hp) as [Hp1 | [k Hk]].
        -- lia.
        -- lia.
      * apply Nat.eqb_neq in Hb2.
        left.
        exists p, (t - 1).
        repeat split; try assumption; try lia.
  - intros [(p & t & Hp & Hp_le & Hsum & Hb & Hj & Ht) |
            (Hp & Hb & Hj)].
    + destruct (j <? n) eqn:Hjlt.
      * apply Nat.ltb_lt in Hjlt.
        left.
        exists p, t.
        repeat split; try assumption; lia.
      * apply Nat.ltb_ge in Hjlt.
        assert (Hj_eq : j = n) by lia.
        subst j.
        destruct (b =? 2) eqn:Hb2.
        -- apply Nat.eqb_eq in Hb2.
           subst b.
           assert (Ht1 : t = 1) by lia.
           subst t.
           right.
           replace (2 * n + 2) with p by lia.
           unfold G2o.
           repeat split; try assumption; lia.
        -- apply Nat.eqb_neq in Hb2.
           exists p, (t - 1).
           repeat split; try assumption; try lia.
    + destruct (j <? n) eqn:Hjlt.
      * apply Nat.ltb_lt in Hjlt.
        right.
        repeat split; try assumption; lia.
      * apply Nat.ltb_ge in Hjlt.
        assert (Hj_eq : j = n) by lia.
        subst j.
        destruct (b =? 2) eqn:Hb2.
        -- apply Nat.eqb_eq in Hb2.
           lia.
        -- exists (2 * (2 * n + 2)), (2 * n + 2).
           repeat split; try lia.
           apply Pow2_double.
           exact Hp.
Qed.

Lemma Bstep2_Good h :
  Good2 h ->
  Bcfg h -->+ Bcfg (Bnext2 h).
Proof.
  destruct h as [| | n r | n r | n j b | n j b | n q b | n q b];
    cbn [Good2 Bnext2]; try contradiction.
  - intros (p & t & Hp & Hp_le & Hsum & Hb & Hj & Ht).
    destruct (j <? n) eqn:Hjlt.
    + apply Nat.ltb_lt in Hjlt.
      subst b.
      destruct j as [| j0].
      * destruct n as [| n0].
        { lia. }
        destruct t as [| [| k]].
        { lia. }
        { destruct (Pow2_even_or_one _ Hp) as [Hp1 | [u Hu]]; lia. }
        replace (2 * S (S k)) with (2 * k + 4) by lia.
        replace (0 + 1) with 1 by lia.
        replace (S n0) with (n0 + 1) by lia.
        apply Bstep2_Be0_even_tail.
        lia.
      * destruct t as [| [| k]].
        { lia. }
        { destruct (Pow2_even_or_one _ Hp) as [Hp1 | [u Hu]]; lia. }
        replace (2 * S (S k)) with (2 * k + 4) by lia.
        apply Bstep2_Be_pos_long; lia.
    + apply Nat.ltb_ge in Hjlt.
      assert (Hj_eq : j = n) by lia.
      subst j.
      subst b.
      destruct (2 * t =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        assert (Ht1 : t = 1) by lia.
        subst t.
        destruct (Pow2_even_or_one _ Hp) as [Hp1 | [u Hu]]; lia.
      * apply Nat.eqb_neq in Hb2.
        destruct t as [| [| [| k]]].
        { lia. }
        { lia. }
        { apply Bstep2_Be_diag_tail4. }
        replace (2 * S (S (S k))) with (2 * k + 6) by lia.
        replace (2 * k + 6 - 2) with (2 * k + 4) by lia.
        apply Bstep2_Be_diag_long_low.
        lia.
  - intros [(p & t & Hp & Hn1 & Hp_le & Hsum & Hb & Hj & Ht) |
            (Hp & Hn1 & Hb & Hj)].
    + destruct (j <? n) eqn:Hjlt.
      * apply Nat.ltb_lt in Hjlt.
        subst b.
        destruct t as [| [| k]].
        { lia. }
        -- destruct j as [| j0].
           ++ destruct n as [| n0].
              { lia. }
              replace (0 + 1) with 1 by lia.
              replace (S n0) with (n0 + 1) by lia.
              apply Bstep2_Bo0_tail2.
           ++ apply Bstep2_Bo_pos_tail2; lia.
        -- replace (2 * S (S k)) with (2 * k + 4) by lia.
           destruct j as [| j0].
           ++ destruct n as [| n0].
              { lia. }
              replace (0 + 1) with 1 by lia.
              replace (S n0) with (n0 + 1) by lia.
              apply Bstep2_Bo0_even_tail.
              lia.
           ++ apply Bstep2_Bo_pos_long; lia.
      * apply Nat.ltb_ge in Hjlt.
        assert (Hj_eq : j = n) by lia.
        subst j.
        subst b.
        destruct (2 * t =? 2) eqn:Hb2.
        -- apply Nat.eqb_eq in Hb2.
           assert (Ht1 : t = 1) by lia.
           subst t.
           apply Bstep2_Bo_diag_tail2.
        -- apply Nat.eqb_neq in Hb2.
           destruct t as [| [| [| k]]].
           ++ lia.
           ++ lia.
           ++ destruct (Pow2_even_or_one _ Hp) as [Hp1 | [u Hu]]; lia.
           ++ replace (2 * S (S (S k))) with (2 * k + 6) by lia.
              replace (2 * k + 6 - 2) with (2 * k + 4) by lia.
              apply Bstep2_Bo_diag_long_low.
              lia.
    + subst b.
      destruct (j <? n) eqn:Hjlt.
      * apply Nat.ltb_lt in Hjlt.
        destruct j as [| j0].
        -- replace (0 + 1) with 1 by lia.
           apply Bstep2_Bo0_special.
           lia.
        -- replace (4 * n + 6) with (2 * (2 * n + 1) + 4) by lia.
           apply Bstep2_Bo_pos_long; lia.
      * apply Nat.ltb_ge in Hjlt.
        assert (Hj_eq : j = n) by lia.
        subst j.
        destruct (4 * n + 6 =? 2) eqn:Hb2.
        -- apply Nat.eqb_eq in Hb2.
           lia.
        -- apply Nat.eqb_neq in Hb2.
           replace (4 * n + 6) with (2 * (2 * n) + 6) by lia.
           replace (2 * (2 * n) + 6 - 2) with (2 * (2 * n) + 4) by lia.
           apply Bstep2_Bo_diag_long_low.
           lia.
Qed.

Example start_is_candidate :
  Bnext2 (SBe 1 0 4) = SBe 1 1 4.
Proof. reflexivity. Qed.

Example candidate_wrap_even :
  Bnext2 (SBe 1 1 4) = SBo 1 0 2.
Proof. reflexivity. Qed.

Example candidate_top_odd :
  Bnext2 (SBo 1 1 2) = SBo 1 0 10.
Proof. reflexivity. Qed.

Example candidate_next_block :
  Bnext2 (SBo 1 1 10) = SBe 2 0 8.
Proof. reflexivity. Qed.

Theorem nonhalt :
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply init_to_start.
  - eapply progress_nonhalt_cond with
      (A := Side)
      (i0 := SBe 1 0 4)
      (C := Bcfg)
      (P := Good2).
    + intros h Hgood.
      exists (Bnext2 h).
      split.
      * apply Bstep2_Good.
        exact Hgood.
      * apply Good2_next.
        exact Hgood.
    + apply Good2_start.
Qed.
