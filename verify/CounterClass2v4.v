From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import List.
Require Import PeanoNat.
Require Import String.
Require Import Wf_nat.
Import ListNotations.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LA---_0RE1LD_0LF0LC_1RA1RF_1RE0LF").

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
  | D, SBe _ _ _ => 3
  | D, SBo _ _ _ => 3
  | C, SBe _ _ _ => 2
  | C, SBo _ _ _ => 2
  | F, SBe _ _ _ => 1
  | F, SBo _ _ _ => 1
  | F, SAe _ _ _ => 1
  | F, SAo _ _ _ => 1
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


Inductive ABeTail2N : nat -> Prop :=
| ABeTail2N_0 : ABeTail2N 0
| ABeTail2N_1 : ABeTail2N 1
| ABeTail2N_3 : ABeTail2N 3
| ABeTail2N_7 : ABeTail2N 7
| ABeTail2N_15 : ABeTail2N 15
| ABeTail2N_31 : ABeTail2N 31.

Inductive ClosedCall : Q -> Side -> Q -> Side -> Prop :=
| CC_A_Ae_full n q t :
    n <= 42 ->
    q <= n ->
    t <= 2 * n + 1 ->
    ClosedCall A (SAe n q (4 * t + 6)) C (SAe n q (4 * t + 6))
| CC_A_Ae_front q t :
    q + t <= 40 ->
    ClosedCall A (SAe 43 q (4 * t + 6)) C (SAe 43 q (4 * t + 6))
| CC_A_Ao_full n q t :
    n <= 41 ->
    q <= n ->
    t <= 2 * n + 2 ->
    ClosedCall A (SAo n q (4 * t + 6)) C (SAo n q (4 * t + 6))
| CC_A_Ao_front q t :
    q <= 42 ->
    q + t <= 84 ->
    ClosedCall A (SAo 42 q (4 * t + 6)) C (SAo 42 q (4 * t + 6))

| CC_A_Pe_odd_full n t :
    n <= 42 ->
    t <= n ->
    ClosedCall A (SPe n (4 * t + 3)) C (SPe n (4 * t + 3))
| CC_A_Pe_odd_front t :
    t <= 42 ->
    ClosedCall A (SPe 43 (4 * t + 3)) C (SPe 43 (4 * t + 3))
| CC_A_Pe_4 n :
    1 <= n ->
    n <= 43 ->
    ClosedCall A (SPe n 4) C (SPe n 4)
| CC_A_Po_0 n :
    n <= 42 ->
    ClosedCall A (SPo n 0) C (SPo n 0)
| CC_A_Po_odd n t :
    n <= 42 ->
    t <= n ->
    ClosedCall A (SPo n (4 * t + 3)) C (SPo n (4 * t + 3))

| CC_A_Be0_odd_tail n t :
    n <= 43 ->
    t <= n ->
    n + t <= 84 ->
    ClosedCall A (SBe n 0 (4 * t + 5)) C (SBe n 0 (4 * t + 5))
| CC_A_Be_tail2 n j :
    ABeTail2N n ->
    j <= n ->
    ClosedCall A (SBe n j 2) C (SBe n j 2)
| CC_A_Be_low_4 j :
    j <= 2 ->
    ClosedCall A (SBe 2 j 6) C (SBe 2 j 6)
| CC_A_Be_low_8 n d j :
    4 <= n ->
    1 <= d ->
    n + d + 1 = 8 ->
    j <= n ->
    ClosedCall A (SBe n j (4 * d + 2)) C (SBe n j (4 * d + 2))
| CC_A_Be_low_16 n d j :
    8 <= n ->
    1 <= d ->
    n + d + 1 = 16 ->
    j <= n ->
    ClosedCall A (SBe n j (4 * d + 2)) C (SBe n j (4 * d + 2))
| CC_A_Be_low_32 n d j :
    16 <= n ->
    1 <= d ->
    n + d + 1 = 32 ->
    j <= n ->
    ClosedCall A (SBe n j (4 * d + 2)) C (SBe n j (4 * d + 2))
| CC_A_Be_low_64 n d j :
    32 <= n ->
    n <= 42 ->
    n + d + 1 = 64 ->
    j <= n ->
    ClosedCall A (SBe n j (4 * d + 2)) C (SBe n j (4 * d + 2))
| CC_A_Be_low_64_front j :
    j <= 22 ->
    ClosedCall A (SBe 43 j 82) C (SBe 43 j 82)
| CC_A_Be_high n j :
    n <= 42 ->
    1 <= j ->
    j <= n ->
    ClosedCall A (SBe n j (4 * n + 6)) C (SBe n j (4 * n + 6))

| CC_A_Bo0_odd_tail n t :
    n <= 42 ->
    t <= n ->
    ClosedCall A (SBo n 0 (4 * t + 5)) C (SBo n 0 (4 * t + 5))
| CC_A_Bo_low_2 :
    ClosedCall A (SBo 0 0 4) C (SBo 0 0 4)
| CC_A_Bo_low_4 n d j :
    1 <= n ->
    1 <= d ->
    n + d + 1 = 4 ->
    j <= n ->
    ClosedCall A (SBo n j (4 * d)) C (SBo n j (4 * d))
| CC_A_Bo_low_8 n d j :
    3 <= n ->
    1 <= d ->
    n + d + 1 = 8 ->
    j <= n ->
    ClosedCall A (SBo n j (4 * d)) C (SBo n j (4 * d))
| CC_A_Bo_low_16 n d j :
    7 <= n ->
    1 <= d ->
    n + d + 1 = 16 ->
    j <= n ->
    ClosedCall A (SBo n j (4 * d)) C (SBo n j (4 * d))
| CC_A_Bo_low_32 n d j :
    15 <= n ->
    1 <= d ->
    n + d + 1 = 32 ->
    j <= n ->
    ClosedCall A (SBo n j (4 * d)) C (SBo n j (4 * d))
| CC_A_Bo_low_64 n d j :
    31 <= n ->
    n <= 42 ->
    n + d + 1 = 64 ->
    j <= n ->
    ClosedCall A (SBo n j (4 * d)) C (SBo n j (4 * d))
| CC_A_Bo_high n j :
    n <= 42 ->
    1 <= j ->
    j <= n ->
    ClosedCall A (SBo n j (4 * n + 10)) C (SBo n j (4 * n + 10))

| CC_D_Ao_zero n q :
    q <= n ->
    ClosedCall D (SAo n q 0) F (SAe n q (7 + 4 * n))
| CC_D_Ae_succ_zero n q :
    q <= n ->
    ClosedCall D (SAe (n + 1) q 0) F (SAo n q (7 + 4 * n))
| CC_D_Ae_succ_diag_zero n :
    ClosedCall D (SAe (n + 1) (n + 1) 0) F (SBe (n + 1) 0 (7 + 4 * n))
| CC_D_Ae_tail2 n q :
    q <= n ->
    ClosedCall D (SAe n q 2) A (SBe n 0 (4 * q + 5))
| CC_D_Ao_tail2 n q :
    q <= n ->
    ClosedCall D (SAo n q 2) A (SBo n 0 (4 * q + 5))
| CC_D_Ae_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 3 ->
    ClosedCall D (SAe n q (2 * k + 4)) E (SAe n (q + 1) (2 * k))
| CC_D_Ao_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 5 ->
    ClosedCall D (SAo n q (2 * k + 4)) E (SAo n (q + 1) (2 * k))
| CC_D_Ae_long_diag_low n k :
    k <= 2 * n + 2 ->
    ClosedCall D (SAe n n (2 * k + 4)) E (SBo n 0 (2 * k))
| CC_D_Ae_long_diag_high n s :
    s <= 2 * n ->
    ClosedCall D (SAe n n (2 * (2 * n + 3 + s) + 4)) E (SPe (n + 1) (2 * s))
| CC_D_Ao_long_diag_low n k :
    k <= 2 * n + 4 ->
    ClosedCall D (SAo n n (2 * k + 4)) E (SBe (n + 1) 0 (2 * k))
| CC_D_Ao_long_diag_high n s :
    s <= 2 * n ->
    ClosedCall D (SAo n n (2 * (2 * n + 5 + s) + 4)) E (SPo (n + 1) (2 * s))

| CC_D_Be0_0_succ n :
    ClosedCall D (SBe (n + 1) 0 0) F (SPe (n + 1) 1)
| CC_D_Bo_succ0_0 n :
    ClosedCall D (SBo (n + 1) 0 0) F (SBe (n + 1) 1 (7 + 4 * n))
| CC_D_Be0_1 n :
    ClosedCall D (SBe n 0 1) A (SBe n 0 1)
| CC_D_Bo0_1 n :
    ClosedCall D (SBo n 0 1) A (SBo n 0 1)
| CC_D_Be0_2_succ n :
    ClosedCall D (SBe (n + 1) 0 2) A (SPe (n + 1) 3)
| CC_D_Bo0_2 n :
    ClosedCall D (SBo (n + 1) 0 2) A (SPo (n + 1) 3)
| CC_D_Be0_odd_tail n k :
    k <= 2 * n + 1 ->
    ClosedCall D (SBe n 0 (2 * k + 3)) E (SAe n 0 (2 * k))
| CC_D_Bo0_odd_tail n k :
    k <= 2 * n + 1 ->
    ClosedCall D (SBo n 0 (2 * k + 3)) E (SAo n 0 (2 * k))
| CC_D_Be0_even_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall D (SBe (n + 1) 0 (2 * k + 4)) E (SBe (n + 1) 1 (2 * k))
| CC_D_Bo0_even_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall D (SBo (n + 1) 0 (2 * k + 4)) E (SBo (n + 1) 1 (2 * k))

| CC_D_Be_succ_pos_zero n j :
    1 <= j ->
    j < n + 1 ->
    ClosedCall D (SBe (n + 1) j 0) F (SBo n j (7 + 4 * n))
| CC_D_Be_diag_zero n :
    ClosedCall D (SBe n n 0) F (SBe n 0 (4 * n + 1))
| CC_D_Be_pos_tail2 n j :
    1 <= j ->
    j < n ->
    ClosedCall D (SBe n j 2) A (SPe n (4 * j + 3))
| CC_D_Be_diag_tail2 n :
    ClosedCall D (SBe n n 2) F (SBe n 0 (4 * n + 3))
| CC_D_Be_diag_tail4 n :
    ClosedCall D (SBe n n 4) A (SBe n 0 (4 * n + 5))
| CC_D_Be_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n + 1 ->
    ClosedCall D (SBe n j (2 * k + 4)) E (SBe n (j + 1) (2 * k))
| CC_D_Be_diag_long_low n k :
    k <= 2 * n ->
    ClosedCall D (SBe n n (2 * k + 6)) E (SBo n 0 (2 * k))
| CC_D_Bo_succ_pos_zero n j :
    1 <= j ->
    j < n + 1 ->
    ClosedCall D (SBo (n + 1) j 0) F (SBe (n + 1) (j + 1) (7 + 4 * n))
| CC_D_Bo_diag_zero n :
    ClosedCall D (SBo n n 0) F (SBo n 0 (4 * n + 1))
| CC_D_Bo_pos_tail2 n j :
    1 <= j ->
    j < n ->
    ClosedCall D (SBo n j 2) A (SPo n (4 * j + 3))
| CC_D_Bo_diag_tail2 n :
    ClosedCall D (SBo n n 2) F (SAe n n (7 + 4 * n))
| CC_D_Bo_diag_tail4 n :
    ClosedCall D (SBo n n 4) A (SBo n 0 (4 * n + 5))
| CC_D_Bo_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n + 3 ->
    ClosedCall D (SBo n j (2 * k + 4)) E (SBo n (j + 1) (2 * k))
| CC_D_Bo_diag_long_low n k :
    k <= 2 * n + 2 ->
    ClosedCall D (SBo n n (2 * k + 6)) E (SBe (n + 1) 0 (2 * k))

| CC_D_Pe_succ_even n k :
    k <= 2 ->
    ClosedCall D (SPe (n + 2) (2 * k)) E (SBo (n + 1) 1 (6 + 4 * n + 2 * k))
| CC_D_Pe_odd n k :
    k <= 2 * n + 3 ->
    ClosedCall D (SPe (n + 1) (2 * k + 1)) E (SAo n 0 (4 + 4 * n + 2 * k))
| CC_D_Po_even n k :
    k = 0 ->
    ClosedCall D (SPo (n + 1) (2 * k)) E (SBe (n + 1) 1 (6 + 4 * n + 2 * k))
| CC_D_Po_odd n k :
    k <= 2 * n + 1 ->
    ClosedCall D (SPo n (2 * k + 1)) E (SAe n 0 (4 + 4 * n + 2 * k))

| CC_C_Ae_1 n q :
    q <= n ->
    ClosedCall C (SAe n q 1) E (SBe n 0 (4 * q + 4))
| CC_C_Ao_1 n q :
    q <= n ->
    ClosedCall C (SAo n q 1) E (SBo n 0 (4 * q + 4))
| CC_C_Ae_3_nonmax n q :
    q < n ->
    ClosedCall C (SAe n q 3) C (SBe n 0 (4 * q + 6))
| CC_C_Ae_3_diag n :
    ClosedCall C (SAe n n 3) C (SPo n 0)
| CC_C_Ao_3_nonmax n q :
    q < n ->
    ClosedCall C (SAo n q 3) C (SBo n 0 (4 * q + 6))
| CC_C_Ao_3_diag n :
    ClosedCall C (SAo n n 3) C (SPe (n + 1) 0)
| CC_C_Ae_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 2 ->
    ClosedCall C (SAe n q (2 * k + 5)) F (SAe n (q + 1) (2 * k + 1))
| CC_C_Ao_long_nonmax n q k :
    q < n ->
    k <= 4 * n + 4 ->
    ClosedCall C (SAo n q (2 * k + 5)) F (SAo n (q + 1) (2 * k + 1))
| CC_C_Ae_long_diag_low n k :
    k <= 2 * n + 2 ->
    ClosedCall C (SAe n n (2 * k + 5)) F (SBo n 0 (2 * k + 1))
| CC_C_Ae_long_diag_high n s :
    s < 2 * n ->
    ClosedCall C (SAe n n (2 * (2 * n + 3 + s) + 5)) F (SPe (n + 1) (2 * s + 1))
| CC_C_Ao_long_diag_low n k :
    k <= 2 * n + 4 ->
    ClosedCall C (SAo n n (2 * k + 5)) F (SBe (n + 1) 0 (2 * k + 1))
| CC_C_Ao_long_diag_high n s :
    s < 2 * n ->
    ClosedCall C (SAo n n (2 * (2 * n + 5 + s) + 5)) F (SPo (n + 1) (2 * s + 1))

| CC_C_Be0_0 n :
    ClosedCall C (SBe n 0 0) E (SBe n 0 0)
| CC_C_Bo0_0 n :
    ClosedCall C (SBo n 0 0) E (SBo n 0 0)
| CC_C_Be0_1 n :
    ClosedCall C (SBe (n + 1) 0 1) E (SPe (n + 1) 2)
| CC_C_Bo0_1 n :
    ClosedCall C (SBo (n + 1) 0 1) E (SPo (n + 1) 2)
| CC_C_Be0_2 n :
    ClosedCall C (SBe n 0 2) C (SBe n 0 2)
| CC_C_Bo0_2 n :
    ClosedCall C (SBo n 0 2) C (SBo n 0 2)
| CC_C_Be0_3 n :
    ClosedCall C (SBe (n + 1) 0 3) C (SPe (n + 1) 4)
| CC_C_Bo0_3 n :
    ClosedCall C (SBo (n + 1) 0 3) C (SPo (n + 1) 4)
| CC_C_Be0_even_tail n k :
    k <= 2 * n ->
    ClosedCall C (SBe n 0 (2 * k + 4)) F (SAe n 0 (2 * k + 1))
| CC_C_Bo0_even_tail n k :
    k <= 2 * n ->
    ClosedCall C (SBo n 0 (2 * k + 4)) F (SAo n 0 (2 * k + 1))
| CC_C_Be0_odd_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall C (SBe (n + 1) 0 (2 * k + 5)) F (SBe (n + 1) 1 (2 * k + 1))
| CC_C_Bo0_odd_tail n k :
    k <= 2 * (n + 1) ->
    ClosedCall C (SBo (n + 1) 0 (2 * k + 5)) F (SBo (n + 1) 1 (2 * k + 1))

| CC_C_Be_pos_1 n j :
    1 <= j ->
    j < n ->
    ClosedCall C (SBe n j 1) E (SPe n (4 * j + 2))
| CC_C_Be_succ_diag_1 n :
    ClosedCall C (SBe (n + 1) (n + 1) 1) B (SAo n n (10 + 4 * n))
| CC_C_Be_pos_3 n j :
    1 <= j ->
    j < n ->
    ClosedCall C (SBe n j 3) C (SPe n (4 * j + 4))
| CC_C_Be_diag_3 n :
    ClosedCall C (SBe n n 3) E (SBe n 0 (4 * n + 4))
| CC_C_Be_diag_5 n :
    ClosedCall C (SBe n n 5) C (SPo n 0)
| CC_C_Be_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n ->
    ClosedCall C (SBe n j (2 * k + 5)) F (SBe n (j + 1) (2 * k + 1))
| CC_C_Be_diag_long_low n k :
    k < 2 * n ->
    ClosedCall C (SBe n n (2 * k + 7)) F (SBo n 0 (2 * k + 1))
| CC_C_Bo_pos_1 n j :
    1 <= j ->
    j < n ->
    ClosedCall C (SBo n j 1) E (SPo n (4 * j + 2))
| CC_C_Bo_succ_diag_1 n :
    ClosedCall C (SBo (n + 1) (n + 1) 1) B (SAe (n + 1) n (10 + 4 * (n + 1)))
| CC_C_Bo_pos_3 n j :
    1 <= j ->
    j < n ->
    ClosedCall C (SBo n j 3) C (SPo n (4 * j + 4))
| CC_C_Bo_diag_3 n :
    ClosedCall C (SBo n n 3) E (SBo n 0 (4 * n + 4))
| CC_C_Bo_diag_5 n :
    ClosedCall C (SBo n n 5) C (SPe (n + 1) 0)
| CC_C_Bo_pos_long n j k :
    1 <= j ->
    j < n ->
    k <= 2 * n + 2 ->
    ClosedCall C (SBo n j (2 * k + 5)) F (SBo n (j + 1) (2 * k + 1))
| CC_C_Bo_diag_long_low n k :
    k <= 2 * n + 1 ->
    ClosedCall C (SBo n n (2 * k + 7)) F (SBe (n + 1) 0 (2 * k + 1))

| CC_C_Pe_even n k :
    k <= 2 * n + 3 ->
    ClosedCall C (SPe (n + 1) (2 * k)) F (SAo n 0 (3 + 4 * n + 2 * k))
| CC_C_Pe_succ_odd n k :
    k <= 1 ->
    ClosedCall C (SPe (n + 2) (2 * k + 1)) F (SBo (n + 1) 1 (7 + 4 * n + 2 * k))
| CC_C_Po_even n k :
    k <= 2 * n + 1 ->
    ClosedCall C (SPo n (2 * k)) F (SAe n 0 (3 + 4 * n + 2 * k))

| CC_F_Ae_0 n q :
    q <= n ->
    ClosedCall F (SAe n q 0) E (SBe n 0 (4 * q + 3))
| CC_F_Ao_0 n q :
    q <= n ->
    ClosedCall F (SAo n q 0) E (SBo n 0 (4 * q + 3))
| CC_F_Ae_1 n q :
    q <= n ->
    ClosedCall F (SAe n q 1) A (SBe n 0 (4 * q + 4))
| CC_F_Ao_1 n q :
    q <= n ->
    ClosedCall F (SAo n q 1) A (SBo n 0 (4 * q + 4))
| CC_F_Ae_2 n q :
    q <= n ->
    ClosedCall F (SAe n q 2) B (SBe n 0 (4 * q + 5))
| CC_F_Ao_2 n q :
    q <= n ->
    ClosedCall F (SAo n q 2) B (SBo n 0 (4 * q + 5))
| CC_F_Ae_special n q :
    q <= n ->
    ClosedCall F (SAe n q (7 + 4 * n)) F (SBo n 0 (4 * q + 3))
| CC_F_Ao_special n q :
    q <= n ->
    ClosedCall F (SAo n q (7 + 4 * n)) F (SBe (n + 1) 0 (4 * q + 3))
| CC_F_Ae_tail_0 n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAe n q (4 * m + 4)) E (SAe n m (4 * q + 4))
| CC_F_Ao_tail_0 n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAo n q (4 * m + 4)) E (SAo n m (4 * q + 4))
| CC_F_Ae_tail_1 n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAe n q (4 * m + 5)) A (SAe n m (4 * q + 5))
| CC_F_Ao_tail_1 n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAo n q (4 * m + 5)) A (SAo n m (4 * q + 5))
| CC_F_Ae_tail_2 n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAe n q (4 * m + 6)) B (SAe n m (4 * q + 6))
| CC_F_Ao_tail_2 n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAo n q (4 * m + 6)) B (SAo n m (4 * q + 6))
| CC_F_Ae_tail_3_low n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAe n q (4 * m + 3)) F (SAe n m (4 * q + 3))
| CC_F_Ao_tail_3_low n q m :
    q <= n ->
    m <= n ->
    ClosedCall F (SAo n q (4 * m + 3)) F (SAo n m (4 * q + 3))

| CC_F_Be_small0 n j :
    ClosedCall F (SBe n j 0) E (SPe n (4 * j + 1))
| CC_F_Bo_small0 n j :
    ClosedCall F (SBo n j 0) E (SPo n (4 * j + 1))
| CC_F_Be_small1 n j :
    ClosedCall F (SBe n j 1) A (SPe n (4 * j + 2))
| CC_F_Bo_small1 n j :
    ClosedCall F (SBo n j 1) A (SPo n (4 * j + 2))
| CC_F_Be_small2 n j :
    ClosedCall F (SBe n j 2) B (SPe n (4 * j + 3))
| CC_F_Bo_small2 n j :
    ClosedCall F (SBo n j 2) B (SPo n (4 * j + 3))
| CC_F_Be_A_range_3 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBe (n + 1) j (4 * m + 3)) F (SAo n m (7 + 4 * n + 4 * j))
| CC_F_Be_A_range_4 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBe (n + 1) j (4 * m + 4)) E (SAo n m (8 + 4 * n + 4 * j))
| CC_F_Be_A_range_5 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBe (n + 1) j (4 * m + 5)) A (SAo n m (9 + 4 * n + 4 * j))
| CC_F_Be_A_range_6 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBe (n + 1) j (4 * m + 6)) B (SAo n m (10 + 4 * n + 4 * j))
| CC_F_Bo_A_range_3 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBo n j (4 * m + 3)) F (SAe n m (7 + 4 * n + 4 * j))
| CC_F_Bo_A_range_4 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBo n j (4 * m + 4)) E (SAe n m (8 + 4 * n + 4 * j))
| CC_F_Bo_A_range_5 n j m :
    j <= n ->
    m <= n ->
    ClosedCall F (SBo n j (4 * m + 5)) A (SAe n m (9 + 4 * n + 4 * j))
| CC_F_Bo_A_range_6 n j m :
    j <= n ->
    m <= n ->
    (m < n \/ 1 <= j) ->
    ClosedCall F (SBo n j (4 * m + 6)) B (SAe n m (10 + 4 * n + 4 * j))

| CC_F_Be_past_3_j0 n s :
    s = 0 ->
    ClosedCall F (SBe (n + 1) 0 (4 * (n + 1 + s) + 3)) F (SBe (n + 1) 0 (7 + 4 * n))
| CC_F_Be_past_3_jpos n j s :
    j + 1 <= n ->
    s = 0 ->
    ClosedCall F (SBe (n + 1) (j + 1) (4 * (n + 1 + s) + 3)) F (SPo (n + 1) (4 * j + 1))
| CC_F_Be_past_4_j0 n s :
    s = 0 ->
    ClosedCall F (SBe (n + 1) 0 (4 * (n + 1 + s) + 4)) E (SBe (n + 1) 0 (8 + 4 * n))
| CC_F_Be_past_5_j0 n s :
    s = 0 ->
    ClosedCall F (SBe (n + 1) 0 (4 * (n + 1 + s) + 5)) A (SBe (n + 1) 0 (9 + 4 * n))
| CC_F_Bo_past_3_jpos n j s :
    j + 1 <= n ->
    s = 0 ->
    ClosedCall F (SBo n (j + 1) (4 * (n + 1 + s) + 3)) F (SPe (n + 1) (4 * j + 5))

| CC_F_Pe_succ_0 n :
    ClosedCall F (SPe (n + 1) 0) B (SAe n n (10 + 4 * n))
| CC_F_Po_0 n :
    ClosedCall F (SPo n 0) B (SPo n 0)
| CC_F_Pe_1 n :
    1 <= n ->
    ClosedCall F (SPe n 1) F (SPe n 1)
| CC_F_Pe_2 n :
    1 <= n ->
    ClosedCall F (SPe n 2) E (SPe n 2)
| CC_F_Pe_3 n :
    1 <= n ->
    ClosedCall F (SPe n 3) A (SPe n 3)
| CC_F_Pe_4 n :
    1 <= n ->
    ClosedCall F (SPe n 4) B (SPe n 4)
| CC_F_Pe_large_1 n m :
    m < n ->
    ClosedCall F (SPe (n + 1) (4 * m + 5)) F (SBo n (m + 1) (7 + 4 * n))
| CC_F_Pe_large_2 n m :
    m < n ->
    ClosedCall F (SPe (n + 1) (4 * m + 6)) E (SBo n (m + 1) (8 + 4 * n))
| CC_F_Pe_large_3 n m :
    m < n ->
    ClosedCall F (SPe (n + 1) (4 * m + 7)) A (SBo n (m + 1) (9 + 4 * n))
| CC_F_Pe_large_4 n m :
    m < n ->
    ClosedCall F (SPe (n + 1) (4 * m + 8)) B (SBo n (m + 1) (10 + 4 * n))
| CC_F_Po_pos_1 n m :
    m <= n ->
    ClosedCall F (SPo (n + 1) (4 * m + 1)) F (SBe (n + 1) (m + 1) (7 + 4 * n))
| CC_F_Po_pos_2 n m :
    m <= n ->
    ClosedCall F (SPo (n + 1) (4 * m + 2)) E (SBe (n + 1) (m + 1) (8 + 4 * n))
| CC_F_Po_pos_3 n m :
    m <= n ->
    ClosedCall F (SPo (n + 1) (4 * m + 3)) A (SBe (n + 1) (m + 1) (9 + 4 * n))
| CC_F_Po_pos_4 n m :
    m <= n ->
    ClosedCall F (SPo (n + 1) (4 * m + 4)) B (SBe (n + 1) (m + 1) (10 + 4 * n))
| CC_F_Be_top_3 n m :
    m <= n ->
    ClosedCall F (SBe (n + 1) (n + 1) (4 * m + 3)) F (SAo n m (11 + 8 * n))
| CC_F_Be_top_4 n m :
    m <= n ->
    ClosedCall F (SBe (n + 1) (n + 1) (4 * m + 4)) E (SAo n m (12 + 8 * n))
| CC_F_Be_top_5 n m :
    m <= n ->
    ClosedCall F (SBe (n + 1) (n + 1) (4 * m + 5)) A (SAo n m (13 + 8 * n))
| CC_F_Be_top_6 n m :
    m <= n ->
    ClosedCall F (SBe (n + 1) (n + 1) (4 * m + 6)) B (SAo n m (14 + 8 * n))
| CC_F_Be_top_past_3 n :
    ClosedCall F (SBe (n + 1) (n + 1) (4 * n + 7)) F (SPo (n + 1) (4 * n + 1))

.

Transparent SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Lemma sideRLs_D_Bo0_1 :
  sideRLs (flip tm) [((C, []), (B, []))] (to_side (SBo 0 0 1)) (to_side (SPo 0 3)).
Proof.
  cbn [to_side].
  unfold Bo, Po, Bside, Pside, SkelO, SkelE.
  cbn.
  esc.
Qed.

Lemma sideRLs_D_Bo0_5 :
  sideRLs (flip tm) [((C, []), (C, []))] (to_side (SBo 0 0 5)) (to_side (SPe 1 0)).
Proof.
  cbn [to_side].
  unfold Bo, Pe, Bside, Pside, SkelO, SkelE.
  cbn.
  esc.
Qed.

Lemma sideRLs_E_keep_1 r :
  sideRLs (flip tm) [((E, []), (F, []))] (S1 >> r) (S1 >> r).
Proof.
  esx.
Qed.

Lemma sideRLs_F_0_to_1 r :
  sideRLs (flip tm) [((F, []), (E, []))] (S0 >> r) (S1 >> r).
Proof.
  esx.
Qed.

Lemma sideRLs_A_C_1 r :
  sideRLs (flip tm) [((A, []), (C, []))] (S1 >> r) (S1 >> r).
Proof.
  esx.
Qed.

Lemma sideRLs_A_C_SPe_succ n r :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SPe n (S r))) (to_side (SPe n (S r))).
Proof.
  repeat rewrite to_side_SPe_succ_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SPo_zero n :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SPo n 0)) (to_side (SPo n 0)).
Proof.
  repeat rewrite to_side_SPo_zero_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SPo_succ n r :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SPo n (S r))) (to_side (SPo n (S r))).
Proof.
  repeat rewrite to_side_SPo_succ_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SBe_succ n j b :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SBe n j (S b))) (to_side (SBe n j (S b))).
Proof.
  repeat rewrite to_side_SBe_succ_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SBo_succ n j b :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SBo n j (S b))) (to_side (SBo n j (S b))).
Proof.
  repeat rewrite to_side_SBo_succ_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SAe_succ n q b :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SAe n q (S b))) (to_side (SAe n q (S b))).
Proof.
  repeat rewrite to_side_SAe_succ_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SAo_succ n q b :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SAo n q (S b))) (to_side (SAo n q (S b))).
Proof.
  repeat rewrite to_side_SAo_succ_step.
  apply sideRLs_A_C_1.
Qed.

Lemma sideRLs_A_C_SPe_pos n r :
  1 <= r ->
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SPe n r)) (to_side (SPe n r)).
Proof.
  intros Hr.
  destruct r as [| r]; [lia | apply sideRLs_A_C_SPe_succ].
Qed.

Lemma sideRLs_A_C_SPo_any n r :
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SPo n r)) (to_side (SPo n r)).
Proof.
  destruct r as [| r].
  - apply sideRLs_A_C_SPo_zero.
  - apply sideRLs_A_C_SPo_succ.
Qed.

Lemma sideRLs_A_C_SBe_pos n j b :
  1 <= b ->
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SBe n j b)) (to_side (SBe n j b)).
Proof.
  intros Hb.
  destruct b as [| b]; [lia | apply sideRLs_A_C_SBe_succ].
Qed.

Lemma sideRLs_A_C_SBo_pos n j b :
  1 <= b ->
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SBo n j b)) (to_side (SBo n j b)).
Proof.
  intros Hb.
  destruct b as [| b]; [lia | apply sideRLs_A_C_SBo_succ].
Qed.

Lemma sideRLs_A_C_SAe_pos n q b :
  1 <= b ->
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SAe n q b)) (to_side (SAe n q b)).
Proof.
  intros Hb.
  destruct b as [| b]; [lia | apply sideRLs_A_C_SAe_succ].
Qed.

Lemma sideRLs_A_C_SAo_pos n q b :
  1 <= b ->
  sideRLs (flip tm) [((A, []), (C, []))]
    (to_side (SAo n q b)) (to_side (SAo n q b)).
Proof.
  intros Hb.
  destruct b as [| b]; [lia | apply sideRLs_A_C_SAo_succ].
Qed.

Ltac solve_A_C_positive :=
  first
    [ apply sideRLs_A_C_SPo_any
    | lazymatch goal with
      | |- sideRLs _ _ (to_side (SPe _ ?r)) _ =>
          eapply sideRLs_A_C_SPe_pos; flia
      | |- sideRLs _ _ (to_side (SPo _ ?r)) _ =>
          apply sideRLs_A_C_SPo_any
      | |- sideRLs _ _ (to_side (SBe _ _ ?b)) _ =>
          eapply sideRLs_A_C_SBe_pos; flia
      | |- sideRLs _ _ (to_side (SBo _ _ ?b)) _ =>
          eapply sideRLs_A_C_SBo_pos; flia
      | |- sideRLs _ _ (to_side (SAe _ _ ?b)) _ =>
          eapply sideRLs_A_C_SAe_pos; flia
      | |- sideRLs _ _ (to_side (SAo _ _ ?b)) _ =>
          eapply sideRLs_A_C_SAo_pos; flia
      end ].

Opaque SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.


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
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - solve_A_C_positive.
  - replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        destruct q2 as [| q0].
        { eapply sideRLs_trans.
          { eapply (IH (measure F (SBo n 0 2))).
            { unfold measure, side_measure, class_rank, skelO_measure.
              cbn [skelE_measure skelO_measure].
              flia. }
            { reflexivity. }
            { apply CC_F_Bo_small2. } }
          eapply sideRLs_trans.
          { solve_A_C_positive. }
          eapply (IH (measure D (SPo n 3))).
          { unfold measure, side_measure, class_rank, skelO_measure.
            cbn [skelE_measure skelO_measure].
            flia. }
          { flia. }
          { applys_eq (CC_D_Po_odd n 1); flia. } }
        { eapply sideRLs_trans.
          { eapply (IH (measure F (SBo n 0 (4 * q0 + 6)))).
            { unfold measure, side_measure, class_rank, skelO_measure.
              cbn [skelE_measure skelO_measure].
              flia. }
            { flia. }
            { applys_eq (CC_F_Bo_A_range_6 n 0 q0); flia. } }
          eapply sideRLs_trans.
          { solve_A_C_positive. }
          eapply (IH (measure D (SAe n q0 (10 + 4 * n)))).
          { unfold measure, side_measure, class_rank, skelO_measure.
            cbn [skelE_measure skelO_measure].
            flia. }
          { flia. }
          { applys_eq (CC_D_Ae_long_nonmax n q0 (2 * n + 3)); flia. } }
      }
      Unshelve.
      all: esc.
  - replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      destruct q2 as [| qn].
      { eapply sideRLs_trans.
        { ih_by IH F (SBe (n + 1) 0 (4 * 0 + 2))
            ltac:(apply CC_F_Be_small2). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPe (n + 1) (4 * 0 + 3))
          ltac:(applys_eq (CC_D_Pe_odd n 1); flia). }
      { eapply sideRLs_trans.
        { ih_by IH F (SBe (n + 1) 0 (4 * S qn + 2))
            ltac:(applys_eq (CC_F_Be_A_range_6 n 0 qn); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        eapply (IH (measure D (SAo n qn (10 + 4 * n)))).
        { measure_decr. }
        { flia. }
        { applys_eq (CC_D_Ao_long_nonmax n qn (2 * n + 3)); flia. } }
    }
    Unshelve.
    all: esc.
  - replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SBe (n + 1) 0 (4 * (n + 1) + 2))
          ltac:(applys_eq (CC_F_Be_A_range_6 n 0 n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAo n n (10 + 4 * n + 4 * 0))
        ltac:(applys_eq (CC_D_Ao_long_diag_low n (2 * n + 3)); flia).
    }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAe n q2 1) ltac:(apply CC_C_Ae_1; flia). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SAo n q2 1) ltac:(apply CC_C_Ao_1; flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAe_succ_step.
      rewrite to_side_SAe_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SAe n q2 3)
          ltac:(applys_eq (CC_C_Ae_3_nonmax n q2); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SAe n q2 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Ae_long_nonmax n q2 k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAo_succ_step.
      rewrite to_side_SAo_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SAo n q2 3)
          ltac:(applys_eq (CC_C_Ao_3_nonmax n q2); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SAo n q2 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Ao_long_nonmax n q2 k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAe_succ_step.
      rewrite to_side_SBo_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SAe n n 3) ltac:(apply CC_C_Ae_3_diag). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SAe n n (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Ae_long_diag_low n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * (2 * n + 3 + s2) + 4) with
      (S (2 * (2 * n + 3 + s2) + 3)) by flia.
    rewrite to_side_SAe_succ_step.
    destruct s2 as [| s0].
    { replace (n + 1) with (S n) by flia.
      rewrite to_side_SPe_succ_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SAe n n (2 * (2 * n + 3 + 0) + 3))
          ltac:(applys_eq (CC_C_Ae_long_diag_low n (2 * n + 2)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S s0) with (S (2 * s0 + 1)) by flia.
      rewrite to_side_SPe_succ_step.
      split_sideRLs_concat.
      { ih_by IH C (SAe n n (2 * (2 * n + 3 + S s0) + 3))
          ltac:(applys_eq (CC_C_Ae_long_diag_high n s0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SAo_succ_step.
      rewrite to_side_SBe_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SAo n n 3) ltac:(apply CC_C_Ao_3_diag). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SAo n n (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Ao_long_diag_low n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * (2 * n + 5 + s2) + 4) with
      (S (2 * (2 * n + 5 + s2) + 3)) by flia.
    rewrite to_side_SAo_succ_step.
    destruct s2 as [| s0].
    { rewrite to_side_SPo_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SAo n n (2 * (2 * n + 5 + 0) + 3))
          ltac:(applys_eq (CC_C_Ao_long_diag_low n (2 * n + 4)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S s0) with (S (2 * s0 + 1)) by flia.
      rewrite to_side_SPo_succ_step.
      split_sideRLs_concat.
      { ih_by IH C (SAo n n (2 * (2 * n + 5 + S s0) + 3))
          ltac:(applys_eq (CC_C_Ao_long_diag_high n s0); flia). }
      Unshelve.
      all: esc. }
  - rewrite to_side_SBe_zero_step.
    replace 1 with (S 0) by flia.
    rewrite to_side_SPe_succ_step.
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SPe (n + 1) 0) ltac:(apply CC_F_Pe_succ_0). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAe n n (10 + 4 * n))
        ltac:(applys_eq (CC_D_Ae_long_diag_high n 0); flia).
    }
    Unshelve.
    all: esc.
  - rewrite to_side_SBo_zero_step.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SPo (n + 1) 0) ltac:(apply CC_F_Po_0). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SPo (n + 1) 0)
        ltac:(applys_eq (CC_D_Po_even n 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    { ih_by IH C (SBe n 0 0) ltac:(apply CC_C_Be0_0). }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    rewrite to_side_SBo_succ_step.
    split_sideRLs_concat.
    { ih_by IH C (SBo n 0 0) ltac:(apply CC_C_Bo0_0). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace 3 with (S 2) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe (n + 1) 0 1) ltac:(apply CC_C_Be0_1). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace 3 with (S 2) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo (n + 1) 0 1) ltac:(apply CC_C_Bo0_1). }
    Unshelve.
    all: esc.
  - replace (2 * k + 3) with (S (2 * k + 2)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SBe_succ_step.
      rewrite to_side_SAe_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SBe n 0 2) ltac:(apply CC_C_Be0_2). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SBe n 0 (S (2 * k0 + 1) + 2))
          ltac:(applys_eq (CC_C_Be0_even_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 3) with (S (2 * k + 2)) by flia.
    destruct k as [| k0].
    { rewrite to_side_SBo_succ_step.
      rewrite to_side_SAo_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SBo n 0 2) ltac:(apply CC_C_Bo0_2). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SBo n 0 (S (2 * k0 + 1) + 2))
          ltac:(applys_eq (CC_C_Bo0_even_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite to_side_SBe_succ_step.
    destruct k as [| k0].
    { rewrite to_side_SBe_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SBe (n + 1) 0 3) ltac:(apply CC_C_Be0_3). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite to_side_SBe_succ_step.
      split_sideRLs_concat.
      { ih_by IH C (SBe (n + 1) 0 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Be0_odd_tail n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite to_side_SBo_succ_step.
    destruct k as [| k0].
    { rewrite to_side_SBo_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SBo (n + 1) 0 3) ltac:(apply CC_C_Bo0_3). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite to_side_SBo_succ_step.
      split_sideRLs_concat.
      { ih_by IH C (SBo (n + 1) 0 (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Bo0_odd_tail n k0); flia). }
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
        { ih_by IH F (SPe (S n0 + 1) 4)
            ltac:(applys_eq (CC_F_Pe_4 (S n0 + 1)); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPe (S n0 + 1) 4)
          ltac:(applys_eq (CC_D_Pe_succ_even n0 2); flia). }
      { eapply sideRLs_trans.
        { ih_by IH F (SPe (n + 1) (4 * S (S j0)))
            ltac:(applys_eq (CC_F_Pe_large_4 n j0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBo n (j0 + 1) (10 + 4 * n))
          ltac:(applys_eq (CC_D_Bo_pos_long n (j0 + 1) (2 * n + 3)); flia). }
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
        { ih_by IH F (SPe (S (S n0)) (4 * S (S n0)))
            ltac:(applys_eq (CC_F_Pe_large_4 (n0 + 1) n0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBo (n0 + 1) (n0 + 1) (10 + 4 * (n0 + 1)))
          ltac:(applys_eq (CC_D_Bo_diag_long_low (n0 + 1) (2 * (n0 + 1) + 2)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe n j 1)
        ltac:(apply CC_C_Be_pos_1; flia). }
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
        { ih_by IH C (SBe (S n0) (S n0) 1)
            ltac:(applys_eq (CC_C_Be_succ_diag_1 n0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAo n0 n0 (10 + 4 * n0))
          ltac:(applys_eq (CC_D_Ao_long_diag_low n0 (2 * n0 + 3)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 4 with (S 3) by flia.
    replace (4 * n + 5) with (S (4 * n + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBe n n 3) ltac:(apply CC_C_Be_diag_3). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite (to_side_SBe_succ_step n j (2 * k + 3)).
    destruct k as [| k0].
    { rewrite to_side_SBe_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SBe n j 3)
          ltac:(applys_eq (CC_C_Be_pos_3 n j); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite (to_side_SBe_succ_step n (j + 1) (2 * k0 + 1)).
      split_sideRLs_concat.
      { ih_by IH C (SBe n j (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Be_pos_long n j k0); flia). }
      Unshelve.
      all: esc. }
  - destruct k as [| k0].
    { replace (2 * 0 + 6) with (S 5) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SBe n n 5) ltac:(apply CC_C_Be_diag_5). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0 + 6) with (S (2 * k0 + 7)) by flia.
      replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SBe n n (2 * k0 + 7))
          ltac:(applys_eq (CC_C_Be_diag_long_low n k0); flia). }
      Unshelve.
      all: esc. }
  - rewrite to_side_SBo_zero_step.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SPo (n + 1) (4 * j))
          ltac:(applys_eq (CC_F_Po_pos_4 n (j - 1)); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SBe (n + 1) (j - 1 + 1) (10 + 4 * n))
        ltac:(applys_eq (CC_D_Be_pos_long (n + 1) j (2 * n + 3)); flia).
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
        { ih_by IH F (SPo (S n0) (4 * S n0))
            ltac:(applys_eq (CC_F_Po_pos_4 n0 n0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBe (n0 + 1) (n0 + 1) (10 + 4 * n0))
          ltac:(applys_eq (CC_D_Be_diag_long_low (S n0) (2 * S n0)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n j 1)
        ltac:(apply CC_C_Bo_pos_1; flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { replace 2 with (S 1) by flia.
      replace (7 + 4 * 0) with (S 6) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { apply sideRLs_D_Bo0_1. }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPo 0 3) ltac:(applys_eq (CC_D_Po_odd 0 1); flia).
      }
      Unshelve.
      all: esc. }
    { replace 2 with (S 1) by flia.
      replace (7 + 4 * S n0) with (S (6 + 4 * S n0)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH C (SBo (S n0) (S n0) 1)
            ltac:(applys_eq (CC_C_Bo_succ_diag_1 n0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAe (n0 + 1) n0 (10 + 4 * (n0 + 1)))
          ltac:(applys_eq (CC_D_Ae_long_nonmax (S n0) n0 (2 * n0 + 5)); flia).
      }
      Unshelve.
      all: esc. }
  - replace 4 with (S 3) by flia.
    replace (4 * n + 5) with (S (4 * n + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SBo n n 3) ltac:(apply CC_C_Bo_diag_3). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    rewrite (to_side_SBo_succ_step n j (2 * k + 3)).
    destruct k as [| k0].
    { rewrite to_side_SBo_zero_step.
      split_sideRLs_concat.
      { ih_by IH C (SBo n j 3)
          ltac:(applys_eq (CC_C_Bo_pos_3 n j); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      rewrite (to_side_SBo_succ_step n (j + 1) (2 * k0 + 1)).
      split_sideRLs_concat.
      { ih_by IH C (SBo n j (S (2 * k0 + 1) + 3))
          ltac:(applys_eq (CC_C_Bo_pos_long n j k0); flia). }
      Unshelve.
      all: esc. }
  - destruct k as [| k0].
    { replace (2 * 0 + 6) with (S 5) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SBo n n 5) ltac:(apply CC_C_Bo_diag_5). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0 + 6) with (S (2 * k0 + 7)) by flia.
      replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SBo n n (2 * k0 + 7))
          ltac:(applys_eq (CC_C_Bo_diag_long_low n k0); flia). }
      Unshelve.
      all: esc. }
  - destruct k as [| k0].
    { replace (n + 2) with (S (n + 1)) by flia.
      replace (6 + 4 * n + 2 * 0) with (S (5 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      { eapply (IH (measure C (SBo (n + 1) 0 (5 + 4 * (n + 1))))).
        { replace (n + 2) with (S (n + 1)) by flia; measure_decr. }
        { flia. }
        { applys_eq (CC_C_Bo0_odd_tail n (2 * n + 2)); flia. } }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      replace (6 + 4 * n + S (2 * k0 + 1)) with (S (7 + 4 * n + 2 * k0)) by flia.
      normalize_split_sideRLs_concat.
      { ih_by IH C (SPe (n + 2) (2 * k0 + 1))
          ltac:(applys_eq (CC_C_Pe_succ_odd n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 1) with (S (2 * k)) by flia.
    replace (4 + 4 * n + 2 * k) with (S (3 + 4 * n + 2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPe (n + 1) (2 * k))
        ltac:(applys_eq (CC_C_Pe_even n k); flia). }
    Unshelve.
    all: esc.
  - replace (n + 1) with (S n) by flia.
    replace (6 + 4 * n) with (S (5 + 4 * n)) by flia.
    rewrite to_side_SPo_zero_step.
    replace (S (5 + 4 * n) + 2 * 0) with (S (5 + 4 * n)) by flia.
    rewrite to_side_SBe_succ_step.
    split_sideRLs_concat.
    { ih_by IH C (SBe (S n) 0 (5 + 4 * S n))
        ltac:(applys_eq (CC_C_Be0_odd_tail n (2 * n + 2)); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 1) with (S (2 * k)) by flia.
    replace (4 + 4 * n + 2 * k) with (S (3 + 4 * n + 2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH C (SPo n (2 * k))
        ltac:(applys_eq (CC_C_Po_even n k); flia). }
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
        { ih_by IH D (SAe (S n0) (S n0) 0)
            ltac:(applys_eq (CC_D_Ae_succ_diag_zero n0); flia). }
        ih_by IH F (SBe (n0 + 1) 0 (7 + 4 * n0))
          ltac:(applys_eq (CC_F_Be_past_3_j0 n0 0); flia). }
      { eapply sideRLs_trans.
        { ih_by IH D (SAe (S n0) q2 0)
            ltac:(applys_eq (CC_D_Ae_succ_zero n0 q2); flia). }
        ih_by IH F (SAo n0 q2 (7 + 4 * n0))
          ltac:(applys_eq (CC_F_Ao_special n0 q2); flia). }
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH D (SAo n q2 0)
          ltac:(applys_eq (CC_D_Ao_zero n q2); flia). }
      ih_by IH F (SAe n q2 (7 + 4 * n))
        ltac:(applys_eq (CC_F_Ae_special n q2); flia).
    }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAe n q2 2)
        ltac:(apply CC_D_Ae_tail2; flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAe n n 2)
        ltac:(applys_eq (CC_D_Ae_tail2 n n); flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAo n q2 2)
        ltac:(apply CC_D_Ao_tail2; flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SAo_succ_step n n 2).
    replace (n + 1) with (S n) by flia.
    rewrite to_side_SPe_succ_zero_step.
    split_sideRLs_concat.
    { ih_by IH D (SAo n n 2)
        ltac:(applys_eq (CC_D_Ao_tail2 n n); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAe n q2 (2 * k + 4))
        ltac:(applys_eq (CC_D_Ae_long_nonmax n q2 k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAo n q2 (2 * k + 4))
        ltac:(applys_eq (CC_D_Ao_long_nonmax n q2 k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAe n n (2 * k + 4))
        ltac:(applys_eq (CC_D_Ae_long_diag_low n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * (2 * n + 3 + s2) + 5) with (S (2 * (2 * n + 3 + s2) + 4)) by flia.
    replace (2 * s2 + 1) with (S (2 * s2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAe n n (2 * (2 * n + 3 + s2) + 4))
        ltac:(applys_eq (CC_D_Ae_long_diag_high n s2); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAo n n (2 * k + 4))
        ltac:(applys_eq (CC_D_Ao_long_diag_low n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * (2 * n + 5 + s2) + 5) with (S (2 * (2 * n + 5 + s2) + 4)) by flia.
    replace (2 * s2 + 1) with (S (2 * s2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SAo n n (2 * (2 * n + 5 + s2) + 4))
        ltac:(applys_eq (CC_D_Ao_long_diag_high n s2); flia). }
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
      { ih_by IH D (SBe (n + 1) 0 0)
          ltac:(applys_eq (CC_D_Be0_0_succ n); flia). }
      ih_by IH F (SPe (n + 1) 1)
        ltac:(applys_eq (CC_F_Pe_1 (n + 1)); flia).
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
      { ih_by IH D (SBo (S n0 + 1) 0 0)
          ltac:(applys_eq (CC_D_Bo_succ0_0 (S n0)); flia). }
      ih_by IH F (SBe (S n0 + 1) 1 (7 + 4 * S n0))
        ltac:(applys_eq (CC_F_Be_past_3_jpos (S n0) 0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    rewrite (to_side_SBe_succ_step n 0 1).
    split_sideRLs_concat.
    { ih_by IH D (SBe n 0 1)
        ltac:(apply CC_D_Be0_1). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    rewrite (to_side_SBo_succ_step n 0 1).
    split_sideRLs_concat.
    { ih_by IH D (SBo n 0 1)
        ltac:(apply CC_D_Bo0_1). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SBe_succ_step (n + 1) 0 2).
    replace 4 with (S 3) by flia.
    rewrite (to_side_SPe_succ_step (n + 1) 3).
    split_sideRLs_concat.
    { ih_by IH D (SBe (n + 1) 0 2)
        ltac:(apply CC_D_Be0_2_succ). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SBo_succ_step (n + 1) 0 2).
    replace 4 with (S 3) by flia.
    rewrite (to_side_SPo_succ_step (n + 1) 3).
    split_sideRLs_concat.
    { ih_by IH D (SBo (n + 1) 0 2)
        ltac:(apply CC_D_Bo0_2). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBe n 0 (2 * k + 3))
        ltac:(applys_eq (CC_D_Be0_odd_tail n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 4) with (S (2 * k + 3)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBo n 0 (2 * k + 3))
        ltac:(applys_eq (CC_D_Bo0_odd_tail n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBe (n + 1) 0 (2 * k + 4))
        ltac:(applys_eq (CC_D_Be0_even_tail n k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBo (n + 1) 0 (2 * k + 4))
        ltac:(applys_eq (CC_D_Bo0_even_tail n k); flia). }
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
    { ih_by IH D (SBe (S n0) (S j0) 0)
          ltac:(applys_eq (CC_D_Be_succ_pos_zero n0 (S j0)); flia). }
      ih_by IH F (SBo n0 (S j0) (7 + 4 * n0))
        ltac:(applys_eq (CC_F_Bo_past_3_jpos n0 j0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    replace (n + 1) with (S n) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH D (SBe (S n) (S n) 0)
          ltac:(applys_eq (CC_D_Be_diag_zero (S n)); flia). }
      ih_by IH F (SBe (S n) 0 (4 * S n + 1))
        ltac:(applys_eq (CC_F_Be_A_range_5 n 0 n); flia).
    }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * j + 4) with (S (4 * j + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBe n j 2)
        ltac:(apply CC_D_Be_pos_tail2; flia). }
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
      { ih_by IH D (SBe (S n0) (S n0) 2)
          ltac:(applys_eq (CC_D_Be_diag_tail2 (S n0)); flia). }
      ih_by IH F (SBe (S n0) 0 (4 * S n0 + 3))
        ltac:(applys_eq (CC_F_Be_past_3_j0 n0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 5 with (S 4) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBe n n 4)
        ltac:(applys_eq (CC_D_Be_diag_tail4 n); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBe n j (2 * k + 4))
        ltac:(applys_eq (CC_D_Be_pos_long n j k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 7) with (S (2 * k + 6)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBe n n (2 * k + 6))
        ltac:(applys_eq (CC_D_Be_diag_long_low n k); flia). }
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
      { ih_by IH D (SBo (S n0) (S j0) 0)
          ltac:(applys_eq (CC_D_Bo_succ_pos_zero n0 (S j0)); flia). }
      destruct (Nat.eq_dec (S j0) n0) as [Htop | Hntop].
      { subst n0.
        ih_by IH F (SBe (S j0 + 1) (S j0 + 1) (7 + 4 * S j0))
          ltac:(applys_eq (CC_F_Be_top_past_3 (S j0)); flia). }
      ih_by IH F (SBe (n0 + 1) (S j0 + 1) (7 + 4 * n0))
        ltac:(applys_eq (CC_F_Be_past_3_jpos n0 (S j0) 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (10 + 4 * (n + 1)) with (S (9 + 4 * (n + 1))) by flia.
    replace (n + 1) with (S n) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH D (SBo (S n) (S n) 0)
          ltac:(applys_eq (CC_D_Bo_diag_zero (S n)); flia). }
      ih_by IH F (SBo (S n) 0 (4 * S n + 1))
        ltac:(applys_eq (CC_F_Bo_A_range_5 (S n) 0 n); flia).
    }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    replace (4 * j + 4) with (S (4 * j + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBo n j 2)
        ltac:(apply CC_D_Bo_pos_tail2; flia). }
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
      { ih_by IH D (SBo (S n0) (S n0) 2)
          ltac:(applys_eq (CC_D_Bo_diag_tail2 (S n0)); flia). }
      ih_by IH F (SAe (S n0) (S n0) (7 + 4 * S n0))
        ltac:(applys_eq (CC_F_Ae_special (S n0) (S n0)); flia).
    }
    Unshelve.
    all: esc.
  - replace 5 with (S 4) by flia.
    rewrite (to_side_SBo_succ_step n n 4).
    replace (n + 1) with (S n) by flia.
    rewrite to_side_SPe_succ_zero_step.
    split_sideRLs_concat.
    { ih_by IH D (SBo n n 4)
        ltac:(applys_eq (CC_D_Bo_diag_tail4 n); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 5) with (S (2 * k + 4)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBo n j (2 * k + 4))
        ltac:(applys_eq (CC_D_Bo_pos_long n j k); flia). }
    Unshelve.
    all: esc.
  - replace (2 * k + 7) with (S (2 * k + 6)) by flia.
    replace (2 * k + 1) with (S (2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SBo n n (2 * k + 6))
        ltac:(applys_eq (CC_D_Bo_diag_long_low n k); flia). }
    Unshelve.
    all: esc.
  - destruct k as [| k0].
    { replace (n + 1) with (S n) by flia.
      rewrite to_side_SPe_succ_zero_step.
      replace (3 + 4 * n + 2 * 0) with (S (2 + 4 * n)) by flia.
      rewrite (to_side_SAo_succ_step n 0 (2 + 4 * n)).
      split_sideRLs_concat.
      { ih_by IH D (SBo n 0 (5 + 4 * n))
          ltac:(applys_eq (CC_D_Bo0_odd_tail n (2 * n + 1)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      replace (3 + 4 * n + 2 * S k0) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SPe_succ_step (n + 1) (2 * k0 + 1)).
      replace (3 + 4 * n + S (2 * k0 + 1)) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SAo_succ_step n 0 (4 + 4 * n + 2 * k0)).
      split_sideRLs_concat.
      { ih_by IH D (SPe (n + 1) (2 * k0 + 1))
          ltac:(applys_eq (CC_D_Pe_odd n k0); flia). }
      Unshelve.
      all: esc. }
  - replace (2 * k + 1) with (S (2 * k)) by flia.
    replace (7 + 4 * n + 2 * k) with (S (6 + 4 * n + 2 * k)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH D (SPe (n + 2) (2 * k))
        ltac:(applys_eq (CC_D_Pe_succ_even n k); flia). }
    Unshelve.
    all: esc.
  - destruct k as [| k0].
    { rewrite to_side_SPo_zero_step.
      replace (3 + 4 * n + 2 * 0) with (S (2 + 4 * n)) by flia.
      rewrite (to_side_SAe_succ_step n 0 (2 + 4 * n)).
      split_sideRLs_concat.
      { ih_by IH D (SBe n 0 (5 + 4 * n))
          ltac:(applys_eq (CC_D_Be0_odd_tail n (2 * n + 1)); flia). }
      Unshelve.
      all: esc. }
    { replace (2 * S k0) with (S (2 * k0 + 1)) by flia.
      replace (3 + 4 * n + 2 * S k0) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SPo_succ_step n (2 * k0 + 1)).
      replace (3 + 4 * n + S (2 * k0 + 1)) with (S (4 + 4 * n + 2 * k0)) by flia.
      rewrite (to_side_SAe_succ_step n 0 (4 + 4 * n + 2 * k0)).
      split_sideRLs_concat.
      { ih_by IH D (SPo n (2 * k0 + 1))
          ltac:(applys_eq (CC_D_Po_odd n k0); flia). }
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
    { ih_by IH F (SAe n q2 0) ltac:(applys_eq (CC_F_Ae_0 n q2); flia). }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAo n q2 0) ltac:(applys_eq (CC_F_Ao_0 n q2); flia). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAe n q2 1) ltac:(applys_eq (CC_F_Ae_1 n q2); flia). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAo n q2 1) ltac:(applys_eq (CC_F_Ao_1 n q2); flia). }
    Unshelve.
    all: esc.
  - replace (7 + 4 * n) with (S (4 * n + 6)) by flia.
    replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SAe n q2 (4 * n + 6))
          ltac:(applys_eq (CC_F_Ae_tail_2 n q2 n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAe n n (4 * q2 + 6))
        ltac:(applys_eq (CC_D_Ae_long_diag_low n (2 * q2 + 1)); flia).
    }
    Unshelve.
    all: esc.
  - replace (7 + 4 * n) with (S (4 * n + 6)) by flia.
    replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SAo n q2 (4 * n + 6))
          ltac:(applys_eq (CC_F_Ao_tail_2 n q2 n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAo n n (4 * q2 + 6))
        ltac:(applys_eq (CC_D_Ao_long_diag_low n (2 * q2 + 1)); flia).
    }
    Unshelve.
    all: esc.
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAe n q2 (4 * m + 3))
        ltac:(applys_eq (CC_F_Ae_tail_3_low n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (4 * q2 + 4) with (S (4 * q2 + 3)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAo n q2 (4 * m + 3))
        ltac:(applys_eq (CC_F_Ao_tail_3_low n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAe n q2 (4 * m + 4))
        ltac:(applys_eq (CC_F_Ae_tail_0 n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (4 * q2 + 5) with (S (4 * q2 + 4)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAo n q2 (4 * m + 4))
        ltac:(applys_eq (CC_F_Ao_tail_0 n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAe n q2 (4 * m + 5))
        ltac:(applys_eq (CC_F_Ae_tail_1 n q2 m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (4 * q2 + 6) with (S (4 * q2 + 5)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SAo n q2 (4 * m + 5))
        ltac:(applys_eq (CC_F_Ao_tail_1 n q2 m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SAe n q2 2)
            ltac:(applys_eq (CC_F_Ae_2 n q2); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBe n 0 (4 * q2 + 5))
          ltac:(applys_eq (CC_D_Be0_odd_tail n (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SAe n q2 (4 * m0 + 6))
            ltac:(applys_eq (CC_F_Ae_tail_2 n q2 m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAe n m0 (4 * q2 + 6))
          ltac:(applys_eq (CC_D_Ae_long_nonmax n m0 (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SAo n q2 2)
            ltac:(applys_eq (CC_F_Ao_2 n q2); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBo n 0 (4 * q2 + 5))
          ltac:(applys_eq (CC_D_Bo0_odd_tail n (2 * q2 + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (4 * q2 + 3) with (S (4 * q2 + 2)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SAo n q2 (4 * m0 + 6))
            ltac:(applys_eq (CC_F_Ao_tail_2 n q2 m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAo n m0 (4 * q2 + 6))
          ltac:(applys_eq (CC_D_Ao_long_nonmax n m0 (2 * q2 + 1)); flia).
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
    { ih_by IH F (SBe n j 0) ltac:(apply CC_F_Be_small0). }
    Unshelve.
    all: esc.
  - replace 1 with (S 0) by flia.
    replace (4 * j + 2) with (S (4 * j + 1)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n j 0) ltac:(apply CC_F_Bo_small0). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe n j 1) ltac:(apply CC_F_Be_small1). }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    replace (4 * j + 3) with (S (4 * j + 2)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n j 1) ltac:(apply CC_F_Bo_small1). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBe (n + 1) j 2) ltac:(apply CC_F_Be_small2). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPe (n + 1) (4 * j + 3))
          ltac:(applys_eq (CC_D_Pe_odd n (2 * j + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBe (n + 1) j (4 * m0 + 6))
            ltac:(applys_eq (CC_F_Be_A_range_6 n j m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAo n m0 (10 + 4 * n + 4 * j))
          ltac:(applys_eq (CC_D_Ao_long_nonmax n m0 (3 + 2 * n + 2 * j)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (8 + 4 * n + 4 * j) with (S (7 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) j (4 * m + 3))
        ltac:(applys_eq (CC_F_Be_A_range_3 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (9 + 4 * n + 4 * j) with (S (8 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) j (4 * m + 4))
        ltac:(applys_eq (CC_F_Be_A_range_4 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (10 + 4 * n + 4 * j) with (S (9 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) j (4 * m + 5))
        ltac:(applys_eq (CC_F_Be_A_range_5 n j m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBo n j 2) ltac:(apply CC_F_Bo_small2). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPo n (4 * j + 3))
          ltac:(applys_eq (CC_D_Po_odd n (2 * j + 1)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (7 + 4 * n + 4 * j) with (S (6 + 4 * n + 4 * j)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBo n j (4 * m0 + 6))
            ltac:(applys_eq (CC_F_Bo_A_range_6 n j m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAe n m0 (10 + 4 * n + 4 * j))
          ltac:(applys_eq (CC_D_Ae_long_nonmax n m0 (3 + 2 * n + 2 * j)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (8 + 4 * n + 4 * j) with (S (7 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n j (4 * m + 3))
        ltac:(applys_eq (CC_F_Bo_A_range_3 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (9 + 4 * n + 4 * j) with (S (8 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n j (4 * m + 4))
        ltac:(applys_eq (CC_F_Bo_A_range_4 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (10 + 4 * n + 4 * j) with (S (9 + 4 * n + 4 * j)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBo n j (4 * m + 5))
        ltac:(applys_eq (CC_F_Bo_A_range_5 n j m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 3) with (S (4 * n + 6)) by flia.
    replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SBe (n + 1) 0 (4 * n + 6))
          ltac:(applys_eq (CC_F_Be_A_range_6 n 0 n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAo n n (10 + 4 * n + 4 * 0))
        ltac:(applys_eq (CC_D_Ao_long_diag_low n (2 * n + 3)); flia).
    }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 3) with (S (4 * n + 6)) by flia.
    replace (4 * j + 1) with (S (4 * j)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SBe (n + 1) (j + 1) (4 * n + 6))
          ltac:(applys_eq (CC_F_Be_A_range_6 n (j + 1) n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAo n n (10 + 4 * n + 4 * (j + 1)))
        ltac:(applys_eq (CC_D_Ao_long_diag_high n (2 * j)); flia).
    }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 4) with (S (4 * (n + 1 + 0) + 3)) by flia.
    replace (8 + 4 * n) with (S (7 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) 0 (4 * (n + 1 + 0) + 3))
        ltac:(applys_eq (CC_F_Be_past_3_j0 n 0); flia). }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 5) with (S (4 * (n + 1 + 0) + 4)) by flia.
    replace (9 + 4 * n) with (S (8 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) 0 (4 * (n + 1 + 0) + 4))
        ltac:(applys_eq (CC_F_Be_past_4_j0 n 0); flia). }
    Unshelve.
    all: esc.
  - replace (4 * (n + 1 + 0) + 3) with (S (4 * n + 6)) by flia.
    replace (4 * j + 5) with (S (4 * j + 4)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SBo n (j + 1) (4 * n + 6))
          ltac:(applys_eq (CC_F_Bo_A_range_6 n (j + 1) n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAe n n (10 + 4 * n + 4 * (j + 1)))
        ltac:(applys_eq (CC_D_Ae_long_diag_high n (2 * j + 2)); flia).
    }
    Unshelve.
    all: esc.
  - replace (n + 1) with (S n) by flia.
    rewrite to_side_SPe_succ_zero_step.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    rewrite (to_side_SAe_succ_step n n (9 + 4 * n)).
    split_sideRLs_concat.
    { ih_by IH F (SBo n 0 (5 + 4 * n))
        ltac:(applys_eq (CC_F_Bo_A_range_5 n 0 n); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { unfold to_side. cbn. esc. }
    rewrite to_side_SPo_zero_step.
    split_sideRLs_concat.
    { ih_by IH F (SBe (S n0) 0 (5 + 4 * S n0))
        ltac:(applys_eq (CC_F_Be_past_5_j0 n0 0); flia). }
    Unshelve.
    all: esc.
  - destruct n as [| n0].
    { exfalso; flia. }
    replace 1 with (S 0) by flia.
    rewrite (to_side_SPe_succ_step (S n0) 0).
    split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SPe (S n0) 0)
          ltac:(applys_eq (CC_F_Pe_succ_0 n0); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAe n0 n0 (10 + 4 * n0))
        ltac:(applys_eq (CC_D_Ae_long_diag_high n0 0); flia).
    }
    Unshelve.
    all: esc.
  - replace 2 with (S 1) by flia.
    rewrite (to_side_SPe_succ_step n 1).
    split_sideRLs_concat.
    { ih_by IH F (SPe n 1) ltac:(applys_eq (CC_F_Pe_1 n); flia). }
    Unshelve.
    all: esc.
  - replace 3 with (S 2) by flia.
    rewrite (to_side_SPe_succ_step n 2).
    split_sideRLs_concat.
    { ih_by IH F (SPe n 2) ltac:(applys_eq (CC_F_Pe_2 n); flia). }
    Unshelve.
    all: esc.
  - replace 4 with (S 3) by flia.
    rewrite (to_side_SPe_succ_step n 3).
    split_sideRLs_concat.
    { ih_by IH F (SPe n 3) ltac:(applys_eq (CC_F_Pe_3 n); flia). }
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
        { ih_by IH F (SPe (S n0 + 1) 4)
            ltac:(applys_eq (CC_F_Pe_4 (S n0 + 1)); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPe (S n0 + 1) 4)
          ltac:(applys_eq (CC_D_Pe_succ_even n0 2); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 5) with (S (4 * m0 + 8)) by flia.
      replace (S m0 + 1) with (m0 + 2) by flia.
      replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SPe (n + 1) (4 * m0 + 8))
            ltac:(applys_eq (CC_F_Pe_large_4 n m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBo n (m0 + 1) (10 + 4 * n))
          ltac:(applys_eq (CC_D_Bo_pos_long n (m0 + 1) (2 * n + 3)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (8 + 4 * n) with (S (7 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPe (n + 1) (4 * m + 5))
        ltac:(applys_eq (CC_F_Pe_large_1 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 7) with (S (4 * m + 6)) by flia.
    replace (9 + 4 * n) with (S (8 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPe (n + 1) (4 * m + 6))
        ltac:(applys_eq (CC_F_Pe_large_2 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 8) with (S (4 * m + 7)) by flia.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPe (n + 1) (4 * m + 7))
        ltac:(applys_eq (CC_F_Pe_large_3 n m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 1) with (S 0) by flia.
      replace (0 + 1) with 1 by flia.
      replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SPo (n + 1) 0)
            ltac:(applys_eq (CC_F_Po_0 (n + 1)); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPo (n + 1) 0)
          ltac:(applys_eq (CC_D_Po_even n 0); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 1) with (S (4 * m0 + 4)) by flia.
      replace (S m0 + 1) with (m0 + 2) by flia.
      replace (7 + 4 * n) with (S (6 + 4 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SPo (n + 1) (4 * m0 + 4))
            ltac:(applys_eq (CC_F_Po_pos_4 n m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SBe (n + 1) (m0 + 1) (10 + 4 * n))
          ltac:(applys_eq (CC_D_Be_pos_long (n + 1) (m0 + 1) (2 * n + 3)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 2) with (S (4 * m + 1)) by flia.
    replace (8 + 4 * n) with (S (7 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPo (n + 1) (4 * m + 1))
        ltac:(applys_eq (CC_F_Po_pos_1 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 3) with (S (4 * m + 2)) by flia.
    replace (9 + 4 * n) with (S (8 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPo (n + 1) (4 * m + 2))
        ltac:(applys_eq (CC_F_Po_pos_2 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (10 + 4 * n) with (S (9 + 4 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SPo (n + 1) (4 * m + 3))
        ltac:(applys_eq (CC_F_Po_pos_3 n m); flia). }
    Unshelve.
    all: esc.
  - destruct m as [| m0].
    { replace (4 * 0 + 3) with (S 2) by flia.
      replace (11 + 8 * n) with (S (10 + 8 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBe (n + 1) (n + 1) 2)
            ltac:(apply CC_F_Be_small2). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SPe (n + 1) (4 * (n + 1) + 3))
          ltac:(applys_eq (CC_D_Pe_odd n (2 * n + 3)); flia).
      }
      Unshelve.
      all: esc. }
    { replace (4 * S m0 + 3) with (S (4 * m0 + 6)) by flia.
      replace (S m0) with (m0 + 1) by flia.
      replace (11 + 8 * n) with (S (10 + 8 * n)) by flia.
      normalize_split_sideRLs_concat.
      {
        eapply sideRLs_trans.
        { ih_by IH F (SBe (n + 1) (n + 1) (4 * m0 + 6))
            ltac:(applys_eq (CC_F_Be_top_6 n m0); flia). }
        eapply sideRLs_trans.
        { solve_A_C_positive. }
        ih_by IH D (SAo n m0 (14 + 8 * n))
          ltac:(applys_eq (CC_D_Ao_long_nonmax n m0 (4 * n + 5)); flia).
      }
      Unshelve.
      all: esc. }
  - replace (4 * m + 4) with (S (4 * m + 3)) by flia.
    replace (12 + 8 * n) with (S (11 + 8 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) (n + 1) (4 * m + 3))
        ltac:(applys_eq (CC_F_Be_top_3 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 5) with (S (4 * m + 4)) by flia.
    replace (13 + 8 * n) with (S (12 + 8 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) (n + 1) (4 * m + 4))
        ltac:(applys_eq (CC_F_Be_top_4 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * m + 6) with (S (4 * m + 5)) by flia.
    replace (14 + 8 * n) with (S (13 + 8 * n)) by flia.
    normalize_split_sideRLs_concat.
    { ih_by IH F (SBe (n + 1) (n + 1) (4 * m + 5))
        ltac:(applys_eq (CC_F_Be_top_5 n m); flia). }
    Unshelve.
    all: esc.
  - replace (4 * n + 7) with (S (4 * n + 6)) by flia.
    replace (4 * n + 1) with (S (4 * n)) by flia.
    normalize_split_sideRLs_concat.
    {
      eapply sideRLs_trans.
      { ih_by IH F (SBe (n + 1) (n + 1) (4 * n + 6))
          ltac:(applys_eq (CC_F_Be_top_6 n n); flia). }
      eapply sideRLs_trans.
      { solve_A_C_positive. }
      ih_by IH D (SAo n n (14 + 8 * n))
        ltac:(applys_eq (CC_D_Ao_long_diag_high n (2 * n)); flia).
    }
    Unshelve.
    all: esc.
Qed.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma ClosedCall_progress_any : forall q s q' s' r,
  ClosedCall q s q' s' ->
  to_side s {{{ ((q, []), L) }}} r -->+
  to_side s' {{{ ((q', []), R) }}} r.
Proof.
  intros q s q' s' r H.
  eapply sideRLs_1L.
  apply ClosedCall_sideRLs.
  exact H.
Qed.

Lemma ClosedCall_progress q s q' s' :
  ClosedCall q s q' s' ->
  to_side s {{{ ((q, []), L) }}} const S0 -->+
  to_side s' {{{ ((q', []), R) }}} const S0.
Proof.
  intro H.
  apply ClosedCall_progress_any.
  exact H.
Qed.

Lemma ClosedCall_evstep_any q s q' s' r :
  ClosedCall q s q' s' ->
  to_side s {{{ ((q, []), L) }}} r -->*
  to_side s' {{{ ((q', []), R) }}} r.
Proof.
  intro H.
  apply progress_evstep.
  apply ClosedCall_progress_any.
  exact H.
Qed.

Definition Bcfg (h : Side) : Q * tape :=
  to_side h {{{ ((B, []), R) }}} const S0.

Lemma B_to_A4 h :
  Bcfg h -[ tm ]->+ to_side h {{{ ((A, []), L) }}} (S1 >> const S0).
Proof.
  unfold Bcfg, tm.
  step1s.
Qed.

Lemma C_to_D4 h :
  to_side h {{{ ((C, []), R) }}} (S1 >> const S0) -[ tm ]->+
  to_side h {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  unfold tm.
  step1s.
Qed.

Lemma A_to_C_SPe_succ_zero n :
  to_side (SPe (S n) 0) {{{ ((A, []), L) }}} (S1 >> const S0) -[ tm ]->+
  to_side (SPe (S n) 0) {{{ ((C, []), R) }}} (S1 >> const S0).
Proof.
  rewrite to_side_SPe_succ_zero_step.
  eapply sideRLs_1L.
  apply sideRLs_A_C_1.
Qed.

Lemma A_to_C_SPo_zero n :
  to_side (SPo n 0) {{{ ((A, []), L) }}} (S1 >> const S0) -[ tm ]->+
  to_side (SPo n 0) {{{ ((C, []), R) }}} (S1 >> const S0).
Proof.
  rewrite to_side_SPo_zero_step.
  eapply sideRLs_1L.
  apply sideRLs_A_C_1.
Qed.

Lemma A_to_C_SBe_succ n j b :
  to_side (SBe n j (S b)) {{{ ((A, []), L) }}} (S1 >> const S0) -[ tm ]->+
  to_side (SBe n j (S b)) {{{ ((C, []), R) }}} (S1 >> const S0).
Proof.
  rewrite to_side_SBe_succ_step.
  eapply sideRLs_1L.
  apply sideRLs_A_C_1.
Qed.

Lemma A_to_C_SBo_succ n j b :
  to_side (SBo n j (S b)) {{{ ((A, []), L) }}} (S1 >> const S0) -[ tm ]->+
  to_side (SBo n j (S b)) {{{ ((C, []), R) }}} (S1 >> const S0).
Proof.
  rewrite to_side_SBo_succ_step.
  eapply sideRLs_1L.
  apply sideRLs_A_C_1.
Qed.

Lemma B_to_C_SPe_succ_zero n :
  Bcfg (SPe (S n) 0) -[ tm ]->+
  to_side (SPe (S n) 0) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  eapply progress_trans.
  - apply B_to_A4.
  - eapply progress_trans.
    + apply A_to_C_SPe_succ_zero.
    + apply C_to_D4.
Qed.

Lemma B_to_C_SPe_plus2 n :
  Bcfg (SPe (n + 2) 0) -[ tm ]->+
  to_side (SPe (n + 2) 0) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  replace (n + 2) with (S (n + 1)) by lia.
  apply B_to_C_SPe_succ_zero.
Qed.

Lemma B_to_C_SPe_pos_zero n :
  1 <= n ->
  Bcfg (SPe n 0) -[ tm ]->+
  to_side (SPe n 0) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  intro Hn.
  replace n with (S (Nat.pred n)) by lia.
  apply B_to_C_SPe_succ_zero.
Qed.

Lemma B_to_C_SPo_zero n :
  Bcfg (SPo n 0) -[ tm ]->+
  to_side (SPo n 0) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  eapply progress_trans.
  - apply B_to_A4.
  - eapply progress_trans.
    + apply A_to_C_SPo_zero.
    + apply C_to_D4.
Qed.

Lemma B_to_C_SBe_succ n j b :
  Bcfg (SBe n j (S b)) -[ tm ]->+
  to_side (SBe n j (S b)) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  eapply progress_trans.
  - apply B_to_A4.
  - eapply progress_trans.
    + apply A_to_C_SBe_succ.
    + apply C_to_D4.
Qed.

Lemma B_to_C_SBe_pos n j b :
  1 <= b ->
  Bcfg (SBe n j b) -[ tm ]->+
  to_side (SBe n j b) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  intro Hb.
  replace b with (S (Nat.pred b)) by lia.
  apply B_to_C_SBe_succ.
Qed.

Lemma B_to_C_SBo_succ n j b :
  Bcfg (SBo n j (S b)) -[ tm ]->+
  to_side (SBo n j (S b)) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  eapply progress_trans.
  - apply B_to_A4.
  - eapply progress_trans.
    + apply A_to_C_SBo_succ.
    + apply C_to_D4.
Qed.

Lemma B_to_C_SBo_pos n j b :
  1 <= b ->
  Bcfg (SBo n j b) -[ tm ]->+
  to_side (SBo n j b) {{{ ((D, []), L) }}} (S1 >> const S0).
Proof.
  intro Hb.
  replace b with (S (Nat.pred b)) by lia.
  apply B_to_C_SBo_succ.
Qed.

Ltac apply_B_to_C_positive :=
  first
    [ lazymatch goal with
      | |- Bcfg (SPe (?n + 2) 0) -[ tm ]->+ _ =>
          apply B_to_C_SPe_plus2
      | |- to_side (SPe (?n + 2) 0) {{{ ((B, []), R) }}} const S0 -[ tm ]->+ _ =>
          apply B_to_C_SPe_plus2
      | |- Bcfg (SPe ?n 0) -[ tm ]->+ _ =>
          eapply B_to_C_SPe_pos_zero; lia
      | |- to_side (SPe ?n 0) {{{ ((B, []), R) }}} const S0 -[ tm ]->+ _ =>
          eapply B_to_C_SPe_pos_zero; lia
      | |- Bcfg (SPo ?n 0) -[ tm ]->+ _ =>
          apply B_to_C_SPo_zero
      | |- to_side (SPo ?n 0) {{{ ((B, []), R) }}} const S0 -[ tm ]->+ _ =>
          apply B_to_C_SPo_zero
      | |- Bcfg (SBe _ _ ?b) -[ tm ]->+ _ =>
          eapply B_to_C_SBe_pos; lia
      | |- to_side (SBe _ _ ?b) {{{ ((B, []), R) }}} const S0 -[ tm ]->+ _ =>
          eapply B_to_C_SBe_pos; lia
      | |- Bcfg (SBo _ _ ?b) -[ tm ]->+ _ =>
          eapply B_to_C_SBo_pos; lia
      | |- to_side (SBo _ _ ?b) {{{ ((B, []), R) }}} const S0 -[ tm ]->+ _ =>
          eapply B_to_C_SBo_pos; lia
      end ].

Lemma Btail_E_to_B l :
  l {{{ ((E, []), R) }}} (S1 >> const S0) -[ tm ]->+
  S1 >> S1 >> S1 >> S1 >> l {{{ ((B, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma boundary_A0 l :
  l {{{ ((A, []), R) }}} const S0 -[ tm ]->+
  S1 >> l {{{ ((B, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma boundary_E0 l :
  l {{{ ((E, []), R) }}} const S0 -[ tm ]->+
  S1 >> l {{{ ((A, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma boundary_F0 l :
  l {{{ ((F, []), R) }}} const S0 -[ tm ]->+
  S1 >> l {{{ ((E, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma marker1_A l :
  l {{{ ((A, []), R) }}} (S1 >> const S0) -[ tm ]->+
  S1 >> l {{{ ((C, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma marker1_E l :
  l {{{ ((E, []), R) }}} (S1 >> const S0) -[ tm ]->+
  S1 >> l {{{ ((F, []), R) }}} const S0.
Proof.
  unfold tm.
  step1s.
Qed.

Lemma marker1_F s s' :
  ClosedCall F s F s' ->
  to_side s {{{ ((F, []), R) }}} (S1 >> const S0) -[ tm ]->+
  to_side s' {{{ ((F, []), R) }}} const S0.
Proof.
  intro HF.
  eapply progress_trans.
  - unfold tm.
    step1s.
  - apply ClosedCall_progress_any.
    exact HF.
Qed.

Lemma boundary_E0_to_B l :
  l {{{ ((E, []), R) }}} const S0 -[ tm ]->+
  S1 >> S1 >> l {{{ ((B, []), R) }}} const S0.
Proof.
  eapply progress_trans.
  - apply boundary_E0.
  - apply boundary_A0.
Qed.

Lemma boundary_F0_to_B l :
  l {{{ ((F, []), R) }}} const S0 -[ tm ]->+
  S1 >> S1 >> S1 >> l {{{ ((B, []), R) }}} const S0.
Proof.
  eapply progress_trans.
  - apply boundary_F0.
  - apply boundary_E0_to_B.
Qed.

Lemma Btail_F_to_B s s' :
  ClosedCall F s F s' ->
  to_side s {{{ ((F, []), R) }}} (S1 >> const S0) -[ tm ]->+
  S1 >> S1 >> S1 >> to_side s' {{{ ((B, []), R) }}} const S0.
Proof.
  intro HF.
  eapply progress_trans.
  - apply marker1_F.
    exact HF.
  - apply boundary_F0_to_B.
Qed.

Lemma boundary_D0_Pe4_to_B n k :
  to_side (SPe n (4 * k)) {{{ ((C, []), R) }}} const S0 -[ tm ]->+
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
  - apply boundary_E0_to_B.
Qed.

Lemma boundary_D0_Po4_to_B n k :
  to_side (SPo n (4 * k)) {{{ ((C, []), R) }}} const S0 -[ tm ]->+
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
  - apply boundary_E0_to_B.
Qed.

Lemma Bstep_Pe_even n :
  Bcfg (SPe (n + 2) 0) -[ tm ]->+
  Bcfg (SBo (n + 1) 1 (10 + 4 * n)).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Pe_succ_even n 0); lia.
    + cbn [to_side].
      replace (6 + 4 * n + 2 * 0) with (6 + 4 * n) by lia.
      replace (10 + 4 * n) with (S (S (S (S (6 + 4 * n))))) by lia.
      repeat rewrite Bo_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Bstep_Po_even n :
  Bcfg (SPo (n + 1) 0) -[ tm ]->+
  Bcfg (SBe (n + 1) 1 (10 + 4 * n)).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Po_even n 0); lia.
    + cbn [to_side].
      replace (6 + 4 * n + 2 * 0) with (6 + 4 * n) by lia.
      replace (10 + 4 * n) with (S (S (S (S (6 + 4 * n))))) by lia.
      repeat rewrite Be_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Bstep_Be_pos_long n j k :
  1 <= j ->
  j < n ->
  k <= 2 * n + 1 ->
  Bcfg (SBe n j (2 * k + 4)) -[ tm ]->+
  Bcfg (SBe n (j + 1) (2 * k + 4)).
Proof.
  intros Hj0 Hjn Hk.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_D_Be_pos_long; lia.
    + cbn [to_side].
      replace (2 * k + 4) with (S (S (S (S (2 * k))))) by lia.
      repeat rewrite Be_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Bstep_Be_pos_tail2 n j :
  1 <= j ->
  j < n ->
  Bcfg (SBe n j 2) -[ tm ]->+
  Bcfg (SBe n (j + 1) 2).
Proof.
  intros Hj0 Hjn.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Be_pos_tail2 n j); lia.
    + eapply progress_trans.
      * apply marker1_A.
      * cbn [to_side].
        rewrite <- Pe_succ_step.
        replace (S (4 * j + 3)) with (4 * (j + 1)) by lia.
        apply boundary_D0_Pe4_to_B.
Qed.

Lemma Bstep_Be0_tail2 n :
  Bcfg (SBe (n + 1) 0 2) -[ tm ]->+
  Bcfg (SBe (n + 1) 1 2).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_D_Be0_2_succ.
    + eapply progress_trans.
      * apply marker1_A.
      * cbn [to_side].
        rewrite <- Pe_succ_step.
        replace (S 3) with (4 * 1) by lia.
        apply boundary_D0_Pe4_to_B.
Qed.

Lemma Bstep_Be0_even_tail n k :
  k <= 2 * (n + 1) ->
  Bcfg (SBe (n + 1) 0 (2 * k + 4)) -[ tm ]->+
  Bcfg (SBe (n + 1) 1 (2 * k + 4)).
Proof.
  intro Hk.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Be0_even_tail n k); lia.
    + cbn [to_side].
      replace (2 * k + 4) with (S (S (S (S (2 * k))))) by lia.
      repeat rewrite Be_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Be_diag_tail2_to_Po n :
  S1 >> S1 >> S1 >> to_side (SBe n 0 (4 * n + 3)) =
  to_side (SPo n 0).
Proof.
  cbn [to_side].
  rewrite <- Be_succ_step.
  rewrite <- Be_succ_step.
  replace (S (S (4 * n + 3))) with (5 + 4 * n) by lia.
  rewrite <- Po_zero_step.
  reflexivity.
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

Lemma Bo_diag_tail4_to_Pe n :
  S1 >> to_side (SBo n 0 (4 * n + 5)) =
  to_side (SPe (n + 1) 0).
Proof.
  cbn [to_side].
  replace (n + 1) with (S n) by lia.
  replace (4 * n + 5) with (5 + 4 * n) by lia.
  rewrite <- Pe_succ_zero_step.
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

Lemma Bstep_Be_diag_tail2 n :
  1 <= n ->
  Bcfg (SBe n n 2) -[ tm ]->+
  Bcfg (SPo n 0).
Proof.
  intro Hn.
  destruct n as [| n].
  - lia.
  - unfold Bcfg.
    eapply progress_trans.
    + apply_B_to_C_positive.
    + eapply progress_trans.
      * apply ClosedCall_progress_any.
        apply CC_D_Be_diag_tail2.
      * rewrite <- Be_diag_tail2_to_Po.
        replace (S n) with (n + 1) by lia.
        replace (4 * (n + 1) + 3) with (7 + 4 * n) by lia.
        apply Btail_F_to_B.
        replace (7 + 4 * n) with (4 * (n + 1 + 0) + 3) at 1 by lia.
        apply CC_F_Be_past_3_j0.
        reflexivity.
Qed.

Lemma Bstep_Be_diag_tail4 n :
  Bcfg (SBe n n 4) -[ tm ]->+
  Bcfg (SBo n 0 2).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_D_Be_diag_tail4.
    + eapply progress_trans.
      * apply marker1_A.
      * rewrite Be_diag_tail4_to_Po.
        replace (to_side (SPo n 0)) with (to_side (SPo n (4 * 0))) by (f_equal; lia).
        apply boundary_D0_Po4_to_B.
Qed.

Lemma Bstep_Be_diag_long_low n k :
  k <= 2 * n ->
  Bcfg (SBe n n (2 * k + 6)) -[ tm ]->+
  Bcfg (SBo n 0 (2 * k + 4)).
Proof.
  intro Hk.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Be_diag_long_low n k); lia.
    + cbn [to_side].
      replace (2 * k + 4) with (S (S (S (S (2 * k))))) by lia.
      repeat rewrite Bo_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Bstep_Bo_pos_long n j k :
  1 <= j ->
  j < n ->
  k <= 2 * n + 3 ->
  Bcfg (SBo n j (2 * k + 4)) -[ tm ]->+
  Bcfg (SBo n (j + 1) (2 * k + 4)).
Proof.
  intros Hj0 Hjn Hk.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Bo_pos_long n j k); lia.
    + cbn [to_side].
      replace (2 * k + 4) with (S (S (S (S (2 * k))))) by lia.
      repeat rewrite Bo_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Bstep_Bo_pos_tail2 n j :
  1 <= j ->
  j < n ->
  Bcfg (SBo n j 2) -[ tm ]->+
  Bcfg (SBo n (j + 1) 2).
Proof.
  intros Hj0 Hjn.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Bo_pos_tail2 n j); lia.
    + eapply progress_trans.
      * apply marker1_A.
      * cbn [to_side].
        rewrite <- Po_succ_step.
        replace (S (4 * j + 3)) with (4 * (j + 1)) by lia.
        apply boundary_D0_Po4_to_B.
Qed.

Lemma Bstep_Bo_diag_tail2 n :
  Bcfg (SBo n n 2) -[ tm ]->+
  Bcfg (SPe (n + 1) 0).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_D_Bo_diag_tail2.
    + rewrite <- Bo_diag_tail2_to_Pe.
      apply Btail_F_to_B.
      applys_eq (CC_F_Ae_special n n); lia.
Qed.

Lemma Bstep_Bo_diag_tail4 n :
  Bcfg (SBo n n 4) -[ tm ]->+
  Bcfg (SBe (n + 1) 0 2).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_D_Bo_diag_tail4.
    + eapply progress_trans.
      * apply marker1_A.
      * rewrite Bo_diag_tail4_to_Pe.
        replace (to_side (SPe (n + 1) 0)) with (to_side (SPe (n + 1) (4 * 0))) by (f_equal; lia).
        apply boundary_D0_Pe4_to_B.
Qed.

Lemma Bstep_Bo0_tail2 n :
  Bcfg (SBo (n + 1) 0 2) -[ tm ]->+
  Bcfg (SBo (n + 1) 1 2).
Proof.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      apply CC_D_Bo0_2.
    + eapply progress_trans.
      * apply marker1_A.
      * cbn [to_side].
        rewrite <- Po_succ_step.
        replace (S 3) with (4 * 1) by lia.
        apply boundary_D0_Po4_to_B.
Qed.

Lemma Bstep_Bo0_even_tail n k :
  k <= 2 * (n + 1) ->
  Bcfg (SBo (n + 1) 0 (2 * k + 4)) -[ tm ]->+
  Bcfg (SBo (n + 1) 1 (2 * k + 4)).
Proof.
  intro Hk.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Bo0_even_tail n k); lia.
    + cbn [to_side].
      replace (2 * k + 4) with (S (S (S (S (2 * k))))) by lia.
      repeat rewrite Bo_succ_step.
      apply Btail_E_to_B.
Qed.

Lemma Bstep_Bo_diag_long_low n k :
  k <= 2 * n + 2 ->
  Bcfg (SBo n n (2 * k + 6)) -[ tm ]->+
  Bcfg (SBe (n + 1) 0 (2 * k + 4)).
Proof.
  intro Hk.
  unfold Bcfg.
  eapply progress_trans.
  - apply_B_to_C_positive.
  - eapply progress_trans.
    + apply ClosedCall_progress_any.
      applys_eq (CC_D_Bo_diag_long_low n k); lia.
    + cbn [to_side].
      replace (2 * k + 4) with (S (S (S (S (2 * k))))) by lia.
      repeat rewrite Be_succ_step.
      apply Btail_E_to_B.
Qed.

Definition GoodB (h : Side) : Prop :=
  match h with
  | SPe n 0 => 2 <= n
  | SPo n 0 => 1 <= n
  | SBe n j b =>
      1 <= n /\
      j <= n /\
      Nat.Even b /\
      2 <= b <= 7 + 4 * n - 1 /\
      (b = 7 + 4 * n - 1 -> 1 <= j)
  | SBo n j b =>
      1 <= n /\
      j <= n /\
      Nat.Even b /\
      2 <= b <= 7 + 4 * n - 1 /\
      (b = 7 + 4 * n - 1 -> 1 <= j)
  | _ => False
  end.

Definition Bnext (h : Side) : Side :=
  match h with
  | SPe (S n) 0 => SBo n 1 (7 + 4 * n - 1)
  | SPo n 0 => SBe n 1 (7 + 4 * n - 1)
  | SBe n j b =>
      if j <? n then SBe n (j + 1) b
      else if b =? 2 then SPo n 0
      else SBo n 0 (b - 2)
  | SBo n j b =>
      if j <? n then SBo n (j + 1) b
      else if b =? 2 then SPe (n + 1) 0
      else SBe (n + 1) 0 (b - 2)
  | _ => h
  end.

Lemma even_minus_2 b :
  Nat.Even b ->
  2 <= b ->
  Nat.Even (b - 2).
Proof.
  intros [k Hk] Hb.
  exists (k - 1).
  lia.
Qed.

Lemma even_ge4_if_ge2_ne2 b :
  Nat.Even b ->
  2 <= b ->
  b <> 2 ->
  4 <= b.
Proof.
  intros [k Hk] Hb Hne.
  lia.
Qed.

Lemma GoodB_next h :
  GoodB h ->
  GoodB (Bnext h).
Proof.
  destruct h as [| | n r | n r | n j b | n j b | | ];
    cbn [GoodB Bnext]; try contradiction.
  - destruct r as [| r].
    + destruct n as [| n].
      * cbn [GoodB Bnext]. lia.
      * cbn [GoodB Bnext].
        intro Hn.
        repeat split; try lia; try (exists (3 + 2 * n); lia);
          try (intro H; lia).
    + cbn [GoodB]. contradiction.
  - destruct r as [| r].
    + cbn [GoodB Bnext].
      intro Hn.
      repeat split; try lia; try (exists (3 + 2 * n); lia);
        try (intro H; lia).
    + cbn [GoodB]. contradiction.
  - intros (Hn & Hj & He & Hb & Htop).
    destruct Hb as [Hb0 Hb1].
    destruct (j <? n) eqn:Hjlt.
    + apply Nat.ltb_lt in Hjlt.
      repeat split; try lia; try exact He; try (intro H; lia).
    + apply Nat.ltb_ge in Hjlt.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        cbn [GoodB].
        lia.
      * apply Nat.eqb_neq in Hb2.
        cbn [GoodB].
        repeat split; try lia;
          try (apply even_minus_2; lia || exact He);
          try (pose proof (even_ge4_if_ge2_ne2 b He Hb0 Hb2); lia);
          try (intro H; lia).
  - intros (Hn & Hj & He & Hb & Htop).
    destruct Hb as [Hb0 Hb1].
    destruct (j <? n) eqn:Hjlt.
    + apply Nat.ltb_lt in Hjlt.
      repeat split; try lia; try exact He; try (intro H; lia).
    + apply Nat.ltb_ge in Hjlt.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        cbn [GoodB].
        lia.
      * apply Nat.eqb_neq in Hb2.
        cbn [GoodB].
        repeat split; try lia;
          try (apply even_minus_2; lia || exact He);
          try (pose proof (even_ge4_if_ge2_ne2 b He Hb0 Hb2); lia);
          try (intro H; lia).
Qed.

Lemma Bstep_Good h :
  GoodB h ->
  Bcfg h -[ tm ]->+ Bcfg (Bnext h).
Proof.
  destruct h as [| | n r | n r | n j b | n j b | | ];
    cbn [GoodB Bnext]; try contradiction.
  - destruct r as [| r].
    + intro Hn.
      destruct n as [| [| n]].
      * lia.
      * lia.
      * cbn [Bnext].
        replace (S (S n)) with (n + 2) by lia.
        replace (S n) with (n + 1) by lia.
        replace (7 + 4 * (n + 1) - 1) with (10 + 4 * n) by lia.
        apply Bstep_Pe_even.
    + contradiction.
  - destruct r as [| r].
    + intro Hn.
      destruct n as [| n].
      * lia.
      * cbn [Bnext].
        replace (S n) with (n + 1) by lia.
        replace (7 + 4 * (n + 1) - 1) with (10 + 4 * n) by lia.
        apply Bstep_Po_even.
    + contradiction.
  - intros (Hn & Hj & He & Hb & Htop).
    destruct Hb as [Hb0 Hb1].
    destruct (j <? n) eqn:Hjlt.
    + apply Nat.ltb_lt in Hjlt.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        destruct j as [| j].
        -- replace n with ((n - 1) + 1) by lia.
           change (0 + 1) with 1.
           apply Bstep_Be0_tail2.
        -- apply Bstep_Be_pos_tail2; lia.
      * apply Nat.eqb_neq in Hb2.
        destruct He as [t Ht].
        assert (Ht2 : 2 <= t) by lia.
        replace b with (2 * (t - 2) + 4) by lia.
        destruct j as [| j].
        -- replace n with ((n - 1) + 1) by lia.
           change (0 + 1) with 1.
           apply Bstep_Be0_even_tail.
           lia.
        -- apply Bstep_Be_pos_long; lia.
    + apply Nat.ltb_ge in Hjlt.
      assert (Hj_eq : j = n) by lia.
      subst j.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        apply Bstep_Be_diag_tail2.
        lia.
      * apply Nat.eqb_neq in Hb2.
        destruct (b =? 4) eqn:Hb4.
        -- apply Nat.eqb_eq in Hb4.
           subst b.
           apply Bstep_Be_diag_tail4.
        -- apply Nat.eqb_neq in Hb4.
           destruct He as [t Ht].
           assert (Ht3 : 3 <= t) by lia.
           replace b with (2 * (t - 3) + 6) by lia.
           replace (2 * (t - 3) + 6 - 2) with (2 * (t - 3) + 4) by lia.
           apply Bstep_Be_diag_long_low.
           lia.
  - intros (Hn & Hj & He & Hb & Htop).
    destruct Hb as [Hb0 Hb1].
    destruct (j <? n) eqn:Hjlt.
    + apply Nat.ltb_lt in Hjlt.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        destruct j as [| j].
        -- replace n with ((n - 1) + 1) by lia.
           change (0 + 1) with 1.
           apply Bstep_Bo0_tail2.
        -- apply Bstep_Bo_pos_tail2; lia.
      * apply Nat.eqb_neq in Hb2.
        destruct He as [t Ht].
        assert (Ht2 : 2 <= t) by lia.
        replace b with (2 * (t - 2) + 4) by lia.
        destruct j as [| j].
        -- replace n with ((n - 1) + 1) by lia.
           change (0 + 1) with 1.
           apply Bstep_Bo0_even_tail.
           lia.
        -- apply Bstep_Bo_pos_long; lia.
    + apply Nat.ltb_ge in Hjlt.
      assert (Hj_eq : j = n) by lia.
      subst j.
      destruct (b =? 2) eqn:Hb2.
      * apply Nat.eqb_eq in Hb2.
        subst b.
        apply Bstep_Bo_diag_tail2.
      * apply Nat.eqb_neq in Hb2.
        destruct (b =? 4) eqn:Hb4.
        -- apply Nat.eqb_eq in Hb4.
           subst b.
           apply Bstep_Bo_diag_tail4.
        -- apply Nat.eqb_neq in Hb4.
           destruct He as [t Ht].
           assert (Ht3 : 3 <= t) by lia.
           replace b with (2 * (t - 3) + 6) by lia.
           replace (2 * (t - 3) + 6 - 2) with (2 * (t - 3) + 4) by lia.
           apply Bstep_Bo_diag_long_low.
           lia.
Qed.

Lemma GoodB_start :
  GoodB (SBe 1 0 2).
Proof.
  cbn [GoodB].
  repeat split; try lia.
  exists 1.
  reflexivity.
Qed.

Transparent SkelE SkelO Pside Bside Aside Pe Po Be Bo Ae Ao K0 K1.

Lemma init_to_start :
  c0 -[ tm ]->* Bcfg (SBe 1 0 2).
Proof.
  cbn.
  solve_init.
Qed.

Theorem nonhalt :
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply init_to_start.
  - eapply progress_nonhalt_cond with
      (A := Side)
      (i0 := SBe 1 0 2)
      (C := Bcfg)
      (P := GoodB).
    + intros h Hgood.
      exists (Bnext h).
      split.
      * apply Bstep_Good.
        exact Hgood.
      * apply GoodB_next.
        exact Hgood.
    + apply GoodB_start.
Qed.
