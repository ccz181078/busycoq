(* Classification: bouncer + chaotic edge.
   Consolidated from busycoq PR #27, pinned in PR19_28_INVENTORY.json.
   Original proofs: Dennis Koshta.
   Common declarations are reused; each blank-state initialization is checked separately. *)

From BusyCoq Require Import Individual62.
Require Import ZArith Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.

Module TM1.
Import BusyCoq.Individual62.

Import ZArith Lia.

Import String.

Import List.

Import BusyCoq.ES_v3.

Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition G : list sym :=
  [0;0;1;1;0;1;1;1;1;0;1;1;0;1;1;1;1;1;1;0;1;1;0;1;1;1;1;1;0;0;1;1;0;1;1;1;1;1;0;1;1;0;0].

Definition Kr n a b c d :=
  0inf <{{F}} G *> [1] *> [1;1]^^n *> [0] *> [1;1]^^a *> [0;1;1;0] *> [1;1]^^b
    *> [0;0;0;0;0;0] *> [1] *> [1;1]^^c *> [0;1;1;0;1;1;1;1;0;0;0;0;0;0] *> [1;1]^^d
    *> [0;1;1;0;0;1;1;0;1;1;1] *> 0inf.

Ltac ES_v3.es_v3_pre ::= unfold Kr, G.

Lemma S_step n a b c d:
  Kr n (5+a) (3+b) (3+c) (1+d) -->+ Kr (24+n) (1+a) (5+b) (3+c) (3+d).
Proof.
  es' n a b c d.
Qed.

Lemma TE n b d:
  Kr n 2 (44+b) 17 (10+d) -->+ Kr (278+n) (1+b) 41 (35+d) 9.
Proof.
  es' n b d.
Qed.

Lemma TO n b c d:
  Kr n 1 (41+b) (18+c) (9+d) -->+ Kr (294+n) (14+b+c) (40+d) 17 9.
Proof.
  es' n b c d.
Qed.

Lemma T6 n b c d:
  Kr n 3 (41+b) (17+c) (9+d) -->+ Kr (296+n) (13+b+c) (40+d) 17 9.
Proof.
  es' n b c d.
Qed.

Lemma T8 n b d:
  Kr n 4 (44+b) 17 (10+d) -->+ Kr (270+n) (7+b) 43 (33+d) 9.
Proof.
  es' n b d.
Qed.

Lemma S_step' n a b c d:
  Kr n (5+a) (3+b) (3+c) (1+d) -->* Kr (24+n) (1+a) (5+b) (3+c) (3+d).
Proof. apply progress_evstep, S_step. Qed.

Lemma TE' n b d:
  Kr n 2 (44+b) 17 (10+d) -->* Kr (278+n) (1+b) 41 (35+d) 9.
Proof. apply progress_evstep, TE. Qed.

Lemma TO' n b c d:
  Kr n 1 (41+b) (18+c) (9+d) -->* Kr (294+n) (14+b+c) (40+d) 17 9.
Proof. apply progress_evstep, TO. Qed.

Lemma T6' n b c d:
  Kr n 3 (41+b) (17+c) (9+d) -->* Kr (296+n) (13+b+c) (40+d) 17 9.
Proof. apply progress_evstep, T6. Qed.

Lemma T8' n b d:
  Kr n 4 (44+b) 17 (10+d) -->* Kr (270+n) (7+b) 43 (33+d) 9.
Proof. apply progress_evstep, T8. Qed.

Lemma S_iter k: forall n a b c d,
  Kr n (4*k+1+a) (3+b) (3+c) (1+d) -->* Kr (24*k+n) (1+a) (2*k+3+b) (3+c) (2*k+1+d).
Proof.
  induction k; intros.
  - finish.
  - follow (S_step' n (4*k+a) b c d).
    follow (IHk (24+n) a (2+b) c (2+d)).
    finish.
Qed.

Definition Ev N X := Kr N (4*X+26) (2*X+32) 17 9.

Lemma prog_eq c1 c2 c1' c2':
  c1 -->+ c2 -> c1 = c1' -> c2 = c2' -> c1' -->+ c2'.
Proof. intros H E1 E2. subst. exact H. Qed.

Lemma DC N X:
  Ev N X -->+ Ev (48*X+716+N) (4+X).
Proof.
  unfold Ev.
  follow (S_iter (X+6) N 1 (2*X+29) 14 8).
  follow (TE' (24*(X+6)+N) (4*X) (2*X+11)).
  follow (S_iter X (278+(24*(X+6)+N)) 0 38 (2*X+43) 8).
  eapply prog_eq.
  1: apply (TO (24*X+(278+(24*(X+6)+N))) (2*X) (2*X+28) (2*X)).
  all: lia_refl.
Qed.

Fixpoint cc_steps (n:nat) (x:cconfig) : option cconfig :=
match n with
| O => Some x
| S n0 =>
  match cconfig_step tm x with
  | Some x0 => cc_steps n0 x0
  | None => None
  end
end.

Lemma cc_steps_spec n x y:
  cc_steps n x = Some y -> cconfig_to_config x -->* cconfig_to_config y.
Proof.
  gen x.
  induction n; cbn[cc_steps]; intros x H.
  - inverts H. apply evstep_refl.
  - pose proof (cconfig_step_spec tm x) as HE.
    destruct (cconfig_step tm x) as [x0|]. 2: congruence.
    eapply evstep_step; eauto.
Qed.

Fixpoint cc_steps' (n1 n2 n3:nat) (x:cconfig) : option cconfig :=
match n1 with
| O => cc_steps n3 x
| S n1 =>
  match cc_steps n2 x with
  | Some x0 => cc_steps' n1 n2 n3 x0
  | None => None
  end
end.

Lemma cc_steps'_spec n1 n2 n3 x y:
  cc_steps' n1 n2 n3 x = Some y -> cconfig_to_config x -->* cconfig_to_config y.
Proof.
  gen x.
  induction n1; cbn[cc_steps']; intros x H.
  - exact (cc_steps_spec _ _ _ H).
  - destruct (cc_steps n2 x) as [x0|] eqn:E. 2: congruence.
    eapply evstep_trans.
    + exact (cc_steps_spec _ _ _ E).
    + apply IHn1, H.
Qed.

Fixpoint rl (xs : list (nat*nat)) : list sym :=
match xs with
| [] => []
| (z,o)::t => [0]^^z ++ [1]^^o ++ rl t
end.

Definition LR (xs : list (nat*nat)) : Q * tape := cconfig_to_config ([], rl xs, 0, F).

Definition Kr_list n a b c d : list sym :=
  G ++ [1] ++ [1;1]^^n ++ [0] ++ [1;1]^^a ++ [0;1;1;0] ++ [1;1]^^b
    ++ [0;0;0;0;0;0] ++ [1] ++ [1;1]^^c ++ [0;1;1;0;1;1;1;1;0;0;0;0;0;0] ++ [1;1]^^d
    ++ [0;1;1;0;0;1;1;0;1;1;1].

Lemma Kr_cc n a b c d:
  Kr n a b c d = cconfig_to_config ([], Kr_list n a b c d, 0, F).
Proof.
  unfold Kr, Kr_list, cconfig_to_config.
  cbn [Str_app]. rewrite !Str_app_assoc. reflexivity.
Qed.

Definition W1 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,746);(2,20);(12,47);(1,20);(6,2);(2,4);(6,2);(1,2)])%nat.

Definition W2 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1102);(1,2);(1,38);(1,2);(7,35);(1,22);(2,4);(1,2);(2,2);(2,4);(1,2)])%nat.

Definition W3 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1374);(2,132);(6,2);(2,4);(6,7);(1,2);(1,2);(1,2)])%nat.

Definition W4 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1599);(1,94);(1,2);(7,35);(1,20);(2,20);(1,2);(1,4);(1,2);(3,4);(1,2)])%nat.

Definition W5 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1798);(1,2);(2,58);(2,60);(2,44);(1,2);(1,4);(1,2);(1,4);(6,8);(3,6);(1,2)])%nat.

Lemma init1:
  c0 -->* LR W1.
Proof.
  change c0 with (cconfig_to_config ([], [], 0, A)).
  unfold LR.
  apply (cc_steps'_spec 694 1000 884).
  vm_compute.
  reflexivity.
Qed.

Lemma init2:
  LR W1 -->* LR W2.
Proof.
  unfold LR.
  apply (cc_steps'_spec 702 1000 616).
  vm_compute.
  reflexivity.
Qed.

Lemma init3:
  LR W2 -->* LR W3.
Proof.
  unfold LR.
  apply (cc_steps'_spec 702 1000 120).
  vm_compute.
  reflexivity.
Qed.

Lemma init4:
  LR W3 -->* LR W4.
Proof.
  unfold LR.
  apply (cc_steps'_spec 690 1000 676).
  vm_compute.
  reflexivity.
Qed.

Lemma init5:
  LR W4 -->* LR W5.
Proof.
  unfold LR.
  apply (cc_steps'_spec 702 1000 744).
  vm_compute.
  reflexivity.
Qed.

Lemma init6:
  LR W5 -->* Kr 979 17 34 22 9.
Proof.
  unfold LR.
  rewrite Kr_cc.
  apply (cc_steps'_spec 604 1000 857).
  vm_compute.
  reflexivity.
Qed.

Lemma init:
  c0 -->* Kr 979 17 34 22 9.
Proof.
  follow init1.
  follow init2.
  follow init3.
  follow init4.
  follow init5.
  apply init6.
Qed.

Lemma opening:
  Kr 979 17 34 22 9 -->* Ev 6431 20.
Proof.
  unfold Ev.
  follow (S_iter 4 979 0 31 19 8).
  follow (TO' 1075 1 4 8).
  follow (S_iter 4 1369 2 45 14 8).
  follow (T6' 1465 15 0 8).
  follow (S_iter 6 1761 3 45 14 8).
  follow (T8' 1905 16 11).
  follow (S_iter 5 2175 2 40 41 8).
  follow (T6' 2295 12 27 10).
  follow (S_iter 12 2591 3 47 14 8).
  follow (T8' 2879 30 23).
  follow (S_iter 9 3149 0 40 53 8).
  follow (TO' 3365 20 38 18).
  follow (S_iter 17 3659 3 55 14 8).
  follow (T8' 4067 48 33).
  follow (S_iter 13 4337 2 40 63 8).
  follow (T6' 4649 28 49 26).
  follow (S_iter 22 4945 1 63 14 8).
  follow (TE' 5473 66 43).
  follow (S_iter 16 5751 2 38 75 8).
  follow (T6' 6135 32 61 32).
  finish.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: { follow init. apply opening. }
  apply (progress_nonhalt_simple tm (nat*nat) (fun p => Ev (fst p) (snd p)) (6431,20)).
  intros [N X].
  exists (48*X+716+N, 4+X).
  apply DC.
Qed.

End TM1.
Print Assumptions TM1.nonhalt.



Module TM2.
Import BusyCoq.Individual62.

Import ZArith Lia.

Import String.

Import List.

Import BusyCoq.ES_v3.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA").

Notation tmP := TM1.tm.

Notation "c -->* c'" := (c -[ tmP ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tmP ]->+ c') (at level 40).

Notation G := TM1.G.

Notation Kr := TM1.Kr.

Ltac ES_v3.es_v3_pre ::= unfold Kr, G.

Notation S_step := TM1.S_step.

Notation TE := TM1.TE.

Notation TO := TM1.TO.

Notation T6 := TM1.T6.

Notation T8 := TM1.T8.

Notation S_step' := TM1.S_step'.

Notation TE' := TM1.TE'.

Notation TO' := TM1.TO'.

Notation T6' := TM1.T6'.

Notation T8' := TM1.T8'.

Notation S_iter := TM1.S_iter.

Notation Ev := TM1.Ev.

Notation prog_eq := TM1.prog_eq.

Notation DC := TM1.DC.

Notation cc_steps := TM1.cc_steps.

Notation cc_steps_spec := TM1.cc_steps_spec.

Notation cc_steps' := TM1.cc_steps'.

Notation cc_steps'_spec := TM1.cc_steps'_spec.

Notation rl := TM1.rl.

Notation LR := TM1.LR.

Notation Kr_list := TM1.Kr_list.

Notation Kr_cc := TM1.Kr_cc.

Definition W1 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,750);(1,2);(2,18);(2,34);(2,6);(1,2);(1,18);(1,2);(1,20)])%nat.

Definition W2 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1094);(3,50);(2,4);(1,49);(1,20)])%nat.

Definition W3 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1362);(1,2);(2,4);(2,4);(6,71);(1,2);(1,54);(2,20);(1,2);(1,4);(1,2);(3,4);(1,2)])%nat.

Definition W4 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1586);(3,48);(2,4);(1,103);(1,29);(1,2);(1,7)])%nat.

Definition W5 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1787);(2,14);(2,126);(2,58);(1,2);(1,4);(1,2);(1,4);(6,4);(11,4);(1,2)])%nat.

Definition W6 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1971);(2,170);(2,4);(6,19);(1,6);(1,2);(2,2);(2,8);(1,2)])%nat.

Definition W7 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,2139);(2,142);(2,44);(2,26);(1,2);(1,7)])%nat.

Definition W8 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,2295);(1,118);(1,2);(1,52);(6,43);(1,2);(1,4);(6,4);(11,4);(1,2)])%nat.

Definition W9 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,2442);(3,92);(6,62);(2,2);(2,46);(3,2);(2,2);(2,10);(1,2);(1,6);(2,2);(2,4);(1,2)])%nat.

Lemma init1:
  E;; tape0 -->* LR W1.
Proof.
  change (E;; tape0) with (cconfig_to_config ([], [], 0, E)).
  unfold LR.
  apply (cc_steps'_spec 694 1000 787).
  vm_compute.
  reflexivity.
Qed.

Lemma init2:
  LR W1 -->* LR W2.
Proof.
  unfold LR.
  apply (cc_steps'_spec 683 1000 978).
  vm_compute.
  reflexivity.
Qed.

Lemma init3:
  LR W2 -->* LR W3.
Proof.
  unfold LR.
  apply (cc_steps'_spec 698 1000 386).
  vm_compute.
  reflexivity.
Qed.

Lemma init4:
  LR W3 -->* LR W4.
Proof.
  unfold LR.
  apply (cc_steps'_spec 690 1000 894).
  vm_compute.
  reflexivity.
Qed.

Lemma init5:
  LR W4 -->* LR W5.
Proof.
  unfold LR.
  apply (cc_steps'_spec 701 1000 10).
  vm_compute.
  reflexivity.
Qed.

Lemma init6:
  LR W5 -->* LR W6.
Proof.
  unfold LR.
  apply (cc_steps'_spec 686 1000 460).
  vm_compute.
  reflexivity.
Qed.

Lemma init7:
  LR W6 -->* LR W7.
Proof.
  unfold LR.
  apply (cc_steps'_spec 699 1000 330).
  vm_compute.
  reflexivity.
Qed.

Lemma init8:
  LR W7 -->* LR W8.
Proof.
  unfold LR.
  apply (cc_steps'_spec 697 1000 792).
  vm_compute.
  reflexivity.
Qed.

Lemma init9:
  LR W8 -->* LR W9.
Proof.
  unfold LR.
  apply (cc_steps'_spec 702 1000 214).
  vm_compute.
  reflexivity.
Qed.

Lemma init10:
  LR W9 -->* Kr 1291 35 38 21 9.
Proof.
  unfold LR.
  rewrite Kr_cc.
  apply (cc_steps'_spec 695 1000 979).
  vm_compute.
  reflexivity.
Qed.

Lemma init:
  E;; tape0 -->* Kr 1291 35 38 21 9.
Proof.
  follow init1.
  follow init2.
  follow init3.
  follow init4.
  follow init5.
  follow init6.
  follow init7.
  follow init8.
  follow init9.
  apply init10.
Qed.

Lemma opening:
  Kr 1291 35 38 21 9 -->* Ev 6649 21.
Proof.
  unfold Ev.
  follow (S_iter 8 1291 2 35 18 8).
  follow (T6' 1483 13 4 16).
  follow (S_iter 7 1779 1 53 14 8).
  follow (TE' 1947 26 13).
  follow (S_iter 6 2225 2 38 45 8).
  follow (T6' 2369 12 31 12).
  follow (S_iter 13 2665 3 49 14 8).
  follow (T8' 2977 34 25).
  follow (S_iter 10 3247 0 40 55 8).
  follow (TO' 3487 22 40 20).
  follow (S_iter 18 3781 3 57 14 8).
  follow (T8' 4213 52 35).
  follow (S_iter 14 4483 2 40 65 8).
  follow (T6' 4819 30 51 28).
  follow (S_iter 23 5115 1 65 14 8).
  follow (TE' 5667 70 45).
  follow (S_iter 17 5945 2 38 77 8).
  follow (T6' 6353 34 63 34).
  finish.
Qed.

Lemma nonhaltP: ~halts tmP (E;; tape0).
Proof.
  eapply multistep_nonhalt.
  1: { follow init. apply opening. }
  apply (progress_nonhalt_simple tmP (nat*nat) (fun p => Ev (fst p) (snd p)) (6649,21)).
  intros [N X].
  exists (48*X+716+N, 4+X).
  apply DC.
Qed.

Definition phi (q : Q) : Q :=
  match q with
  | A => E | B => F | C => B | D => C | E => A | F => D
  end.

Lemma perm: Perm tm tmP phi.
Proof.
  split.
  - intros [] [] H; cbn in *; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in *; inversion H; subst; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  intros H.
  change (halts tm (A;; tape0)) in H.
  exact (nonhaltP (perm_halts _ _ _ _ _ perm H)).
Qed.

End TM2.
Print Assumptions TM2.nonhalt.



Module TM3.
Import BusyCoq.Individual62.

Import ZArith Lia.

Import String.

Import List.

Import BusyCoq.ES_v3.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF").

Notation tmP := TM1.tm.

Notation "c -->* c'" := (c -[ tmP ]->* c') (at level 40).

Notation "c -->+ c'" := (c -[ tmP ]->+ c') (at level 40).

Notation G := TM1.G.

Notation Kr := TM1.Kr.

Ltac ES_v3.es_v3_pre ::= unfold Kr, G.

Notation S_step := TM1.S_step.

Notation TE := TM1.TE.

Notation TO := TM1.TO.

Notation T6 := TM1.T6.

Notation T8 := TM1.T8.

Notation S_step' := TM1.S_step'.

Notation TE' := TM1.TE'.

Notation TO' := TM1.TO'.

Notation T6' := TM1.T6'.

Notation T8' := TM1.T8'.

Notation S_iter := TM1.S_iter.

Notation Ev := TM1.Ev.

Notation prog_eq := TM1.prog_eq.

Notation DC := TM1.DC.

Notation cc_steps := TM1.cc_steps.

Notation cc_steps_spec := TM1.cc_steps_spec.

Notation cc_steps' := TM1.cc_steps'.

Notation cc_steps'_spec := TM1.cc_steps'_spec.

Notation rl := TM1.rl.

Notation LR := TM1.LR.

Notation Kr_list := TM1.Kr_list.

Notation Kr_cc := TM1.Kr_cc.

Definition W1 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,732);(1,2);(2,14);(2,4);(6,51);(1,2);(1,20);(6,2);(2,4);(6,2);(1,2)])%nat.

Definition W2 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1088);(2,44);(12,35);(1,22);(2,4);(1,2);(2,2);(2,4);(1,2)])%nat.

Definition W3 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1365);(2,130);(6,4);(2,2);(2,8);(1,2);(1,2);(1,2);(1,2);(1,2)])%nat.

Definition W4 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1593);(1,94);(1,2);(7,35);(1,20);(2,20);(1,2);(1,4);(1,2);(3,4);(1,2)])%nat.

Definition W5 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1792);(1,2);(2,58);(2,60);(2,44);(1,2);(1,4);(1,2);(1,4);(6,8);(3,6);(1,2)])%nat.

Lemma init1:
  C;; tape0 -->* LR W1.
Proof.
  change (C;; tape0) with (cconfig_to_config ([], [], 0, C)).
  unfold LR.
  apply (cc_steps'_spec 696 1000 153).
  vm_compute.
  reflexivity.
Qed.

Lemma init2:
  LR W1 -->* LR W2.
Proof.
  unfold LR.
  apply (cc_steps'_spec 701 1000 948).
  vm_compute.
  reflexivity.
Qed.

Lemma init3:
  LR W2 -->* LR W3.
Proof.
  unfold LR.
  apply (cc_steps'_spec 696 1000 114).
  vm_compute.
  reflexivity.
Qed.

Lemma init4:
  LR W3 -->* LR W4.
Proof.
  unfold LR.
  apply (cc_steps'_spec 700 1000 790).
  vm_compute.
  reflexivity.
Qed.

Lemma init5:
  LR W4 -->* LR W5.
Proof.
  unfold LR.
  apply (cc_steps'_spec 700 1000 644).
  vm_compute.
  reflexivity.
Qed.

Lemma init6:
  LR W5 -->* Kr 976 17 34 22 9.
Proof.
  unfold LR.
  rewrite Kr_cc.
  apply (cc_steps'_spec 603 1000 177).
  vm_compute.
  reflexivity.
Qed.

Lemma init:
  C;; tape0 -->* Kr 976 17 34 22 9.
Proof.
  follow init1.
  follow init2.
  follow init3.
  follow init4.
  follow init5.
  apply init6.
Qed.

Lemma opening:
  Kr 976 17 34 22 9 -->* Ev 6428 20.
Proof.
  unfold Ev.
  follow (S_iter 4 976 0 31 19 8).
  follow (TO' 1072 1 4 8).
  follow (S_iter 4 1366 2 45 14 8).
  follow (T6' 1462 15 0 8).
  follow (S_iter 6 1758 3 45 14 8).
  follow (T8' 1902 16 11).
  follow (S_iter 5 2172 2 40 41 8).
  follow (T6' 2292 12 27 10).
  follow (S_iter 12 2588 3 47 14 8).
  follow (T8' 2876 30 23).
  follow (S_iter 9 3146 0 40 53 8).
  follow (TO' 3362 20 38 18).
  follow (S_iter 17 3656 3 55 14 8).
  follow (T8' 4064 48 33).
  follow (S_iter 13 4334 2 40 63 8).
  follow (T6' 4646 28 49 26).
  follow (S_iter 22 4942 1 63 14 8).
  follow (TE' 5470 66 43).
  follow (S_iter 16 5748 2 38 75 8).
  follow (T6' 6132 32 61 32).
  finish.
Qed.

Lemma nonhaltP: ~halts tmP (C;; tape0).
Proof.
  eapply multistep_nonhalt.
  1: { follow init. apply opening. }
  apply (progress_nonhalt_simple tmP (nat*nat) (fun p => Ev (fst p) (snd p)) (6428,20)).
  intros [N X].
  exists (48*X+716+N, 4+X).
  apply DC.
Qed.

Definition phi (q : Q) : Q :=
  match q with
  | A => C | B => A | C => B | D => D | E => E | F => F
  end.

Lemma perm: Perm (flip tm) tmP phi.
Proof.
  split.
  - intros [] [] H; cbn in *; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in *; inversion H; subst; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  intros H.
  apply flip_halts in H.
  change (halts (flip tm) (A;; tape0)) in H.
  exact (nonhaltP (perm_halts _ _ _ _ _ perm H)).
Qed.

End TM3.
Print Assumptions TM3.nonhalt.
