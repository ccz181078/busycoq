From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia ZArith String List.
From BusyCoq Require Import SimplTape NatMod.
From BusyCoq Require Import DivModCases.
From BusyCoq Require ES_v2.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0LC1RE_1RD1LB_0RA---_0RE0RF_1LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [0;1;0;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[0;1] {{A}}> r) (at level 30).

Lemma LR0 l r n:
  l <* [0] <* [1]^^(n*2) <| r -->*
  l <* [1] <* [0] <* [1]^^(n*2+4) |> r.
Proof. es. Qed.

Lemma L1 l r n:
  l <* [0] <* [1]^^(n*2+5) <| r -->*
  l <| [1]^^(n*2+1) *> [0;1;1;1;1] *> r.
Proof. es. Qed.

Lemma R1 l r n:
  l |> [1]^^(n*2+1) *> [0;1;1;1;1] *> r -->*
  l <* [0] <* [1]^^(n*2+5) |> r.
Proof. es. Qed.

Notation lh1 := (0inf <* <[1]).

Lemma LRh1 r n:
  lh1 <* [0] <* [1]^^(n*2+3) <| r -->*
  lh1 <* [0] <* [1]^^3 <* [0] <* [1]^^1
      <* [0] <* [1]^^(n*2+4) |> r.
Proof. es. Qed.

Lemma LRh1' r n n0:
  lh1 <* [0] <* [1]^^(n*2+3) <* [0] <* [1]^^1
      <* [0] <* [1]^^(n0*2+3) <| r -->*
  lh1 <* [0] <* [1]^^3 <* [0] <* [1]^^1
      <* [0] <* [1]^^(n*2+3) <* [0] <* [1]^^1
      <* [0] <* [1]^^(n0*2+4) |> r.
Proof. es. Qed.

Fixpoint LC (x : list nat) : side :=
  match x with
  | [] => 0inf
  | n :: t => LC t <* [0] <* [1]^^n
  end.

Close Scope sym.

Inductive Op := I | P.

Inductive LOp : Op -> list nat -> list nat -> Prop :=
| LPush1 n t : LOp P (n::t) ((1+n)::t)
| LPush1_0 : LOp P [] [1]
| LInc0 n t t' :
    LOp P t t' ->
    LOp I ((n*2)::t) ((n*2+4)::t')
| LInc1 n t t' :
    LOp I t t' ->
    LOp I ((n*2+5)::t) ((n*2+5)::t')
| LInch n :
    LOp I [n*2+3;1] [n*2+4;1;3;1]
| LInch2 n n0 :
    LOp I [n*2+3;1;n0*2+3;1]
            [n*2+4;1;n0*2+3;1;3;1].

Open Scope sym.

Lemma LPush1_spec [x x']:
  LOp P x x' ->
  LC x' = LC x <* [1].
Proof.
  intros H; inverts H; simpl_tape; reflexivity.
Qed.

Lemma LInc_spec [x x']:
  LOp I x x' ->
  forall r, LC x <| r -->* LC x' |> r.
Proof.
  gen x'; induction x; intros.
  - inverts H.
  - inverts H; cbn[LC].
    all: try (rewrite (LPush1_spec H2); es).
    all: try (specialize (IHx _ H2); es; er; follow IHx; es).
    all: es.
Qed.

Inductive LOps : list Op -> list nat -> list nat -> Prop :=
| LOps_O x : LOps [] x x
| LOps_S h t x x0 x1 :
    LOp h x x0 ->
    LOps t x0 x1 ->
    LOps (h::t) x x1.

Lemma LOps_trans [h1 h2 x x'' x']:
  LOps h1 x x'' ->
  LOps h2 x'' x' ->
  LOps (h1++h2) x x'.
Proof.
  intros H; gen h2 x'.
  induction H; intros; cbn.
  - assumption.
  - econstructor; [eassumption|]. eapply IHLOps; eassumption.
Qed.

Definition LOps1 h1 h2 n1 n2 :=
  forall x x', LOps h2 x x' -> LOps h1 (n1::x) (n2::x').

Lemma LOps_split [h1 h2 x x']:
  LOps (h1++h2) x x' ->
  exists x'', LOps h1 x x'' /\ LOps h2 x'' x'.
Proof.
  gen h2 x x'; induction h1; intros.
  - exists x; split; [constructor|assumption].
  - cbn in H. inverts H.
    epose proof (IHh1 _ _ _ H5) as [x'' [? ?]].
    eexists; split; [econstructor|]; eassumption.
Qed.

Lemma LOps1_trans h1 h2 h3 h4 n1 n2 n3:
  LOps1 h1 h3 n1 n3 ->
  LOps1 h2 h4 n3 n2 ->
  LOps1 (h1++h2) (h3++h4) n1 n2.
Proof.
  unfold LOps1; intros.
  apply LOps_split in H1 as [x'' [? ?]].
  eapply LOps_trans; [eapply H|eapply H0]; eassumption.
Qed.

Lemma LOps1_O n: LOps1 [] [] n n.
Proof. intros x x' H; inverts H; constructor. Qed.

Ltac solve_v2 :=
  repeat
  match goal with
  | [H:LOps (_::_) _ _ |- _] => inverts H
  | [H:LOps [] _ _ |- _] => inverts H
  end.

Ltac solve_v1 :=
  solve_v2;
  repeat
  match goal with
  | [H:LOp I _ _ |- _] => eapply LInc_spec in H
  | [H:LOp P _ _ |- _] => eapply LPush1_spec in H
  end;
  cbn[LC].

Ltac solve_P := econstructor; [constructor|].
Ltac solve_I x :=
  econstructor; [applys_eq x; [f_equal; lia|eassumption]|].
Ltac solve_nil := applys_eq LOps_O; f_equal; lia.

Lemma A_odd_even n m:
  LOps1 ([P;I]^^(m*2)) ([P;I]^^m)
        (n*2+5) ((n+m*3)*2+5).
Proof.
  gen n; induction m; intros.
  - applys_eq LOps1_O; lia.
  - replace (S m*2) with (2+m*2) by lia.
    replace (S m) with (1+m) by lia.
    do 2 rewrite lpow_add.
    eapply LOps1_trans.
    2: applys_eq (IHm (n+3)); lia.
    intros x x' H; cbn in *; solve_v2.
    solve_P. solve_I (LInc0 (n+3)).
    solve_P. solve_I (LInc1 (n+3)). solve_nil.
Qed.

Lemma A_odd_odd n m:
  LOps1 ([P;I]^^(m*2+1)) (([P;I]^^m)++[P])
        (n*2+5) ((n+m*3)*2+10).
Proof.
  rewrite lpow_add.
  eapply LOps1_trans.
  - apply A_odd_even.
  - intros x x' H; cbn in *; solve_v2.
    solve_P. solve_I (LInc0 (n+m*3+3)). solve_nil.
Qed.

Lemma A_even_odd n m:
  LOps1 ([P;I]^^(m*2+1)) (I::[P;I]^^m)
        (n*2+4) ((n+m*3)*2+5).
Proof.
  replace (m*2+1) with (1+m*2) by lia.
  rewrite lpow_add.
  change (LOps1 (([P;I]^^1)++([P;I]^^(m*2)))
                ([I]++[P;I]^^m)
                (n*2+4) ((n+m*3)*2+5)).
  eapply LOps1_trans.
  - intros x x' H; cbn in *; solve_v2.
    solve_P. solve_I (LInc1 n). solve_nil.
  - applys_eq A_odd_even; lia.
Qed.

Lemma A_even_even n m:
  LOps1 ([P;I]^^((S m)*2))
        (I::([P;I]^^m)++[P])
        (n*2+4) ((n+(S m)*3)*2+4).
Proof.
  replace (S m*2) with (1+(m*2+1)) by lia.
  rewrite lpow_add.
  change (LOps1 (([P;I]^^1)++([P;I]^^(m*2+1)))
                ([I]++(([P;I]^^m)++[P]))
                (n*2+4) ((n+(S m)*3)*2+4)).
  eapply LOps1_trans.
  - intros x x' H; cbn in *; solve_v2.
    solve_P. solve_I (LInc1 n). solve_nil.
  - applys_eq A_odd_odd; lia.
Qed.

Inductive Phase :=
| QA | QAP | QIA | QIAP | QIIA | QIIAP | QPA | QPAP.

Definition phase_ops p q :=
  match p with
  | QA => [P;I]^^q
  | QAP => ([P;I]^^q)++[P]
  | QIA => [I]++([P;I]^^q)
  | QIAP => [I]++([P;I]^^q)++[P]
  | QIIA => [I;I]++([P;I]^^q)
  | QIIAP => [I;I]++([P;I]^^q)++[P]
  | QPA => [P]++([P;I]^^q)
  | QPAP => [P]++([P;I]^^q)++[P]
  end.

Definition Pass p q n p' q' n' :=
  LOps1 (phase_ops p q) (phase_ops p' q') n n'.

Lemma Pass_A_ee n m:
  Pass QA ((Nat.succ m)*2) (n*2+4) QIAP m
       ((n+(Nat.succ m)*3)*2+4).
Proof. exact (A_even_even n m). Qed.

Lemma Pass_A_eo n m:
  Pass QA (m*2+1) (n*2+4) QIA m ((n+m*3)*2+5).
Proof. exact (A_even_odd n m). Qed.

Lemma Pass_A_oe n m:
  Pass QA (m*2) (n*2+5) QA m ((n+m*3)*2+5).
Proof. exact (A_odd_even n m). Qed.

Lemma Pass_A_oo n m:
  Pass QA (m*2+1) (n*2+5) QAP m ((n+m*3)*2+10).
Proof. exact (A_odd_odd n m). Qed.

Lemma LOps1_P n: LOps1 [P] [] n (n+1).
Proof.
  intros x x' H; inverts H.
  replace (n+1) with (1+n) by lia.
  econstructor; [apply LPush1|constructor].
Qed.

Lemma Pass_post_P p q n p' q' n':
  Pass p q n p' q' n' ->
  LOps1 ((phase_ops p q)++[P]) (phase_ops p' q') n (n'+1).
Proof.
  unfold Pass, LOps1; intros H x x' K.
  eapply LOps_trans with (x'':=n'::x').
  - apply H, K.
  - replace (n'+1) with (1+n') by lia.
    econstructor; [apply LPush1|constructor].
Qed.

Lemma Pass_AP_ee n m:
  Pass QAP ((Nat.succ m)*2) (n*2+4) QIAP m
       ((n+(Nat.succ m)*3)*2+5).
Proof.
  unfold Pass; cbn [phase_ops].
  applys_eq (Pass_post_P QA ((Nat.succ m)*2) (n*2+4) QIAP m
              ((n+(Nat.succ m)*3)*2+4) (Pass_A_ee n m)); lia.
Qed.

Lemma Pass_AP_eo n m:
  Pass QAP (m*2+1) (n*2+4) QIA m ((n+m*3)*2+6).
Proof.
  unfold Pass; cbn [phase_ops].
  applys_eq (Pass_post_P QA (m*2+1) (n*2+4) QIA m
              ((n+m*3)*2+5) (Pass_A_eo n m)); lia.
Qed.

Lemma Pass_AP_oe n m:
  Pass QAP (m*2) (n*2+5) QA m ((n+m*3)*2+6).
Proof.
  unfold Pass; cbn [phase_ops].
  applys_eq (Pass_post_P QA (m*2) (n*2+5) QA m
              ((n+m*3)*2+5) (Pass_A_oe n m)); lia.
Qed.

Lemma Pass_AP_oo n m:
  Pass QAP (m*2+1) (n*2+5) QAP m ((n+m*3)*2+11).
Proof.
  unfold Pass; cbn [phase_ops].
  applys_eq (Pass_post_P QA (m*2+1) (n*2+5) QAP m
              ((n+m*3)*2+10) (Pass_A_oo n m)); lia.
Qed.

Lemma LOps1_I_even n:
  LOps1 [I] [P] (n*2+4) (n*2+8).
Proof.
  intros x x' H; solve_v2.
  solve_I (LInc0 (n+2)). solve_nil.
Qed.

Lemma LOps1_I_odd n:
  LOps1 [I] [I] (n*2+5) (n*2+5).
Proof.
  intros x x' H; solve_v2.
  econstructor; [econstructor; eassumption|constructor].
Qed.

Lemma Pass_pre_I_even p q n' p' q' n:
  Pass p q (n*2+8) p' q' n' ->
  LOps1 ([I]++phase_ops p q) ([P]++phase_ops p' q')
        (n*2+4) n'.
Proof.
  intros H; eapply LOps1_trans; [apply LOps1_I_even|exact H].
Qed.

Lemma Pass_pre_I_odd p q n' p' q' n:
  Pass p q (n*2+5) p' q' n' ->
  LOps1 ([I]++phase_ops p q) ([I]++phase_ops p' q')
        (n*2+5) n'.
Proof.
  intros H; eapply LOps1_trans; [apply LOps1_I_odd|exact H].
Qed.

Lemma Pass_pre_P p q n0 n' p' q':
  Pass p q (n0+1) p' q' n' ->
  LOps1 ([P]++phase_ops p q) (phase_ops p' q') n0 n'.
Proof.
  unfold Pass, LOps1; intros H x x' K.
  eapply LOps_trans with (x'':=(n0+1)::x).
  - replace (n0+1) with (1+n0) by lia.
    econstructor; [apply LPush1|constructor].
  - apply H, K.
Qed.

Lemma Pass_IA_ee n m:
  Pass QIA ((Nat.succ m)*2) (n*2+4) QAP (Nat.succ m)
       ((n+2+(Nat.succ m)*3)*2+4).
Proof.
  assert (HA:
    Pass QA ((Nat.succ m)*2) (n*2+8) QIAP m
         ((n+2+(Nat.succ m)*3)*2+4)).
  { applys_eq (Pass_A_ee (n+2) m); lia. }
  epose proof
    (Pass_pre_I_even QA ((Nat.succ m)*2)
       ((n+2+(Nat.succ m)*3)*2+4) QIAP m n
       HA) as H.
  unfold Pass in H |- *.
  cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IA_e0 n:
  Pass QIA 0 (n*2+4) QAP 0 (n*2+8).
Proof.
  unfold Pass; cbn [phase_ops lpow].
  exact (LOps1_I_even n).
Qed.

Lemma Pass_IA_eo n m:
  Pass QIA (m*2+1) (n*2+4) QA (Nat.succ m)
       ((n+2+m*3)*2+5).
Proof.
  assert (HA:
    Pass QA (m*2+1) (n*2+8) QIA m ((n+2+m*3)*2+5)).
  { applys_eq (Pass_A_eo (n+2) m); lia. }
  epose proof
    (Pass_pre_I_even QA (m*2+1) ((n+2+m*3)*2+5) QIA m n HA)
    as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IA_oe n m:
  Pass QIA (m*2) (n*2+5) QIA m ((n+m*3)*2+5).
Proof.
  epose proof
    (Pass_pre_I_odd QA (m*2) ((n+m*3)*2+5) QA m n
       (Pass_A_oe n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IA_oo n m:
  Pass QIA (m*2+1) (n*2+5) QIAP m ((n+m*3)*2+10).
Proof.
  epose proof
    (Pass_pre_I_odd QA (m*2+1) ((n+m*3)*2+10) QAP m n
       (Pass_A_oo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IAP_e0 n:
  Pass QIAP 0 (n*2+4) QAP 0 (n*2+9).
Proof.
  epose proof
    (Pass_post_P QIA 0 (n*2+4) QAP 0 (n*2+8) (Pass_IA_e0 n))
    as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IAP_ee n m:
  Pass QIAP ((Nat.succ m)*2) (n*2+4) QAP (Nat.succ m)
       ((n+2+(Nat.succ m)*3)*2+5).
Proof.
  epose proof
    (Pass_post_P QIA ((Nat.succ m)*2) (n*2+4) QAP (Nat.succ m)
       ((n+2+(Nat.succ m)*3)*2+4) (Pass_IA_ee n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IAP_eo n m:
  Pass QIAP (m*2+1) (n*2+4) QA (Nat.succ m)
       ((n+2+m*3)*2+6).
Proof.
  epose proof
    (Pass_post_P QIA (m*2+1) (n*2+4) QA (Nat.succ m)
       ((n+2+m*3)*2+5) (Pass_IA_eo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IAP_oe n m:
  Pass QIAP (m*2) (n*2+5) QIA m ((n+m*3)*2+6).
Proof.
  epose proof
    (Pass_post_P QIA (m*2) (n*2+5) QIA m
       ((n+m*3)*2+5) (Pass_IA_oe n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IAP_oo n m:
  Pass QIAP (m*2+1) (n*2+5) QIAP m ((n+m*3)*2+11).
Proof.
  epose proof
    (Pass_post_P QIA (m*2+1) (n*2+5) QIAP m
       ((n+m*3)*2+10) (Pass_IA_oo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IIA_e0 n:
  Pass QIIA 0 (n*2+4) QPAP 0 ((n+2)*2+8).
Proof.
  assert (HA: Pass QIA 0 (n*2+8) QAP 0 ((n+2)*2+8)).
  { applys_eq (Pass_IA_e0 (n+2)); lia. }
  epose proof
    (Pass_pre_I_even QIA 0 ((n+2)*2+8) QAP 0 n HA) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IIA_ee n m:
  Pass QIIA ((Nat.succ m)*2) (n*2+4) QPAP (Nat.succ m)
       ((n+4+(Nat.succ m)*3)*2+4).
Proof.
  assert (HA:
    Pass QIA ((Nat.succ m)*2) (n*2+8) QAP (Nat.succ m)
         ((n+4+(Nat.succ m)*3)*2+4)).
  { applys_eq (Pass_IA_ee (n+2) m); lia. }
  epose proof
    (Pass_pre_I_even QIA ((Nat.succ m)*2)
       ((n+4+(Nat.succ m)*3)*2+4) QAP (Nat.succ m) n HA) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IIA_eo n m:
  Pass QIIA (m*2+1) (n*2+4) QPA (Nat.succ m)
       ((n+4+m*3)*2+5).
Proof.
  assert (HA:
    Pass QIA (m*2+1) (n*2+8) QA (Nat.succ m)
         ((n+4+m*3)*2+5)).
  { applys_eq (Pass_IA_eo (n+2) m); lia. }
  epose proof
    (Pass_pre_I_even QIA (m*2+1)
       ((n+4+m*3)*2+5) QA (Nat.succ m) n HA) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IIA_oe n m:
  Pass QIIA (m*2) (n*2+5) QIIA m ((n+m*3)*2+5).
Proof.
  epose proof
    (Pass_pre_I_odd QIA (m*2) ((n+m*3)*2+5) QIA m n
       (Pass_IA_oe n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IIA_oo n m:
  Pass QIIA (m*2+1) (n*2+5) QIIAP m ((n+m*3)*2+10).
Proof.
  epose proof
    (Pass_pre_I_odd QIA (m*2+1) ((n+m*3)*2+10) QIAP m n
       (Pass_IA_oo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  exact H.
Qed.

Lemma Pass_IIAP_e0 n:
  Pass QIIAP 0 (n*2+4) QPAP 0 ((n+2)*2+9).
Proof.
  epose proof
    (Pass_post_P QIIA 0 (n*2+4) QPAP 0
       ((n+2)*2+8) (Pass_IIA_e0 n)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IIAP_ee n m:
  Pass QIIAP ((Nat.succ m)*2) (n*2+4) QPAP (Nat.succ m)
       ((n+4+(Nat.succ m)*3)*2+5).
Proof.
  epose proof
    (Pass_post_P QIIA ((Nat.succ m)*2) (n*2+4) QPAP (Nat.succ m)
       ((n+4+(Nat.succ m)*3)*2+4) (Pass_IIA_ee n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IIAP_eo n m:
  Pass QIIAP (m*2+1) (n*2+4) QPA (Nat.succ m)
       ((n+4+m*3)*2+6).
Proof.
  epose proof
    (Pass_post_P QIIA (m*2+1) (n*2+4) QPA (Nat.succ m)
       ((n+4+m*3)*2+5) (Pass_IIA_eo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IIAP_oe n m:
  Pass QIIAP (m*2) (n*2+5) QIIA m ((n+m*3)*2+6).
Proof.
  epose proof
    (Pass_post_P QIIA (m*2) (n*2+5) QIIA m
       ((n+m*3)*2+5) (Pass_IIA_oe n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_IIAP_oo n m:
  Pass QIIAP (m*2+1) (n*2+5) QIIAP m ((n+m*3)*2+11).
Proof.
  epose proof
    (Pass_post_P QIIA (m*2+1) (n*2+5) QIIAP m
       ((n+m*3)*2+10) (Pass_IIA_oo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_PA_ee n m:
  Pass QPA (m*2) (n*2+4) QA m ((n+m*3)*2+5).
Proof.
  epose proof
    (Pass_pre_P QA (m*2) (n*2+4) ((n+m*3)*2+5) QA m)
    as H.
  apply H. applys_eq (Pass_A_oe n m); lia.
Qed.

Lemma Pass_PA_eo n m:
  Pass QPA (m*2+1) (n*2+4) QAP m ((n+m*3)*2+10).
Proof.
  epose proof
    (Pass_pre_P QA (m*2+1) (n*2+4) ((n+m*3)*2+10) QAP m)
    as H.
  apply H. applys_eq (Pass_A_oo n m); lia.
Qed.

Lemma Pass_PA_o0 n:
  Pass QPA 0 (n*2+5) QA 0 (n*2+6).
Proof.
  unfold Pass; cbn [phase_ops lpow].
  applys_eq (LOps1_P (n*2+5)); lia.
Qed.

Lemma Pass_PA_oe n m:
  Pass QPA ((Nat.succ m)*2) (n*2+5) QIAP m
       ((n+1+(Nat.succ m)*3)*2+4).
Proof.
  epose proof
    (Pass_pre_P QA ((Nat.succ m)*2) (n*2+5)
       ((n+1+(Nat.succ m)*3)*2+4) QIAP m) as H.
  apply H. applys_eq (Pass_A_ee (n+1) m); lia.
Qed.

Lemma Pass_PA_oo n m:
  Pass QPA (m*2+1) (n*2+5) QIA m ((n+1+m*3)*2+5).
Proof.
  epose proof
    (Pass_pre_P QA (m*2+1) (n*2+5)
       ((n+1+m*3)*2+5) QIA m) as H.
  apply H. applys_eq (Pass_A_eo (n+1) m); lia.
Qed.

Lemma Pass_PAP_ee n m:
  Pass QPAP (m*2) (n*2+4) QA m ((n+m*3)*2+6).
Proof.
  epose proof
    (Pass_post_P QPA (m*2) (n*2+4) QA m
       ((n+m*3)*2+5) (Pass_PA_ee n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_PAP_eo n m:
  Pass QPAP (m*2+1) (n*2+4) QAP m ((n+m*3)*2+11).
Proof.
  epose proof
    (Pass_post_P QPA (m*2+1) (n*2+4) QAP m
       ((n+m*3)*2+10) (Pass_PA_eo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_PAP_o0 n:
  Pass QPAP 0 (n*2+5) QA 0 (n*2+7).
Proof.
  epose proof
    (Pass_post_P QPA 0 (n*2+5) QA 0 (n*2+6) (Pass_PA_o0 n))
    as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_PAP_oe n m:
  Pass QPAP ((Nat.succ m)*2) (n*2+5) QIAP m
       ((n+1+(Nat.succ m)*3)*2+5).
Proof.
  epose proof
    (Pass_post_P QPA ((Nat.succ m)*2) (n*2+5) QIAP m
       ((n+1+(Nat.succ m)*3)*2+4) (Pass_PA_oe n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma Pass_PAP_oo n m:
  Pass QPAP (m*2+1) (n*2+5) QIA m ((n+1+m*3)*2+6).
Proof.
  epose proof
    (Pass_post_P QPA (m*2+1) (n*2+5) QIA m
       ((n+1+m*3)*2+5) (Pass_PA_oo n m)) as H.
  unfold Pass in H |- *; cbn [phase_ops lpow] in H |- *.
  applys_eq H; lia.
Qed.

Lemma LIncs n x x':
  LOps ([P;I]^^n) x x' ->
  LC x |> [1;1]^^n *> 0inf -->*
  LC x' |> 0inf.
Proof.
  gen x x'; induction n; intros.
  - inverts H. finish.
  - cbn in H. inverts H. inverts H5.
    eapply evstep_trans.
    2: apply IHn; eassumption.
    eapply evstep_trans.
    2: apply LInc_spec; eassumption.
    rewrite (LPush1_spec H2). es.
Qed.

Lemma LIncs_0 n x x':
  LOps (I::I::[P;I]^^n) x x' ->
  LC ((n*2+4)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  intros H. solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  es; er. follow H2. es; er. follow H1. es.
Qed.

Lemma LIncs_1 n x x':
  LOps (P::[P;I]^^(n+2)) x x' ->
  LC ((n*2+1)::x) |> 0inf -->+
  LC x' |> 0inf.
Proof.
  replace (n+2) with (S(n+1)) by lia.
  intros H. cbn in H. solve_v1.
  eapply progress_evstep_trans.
  2: apply LIncs; eassumption.
  eapply progress_evstep_trans.
  2: apply H3.
  rewrite H1,H2. es.
Qed.

Definition S (x : list nat) := LC x |> 0inf.

Inductive BigStep : list nat -> list nat -> Prop :=
| BigStep_0 n x x0 x1 x' :
    LOp I x x0 ->
    LOp I x0 x1 ->
    LOps ([P;I]^^n) x1 x' ->
    BigStep ((n*2+4)::x) x'
| BigStep_1 n x x0 x' :
    LOp P x x0 ->
    LOps ([P;I]^^(n+2)) x0 x' ->
    BigStep ((n*2+1)::x) x'.

Lemma BigStep_spec [x x']:
  BigStep x x' -> S x -->+ S x'.
Proof.
  intros H; inverts H; unfold S.
  - apply LIncs_0.
    econstructor; [eassumption|].
    econstructor; eassumption.
  - apply LIncs_1. econstructor; eassumption.
Qed.

Close Scope sym.

(* A binary capacity carried by the right suffix.  [Lo]/[Hi] records which
   of the two disjoint coordinate intervals the capacity occupies. *)
Inductive Br := Lo | Hi.

Definition flip b := match b with Lo => Hi | Hi => Lo end.

Definition eo_src p :=
  match p with
  | QA | QAP | QIIA | QIIAP => Hi
  | QIA | QIAP | QPA | QPAP => Lo
  end.

Definition eo_dst p :=
  match p with
  | QA | QIA | QIIA | QPA => Hi
  | QAP | QIAP | QIIAP | QPAP => Lo
  end.

Definition oe_src p := flip (eo_src p).
Definition oe_dst p := flip (eo_dst p).

Definition capacity p u v :=
  match p with
  | QA | QAP | QIIA | QIIAP => u
  | QIA | QIAP => v
  | QPA | QPAP => v+1
  end.

Definition residual p u v :=
  match p with
  | QA | QIA | QIIA | QPA => u
  | QAP | QIAP | QIIAP | QPAP => v+1
  end.

Inductive NumE : Br -> nat -> nat -> nat -> list nat -> Prop :=
| NE_1a : NumE Lo 0 1 511 [38;23;9;1;3;1;3;1]
| NE_1b : NumE Lo 0 1 511 [40;23;9;1;3;1;3;1]
| NE_2a : NumE Lo 0 2 510 [33;22;9;1;3;1;3;1]
| NE_2b : NumE Lo 0 2 510 [35;22;9;1;3;1;3;1]
| NE_510a : NumE Hi 0 510 2 [33;18;8;1;3;1;3;1]
| NE_510b : NumE Hi 0 510 2 [35;18;8;1;3;1;3;1]
| NE_511a : NumE Hi 0 511 1 [34;22;9;1;3;1;3;1]
| NE_511b : NumE Hi 0 511 1 [36;22;9;1;3;1;3;1]
| NE_odd b k u v x n :
    NumE b k u v x ->
    NumE b (Datatypes.S k) (u+u) (v+v) ((n+n+5)::x)
| NE_even b k u v x n :
    NumE b k (Datatypes.S u) v x ->
    NumE (flip b) (Datatypes.S k) (v+v+1) (u+u+1) ((n+n+4)::x).

Inductive NumO : Br -> nat -> nat -> nat -> list nat -> Prop :=
| NO_0 : NumO Hi 0 30 10 [9;6;4;1]
| NO_odd b k u v x n :
    NumO b k u v x ->
    NumO b (Datatypes.S k) (u+u) (v+v) ((n+n+5)::x)
| NO_even b k u v x n :
    NumO b k (Datatypes.S u) v x ->
    NumO (flip b) (Datatypes.S k) (v+v+1) (u+u+1) ((n+n+4)::x).

Inductive BitsE : Br -> nat -> nat -> nat -> Prop :=
| BE_1 : BitsE Lo 0 1 511
| BE_2 : BitsE Lo 0 2 510
| BE_510 : BitsE Hi 0 510 2
| BE_511 : BitsE Hi 0 511 1
| BE_odd b k u v :
    BitsE b k u v ->
    BitsE b (Datatypes.S k) (u+u) (v+v)
| BE_even b k u v :
    BitsE b k (Datatypes.S u) v ->
    BitsE (flip b) (Datatypes.S k) (v+v+1) (u+u+1).

Inductive BitsO : Br -> nat -> nat -> nat -> Prop :=
| BO_0 : BitsO Hi 0 30 10
| BO_odd b k u v :
    BitsO b k u v ->
    BitsO b (Datatypes.S k) (u+u) (v+v)
| BO_even b k u v :
    BitsO b k (Datatypes.S u) v ->
    BitsO (flip b) (Datatypes.S k) (v+v+1) (u+u+1).

Lemma NumE_bits [b k u v x]: NumE b k u v x -> BitsE b k u v.
Proof. intros H; induction H; econstructor; eassumption. Qed.

Lemma NumO_bits [b k u v x]: NumO b k u v x -> BitsO b k u v.
Proof. intros H; induction H; econstructor; eassumption. Qed.

Fixpoint scale c k :=
  match k with 0 => c | Datatypes.S k => scale c k + scale c k end.

Lemma BitsE_sum [b k u v]:
  BitsE b k u v -> u+v=scale 512 k.
Proof.
  intros H; induction H.
  1-4: reflexivity.
  - cbn [scale]. rewrite <-IHBitsE. lia.
  - cbn [scale]. rewrite <-IHBitsE. lia.
Qed.

Lemma BitsO_sum [b k u v]:
  BitsO b k u v -> u+v=scale 40 k.
Proof.
  intros H; induction H.
  - reflexivity.
  - cbn [scale]. rewrite <-IHBitsO. lia.
  - cbn [scale]. rewrite <-IHBitsO. lia.
Qed.

Lemma BitsE_bounds [b k u v]:
  BitsE b k u v ->
  let t:=scale 1 k in
  match b with
  | Lo => u+1<=3*t /\ 508*t+1<=v
  | Hi => v+1<=3*t /\ 508*t+1<=u
  end.
Proof.
  intros H; induction H; cbn [scale flip] in *.
  1-4: split; lia.
  all: clear H; destruct b; cbn [flip] in IHBitsE |- *;
       destruct IHBitsE; split; lia.
Qed.

Lemma BitsO_large_upper [b k u v]:
  BitsO b k u v ->
  match b with
  | Lo => v+1<=31*scale 1 k
  | Hi => u+1<=31*scale 1 k
  end.
Proof.
  intros H; induction H; cbn [scale flip] in *.
  - lia.
  - destruct b; cbn [flip] in *; lia.
  - destruct b; cbn [flip] in *; lia.
Qed.

Lemma scale_mul c d k: scale (c*d) k=c*scale d k.
Proof. induction k; cbn [scale] in *; lia. Qed.

Lemma scale_4 k: scale 1 (k+4)=16*scale 1 k.
Proof.
  induction k.
  - reflexivity.
  - replace (Datatypes.S k+4) with (Datatypes.S (k+4)) by lia.
    cbn [scale]. rewrite IHk. lia.
Qed.

Lemma Pass_arith p q n p' q' n' a b c d:
  q=a -> n=b -> q'=c -> n'=d -> Pass p a b p' c d ->
  Pass p q n p' q' n'.
Proof. intros; subst; assumption. Qed.

Ltac pass_arith rule :=
  let T := type of rule in
  lazymatch T with Pass ?p ?q ?n ?p' ?q' ?n' =>
    eapply (Pass_arith _ _ _ _ _ _ q n q' n');
    [first [reflexivity|unfold Nat.succ; lia]|
     first [reflexivity|unfold Nat.succ; lia]|
     first [reflexivity|unfold Nat.succ; lia]|
     first [reflexivity|unfold Nat.succ; lia]|exact rule]
  end.

(* Evaluation of the finite roots uses only the proved LOp constructors. *)
Ltac calc_lop :=
  lazymatch goal with
  | |- LOp P (_::_) _ => apply LPush1
  | |- LOp P [] _ => apply LPush1_0
  | |- LOp I (?n::?t) _ =>
    let n:=eval compute in n in
    let r:=eval compute in (n mod 2) in
    lazymatch r with
    | 0 => let k:=eval compute in (n/2) in
           apply (LInc0 k); calc_lop
    | _ => first [
        let k:=eval compute in ((n-3)/2) in apply (LInch k)
      | lazymatch t with [1;?a;1] =>
          let k:=eval compute in ((n-3)/2) in
          let k0:=eval compute in ((a-3)/2) in apply (LInch2 k k0)
        end
      | let k:=eval compute in ((n-5)/2) in
        apply (LInc1 k); calc_lop ]
    end
  end.

Ltac calc_ops :=
  lazymatch goal with
  | |- LOps [] _ _ => apply LOps_O
  | |- LOps (_::_) _ _ => econstructor; [calc_lop|calc_ops]
  end.

Ltac calc_numO :=
  first [apply NO_0 |
  lazymatch goal with
  | |- NumO ?b ?k ?u ?v (?n::?t) =>
    let k':=eval compute in (k-1) in
    let r:=eval compute in (n mod 2) in
    lazymatch r with
    | 0 =>
      let a:=eval compute in ((n-4)/2) in
      let u':=eval compute in ((v-1)/2) in
      let v':=eval compute in ((u-1)/2) in
      let b':=eval compute in (flip b) in
      apply (NO_even b' k' u' v' t a); calc_numO
    | _ =>
      let a:=eval compute in ((n-5)/2) in
      let u':=eval compute in (u/2) in
      let v':=eval compute in (v/2) in
      apply (NO_odd b k' u' v' t a); calc_numO
    end
  end].

Lemma BitsO_lower [b k u v]:
  BitsO b k u v ->
  9*scale 1 k+1<=u /\ 9*scale 1 k+1<=v.
Proof.
  intros H; induction H.
  - cbn [scale]; split; lia.
  - cbn [scale]; destruct IHBitsO; split; lia.
  - cbn [scale]; destruct IHBitsO; split; lia.
Qed.

Definition CoordRange total lo hi t b u v :=
  u+v=total*t /\
  match b with
  | Lo => lo*t+1<=u /\ u<=hi*t
  | Hi => lo*t<=v /\ v+1<=hi*t
  end.

Lemma fill_range
  (B:Br->nat->nat->nat->Prop) total lo hi
  (base:forall b u v, CoordRange total lo hi 1 b u v -> B b 0 u v)
  (odd:forall b k u v, B b k u v ->
      B b (Datatypes.S k) (u+u) (v+v))
  (even:forall b k u v, B b k (Datatypes.S u) v ->
      B (flip b) (Datatypes.S k) (v+v+1) (u+u+1)):
  forall k b u v, CoordRange total lo hi (scale 1 k) b u v -> B b k u v.
Proof.
  induction k; intros b u v H.
  - apply base; exact H.
  - unfold CoordRange in H; destruct H as [HS HR].
    cbn [scale] in HS,HR.
    repeat rewrite Nat.mul_add_distr_l in HS.
    repeat rewrite Nat.mul_add_distr_l in HR.
    destruct (mod2 u) as [a ->|a ->];
      destruct (mod2 v) as [d ->|d ->]; try solve [exfalso; clear -HS; lia].
    + replace (a*2) with (a+a) by lia.
      replace (d*2) with (d+d) by lia.
      apply odd, IHk; unfold CoordRange; split; [lia|].
      destruct b; cbn in HR |- *; lia.
    + replace (1+a*2) with (a+a+1) by lia.
      replace (1+d*2) with (d+d+1) by lia.
      destruct b; [apply (even Hi k d a)|apply (even Lo k d a)];
        apply IHk; unfold CoordRange; cbn [flip] in HR |- *; split; lia.
Qed.

Ltac calc_bitsE :=
  first [apply BE_1|apply BE_2|apply BE_510|apply BE_511|
  lazymatch goal with |- BitsE ?b ?k ?u ?v =>
    let k':=eval compute in (k-1) in
    let bit:=eval compute in (u mod 2) in
    lazymatch bit with
    | 0 => let u':=eval compute in (u/2) in
           let v':=eval compute in (v/2) in
           apply (BE_odd b k' u' v'); calc_bitsE
    | _ => let u':=eval compute in ((v-1)/2) in
           let v':=eval compute in ((u-1)/2) in
           let b':=eval compute in (flip b) in
           apply (BE_even b' k' u' v'); calc_bitsE
    end
  end].

Lemma BitsE_fill k b u v:
  CoordRange 1024 1 5 (scale 1 k) b u v ->
  BitsE b (Datatypes.S k) u v.
Proof.
  apply (fill_range (fun b k u v => BitsE b (Datatypes.S k) u v)).
  - intros [] u0 v0 [HS HR]; cbn in HS,HR.
    + assert (u0=2 \/ u0=3 \/ u0=4 \/ u0=5) by lia.
      repeat destruct H as [H|H];
        assert (v0=1024-u0) by lia; subst v0; subst u0; calc_bitsE.
    + assert (v0=1 \/ v0=2 \/ v0=3 \/ v0=4) by lia.
      repeat destruct H as [H|H];
        assert (u0=1024-v0) by lia; subst u0; subst v0; calc_bitsE.
  - intros; apply BE_odd; assumption.
  - intros; apply BE_even; assumption.
Qed.

Lemma BitsO_fill k b u v:
  CoordRange 80 20 21 (scale 1 k) b u v ->
  BitsO b (Datatypes.S k) u v.
Proof.
  apply (fill_range (fun b k u v => BitsO b (Datatypes.S k) u v)).
  - intros [] u0 v0 [HS HR]; cbn in HS,HR.
    + assert (u0=21 /\ v0=59) as [-> ->] by lia.
      apply (BO_even Hi 0 29 10); apply BO_0.
    + assert (u0=60 /\ v0=20) as [-> ->] by lia.
      apply (BO_odd Hi 0 30 10); apply BO_0.
  - intros; apply BO_odd; assumption.
  - intros; apply BO_even; assumption.
Qed.

Module Estimates.
Open Scope Z_scope.

Definition Inv_numbers k s n u :=
  12<=k /\ 65536*(k+1)<=s /\
  1024*(k+1)<=16*n-s /\ 1024*(k+1)<=3*s-40*n /\
  -512*(k+1)<=60*u+12*n-s<=512*(k+1).

Lemma pair_numbers k s n u s1 n1 u1 n2 u2 a1 a2 c0 c1:
  Inv_numbers k s n u ->
  -(4*k+136)<=a1<=4*k+136 ->
  -(4*k+140)<=a2<=4*k+140 ->
  -1<=c0<=5 -> -1<=c1<=5 ->
  n1=2*n+a1 -> n2=2*n1+a2 ->
  8*s1=5*s -> 2*u1=s-u-n+c0 -> 2*u2=s1-u1-n1+c1 ->
  Inv_numbers (k+2) (4*s) n2 u2 /\
  59*s+128<=128*u1 /\ 32*u1<=15*s /\
  s+256<=256*u2 /\ 256*u2<=5*s.
Proof. unfold Inv_numbers; intros; repeat split; lia. Qed.

End Estimates.

Lemma init_long:
  c0 -->* S [34;18;8;1;3;1;3;1].
Proof. unfold S; cbn [LC]; esx. Qed.


Open Scope Z_scope.

Definition blo p :=
  match p with QA=> -2 | QAP=> -1 | QIA=>0 | QIAP=>1 |
    QIIA=>0 | QIIAP=>1 | QPA=> -1 | QPAP=>0 end.
Definition bhi p :=
  match p with QA=>2 | QAP=>3 | QIA=>4 | QIAP=>5 |
    QIIA=>8 | QIIAP=>9 | QPA=>3 | QPAP=>4 end.
Definition clo p :=
  match p with QA=> -1 | QAP=>4 | QIA=>0 | QIAP=>5 |
    QIIA=>0 | QIIAP=>5 | QPA=>3 | QPAP=>8 end.
Definition chi p :=
  match p with QA=>2 | QAP=>7 | QIA=>3 | QIAP=>8 |
    QIIA=>1 | QIIAP=>6 | QPA=>4 | QPAP=>9 end.

Definition HeadEstimate p q (x y:list nat) :=
  blo p<=Z.of_nat(hd 0%nat y)-Z.of_nat(hd 0%nat x)-3*Z.of_nat q<=bhi p.
Definition ColumnEstimate p q n p' q' n' :=
  blo p<=Z.of_nat n'-Z.of_nat n-3*Z.of_nat q<=bhi p /\
  clo p'<=Z.of_nat n'-Z.of_nat n-6*Z.of_nat q'<=chi p'.

Fixpoint Cone (k:nat) (c:Z) (x:list nat) : Prop :=
  match k with
  | O => True
  | Datatypes.S j =>
    match x with
    | [] => False
    | n::t =>
      -(8*Z.of_nat k+c)<=Z.of_nat n-2*Z.of_nat(hd 0%nat t)<=8*Z.of_nat k+c /\
      Cone j c t
    end
  end.

Definition Stable p q k l c d x y :=
  HeadEstimate p q x y /\ (Cone k c x -> Cone l d y).

Lemma stable_cons p q n p' q' n' k l c d x y:
  ColumnEstimate p q n p' q' n' ->
  Stable p' q' k l c d x y ->
  8*Z.of_nat(Datatypes.S k)+c+16<=8*Z.of_nat(Datatypes.S l)+d ->
  Stable p q (Datatypes.S k) (Datatypes.S l) c d (n::x) (n'::y).
Proof.
  unfold ColumnEstimate,Stable,HeadEstimate; cbn [hd Cone].
  intros [HB HC] [HB' HT] HL; split; [exact HB|].
  intros [HX HH]; split; [|auto].
  clear -HC HB' HX HL.
  destruct p'; cbn [blo bhi clo chi] in *; lia.
Qed.

Close Scope Z_scope.

Lemma strong_cons_odd p q n p' q' n' b k l u v c d x y:
  NumO b l u v y ->
  LOps (phase_ops p' q') x y ->
  Pass p q n p' q' (n'+n'+5) ->
  ColumnEstimate p q n p' q' (n'+n'+5) ->
  Stable p' q' k l c d x y ->
  (8*Z.of_nat(Datatypes.S k)+c+16<=8*Z.of_nat(Datatypes.S l)+d)%Z ->
  exists z, NumO b (Datatypes.S l) (u+u) (v+v) z /\
    LOps (phase_ops p q) (n::x) z /\
    Stable p q (Datatypes.S k) (Datatypes.S l) c d (n::x) z.
Proof.
  intros HY HR HP HC HS HE; exists ((n'+n'+5)::y); split.
  - apply NO_odd; exact HY.
  - split; [exact (HP _ _ HR)|eapply stable_cons; eassumption].
Qed.

Lemma strong_cons_even p q n p' q' n' b k l u v c d x y:
  NumO b l (Datatypes.S u) v y ->
  LOps (phase_ops p' q') x y ->
  Pass p q n p' q' (n'+n'+4) ->
  ColumnEstimate p q n p' q' (n'+n'+4) ->
  Stable p' q' k l c d x y ->
  (8*Z.of_nat(Datatypes.S k)+c+16<=8*Z.of_nat(Datatypes.S l)+d)%Z ->
  exists z, NumO (flip b) (Datatypes.S l) (v+v+1) (u+u+1) z /\
    LOps (phase_ops p q) (n::x) z /\
    Stable p q (Datatypes.S k) (Datatypes.S l) c d (n::x) z.
Proof.
  intros HY HR HP HC HS HE; exists ((n'+n'+4)::y); split.
  - apply NO_even; exact HY.
  - split; [exact (HP _ _ HR)|eapply stable_cons; eassumption].
Qed.

Ltac solve_column :=
  unfold ColumnEstimate; cbn [blo bhi clo chi]; split;
  lia.

Ltac strong_odd yy half :=
  lazymatch goal with H:Stable ?pp ?qq ?kk ?ll ?cc ?dd _ _ |- _ =>
    eapply strong_cons_odd with (y:=yy) (n':=half) (p':=pp) (q':=qq)
      (k:=kk) (l:=ll) (c:=cc) (d:=dd);
    [idtac|idtac|idtac|solve_column|exact H|lia]
  end.
Ltac strong_even yy half :=
  lazymatch goal with H:Stable ?pp ?qq ?kk ?ll ?cc ?dd _ _ |- _ =>
    eapply strong_cons_even with (y:=yy) (n':=half) (p':=pp) (q':=qq)
      (k:=kk) (l:=ll) (c:=cc) (d:=dd);
    [idtac|idtac|idtac|solve_column|exact H|lia]
  end.

Ltac strong_step IH HT p qq half odd rule :=
  let T := type of HT in
  lazymatch T with BitsO ?b ?k ?u ?v =>
    let yy:=fresh "y" in let HY:=fresh "HY" in let HR:=fresh "HR" in
    let HS:=fresh "HS" in
    destruct (IH p u v qq eq_refl HT
      ltac:(cbn [residual capacity]; lia)) as [yy [HY [HR HS]]];
    lazymatch odd with
    | true => strong_odd yy half
    | false => strong_even yy half
    end;
    [exact HY|exact HR|pass_arith rule]
  end.

Ltac phase_rule pp nn qq :=
  let a:=eval vm_compute in ((nn - (if Nat.even nn then 4 else 5))/2) in
  let m:=eval vm_compute in (qq/2) in
  let m0:=eval vm_compute in (qq/2-1) in
  let nb:=eval vm_compute in (nn mod 2) in
  let qb:=eval vm_compute in (qq mod 2) in
  lazymatch constr:((pp,nb,qb)) with
    | (QA, 0, 0) => constr:(Pass_A_ee a m0)
    | (QA, 0, 1) => constr:(Pass_A_eo a m)
    | (QA, 1, 0) => constr:(Pass_A_oe a m)
    | (QA, 1, 1) => constr:(Pass_A_oo a m)
    | (QAP, 0, 0) => constr:(Pass_AP_ee a m0)
    | (QAP, 0, 1) => constr:(Pass_AP_eo a m)
    | (QAP, 1, 0) => constr:(Pass_AP_oe a m)
    | (QAP, 1, 1) => constr:(Pass_AP_oo a m)
    | (QIA, 0, 0) => constr:(Pass_IA_ee a m0)
    | (QIA, 0, 1) => constr:(Pass_IA_eo a m)
    | (QIA, 1, 0) => constr:(Pass_IA_oe a m)
    | (QIA, 1, 1) => constr:(Pass_IA_oo a m)
    | (QIAP, 0, 0) => constr:(Pass_IAP_ee a m0)
    | (QIAP, 0, 1) => constr:(Pass_IAP_eo a m)
    | (QIAP, 1, 0) => constr:(Pass_IAP_oe a m)
    | (QIAP, 1, 1) => constr:(Pass_IAP_oo a m)
    | (QIIA, 0, 0) => constr:(Pass_IIA_ee a m0)
    | (QIIA, 0, 1) => constr:(Pass_IIA_eo a m)
    | (QIIA, 1, 0) => constr:(Pass_IIA_oe a m)
    | (QIIA, 1, 1) => constr:(Pass_IIA_oo a m)
    | (QIIAP, 0, 0) => constr:(Pass_IIAP_ee a m0)
    | (QIIAP, 0, 1) => constr:(Pass_IIAP_eo a m)
    | (QIIAP, 1, 0) => constr:(Pass_IIAP_oe a m)
    | (QIIAP, 1, 1) => constr:(Pass_IIAP_oo a m)
    | (QPA, 0, 0) => constr:(Pass_PA_ee a m)
    | (QPA, 0, 1) => constr:(Pass_PA_eo a m)
    | (QPA, 1, 0) => constr:(Pass_PA_oe a m0)
    | (QPA, 1, 1) => constr:(Pass_PA_oo a m)
    | (QPAP, 0, 0) => constr:(Pass_PAP_ee a m)
    | (QPAP, 0, 1) => constr:(Pass_PAP_eo a m)
    | (QPAP, 1, 0) => constr:(Pass_PAP_oe a m0)
    | (QPAP, 1, 1) => constr:(Pass_PAP_oo a m)
  end.

Ltac calc_phase :=
  lazymatch goal with |- LOps (phase_ops ?pp ?qq) (?nn::?t) ?yy =>
    let q:=eval vm_compute in qq in
    let n:=eval vm_compute in nn in
    change (LOps (phase_ops pp q) (n::t) yy);
    let len:=eval vm_compute in (List.length (n::t)) in
    let small:=eval vm_compute in (orb (orb (q=?0) (n<?4)) (len<=?4)) in
    lazymatch small with
    | true => cbn [Nat.succ phase_ops lpow app]; calc_ops
    | false => let H:=phase_rule pp n q in eapply H; calc_phase
    end
  end.

Ltac strong_root p HB HT HE :=
  destruct p; cbn [eo_src] in HB; try discriminate;
  repeat match goal with H:BitsO _ _ _ _ |- _ => inverts H end;
  cbn [eo_dst residual capacity flip] in *;
  repeat match goal with
    | H:flip ?b = _ |- _ => is_var b; destruct b; cbn [flip] in *; try discriminate
    | H:Datatypes.S ?a = ?b |- _ =>
        is_var a; let K:=fresh in assert (K:a=b-1) by (clear -H; lia); subst a
    | H:?b = Datatypes.S ?a |- _ =>
        is_var a; let K:=fresh in assert (K:a=b-1) by (clear -H; lia); subst a
    end;
  try discriminate; try solve [exfalso; lia];
  match type of HE with ?qq + ?d = ?c =>
    let v:=eval compute in (c-d) in
    assert (qq=v) by (clear -HE; lia); subst qq
  end;
  (eexists; split; [|split; [calc_phase|]];
   first [calc_numO|
     repeat match goal with H:_ |- _ => clear H end;
     unfold Stable,HeadEstimate,Nat.succ; cbn [blo bhi Cone hd];
     split; [lia|intros; cbn [Cone List.hd]; repeat split; cbn [List.hd]; lia]]).

Lemma E_to_O_stable [b k u v x] (HX:NumE b k u v x):
  forall p u' v' q,
    b=eo_src p ->
    BitsO (eo_dst p) (k+4) u' v' ->
    q+residual p u' v'=capacity p u v ->
    exists y, NumO (eo_dst p) (k+4) u' v' y /\
              LOps (phase_ops p q) x y /\
              Stable p q k (k+4) 256 240 x y.
Proof.
  induction HX; intros p u' v' q HB HT HE.
  1-8: abstract (strong_root p HB HT HE).
  - destruct p; cbn [eo_src] in HB; subst b;
      cbn [eo_dst capacity residual] in HT,HE |- *; inverts HT;
      destruct (mod2 q); subst q; try solve [exfalso; clear -HE; lia].
    1: destruct (IHHX QA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_A_oe n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_A_oo n a); flia.
    1: destruct (IHHX QAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_AP_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+1).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_AP_oe n a); flia.
    1: destruct (IHHX QIA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IA_oe n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IA_oo n a); flia.
    1: destruct (IHHX QIAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IAP_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+1).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IAP_oe n a); flia.
    1: destruct (IHHX QIIA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIA_oe n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIIAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIA_oo n a); flia.
    1: destruct (IHHX QIIAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIAP_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIIA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+1).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIAP_oe n a); flia.
    1: destruct (IHHX QIA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+1+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_PA_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct a.
    1: { pose proof (BitsE_bounds (NumE_bits HX)) as EB.
         pose proof (BitsO_large_upper H1) as OB.
         cbn [eo_src] in EB; cbn in OB.
         rewrite scale_4 in OB. exfalso; lia. }
    1: destruct (IHHX QIAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+1+(Datatypes.S a)*3).
    1: exact HY.
    1: exact HR.
    1: replace (n+n+5) with (n*2+5) by lia.
    1: replace ((n+1+Datatypes.S a*3)+(n+1+Datatypes.S a*3)+4)
         with ((n+1+Datatypes.S a*3)*2+4) by lia.
    1: exact (Pass_PA_oe n a).
    1: destruct a.
    1: { pose proof (BitsE_bounds (NumE_bits HX)) as EB.
         pose proof (BitsO_large_upper H1) as OB.
         cbn [eo_src] in EB; cbn in OB.
         rewrite scale_4 in OB. exfalso; lia. }
    1: destruct (IHHX QIAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_odd y (n+1+(Datatypes.S a)*3).
    1: exact HY.
    1: exact HR.
    1: replace (n+n+5) with (n*2+5) by lia.
    1: replace ((n+1+Datatypes.S a*3)+(n+1+Datatypes.S a*3)+5)
         with ((n+1+Datatypes.S a*3)*2+5) by lia.
    1: exact (Pass_PAP_oe n a).
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: strong_even y (n+a*3+2).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_PAP_oo n a); flia.
  - destruct p; destruct b; cbn [eo_src flip] in HB; try discriminate;
      cbn [eo_dst capacity residual] in HT,HE |- *; inverts HT;
      destruct (mod2 q); subst q; try solve [exfalso; clear -HE; lia].
    all: try (destruct b; cbn [flip] in H; try discriminate).
    1: strong_step IHHX H1 QIA a (n+a*3) true (Pass_A_eo n a).
    1: destruct a.
    1: { pose proof (BitsE_bounds (NumE_bits HX)) as EB.
         pose proof (BitsO_large_upper H1) as OB.
         cbn in EB,OB; rewrite scale_4 in OB. exfalso; lia. }
    1: strong_step IHHX H1 QIAP a (n+Datatypes.S a*3) false (Pass_A_ee n a).
    1: destruct a.
    1: { pose proof (BitsE_bounds (NumE_bits HX)) as EB.
         pose proof (BitsO_large_upper H1) as OB.
         cbn in EB,OB; rewrite scale_4 in OB. exfalso; lia. }
    1: strong_step IHHX H1 QIAP a (n+Datatypes.S a*3) true (Pass_AP_ee n a).
    1: strong_step IHHX H1 QIA a (n+a*3+1) false (Pass_AP_eo n a).
    1: strong_step IHHX H1 QA (Datatypes.S a) (n+2+a*3) true (Pass_IA_eo n a).
    1: destruct a.
    1: strong_step IHHX H1 QAP 0 (n+2) false (Pass_IA_e0 n).
    1: strong_step IHHX H1 QAP (Datatypes.S a) (n+2+Datatypes.S a*3) false (Pass_IA_ee n a).
    1: destruct a.
    1: strong_step IHHX H1 QAP 0 (n+2) true (Pass_IAP_e0 n).
    1: strong_step IHHX H1 QAP (Datatypes.S a) (n+2+Datatypes.S a*3) true (Pass_IAP_ee n a).
    1: strong_step IHHX H1 QA (Datatypes.S a) (n+3+a*3) false (Pass_IAP_eo n a).
    1: strong_step IHHX H1 QPA (Datatypes.S a) (n+4+a*3) true (Pass_IIA_eo n a).
    1: destruct a.
    1: strong_step IHHX H1 QPAP 0 (n+4) false (Pass_IIA_e0 n).
    1: strong_step IHHX H1 QPAP (Datatypes.S a) (n+4+Datatypes.S a*3) false (Pass_IIA_ee n a).
    1: destruct a.
    1: strong_step IHHX H1 QPAP 0 (n+4) true (Pass_IIAP_e0 n).
    1: strong_step IHHX H1 QPAP (Datatypes.S a) (n+4+Datatypes.S a*3) true (Pass_IIAP_ee n a).
    1: strong_step IHHX H1 QPA (Datatypes.S a) (n+5+a*3) false (Pass_IIAP_eo n a).
    1: strong_step IHHX H1 QA a (n+a*3) true (Pass_PA_ee n a).
    1: strong_step IHHX H1 QAP a (n+a*3+3) false (Pass_PA_eo n a).
    1: strong_step IHHX H1 QAP a (n+a*3+3) true (Pass_PAP_eo n a).
    1: strong_step IHHX H1 QA a (n+a*3+1) false (Pass_PAP_ee n a).
Qed.

Import Estimates.
Open Scope list.
Close Scope sym.
Close Scope Z_scope.
Open Scope nat_scope.

Lemma back_cons_odd p q n p' q' n' b k l u v c d x y:
  NumE b l u v y ->
  LOps (phase_ops p' q') x y ->
  Pass p q n p' q' (n'+n'+5) ->
  ColumnEstimate p q n p' q' (n'+n'+5) ->
  Stable p' q' k l c d x y ->
  (8*Z.of_nat(Datatypes.S k)+c+16<=8*Z.of_nat(Datatypes.S l)+d)%Z ->
  exists z, NumE b (Datatypes.S l) (u+u) (v+v) z /\
    LOps (phase_ops p q) (n::x) z /\
    Stable p q (Datatypes.S k) (Datatypes.S l) c d (n::x) z.
Proof.
  intros HY HR HP HC HS HE; exists ((n'+n'+5)::y); split.
  - apply NE_odd; exact HY.
  - split; [exact (HP _ _ HR)|eapply stable_cons; eassumption].
Qed.

Lemma back_cons_even p q n p' q' n' b k l u v c d x y:
  NumE b l (Datatypes.S u) v y ->
  LOps (phase_ops p' q') x y ->
  Pass p q n p' q' (n'+n'+4) ->
  ColumnEstimate p q n p' q' (n'+n'+4) ->
  Stable p' q' k l c d x y ->
  (8*Z.of_nat(Datatypes.S k)+c+16<=8*Z.of_nat(Datatypes.S l)+d)%Z ->
  exists z, NumE (flip b) (Datatypes.S l) (v+v+1) (u+u+1) z /\
    LOps (phase_ops p q) (n::x) z /\
    Stable p q (Datatypes.S k) (Datatypes.S l) c d (n::x) z.
Proof.
  intros HY HR HP HC HS HE; exists ((n'+n'+4)::y); split.
  - apply NE_even; exact HY.
  - split; [exact (HP _ _ HR)|eapply stable_cons; eassumption].
Qed.

Ltac back_odd yy half :=
  lazymatch goal with H:Stable ?pp ?qq ?kk ?ll ?cc ?dd _ _ |- _ =>
    eapply back_cons_odd with (y:=yy) (n':=half) (p':=pp) (q':=qq)
      (k:=kk) (l:=ll) (c:=cc) (d:=dd);
    [idtac|idtac|idtac|solve_column|exact H|lia]
  end.
Ltac back_even yy half :=
  lazymatch goal with H:Stable ?pp ?qq ?kk ?ll ?cc ?dd _ _ |- _ =>
    eapply back_cons_even with (y:=yy) (n':=half) (p':=pp) (q':=qq)
      (k:=kk) (l:=ll) (c:=cc) (d:=dd);
    [idtac|idtac|idtac|solve_column|exact H|lia]
  end.

Ltac back_step IH HT p qq half odd rule :=
  let T := type of HT in
  lazymatch T with BitsE ?b ?k ?u ?v =>
    let yy:=fresh "y" in let HY:=fresh "HY" in let HR:=fresh "HR" in
    let HS:=fresh "HS" in
    destruct (IH p u v qq eq_refl HT
      ltac:(cbn [residual capacity]; lia)) as [yy [HY [HR HS]]];
    lazymatch odd with
    | true => back_odd yy half
    | false => back_even yy half
    end;
    [exact HY|exact HR|pass_arith rule]
  end.

Ltac back_root p HB HT HE :=
  destruct p; cbn [oe_src eo_src flip] in HB; try discriminate;
  inverts HT; cbn [oe_dst eo_dst residual capacity flip] in *;
  try discriminate; try solve [exfalso; lia];
  match type of HE with ?qq + ?d = ?c =>
    let v:=eval compute in (c-d) in
    assert (qq=v) by (clear -HE; lia); subst qq
  end;
  (eexists; split; [|split; [cbn [phase_ops lpow app]; calc_ops|]];
    first [apply NE_1a|apply NE_1b|apply NE_2a|apply NE_2b|
           apply NE_510a|apply NE_510b|apply NE_511a|apply NE_511b|
           repeat match goal with H:_ |- _ => clear H end;
           unfold Stable,HeadEstimate; cbn [blo bhi Cone List.hd];
           split; [lia|intros; cbn [Cone List.hd]; repeat split; lia]]).

Lemma O_to_E_stable [b k u v x] (HX:NumO b k u v x):
  forall p u' v' q,
    b=oe_src p ->
    BitsE (oe_dst p) k u' v' ->
    q+residual p u' v'=capacity p u v ->
    exists y, NumE (oe_dst p) k u' v' y /\
              LOps (phase_ops p q) x y /\
              Stable p q k k 240 256 x y.
Proof.
  induction HX; intros p u' v' q HB HT HE.
  1: abstract (back_root p HB HT HE).
  - destruct p; cbn [oe_src eo_src flip] in HB; subst b;
      cbn [oe_dst eo_dst flip capacity residual] in HT,HE |- *; inverts HT;
      destruct (mod2 q); subst q; try solve [exfalso; clear -HE; lia].
    1: destruct (IHHX QA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_A_oe n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_A_oo n a); flia.
    1: destruct (IHHX QAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_AP_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+1).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_AP_oe n a); flia.
    1: destruct (IHHX QIA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IA_oe n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IA_oo n a); flia.
    1: destruct (IHHX QIAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IAP_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+1).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IAP_oe n a); flia.
    1: destruct (IHHX QIIA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIA_oe n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIIAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIA_oo n a); flia.
    1: destruct (IHHX QIIAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+a*3+3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIAP_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIIA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+1).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_IIAP_oe n a); flia.
    1: destruct (IHHX QIA u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+1+a*3).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_PA_oo n a); flia.
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct a.
    1: { pose proof (BitsO_lower (NumO_bits HX)) as EB.
         pose proof (BitsE_bounds H1) as OB.
         cbn [oe_src] in EB; cbn in OB.
         exfalso; lia. }
    1: destruct (IHHX QIAP (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+1+(Datatypes.S a)*3).
    1: exact HY.
    1: exact HR.
    1: replace (n+n+5) with (n*2+5) by lia.
    1: replace ((n+1+Datatypes.S a*3)+(n+1+Datatypes.S a*3)+4)
         with ((n+1+Datatypes.S a*3)*2+4) by lia.
    1: exact (Pass_PA_oe n a).
    1: destruct a.
    1: { pose proof (BitsO_lower (NumO_bits HX)) as EB.
         pose proof (BitsE_bounds H1) as OB.
         cbn [oe_src] in EB; cbn in OB.
         exfalso; lia. }
    1: destruct (IHHX QIAP u0 v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_odd y (n+1+(Datatypes.S a)*3).
    1: exact HY.
    1: exact HR.
    1: replace (n+n+5) with (n*2+5) by lia.
    1: replace ((n+1+Datatypes.S a*3)+(n+1+Datatypes.S a*3)+5)
         with ((n+1+Datatypes.S a*3)*2+5) by lia.
    1: exact (Pass_PAP_oe n a).
    1: destruct b; cbn [flip] in H; try discriminate.
    1: destruct (IHHX QIA (Datatypes.S u0) v0 a eq_refl H1
         ltac:(cbn [residual capacity]; lia)) as [y [HY [HR HS]]].
    1: back_even y (n+a*3+2).
    1: exact HY.
    1: exact HR.
    1: applys_eq (Pass_PAP_oo n a); flia.
  - destruct p; destruct b; cbn [oe_src eo_src flip] in HB; try discriminate;
      cbn [oe_dst eo_dst flip capacity residual] in HT,HE |- *; inverts HT;
      destruct (mod2 q); subst q; try solve [exfalso; clear -HE; lia].
    all: try (destruct b; cbn [flip] in H; try discriminate).
    1: back_step IHHX H1 QIA a (n+a*3) true (Pass_A_eo n a).
    1: destruct a.
    1: { pose proof (BitsO_lower (NumO_bits HX)) as EB.
         pose proof (BitsE_bounds H1) as OB.
         cbn in EB,OB; exfalso; lia. }
    1: back_step IHHX H1 QIAP a (n+Datatypes.S a*3) false (Pass_A_ee n a).
    1: destruct a.
    1: { pose proof (BitsO_lower (NumO_bits HX)) as EB.
         pose proof (BitsE_bounds H1) as OB.
         cbn in EB,OB; exfalso; lia. }
    1: back_step IHHX H1 QIAP a (n+Datatypes.S a*3) true (Pass_AP_ee n a).
    1: back_step IHHX H1 QIA a (n+a*3+1) false (Pass_AP_eo n a).
    1: back_step IHHX H1 QA (Datatypes.S a) (n+2+a*3) true (Pass_IA_eo n a).
    1: destruct a.
    1: back_step IHHX H1 QAP 0 (n+2) false (Pass_IA_e0 n).
    1: back_step IHHX H1 QAP (Datatypes.S a) (n+2+Datatypes.S a*3) false (Pass_IA_ee n a).
    1: destruct a.
    1: back_step IHHX H1 QAP 0 (n+2) true (Pass_IAP_e0 n).
    1: back_step IHHX H1 QAP (Datatypes.S a) (n+2+Datatypes.S a*3) true (Pass_IAP_ee n a).
    1: back_step IHHX H1 QA (Datatypes.S a) (n+3+a*3) false (Pass_IAP_eo n a).
    1: back_step IHHX H1 QPA (Datatypes.S a) (n+4+a*3) true (Pass_IIA_eo n a).
    1: destruct a.
    1: back_step IHHX H1 QPAP 0 (n+4) false (Pass_IIA_e0 n).
    1: back_step IHHX H1 QPAP (Datatypes.S a) (n+4+Datatypes.S a*3) false (Pass_IIA_ee n a).
    1: destruct a.
    1: back_step IHHX H1 QPAP 0 (n+4) true (Pass_IIAP_e0 n).
    1: back_step IHHX H1 QPAP (Datatypes.S a) (n+4+Datatypes.S a*3) true (Pass_IIAP_ee n a).
    1: back_step IHHX H1 QPA (Datatypes.S a) (n+5+a*3) false (Pass_IIAP_eo n a).
    1: back_step IHHX H1 QA a (n+a*3) true (Pass_PA_ee n a).
    1: back_step IHHX H1 QAP a (n+a*3+3) false (Pass_PA_eo n a).
    1: back_step IHHX H1 QAP a (n+a*3+3) true (Pass_PAP_eo n a).
    1: back_step IHHX H1 QA a (n+a*3+1) false (Pass_PAP_ee n a).
Qed.

Lemma BigStep_even_phase m x y:
  LOps (phase_ops QIIA m) x y -> BigStep ((m*2+4)::x) y.
Proof.
  cbn [phase_ops]; intros H; inverts H; inverts H5.
  econstructor; eassumption.
Qed.

Lemma BigStep_odd_phase m x y:
  LOps (phase_ops QPA (m+4)) x y -> BigStep ((m*2+5)::x) y.
Proof.
  intros H; replace (m*2+5) with ((m+2)*2+1) by lia.
  cbn [phase_ops] in H; inverts H.
  econstructor; [eassumption|].
  applys_eq H5; f_equal; lia.
Qed.

Open Scope Z_scope.

Lemma first_numbers k s n u c:
  Inv_numbers k s n u -> -1<=c<=5 ->
  0<s-u-n+c /\
  59*s+128<=64*(s-u-n+c) /\ 16*(s-u-n+c)<=15*s.
Proof. unfold Inv_numbers; intros; repeat split; lia. Qed.

Lemma second_numbers k s n u s1 n1 u1 a1 c0 c1:
  Inv_numbers k s n u ->
  -(4*k+136)<=a1<=4*k+136 ->
  -1<=c0<=5 -> -1<=c1<=5 ->
  n1=2*n+a1 -> 8*s1=5*s -> 2*u1=s-u-n+c0 ->
  0<s1-u1-n1+c1 /\
  s+256<=128*(s1-u1-n1+c1) /\ 128*(s1-u1-n1+c1)<=5*s.
Proof. unfold Inv_numbers; intros; repeat split; lia. Qed.

Lemma initial_head_estimate p q n k h x y:
  ((p=QIIA /\ n=q*2+4) \/ (p=QPA /\ n+3=q*2))%nat ->
  HeadEstimate p q x y ->
  -(8*Z.of_nat k+2*h)<=Z.of_nat n-2*Z.of_nat(hd 0%nat x)<=8*Z.of_nat k+2*h ->
  -(4*Z.of_nat k+(h+8))<=Z.of_nat(hd 0%nat y)-2*Z.of_nat n<=4*Z.of_nat k+(h+8).
Proof.
  intros [[-> Hn]|[-> Hn]] HB HE;
    unfold HeadEstimate in HB; cbn [blo bhi hd] in HB; lia.
Qed.

Close Scope Z_scope.

Lemma BitsO_between k u v:
  1<=k -> u+v=scale 40 k ->
  (59*Z.of_nat(scale 40 k)+80<=80*Z.of_nat u)%Z ->
  (4*Z.of_nat u<=3*Z.of_nat(scale 40 k))%Z -> BitsO Hi k u v.
Proof.
  intros HK HS HL HU; destruct k; [lia|].
  pose proof (scale_mul 40 1 (Datatypes.S k)) as HT.
  change (scale 40 (Datatypes.S k)=40*(scale 1 k+scale 1 k)) in HT.
  apply BitsO_fill.
  change (u+v=80*scale 1 k /\ 20*scale 1 k<=v /\ v+1<=21*scale 1 k).
  repeat split; lia.
Qed.

Lemma BitsE_between k u v:
  1<=k -> u+v=scale 512 k ->
  (Z.of_nat(scale 512 k)+1024<=1024*Z.of_nat u)%Z ->
  (1024*Z.of_nat u<=5*Z.of_nat(scale 512 k))%Z -> BitsE Lo k u v.
Proof.
  intros HK HS HL HU; destruct k; [lia|].
  pose proof (scale_mul 512 1 (Datatypes.S k)) as HT.
  change (scale 512 (Datatypes.S k)=512*(scale 1 k+scale 1 k)) in HT.
  apply BitsE_fill.
  change (u+v=1024*scale 1 k /\ 1*scale 1 k+1<=u /\ u<=5*scale 1 k).
  repeat split; lia.
Qed.

Lemma EO_scales k: 8*scale 40 (k+4)=5*scale 512 (Datatypes.S k).
Proof. induction k; cbn [scale Nat.add] in *; lia. Qed.

Lemma EO_scale_all k: 8*scale 40 (k+3)=5*scale 512 k.
Proof. induction k; cbn [scale Nat.add] in *; lia. Qed.

Lemma scale_2 c k: scale c (k+2)=4*scale c k.
Proof. induction k; cbn [scale Nat.add] in *; lia. Qed.

Lemma first_capacity k s n u cap q l (c:Z):
  Inv_numbers (Z.of_nat k) (Z.of_nat s) (Z.of_nat n) (Z.of_nat u) ->
  (-1<=c<=5)%Z ->
  (2*Z.of_nat cap-2*Z.of_nat q=Z.of_nat s-Z.of_nat u-Z.of_nat n+c)%Z ->
  1<=l -> (8*Z.of_nat(scale 40 l)=5*Z.of_nat s)%Z ->
  exists u' v', BitsO Hi l u' v' /\ q+u'=cap /\
    (2*Z.of_nat u'=Z.of_nat s-Z.of_nat u-Z.of_nat n+c)%Z.
Proof.
  intros HI HC HE HK HS.
  destruct (first_numbers _ _ _ _ _ HI HC) as [HP [HL HU]].
  assert (HQ:q<=cap) by lia.
  set (w:=cap-q).
  assert (HW:(Z.of_nat w=Z.of_nat cap-Z.of_nat q)%Z) by (unfold w; lia).
  assert (HV:w<=scale 40 l) by lia.
  exists w,(scale 40 l-w); split.
  - apply BitsO_between; lia.
  - split; lia.
Qed.


Lemma E_step k u v x:
  NumE Lo k u v x -> Cone k 256 x ->
  Inv_numbers (Z.of_nat k) (Z.of_nat(scale 512 k))
    (Z.of_nat(hd 0%nat x)) (Z.of_nat u) ->
  exists u1 v1 y (c:Z),
    NumO Hi (k+3) u1 v1 y /\ Cone (k+3) 240 y /\ BigStep x y /\
    (-1<=c<=5 /\
     2*Z.of_nat u1=Z.of_nat(scale 512 k)-Z.of_nat u-Z.of_nat(hd 0%nat x)+c /\
     -(4*Z.of_nat k+136)<=Z.of_nat(hd 0%nat y)-2*Z.of_nat(hd 0%nat x)<=4*Z.of_nat k+136)%Z.
Proof.
  intros HX HC HI.
  pose proof (BitsE_sum (NumE_bits HX)) as HS.
  remember Lo as b eqn:HB in HX.
  destruct HX; cbn [List.hd] in HI |- *.
  1-8: exfalso; unfold Inv_numbers in HI; lia.
  - subst b; cbn [Cone] in HC; destruct HC as [HC0 HC].
    pose proof (EO_scales k) as HScale.
    destruct (first_capacity _ _ _ _ (v+1) (n+4) (k+4) (-1)%Z HI
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as [u1 [v1 [HB1 [HE1 HU1]]]].
    destruct (E_to_O_stable HX QPA u1 v1 (n+4) eq_refl HB1 HE1)
      as [y [HY [HR [HH HT]]]].
    replace (Datatypes.S k+3) with (k+4) by lia.
    exists u1,v1,y,(-1)%Z; split; [exact HY|].
    split; [apply HT; exact HC|].
    split; [applys_eq (BigStep_odd_phase n x y HR); flia|].
    split; [lia|]. split; [exact HU1|].
    eapply (initial_head_estimate QPA (n+4) _ _ 128 x y).
    + right; split; [reflexivity|lia].
    + exact HH.
    + exact HC0.
  - destruct b; cbn [flip] in HB; try discriminate.
    cbn [Cone] in HC; destruct HC as [HC0 HC].
    pose proof (EO_scales k) as HScale.
    destruct (first_capacity _ _ _ _ (Datatypes.S u) n (k+4) 5%Z HI
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as [u1 [v1 [HB1 [HE1 HU1]]]].
    destruct (E_to_O_stable HX QIIA u1 v1 n eq_refl HB1 HE1)
      as [y [HY [HR [HH HT]]]].
    replace (Datatypes.S k+3) with (k+4) by lia.
    exists u1,v1,y,5%Z; split; [exact HY|].
    split; [apply HT; exact HC|].
    split; [applys_eq (BigStep_even_phase n x y HR); flia|].
    split; [lia|]. split; [exact HU1|].
    eapply (initial_head_estimate QIIA n _ _ 128 x y).
    + left; split; [reflexivity|lia].
    + exact HH.
    + exact HC0.
Qed.

Lemma E_capacity l cap q:
  1<=l ->
  (Z.of_nat(scale 512 l)+1024<=1024*(Z.of_nat cap-Z.of_nat q))%Z ->
  (1024*(Z.of_nat cap-Z.of_nat q)<=5*Z.of_nat(scale 512 l))%Z ->
  exists u v, BitsE Lo l u v /\ q+u=cap.
Proof.
  intros HK HL HU.
  assert (HQ:q<=cap) by lia.
  assert (HV:cap-q<=scale 512 l) by lia.
  exists (cap-q),(scale 512 l-(cap-q)); split.
  - apply BitsE_between; lia.
  - lia.
Qed.

Lemma O_step k u n u1 v1 y (c0:Z):
  Inv_numbers (Z.of_nat k) (Z.of_nat(scale 512 k)) (Z.of_nat n) (Z.of_nat u) ->
  NumO Hi (k+3) u1 v1 y -> Cone (k+3) 240 y ->
  (-1<=c0<=5)%Z ->
  (2*Z.of_nat u1=Z.of_nat(scale 512 k)-Z.of_nat u-Z.of_nat n+c0)%Z ->
  (-(4*Z.of_nat k+136)<=Z.of_nat(hd 0%nat y)-2*Z.of_nat n<=4*Z.of_nat k+136)%Z ->
  exists u2 v2 z (c1:Z),
    NumE Lo (k+2) u2 v2 z /\ Cone (k+2) 256 z /\ BigStep y z /\
    (-1<=c1<=5 /\
     2*Z.of_nat u2=Z.of_nat(scale 40 (k+3))-Z.of_nat u1-Z.of_nat(hd 0%nat y)+c1 /\
     -(4*Z.of_nat k+140)<=Z.of_nat(hd 0%nat z)-2*Z.of_nat(hd 0%nat y)<=4*Z.of_nat k+140)%Z.
Proof.
  intros HI HX HC HC0 HU1 HA1.
  pose proof (BitsO_sum (NumO_bits HX)) as HS.
  pose proof (EO_scale_all k) as HS1.
  pose proof (scale_2 512 k) as HS2.
  remember (k+3) as K eqn:HK in HX.
  remember Hi as b eqn:HB in HX.
  destruct HX as [|b j uu vv t m HX|b j uu vv t m HX].
  - exfalso; lia.
  - assert (j=k+2) by lia; subst j b.
    cbn [List.hd] in HA1 |- *.
    rewrite <-HK in HC; cbn [Cone] in HC; destruct HC as [HCtop HC].
    destruct (second_numbers (Z.of_nat k) (Z.of_nat(scale 512 k))
      (Z.of_nat n) (Z.of_nat u) (Z.of_nat(scale 40 (k+3)))
      (Z.of_nat(m+m+5)) (Z.of_nat(uu+uu))
      (Z.of_nat(m+m+5)-2*Z.of_nat n)%Z c0 (-1)%Z
      HI HA1 HC0 ltac:(lia) ltac:(lia) ltac:(lia) HU1) as [HP [HL HU]].
    assert (HRcap:(2*Z.of_nat(vv+1)-2*Z.of_nat(m+4)=
      Z.of_nat(scale 40 (k+3))-Z.of_nat(uu+uu)-Z.of_nat(m+m+5)-1)%Z) by lia.
    destruct (E_capacity (k+2) (vv+1) (m+4) ltac:(lia) ltac:(lia) ltac:(lia))
      as [u2 [v2 [HB2 HE2]]].
    destruct (O_to_E_stable HX QPA u2 v2 (m+4) eq_refl HB2 HE2)
      as [z [HZ [HR [HH HT]]]].
    exists u2,v2,z,(-1)%Z; split; [exact HZ|].
    split; [apply HT; exact HC|].
    split; [applys_eq (BigStep_odd_phase m t z HR); flia|].
    split; [lia|]. split; [lia|].
    pose proof (initial_head_estimate QPA (m+4) (m+m+5)
      (Datatypes.S (k+2)) 120 t z ltac:(right; split; [reflexivity|lia]) HH HCtop).
    lia.
  - assert (j=k+2) by lia; subst j.
    destruct b; cbn [flip] in HB; try discriminate.
    cbn [List.hd] in HA1 |- *.
    rewrite <-HK in HC; cbn [Cone] in HC; destruct HC as [HCtop HC].
    destruct (second_numbers (Z.of_nat k) (Z.of_nat(scale 512 k))
      (Z.of_nat n) (Z.of_nat u) (Z.of_nat(scale 40 (k+3)))
      (Z.of_nat(m+m+4)) (Z.of_nat(vv+vv+1))
      (Z.of_nat(m+m+4)-2*Z.of_nat n)%Z c0 5%Z
      HI HA1 HC0 ltac:(lia) ltac:(lia) ltac:(lia) HU1) as [HP [HL HU]].
    assert (HRcap:(2*Z.of_nat(Datatypes.S uu)-2*Z.of_nat m=
      Z.of_nat(scale 40 (k+3))-Z.of_nat(vv+vv+1)-Z.of_nat(m+m+4)+5)%Z) by lia.
    destruct (E_capacity (k+2) (Datatypes.S uu) m ltac:(lia) ltac:(lia) ltac:(lia))
      as [u2 [v2 [HB2 HE2]]].
    destruct (O_to_E_stable HX QIIA u2 v2 m eq_refl HB2 HE2)
      as [z [HZ [HR [HH HT]]]].
    exists u2,v2,z,5%Z; split; [exact HZ|].
    split; [apply HT; exact HC|].
    split; [applys_eq (BigStep_even_phase m t z HR); flia|].
    split; [lia|]. split; [lia|].
    pose proof (initial_head_estimate QIIA m (m+m+4)
      (Datatypes.S (k+2)) 120 t z ltac:(left; split; [reflexivity|lia]) HH HCtop).
    lia.
Qed.

Ltac calc_bigstep :=
  lazymatch goal with |- BigStep (?n::?t) _ =>
    let n:=eval vm_compute in n in
    let nb:=eval vm_compute in (n mod 2) in
    lazymatch nb with
    | 0 => let m:=eval vm_compute in ((n-4)/2) in
           apply (BigStep_even_phase m); calc_phase
    | _ => let m:=eval vm_compute in ((n-5)/2) in
           apply (BigStep_odd_phase m); calc_phase
    end
  end.

Inductive BigSteps : nat -> list nat -> list nat -> Prop :=
| BigSteps_0 x: BigSteps 0 x x
| BigSteps_S k x y z:
    BigStep x y -> BigSteps k y z -> BigSteps (Datatypes.S k) x z.

Lemma BigSteps_spec k x y: BigSteps k x y -> S x -[tm]->* S y.
Proof.
  intros H; induction H; [apply evstep_refl|].
  eapply evstep_trans; [apply progress_evstep, BigStep_spec; eassumption|assumption].
Qed.

Ltac init_steps fuel :=
  lazymatch fuel with
  | O => apply BigSteps_0
  | Datatypes.S ?f =>
    eapply BigSteps_S; [calc_bigstep|init_steps f]
  end.

Lemma init_large:
  c0 -[tm]->* S
    [142788;71402;35710;17840;8919;4471;2239;1105;554;285;145;64;
     33;22;9;1;3;1;3;1].
Proof.
  eapply evstep_trans; [exact init_long|].
  apply BigSteps_spec with (k:=12).
  init_steps 12.
Qed.

Close Scope Z_scope.
Open Scope nat_scope.

Inductive Invariant (x:list nat) : Prop :=
| Inv_intro k u v:
    NumE Lo k u v x -> Cone k 256 x ->
    Inv_numbers (Z.of_nat k) (Z.of_nat(scale 512 k))
      (Z.of_nat(hd 0%nat x)) (Z.of_nat u) -> Invariant x.

Lemma invariant_step x:
  Invariant x -> exists z, S x -[tm]->+ S z /\ Invariant z.
Proof.
  intros [k u v HX HC HI].
  destruct (E_step k u v x HX HC HI)
    as [u1 [v1 [y [c0 [HY [HC1 [HR1 [HB0 [HU1 HA1]]]]]]]]].
  destruct (O_step k u (hd 0 x) u1 v1 y c0 HI HY HC1 HB0 HU1 HA1)
    as [u2 [v2 [z [c1 [HZ [HC2 [HR2 [HB1 [HU2 HA2]]]]]]]]].
  exists z; split.
  - eapply progress_evstep_trans.
    + apply BigStep_spec; exact HR1.
    + apply progress_evstep, BigStep_spec; exact HR2.
  - econstructor; [exact HZ|exact HC2|].
    pose proof (EO_scale_all k) as HS1.
    destruct (pair_numbers
      (Z.of_nat k) (Z.of_nat(scale 512 k)) (Z.of_nat(hd 0 x)) (Z.of_nat u)
      (Z.of_nat(scale 40 (k+3))) (Z.of_nat(hd 0 y)) (Z.of_nat u1)
      (Z.of_nat(hd 0 z)) (Z.of_nat u2)
      (Z.of_nat(hd 0%nat y)-2*Z.of_nat(hd 0%nat x))%Z
      (Z.of_nat(hd 0%nat z)-2*Z.of_nat(hd 0%nat y))%Z c0 c1
      HI HA1 HA2 HB0 HB1 ltac:(lia) ltac:(lia) ltac:(lia) HU1 HU2)
      as [HI2 _].
    rewrite scale_2, Nat2Z.inj_add, Nat2Z.inj_mul.
    exact HI2.
Qed.

Lemma NumE_positive b k u v x: NumE b k u v x -> 1<=u /\ 1<=v.
Proof. intros H; induction H; lia. Qed.

Lemma NE_even_free b k u v x n:
  NumE b k u v x ->
  NumE (flip b) (Datatypes.S k) (v+v+1) (u+u-1) ((n+n+4)::x).
Proof.
  intros H; destruct u.
  - pose proof (NumE_positive _ _ _ _ _ H); lia.
  - applys_eq (NE_even b k u v x n H); flia.
Qed.

(* Build the capacity expression without expanding its large unary value. *)
Ltac numE_term x :=
  lazymatch x with
  | [38;23;9;1;3;1;3;1] => constr:(NE_1a)
  | [40;23;9;1;3;1;3;1] => constr:(NE_1b)
  | [33;22;9;1;3;1;3;1] => constr:(NE_2a)
  | [35;22;9;1;3;1;3;1] => constr:(NE_2b)
  | [33;18;8;1;3;1;3;1] => constr:(NE_510a)
  | [35;18;8;1;3;1;3;1] => constr:(NE_510b)
  | [34;22;9;1;3;1;3;1] => constr:(NE_511a)
  | [36;22;9;1;3;1;3;1] => constr:(NE_511b)
  | ?n::?t =>
    let H:=numE_term t in
    let T:=type of H in
    lazymatch T with NumE ?bb ?kk ?uu ?vv ?xs =>
      let nb:=eval vm_compute in (Nat.even n) in
      lazymatch nb with
      | true => let a:=eval vm_compute in ((n-4)/2) in
                constr:(NE_even_free bb kk uu vv xs a H)
      | false => let a:=eval vm_compute in ((n-5)/2) in
                 constr:(NE_odd bb kk uu vv xs a H)
      end
    end
  end.

Definition startE :=
  [142788;71402;35710;17840;8919;4471;2239;1105;554;285;145;64;
   33;22;9;1;3;1;3;1].

Lemma initial_invariant: Invariant startE.
Proof.
  unfold startE.
  lazymatch goal with |- Invariant ?x =>
    let H:=numE_term x in
    econstructor; [exact H| |]
  end.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S startE).
  - exact init_large.
  - eapply progress_nonhalt_cond with (P:=Invariant) (C:=S).
    + exact invariant_step.
    + exact initial_invariant.
Qed.

End TM12.
