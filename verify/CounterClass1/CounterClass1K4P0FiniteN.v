Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4FiniteN BusyCoq.CounterClass1.CounterClass1K4P0.
Require Import NArith Lia Bool.
From BusyCoq Require Import LibTactics.

Open Scope N_scope.

Definition k4n_p0_start (a b:N) : option K4NResult :=
  if (a=?0) && (b=?2) then Some (3,1) else None.

Definition k4n_p0_inc1 (a b:N) : option K4NResult :=
  if b=?1 then
    match k4n_sub a 1 with Some a' => Some (a',5) | None => None end
  else None.

Definition k4n_p0_inc2 (a b:N) : option K4NResult :=
  if b=?2 then
    match k4n_sub a 2 with Some a' => Some (a',8) | None => None end
  else None.

Definition k4n_p0_ov (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 3 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c,d) => Some (c,1+d)
      | None => None
      end
  | None => None
  end.

Definition k4n_p0_ov' (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 4 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d) =>
          match k4n_sub c0 1 with
          | Some c => Some (c,4+d)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_p0_lov2 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 4 with
          | Some d =>
              match k4n_get t 0 d with
              | Some (c1,z) =>
                  if (c0=?0) && (c1=?0) && N.odd z
                  then Some (2+N.div2 z,1) else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_p0_lov4 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 4 with
          | Some d =>
              match k4n_get t 0 d with
              | Some (c1,z) =>
                  if (c0=?0) && (c1=?0) && N.even z
                  then Some (2+N.div2 z,2) else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_p0_next (t:K4NTable) (s:K4NResult)
    : option K4NResult :=
  let '(a,b):=s in
  k4n_or_else (k4n_p0_start a b)
  (k4n_or_else (k4n_p0_inc1 a b)
  (k4n_or_else (k4n_p0_inc2 a b)
  (k4n_or_else (k4n_p0_ov t a b)
  (k4n_or_else (k4n_p0_ov' t a b)
  (k4n_or_else (k4n_p0_lov2 t a b)
                (k4n_p0_lov4 t a b)))))).

Section K4NP0Sound.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable P0: nat -> nat -> Prop.
Variable R0: K4P0Rules P P0.
Variable t: K4NTable.
Variable Ht: K4NTableSound P t.
Variable Hstart: P0 0%nat 2%nat -> P0 3%nat 1%nat.

Lemma k4n_p0_start_sound a b c d:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_start a b=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_p0_start. destruct (a=?0) eqn:Ea; [|discriminate].
  destruct (b=?2) eqn:Eb; intros HP H; try discriminate. inverts H.
  apply N.eqb_eq in Ea,Eb. subst. apply Hstart. exact HP.
Qed.

Lemma k4n_p0_inc1_sound a b c d:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_inc1 a b=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_p0_inc1. destruct (b=?1) eqn:Eb; try discriminate.
  destruct (k4n_sub a 1) as [a'|] eqn:Ea; intros HP H; try discriminate.
  inverts H. apply N.eqb_eq in Eb. subst b.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ea)) as Ha.
  rewrite N2Nat.inj_add in Ha. cbn in Ha.
  apply (k4p0_inc00_1 R0 (N.to_nat c)). applys_eq HP; lia.
Qed.

Lemma k4n_p0_inc2_sound a b c d:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_inc2 a b=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_p0_inc2. destruct (b=?2) eqn:Eb; try discriminate.
  destruct (k4n_sub a 2) as [a'|] eqn:Ea; intros HP H; try discriminate.
  inverts H. apply N.eqb_eq in Eb. subst b.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ea)) as Ha.
  rewrite N2Nat.inj_add in Ha. cbn in Ha.
  apply (k4p0_inc00_2 R0 (N.to_nat c)). applys_eq HP; lia.
Qed.

Lemma k4n_p0_ov_sound a b c d:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_ov t a b=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_p0_ov.
  destruct (k4n_sub b 3) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E; intros HP H;
    try discriminate. inverts H.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  rewrite N2Nat.inj_add in Hb. cbn in Hb.
  pose proof (N2Nat.inj_add 1 d0) as Hd. cbn in Hd. rewrite Hd.
  applys_eq (k4p0_ov R0 (N.to_nat a) (N.to_nat b')
    (N.to_nat c) (N.to_nat d0)); try lia.
  - applys_eq HP; lia.
  - exact (Ht _ _ _ _ E).
Qed.

Lemma k4n_p0_ov'_sound a b c d:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_ov' t a b=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_p0_ov'.
  destruct (k4n_sub b 4) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E; try discriminate.
  destruct (k4n_sub c0 1) as [c'|] eqn:Ec; intros HP H; try discriminate.
  inverts H.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ec)) as Hc.
  rewrite !N2Nat.inj_add in Hb,Hc. cbn in Hb,Hc.
  pose proof (N2Nat.inj_add 4 d0) as Hd. cbn in Hd. rewrite Hd.
  applys_eq (k4p0_ov' R0 (N.to_nat a) (N.to_nat b')
    (N.to_nat c) (N.to_nat d0)); try lia.
  - applys_eq HP; lia.
  - applys_eq (Ht _ _ _ _ E); lia.
Qed.

Lemma k4n_p0_lov2_sound a b c z:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_lov2 t a b=Some (c,z) ->
  P0 (N.to_nat c) (N.to_nat z).
Proof.
  unfold k4n_p0_lov2.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 4) as [d|] eqn:Ed; try discriminate.
  destruct (k4n_get t 0 d) as [[c1 z0]|] eqn:E1; try discriminate.
  destruct (c0=?0) eqn:Ec0; try discriminate.
  destruct (c1=?0) eqn:Ec1; try discriminate.
  destruct (N.odd z0) eqn:Ez; intros HP H; try discriminate. inverts H.
  apply N.eqb_eq in Ec0,Ec1. subst c0 c1.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed)) as Hd.
  rewrite !N2Nat.inj_add in Hb,Hd. cbn in Hb,Hd.
  pose proof (N2Nat.inj_add 2 (N.div2 z0)) as Hc. cbn in Hc.
  rewrite N2Nat.inj_div2 in Hc. rewrite Hc.
  applys_eq (k4p0_lov2 R0 (N.to_nat a) (N.to_nat b')
    (N.to_nat d) (Nat.div2 (N.to_nat z0))); try lia.
  - applys_eq HP; lia.
  - applys_eq (Ht _ _ _ _ E0); lia.
  - applys_eq (Ht _ _ _ _ E1); pose proof (k4n_odd_div2 z0 Ez); lia.
Qed.

Lemma k4n_p0_lov4_sound a b c z:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_lov4 t a b=Some (c,z) ->
  P0 (N.to_nat c) (N.to_nat z).
Proof.
  unfold k4n_p0_lov4.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 4) as [d|] eqn:Ed; try discriminate.
  destruct (k4n_get t 0 d) as [[c1 z0]|] eqn:E1; try discriminate.
  destruct (c0=?0) eqn:Ec0; try discriminate.
  destruct (c1=?0) eqn:Ec1; try discriminate.
  destruct (N.even z0) eqn:Ez; intros HP H; try discriminate. inverts H.
  apply N.eqb_eq in Ec0,Ec1. subst c0 c1.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed)) as Hd.
  rewrite !N2Nat.inj_add in Hb,Hd. cbn in Hb,Hd.
  pose proof (N2Nat.inj_add 2 (N.div2 z0)) as Hc. cbn in Hc.
  rewrite N2Nat.inj_div2 in Hc. rewrite Hc.
  applys_eq (k4p0_lov4 R0 (N.to_nat a) (N.to_nat b')
    (N.to_nat d) (Nat.div2 (N.to_nat z0))); try lia.
  - applys_eq HP; lia.
  - applys_eq (Ht _ _ _ _ E0); lia.
  - applys_eq (Ht _ _ _ _ E1); pose proof (k4n_even_div2 z0 Ez); lia.
Qed.

Lemma k4n_p0_next_sound a b c d:
  P0 (N.to_nat a) (N.to_nat b) ->
  k4n_p0_next t (a,b)=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  intros HP. unfold k4n_p0_next,k4n_or_else.
  destruct (k4n_p0_start a b) as [[x y]|] eqn:E0.
  { intros H; inverts H. eapply k4n_p0_start_sound; eauto. }
  destruct (k4n_p0_inc1 a b) as [[x y]|] eqn:E1.
  { intros H; inverts H. eapply k4n_p0_inc1_sound; eauto. }
  destruct (k4n_p0_inc2 a b) as [[x y]|] eqn:E2.
  { intros H; inverts H. eapply k4n_p0_inc2_sound; eauto. }
  destruct (k4n_p0_ov t a b) as [[x y]|] eqn:E3.
  { intros H; inverts H. eapply k4n_p0_ov_sound; eauto. }
  destruct (k4n_p0_ov' t a b) as [[x y]|] eqn:E4.
  { intros H; inverts H. eapply k4n_p0_ov'_sound; eauto. }
  destruct (k4n_p0_lov2 t a b) as [[x y]|] eqn:E5.
  { intros H; inverts H. eapply k4n_p0_lov2_sound; eauto. }
  eapply k4n_p0_lov4_sound; eauto.
Qed.

Definition K4NP0OptionSound (s:option K4NResult) : Prop :=
  match s with
  | Some (a,b) => P0 (N.to_nat a) (N.to_nat b)
  | None => True
  end.

Definition k4n_p0_step (s:option K4NResult) : option K4NResult :=
  match s with Some p => k4n_p0_next t p | None => None end.

Lemma k4n_p0_step_sound s:
  K4NP0OptionSound s -> K4NP0OptionSound (k4n_p0_step s).
Proof.
  destruct s as [[a b]|]; cbn [K4NP0OptionSound k4n_p0_step]; auto.
  intros HP. destruct (k4n_p0_next t (a,b)) as [[c d]|] eqn:E; cbn; auto.
  exact (k4n_p0_next_sound a b c d HP E).
Qed.

Lemma k4n_p0_iter_sound n s:
  K4NP0OptionSound s -> K4NP0OptionSound (N.iter n k4n_p0_step s).
Proof.
  intros H. induction n using N.peano_ind; [exact H|].
  rewrite N.iter_succ. apply k4n_p0_step_sound. exact IHn.
Qed.

Lemma k4n_p0_iter_result_sound n s c d:
  K4NP0OptionSound s ->
  N.iter n k4n_p0_step s=Some (c,d) ->
  P0 (N.to_nat c) (N.to_nat d).
Proof.
  intros Hs E. pose proof (k4n_p0_iter_sound n s Hs) as H.
  rewrite E in H. exact H.
Qed.

End K4NP0Sound.

Definition k4n_tm4_prebase_p0 : option K4NResult :=
  let t:=k4n_build 780 in
  N.iter 383 (k4n_p0_step t) (Some (0,2)).

Lemma k4n_tm4_prebase_p0_check:
  (let t:=k4n_build 780 in
   N.iter 383 (k4n_p0_step t) (Some (0,2)))=Some (381,21).
Proof. native_compute. reflexivity. Qed.

Lemma k4n_tm4_prebase_p0_sound P P0
    (C:K4ComplexRules P K4Low2) (R0:K4P0Rules P P0)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat)
    (Hinit:P0 0%nat 2%nat) (Hstart:P0 0%nat 2%nat -> P0 3%nat 1%nat):
  P0 381%nat 21%nat.
Proof.
  exact (k4n_p0_iter_result_sound P P0 R0 (k4n_build 780)
    (proj2 (k4n_build_sound P C Hrst 780)) Hstart
    383 (Some (0,2)) 381 21 Hinit k4n_tm4_prebase_p0_check).
Qed.
