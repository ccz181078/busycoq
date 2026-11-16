Require Import BusyCoq.CounterClass1.CounterClass1Common.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Definition k4_extend (B: list bool) (L T: nat) : list bool :=
  map negb B ++ repeat true L ++ false :: repeat true T.

Lemma k4_extend_length B L T:
  length (k4_extend B L T)=length B+L+1+T.
Proof.
  unfold k4_extend. rewrite !length_app, length_map, !repeat_length.
  cbn. rewrite repeat_length. lia.
Qed.

Lemma k4_extend_old B L T a:
  a<length B ->
  nth a (k4_extend B L T) false=negb (nth a B false).
Proof.
  intros Ha. unfold k4_extend. rewrite app_nth1; [|rewrite length_map; lia].
  rewrite (nth_indep (map negb B) false (negb false)); [apply map_nth|].
  rewrite length_map. lia.
Qed.

Lemma k4_extend_false_suffix B L T a:
  length B<=a -> a<length (k4_extend B L T) ->
  nth a (k4_extend B L T) false=false -> a=length B+L.
Proof.
  intros Ha Hal Hbit. unfold k4_extend in Hbit.
  rewrite app_nth2 in Hbit; [|rewrite length_map; lia].
  rewrite length_map in Hbit.
  destruct (Compare_dec.lt_dec (a-length B) L) as [Hlt|Hge].
  - rewrite app_nth1 in Hbit; [|rewrite repeat_length; lia].
    rewrite nth_repeat_lt in Hbit; congruence.
  - rewrite app_nth2 in Hbit; [|rewrite repeat_length; lia].
    rewrite repeat_length in Hbit.
    destruct (a-length B-L) as [|q] eqn:E; [lia|].
    cbn in Hbit.
    assert (q<T) by
      (rewrite k4_extend_length in Hal; lia).
    rewrite nth_repeat_lt in Hbit; congruence.
Qed.

Lemma k4_extend_true_suffix B L T a:
  length B<=a -> a<length (k4_extend B L T) ->
  nth a (k4_extend B L T) false=true ->
  (length B<=a<length B+L) \/
  (length B+L+1<=a<length B+L+1+T).
Proof.
  intros Ha Hal Hbit. unfold k4_extend in Hbit.
  rewrite app_nth2 in Hbit; [|rewrite length_map; lia].
  rewrite length_map in Hbit.
  destruct (Compare_dec.lt_dec (a-length B) L) as [Hlt|Hge].
  - left. lia.
  - right. rewrite app_nth2 in Hbit; [|rewrite repeat_length; lia].
    rewrite repeat_length in Hbit.
    destruct (a-length B-L) as [|q] eqn:E; [cbn in Hbit; congruence|].
    rewrite k4_extend_length in Hal. lia.
Qed.

Section K4PhaseProbe.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4SimpleRules P.

Lemma k4_inc01_iter e q de:
  P e 0 q de -> P (e+q) 0 0 (de+4*q).
Proof.
  revert e de. induction q as [|q IH]; intros e de HE.
  - applys_eq HE; lia.
  - applys_eq (IH (S e) (de+4)); try lia.
    applys_eq (k4_inc01 R e q de); try lia.
    applys_eq HE; lia.
Qed.

Lemma k4_second_generator A:
  1<=A -> P A 0 0 (2*A+4) -> P (A+6) 0 (A-1) 18.
Proof.
  intros HA H0.
  assert (H1: P (A+1) 1 (A+3) 1).
  { applys_eq (k4_lov1 R A (A+2)); try lia.
    applys_eq H0; lia. }
  assert (H2: P (A+2) 0 (A+3) 2).
  { applys_eq (k4_inc1 R (A+1) (A+3) 1); try lia.
    applys_eq H1; lia. }
  assert (H3: P (A+3) 0 (A+2) 6).
  { applys_eq (k4_inc01 R (A+2) (A+2) 2); try lia.
    applys_eq H2; lia. }
  assert (H4: P (A+4) 0 (A+1) 10).
  { applys_eq (k4_inc01 R (A+3) (A+1) 6); try lia.
    applys_eq H3; lia. }
  assert (H5: P (A+5) 0 A 14).
  { applys_eq (k4_inc01 R (A+4) A 10); try lia.
    applys_eq H4; lia. }
  assert (H6: P (A+6) 0 (A-1) 18).
  { applys_eq (k4_inc01 R (A+5) (A-1) 14); try lia.
    applys_eq H5; lia. }
  applys_eq H6; lia.
Qed.

Lemma k4_pointer_trace_prefix B u x y n:
  K4PointerTrace B u x y n -> K4PointerPrefix B u x y n 0 0.
Proof.
  intros HT. induction HT.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma k4_pointer_prefix_pair B u x y n xf yf:
  y<=x<=S y -> K4PointerPrefix B u x y n xf yf -> yf<=xf<=S yf.
Proof.
  intros Hxy HP. induction HP.
  - exact Hxy.
  - apply IHHP. apply (proj2 (k4_pointer_pair_step B x y Hxy)).
Qed.

Definition K4ReachPrefix (B: list bool) (v x y: nat) : Prop :=
  exists u x0 y0 n,
    0<n /\ y0<=x0<=S y0 /\ u+2*n=v /\
    K4PointerPrefix B u x0 y0 n x y.

Lemma k4_pointer_prefix_app B u x y n xm ym m xf yf:
  K4PointerPrefix B u x y n xm ym ->
  K4PointerPrefix B (u+2*n) xm ym m xf yf ->
  K4PointerPrefix B u x y (n+m) xf yf.
Proof.
  intros HP. induction HP; intros HS.
  - cbn in *. applys_eq HS; lia.
  - econstructor; eauto.
    assert (HS': K4PointerPrefix B (u+2+2*n) xf0 yf0 m xf yf) by
      (applys_eq HS; lia).
    applys_eq (IHHP HS'); lia.
Qed.

Lemma k4_next_not_11_t4 B x y:
  nth 1 B false=false -> nth 2 B false=false ->
  y<=x<=S y ->
  ~ (k4_next_x B x y=1 /\ k4_next_y B x y=1).
Proof.
  intros B1 B2 Hpair [Hx Hy].
  unfold k4_next_y, k4_next_x in *.
  destruct (nth x B false) eqn:BX,
           (nth y B false) eqn:BY; cbn in *.
  - assert (y=1 \/ y=2) by lia. destruct H; subst y;
      rewrite ?B1,?B2 in BY; discriminate.
  - assert (x=2) by lia. subst x. rewrite B2 in BX. discriminate.
  - assert (y=1) by lia. subst y. rewrite B1 in BY. discriminate.
  - lia.
Qed.

Lemma k4_next_not_21_t2 B x y:
  nth 2 B false=true ->
  y<=x<=S y ->
  ~ (k4_next_x B x y=2 /\ k4_next_y B x y=1).
Proof.
  intros B2 Hpair [Hx Hy].
  unfold k4_next_y, k4_next_x in *.
  destruct (nth x B false) eqn:BX,
           (nth y B false) eqn:BY; cbn in *.
  - lia.
  - assert (y=2) by lia. subst y. rewrite B2 in BY. discriminate.
  - lia.
  - assert (y=2) by lia. subst y. rewrite B2 in BY. discriminate.
Qed.

Lemma k4_pair_live_successor_y B x y:
  y<=x<=S y -> (x<>0 \/ y<>0) ->
  (k4_next_x B x y<>0 \/ k4_next_y B x y<>0) -> 0<y.
Proof.
  intros Hpair Hlive Hnext. destruct y; [|lia].
  assert (x=0 \/ x=1) by lia. destruct H as [E|E]; subst x.
  - destruct Hlive; contradiction.
  - assert (HX: k4_next_x B 1 0=0) by
      (unfold k4_next_x; destruct (nth 1 B false); reflexivity).
    assert (HY: k4_next_y B 1 0=0) by
      (unfold k4_next_y; rewrite HX; destruct (nth 0 B false); reflexivity).
    rewrite HX,HY in Hnext. destruct Hnext; contradiction.
Qed.

Lemma k4_prefix_not_11_t4 B u x y n xf yf:
  nth 1 B false=false -> nth 2 B false=false ->
  y<=x<=S y -> ~(x=1 /\ y=1) ->
  K4PointerPrefix B u x y n xf yf ->
  ~(xf=1 /\ yf=1).
Proof.
  intros B1 B2 Hpair Hbad HP. revert Hpair Hbad. induction HP; intros Hpair Hbad.
  - exact Hbad.
  - apply IHHP.
    + exact (proj2 (k4_pointer_pair_step B x y Hpair)).
    + exact (k4_next_not_11_t4 B x y B1 B2 Hpair).
Qed.

Lemma k4_prefix_not_21_t2 B u x y n xf yf:
  nth 2 B false=true ->
  y<=x<=S y -> ~(x=2 /\ y=1) ->
  K4PointerPrefix B u x y n xf yf ->
  ~(xf=2 /\ yf=1).
Proof.
  intros B2 Hpair Hbad HP. revert Hpair Hbad. induction HP; intros Hpair Hbad.
  - exact Hbad.
  - apply IHHP.
    + exact (proj2 (k4_pointer_pair_step B x y Hpair)).
    + exact (k4_next_not_21_t2 B x y B2 Hpair).
Qed.

Lemma k4_no_long_11_t4 B u n:
  nth 0 B false=true -> nth 1 B false=false ->
  ~ K4PointerPrefix B u 1 1 (3+n) 0 0.
Proof.
  intros B0 B1 HP.
  destruct (k4_pointer_prefix_uncons B u 1 1 (2+n) 0 0 HP) as
    (_&_&_&_&_&_&_&_&HP1).
  assert (X1: k4_next_x B 1 1=1) by
    (unfold k4_next_x; rewrite B1; reflexivity).
  assert (Y1: k4_next_y B 1 1=0) by
    (unfold k4_next_y; rewrite B1; reflexivity).
  rewrite X1,Y1 in HP1.
  destruct (k4_pointer_prefix_uncons B (u+2) 1 0 (1+n) 0 0 HP1) as
    (_&_&_&_&_&_&_&_&HP2).
  assert (X2: k4_next_x B 1 0=0) by
    (unfold k4_next_x; rewrite B1; reflexivity).
  assert (Y2: k4_next_y B 1 0=0) by
    (unfold k4_next_y; rewrite B0,X2; reflexivity).
  rewrite X2,Y2 in HP2.
  destruct (k4_pointer_prefix_uncons B (u+2+2) 0 0 n 0 0 HP2) as
    (_&_&_&_&_&_&_&Hnz&_).
  destruct Hnz; contradiction.
Qed.

Lemma k4_no_long_21_t2 B u n:
  nth 1 B false=true -> nth 2 B false=true ->
  ~ K4PointerPrefix B u 2 1 (3+n) 0 0.
Proof.
  intros B1 B2 HP.
  destruct (k4_pointer_prefix_uncons B u 2 1 (2+n) 0 0 HP) as
    (_&_&_&_&_&_&_&_&HP1).
  assert (X1: k4_next_x B 2 1=1) by
    (unfold k4_next_x; rewrite B2; reflexivity).
  assert (Y1: k4_next_y B 2 1=1) by
    (unfold k4_next_y; rewrite B1,X1; reflexivity).
  rewrite X1,Y1 in HP1.
  destruct (k4_pointer_prefix_uncons B (u+2) 1 1 (1+n) 0 0 HP1) as
    (_&_&_&_&_&_&_&_&HP2).
  assert (X2: k4_next_x B 1 1=0) by
    (unfold k4_next_x; rewrite B1; reflexivity).
  assert (Y2: k4_next_y B 1 1=0) by
    (unfold k4_next_y; rewrite B1,X2; reflexivity).
  rewrite X2,Y2 in HP2.
  destruct (k4_pointer_prefix_uncons B (u+2+2) 0 0 n 0 0 HP2) as
    (_&_&_&_&_&_&_&Hnz&_).
  destruct Hnz; contradiction.
Qed.

Lemma k4_terminal_candidates_t4 B u x y:
  nth 0 B false=true -> nth 1 B false=false -> nth 2 B false=false ->
  y<=x<=S y -> K4PointerPrefix B u x y 2 0 0 ->
  (x=2 /\ y=1) \/ (x=1 /\ y=1).
Proof.
  intros B0 B1 B2 Hxy HP.
  destruct (k4_pointer_prefix_uncons B u x y 1 0 0 HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_pointer_pair_step B x y Hxy) as [Hlow1 Hpair1].
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) 0 0 0 HP1) as
    (Hxl1&Hyl1&Hx01&Hy01&Hxu1&Hyu1&Hlen1&Hnz1&HP2).
  destruct (k4_pointer_pair_step B (k4_next_x B x y)
      (k4_next_y B x y) Hpair1) as [Hlow2 Hpair2].
  inversion HP2; subst.
  assert (Hy: y<=2) by lia.
  assert (Hx: x<=3) by lia.
  destruct y as [|[|[|y]]], x as [|[|[|[|x]]]]; try lia;
    unfold k4_next_x, k4_next_y in *;
    cbn in *; try lia; try congruence;
    destruct (nth 3 B false); cbn in *; try solve [auto | lia | congruence].
  all: try rewrite B0 in *; try rewrite B1 in *; try rewrite B2 in *;
    cbn in *; try solve [auto | lia | congruence].
  all: exfalso; destruct (nth 2 B false); cbn in H2; lia.
Qed.

Lemma k4_terminal_candidates_t2 B u x y:
  nth 0 B false=false -> nth 1 B false=true -> nth 2 B false=true ->
  y<=x<=S y -> K4PointerPrefix B u x y 2 0 0 ->
  (x=2 /\ y=2) \/ (x=2 /\ y=1).
Proof.
  intros B0 B1 B2 Hxy HP.
  destruct (k4_pointer_prefix_uncons B u x y 1 0 0 HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_pointer_pair_step B x y Hxy) as [Hlow1 Hpair1].
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) 0 0 0 HP1) as
    (Hxl1&Hyl1&Hx01&Hy01&Hxu1&Hyu1&Hlen1&Hnz1&HP2).
  destruct (k4_pointer_pair_step B (k4_next_x B x y)
      (k4_next_y B x y) Hpair1) as [Hlow2 Hpair2].
  inversion HP2; subst.
  assert (Hy: y<=2) by lia.
  assert (Hx: x<=3) by lia.
  destruct y as [|[|[|y]]], x as [|[|[|[|x]]]]; try lia;
    unfold k4_next_x, k4_next_y in *;
    cbn in *; try lia; try congruence;
    destruct (nth 3 B false); cbn in *; try solve [auto | lia | congruence].
  all: try rewrite B0 in *; try rewrite B1 in *; try rewrite B2 in *;
    cbn in *; try solve [auto | lia | congruence].
Qed.

Lemma k4_terminal_pair_t4 B u x y:
  nth 0 B false=true -> nth 1 B false=false -> nth 2 B false=false ->
  y<=x<=S y -> K4ReachPrefix B u x y ->
  K4PointerPrefix B u x y 2 0 0 -> x=2 /\ y=1.
Proof.
  intros B0 B1 B2 Hxy (u0&x0&y0&n&Hn&Hpair0&Hu&HR) HP.
  assert (HP': K4PointerPrefix B (u0+2*n) x y 2 0 0) by
    (applys_eq HP; lia).
  assert (Hall: K4PointerPrefix B u0 x0 y0 (n+2) 0 0) by
    exact (k4_pointer_prefix_app B u0 x0 y0 n x y 2 0 0 HR HP').
  assert (Hnot: ~(x=1 /\ y=1)).
  { assert (Hnot0: ~(x0=1 /\ y0=1)).
    { intros [-> ->]. destruct n as [|n]; [lia|].
      apply (k4_no_long_11_t4 B u0 n B0 B1).
      applys_eq Hall; lia. }
    eapply k4_prefix_not_11_t4; eauto. }
  destruct (k4_terminal_candidates_t4 B u x y B0 B1 B2 Hxy HP);
    tauto.
Qed.

Lemma k4_terminal_pair_t2 B u x y:
  nth 0 B false=false -> nth 1 B false=true -> nth 2 B false=true ->
  y<=x<=S y -> K4ReachPrefix B u x y ->
  K4PointerPrefix B u x y 2 0 0 -> x=2 /\ y=2.
Proof.
  intros B0 B1 B2 Hxy (u0&x0&y0&n&Hn&Hpair0&Hu&HR) HP.
  assert (HP': K4PointerPrefix B (u0+2*n) x y 2 0 0) by
    (applys_eq HP; lia).
  assert (Hall: K4PointerPrefix B u0 x0 y0 (n+2) 0 0) by
    exact (k4_pointer_prefix_app B u0 x0 y0 n x y 2 0 0 HR HP').
  assert (Hnot: ~(x=2 /\ y=1)).
  { assert (Hnot0: ~(x0=2 /\ y0=1)).
    { intros [-> ->]. destruct n as [|n]; [lia|].
      apply (k4_no_long_21_t2 B u0 n B1 B2).
      applys_eq Hall; lia. }
    eapply k4_prefix_not_21_t2; eauto. }
  destruct (k4_terminal_candidates_t2 B u x y B0 B1 B2 Hxy HP);
    tauto.
Qed.

Definition K4TopParticle (P: nat -> nat -> nat -> nat -> Prop)
    (u a z: nat) : Prop :=
  exists b d, 2*a+b=u /\ 2*z+d=u+4 /\ P a b z d.

Definition k4_top_follow (B: list bool) (x y z: nat) : nat :=
  if nth z B false then x-1 else y.

Definition K4TopFollowerOK (B: list bool) (x y z: nat) : Prop :=
  z=x \/
  (x=y /\ z=S x /\ nth z B false=true) \/
  (x=S y /\ z=y).

Lemma k4_top_follower_ok_bound B x y z:
  x<length B -> y<length B -> K4TopFollowerOK B x y z -> z<length B.
Proof.
  intros Hx Hy [-> | [[E [-> Hbit]] | [E ->]]]; try lia.
  destruct (Compare_dec.lt_dec (S x) (length B)); [lia|].
  rewrite nth_overflow in Hbit by lia. discriminate.
Qed.

Lemma k4_top_follower_ok_step B x y z:
  (x<>0 \/ y<>0) -> y<=x<=S y -> K4TopFollowerOK B x y z ->
  (nth z B false=true -> 0<x) /\
  K4TopFollowerOK B (k4_next_x B x y) (k4_next_y B x y)
    (k4_top_follow B x y z).
Proof.
  intros Hnz Hxy [-> | [[Hxy' [Hz Hbit]] | [Hxy' ->]]].
  - split.
    + intros Hbit. destruct Hnz; lia.
    + left. unfold k4_top_follow, k4_next_x. reflexivity.
  - subst y z. split; [intros; lia|].
    unfold k4_top_follow, k4_next_y, k4_next_x.
    rewrite Hbit. cbn.
    destruct (nth x B false); cbn.
    + left. reflexivity.
    + right; right. split; lia.
  - subst x. split; [intros; lia|].
    unfold k4_top_follow, k4_next_y, k4_next_x.
    destruct (nth (S y) B false), (nth y B false); cbn; left; lia.
Qed.

Lemma k4_top_follower_two B x y z:
  y<=x<=S y -> K4TopFollowerOK B x y z ->
  k4_top_follow B (k4_next_x B x y) (k4_next_y B x y)
      (k4_top_follow B x y z) =
  k4_next_x B (k4_next_x B x y) (k4_next_y B x y).
Proof.
  intros Hxy [-> | [[Hxy' [Hz Hbit]] | [Hxy' ->]]].
  - unfold k4_top_follow. reflexivity.
  - subst y z. unfold k4_top_follow, k4_next_x, k4_next_y.
    rewrite Hbit. cbn. destruct (nth x B false) eqn:EX;
      destruct (nth (x-1) B false) eqn:EM;
      rewrite ?EX,?EM; cbn; reflexivity.
  - subst x. unfold k4_top_follow, k4_next_x, k4_next_y.
    destruct (nth (S y) B false) eqn:ES;
      destruct (nth y B false) eqn:EY;
      destruct (nth (y-1) B false) eqn:EM;
      rewrite ?ES,?EY,?EM; cbn;
      replace (y-0) with y by lia; try rewrite EY; cbn; lia.
Qed.

Lemma k4_top_particle_step B u x y z a:
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  z<length B -> (nth z B false=true -> 0<x) ->
  2*length B<=u+2 -> K4TopParticle P u a z ->
  K4TopParticle P (u+2) a (k4_top_follow B x y z).
Proof.
  intros [dt [Hdt RT]] [df [Hdf RF]] Hzl Hz0 Hlen
    [b [d [Hab [Hzd HP]]]].
  destruct (nth z B false) eqn:Hz.
  - assert (Hx: 0<x) by (apply Hz0; reflexivity).
    exists (b+2),(4+dt). split; [lia|]. split.
    + unfold k4_top_follow. rewrite Hz. cbn. lia.
    + unfold k4_top_follow. rewrite Hz. cbn.
      applys_eq (k4_rov' R a b z (d-4) (x-1) dt); try lia.
      * applys_eq HP; lia.
      * applys_eq (RT z (d-4)); try assumption; lia.
  - exists (b+2),(1+df). split; [lia|]. split.
    + unfold k4_top_follow. rewrite Hz. cbn. lia.
    + unfold k4_top_follow. rewrite Hz. cbn.
      applys_eq (k4_rov R a b z (d-3) y df); try lia.
      * applys_eq HP; lia.
      * applys_eq (RF z (d-3)); try assumption; lia.
Qed.

Lemma k4_pointer_prefix_top_synced B u x y n xf yf a:
  K4PointerPrefix B u x y n xf yf ->
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  K4TopParticle P u a x -> K4TopParticle P (u+2*n) a xf.
Proof.
  intros HP. induction HP; intros RT RF HA.
  - cbn. applys_eq HA; lia.
  - destruct (k4_rows_step P R B u x y RT RF H H0 H1 H2 H3 H4 H5)
      as [RT1 RF1].
    assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF1; lia).
    assert (HA1: K4TopParticle P (u+2) a (k4_next_x B x y)).
    { applys_eq (k4_top_particle_step B u x y x a RT RF H H1 H5 HA);
        unfold k4_top_follow, k4_next_x; reflexivity || lia. }
    applys_eq (IHHP RT1 RF1' HA1); lia.
Qed.

Lemma k4_pointer_prefix_live_top B u x y n xf yf z a:
  y<=x<=S y -> K4PointerPrefix B u x y (2+n) xf yf ->
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  K4TopFollowerOK B x y z -> K4TopParticle P u a z ->
  K4TopParticle P (u+2*(2+n)) a xf.
Proof.
  intros Hxy HP RT RF HOK HA.
  destruct (k4_pointer_prefix_uncons B u x y (1+n) xf yf HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
    as [RT1 RF1].
  assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
    (applys_eq RF1; lia).
  destruct (k4_top_follower_ok_step B x y z Hnz Hxy HOK)
    as [Hz0 HOK1].
  assert (Hzl: z<length B) by
    exact (k4_top_follower_ok_bound B x y z Hxl Hyl HOK).
  assert (HA1: K4TopParticle P (u+2) a (k4_top_follow B x y z)).
  { exact (k4_top_particle_step B u x y z a RT RF Hzl Hz0 Hlen HA). }
  destruct (k4_pointer_pair_step B x y Hxy) as [Hlow Hpair].
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) n xf yf HP1) as
    (Hxl1&Hyl1&Hx01&Hy01&Hxu1&Hyu1&Hlen1&Hnz1&HP2).
  destruct (k4_rows_step P R B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) RT1 RF1' Hxl1 Hyl1 Hx01 Hy01
      Hxu1 Hyu1 Hlen1) as [RT2 RF2].
  assert (RF2': K4Row P B false (u+4+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RF2; lia).
  destruct (k4_top_follower_ok_step B _ _ _ Hnz1 Hpair HOK1)
    as [Hz01 HOK2].
  assert (Hzl1: k4_top_follow B x y z<length B) by
    exact (k4_top_follower_ok_bound B _ _ _ Hxl1 Hyl1 HOK1).
  assert (HA2: K4TopParticle P (u+4) a
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))).
  { rewrite <- (k4_top_follower_two B x y z Hxy HOK).
    applys_eq (k4_top_particle_step B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_top_follow B x y z) a
      RT1 RF1' Hzl1 Hz01 Hlen1 HA1); lia. }
  assert (HP2': K4PointerPrefix B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)) n xf yf) by
    (applys_eq HP2; lia).
  assert (RT2': K4Row P B true (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RT2; lia).
  applys_eq (k4_pointer_prefix_top_synced B (u+4) _ _ n xf yf a
    HP2' RT2' RF2' HA2); lia.
Qed.

Lemma k4_nested_absorb B u x y A C:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> 0<y ->
  K4Particle P u C y -> K4Particle P u A C ->
  K4Particle P (u+2) A (y-1) /\
  K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y) (y-1).
Proof.
  intros HB Hxy Hy [bc [dc [HCw [Hyw HC]]]]
    [b [d [HAw [HCw' HA]]]].
  assert (Hd: d=bc+4) by lia. subst d.
  split.
  - exists (b+2),(dc+4). repeat split; try lia.
    applys_eq (k4_rov' R A b C bc (y-1) dc); try lia.
    + applys_eq HA; lia.
    + applys_eq HC; lia.
  - apply k4_synced_decrement_ok; assumption.
Qed.

Lemma k4_top_nested_absorb B u x y A C:
  y<=x<=S y ->
  K4Particle P u C y -> K4TopParticle P u A C ->
  K4TopParticle P (u+2) A y /\
  K4TopFollowerOK B (k4_next_x B x y) (k4_next_y B x y) y.
Proof.
  intros Hxy [bc [dc [HCw [Hyw HC]]]]
    [b [d [HAw [HCw' HA]]]].
  assert (Hd: d=bc+3) by lia. subst d.
  split.
  - exists (b+2),(dc+1). repeat split; try lia.
    applys_eq (k4_rov R A b C bc y dc); try lia.
    + applys_eq HA; lia.
    + applys_eq HC; lia.
  - assert (E: x=y \/ x=S y) by lia. destruct E as [E|E]; subst x.
    + unfold K4TopFollowerOK, k4_next_x, k4_next_y.
      destruct (nth y B false) eqn:EY; cbn.
      * destruct y.
        -- left. reflexivity.
        -- unfold k4_next_x. rewrite EY. cbn.
           right; left. repeat split; try lia.
      * left. reflexivity.
    + unfold K4TopFollowerOK, k4_next_x, k4_next_y.
      destruct (nth (S y) B false), (nth y B false); cbn;
        left; lia.
Qed.

Lemma k4_second_generator_start B u x y A xf yf:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> 1<=A -> 2*A+5=u ->
  K4PointerPrefix B u x y 3 xf yf ->
  (xf<>0 \/ yf<>0) ->
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  K4Particle P u A y -> P A 0 0 (2*A+4) ->
  exists z3 z zt,
    K4Row P B true (u+6) xf /\
    K4Row P B false (u+7) yf /\
    yf<=xf<=S yf /\
    K4FollowerOK B xf yf z3 /\ K4Particle P (u+6) (A+3) z3 /\
    K4FollowerOK B xf yf z /\
    K4Particle P (u+6) (A+2) z /\
    K4Particle P (u+6) (A+4) z /\
    K4Particle P (u+6) (A+5) z /\
    K4TopFollowerOK B xf yf zt /\
    K4TopParticle P (u+6) (A+1) zt /\
    P (A+6) 0 (A-1) 18.
Proof.
  intros HB Hpair HApos Huw HP Hlive RT RF HA HZ.
  destruct (k4_pointer_prefix_uncons B u x y 2 xf yf HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
    as [RT1 RF1].
  assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
    (applys_eq RF1; lia).
  destruct (k4_pointer_pair_step B x y Hpair) as [Hlow1 Hpair1].
  assert (HA1: K4Particle P (u+2) A (k4_next_y B x y)).
  { applys_eq (k4_particle_step P R B u x y y A RT1 RF Hyl Hy0 Hlen HA);
      unfold k4_follow, k4_next_y; reflexivity || lia. }
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) 1 xf yf HP1) as
    (Hxl1&Hyl1&Hx01&Hy01&Hxu1&Hyu1&Hlen1&Hnz1&HP2).
  destruct (k4_rows_step P R B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) RT1 RF1' Hxl1 Hyl1 Hx01 Hy01
      Hxu1 Hyu1 Hlen1) as [RT2 RF2].
  assert (RF2': K4Row P B false (u+4+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RF2; lia).
  destruct (k4_pointer_pair_step B (k4_next_x B x y)
      (k4_next_y B x y) Hpair1) as [Hlow2 Hpair2].
  assert (HA2: K4Particle P (u+4) A
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))).
  { applys_eq (k4_particle_step P R B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_next_y B x y) A RT2 RF1'
      Hyl1 Hy01 Hlen1 HA1); unfold k4_follow, k4_next_y;
      reflexivity || lia. }
  assert (HP2': K4PointerPrefix B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      1 xf yf) by (applys_eq HP2; lia).
  assert (RT2': K4Row P B true (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RT2; lia).
  destruct (k4_pointer_prefix_uncons B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      0 xf yf HP2') as
    (Hxl2&Hyl2&Hx02&Hy02&Hxu2&Hyu2&Hlen2&Hnz2&HP3).
  destruct (k4_rows_step P R B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      RT2' RF2' Hxl2 Hyl2 Hx02 Hy02 Hxu2 Hyu2 Hlen2) as [RT3 RF3].
  inversion HP3; subst xf yf.
  destruct (k4_pointer_pair_step B
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)) Hpair2)
    as [Hlow3 Hpair3].
  assert (HG1: P (A+1) 1 (A+3) 1).
  { applys_eq (k4_lov1 R A (A+2)); try lia. applys_eq HZ; lia. }
  assert (H2: P (A+2) 0 (A+3) 2).
  { applys_eq (k4_inc1 R (A+1) (A+3) 1); try lia.
    applys_eq HG1; lia. }
  assert (H20: P (A+2) 2 (A+1) 8).
  { applys_eq (k4_inc00_2 R (A+2) 0 (A+1)); try lia.
    applys_eq H2; lia. }
  assert (HQ: P (A+1) 3 (A+2) 5).
  { applys_eq (k4_inc00_1 R (A+1) 1 (A+2)); try lia.
    applys_eq HG1; lia. }
  assert (HQ2: P (A+1) 5 (A+1) 9).
  { applys_eq (k4_rov R (A+1) 3 (A+2) 2 (A+1) 8); try lia.
    - applys_eq HQ; lia.
    - applys_eq H20; lia. }
  assert (HQ3: P (A+1) 7 A 13).
  { applys_eq (k4_rov' R (A+1) 5 (A+1) 5 A 9); try lia;
      applys_eq HQ2; lia. }
  assert (H24: P (A+2) 4 (A+1) 10).
  { applys_eq (k4_rov R (A+2) 2 (A+1) 5 (A+1) 9); try lia.
    - applys_eq H20; lia.
    - applys_eq HQ2; lia. }
  assert (H26: P (A+2) 6 A 14).
  { applys_eq (k4_rov R (A+2) 4 (A+1) 7 A 13); try lia.
    - applys_eq H24; lia.
    - applys_eq HQ3; lia. }
  assert (H30: P (A+3) 0 (A+2) 6).
  { applys_eq (k4_inc01 R (A+2) (A+2) 2); try lia.
    applys_eq H2; lia. }
  assert (H32: P (A+3) 2 A 12).
  { applys_eq (k4_rov' R (A+3) 0 (A+2) 2 A 8); try lia.
    - applys_eq H30; lia.
    - applys_eq H20; lia. }
  assert (H40: P (A+4) 0 (A+1) 10).
  { applys_eq (k4_inc01 R (A+3) (A+1) 6); try lia.
    applys_eq H30; lia. }
  assert (H42: P (A+4) 2 A 14).
  { applys_eq (k4_rov R (A+4) 0 (A+1) 7 A 13); try lia.
    - applys_eq H40; lia.
    - applys_eq HQ3; lia. }
  assert (H50: P (A+5) 0 A 14).
  { applys_eq (k4_inc01 R (A+4) A 10); try lia.
    applys_eq H40; lia. }
  assert (PA3: K4Particle P (u+2) (A+3) A).
  { exists 2,12. repeat split; try assumption; lia. }
  assert (Hy1: 0<k4_next_y B x y).
  { eapply k4_pair_live_successor_y; eauto. }
  destruct (k4_nested_absorb B (u+2) _ _ (A+3) A HB Hpair1
    Hy1 HA1 PA3) as [PA3' HOK3'].
  destruct (k4_follower_ok_step B _ _ _ HB Hnz2 HOK3')
    as [Hz30 HOK3].
  assert (Hz3l: k4_next_y B x y-1<length B) by
    (unfold K4FollowerOK in HOK3';
     destruct HOK3' as [[E F]|[[E [F G]]|[[E [F [G I]]]|[E [F G]]]]]; lia).
  assert (PA3n: K4Particle P (u+4) (A+3) (k4_next_y B x y-1)) by
    (applys_eq PA3'; lia).
  assert (PA3f: K4Particle P (u+6) (A+3)
      (k4_follow B
        (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B x y-1))).
  { applys_eq (k4_particle_step P R B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B x y-1) (A+3) RT3 RF2' Hz3l Hz30 Hlen2 PA3n); lia. }
  assert (PA2: K4Particle P (u+4) (A+2) A).
  { exists 6,14. repeat split; try assumption; lia. }
  assert (PA4: K4Particle P (u+4) (A+4) A).
  { exists 2,14. repeat split; try assumption; lia. }
  assert (PA5: K4Particle P (u+4) (A+5) A).
  { exists 0,14. repeat split; try assumption; lia. }
  assert (Hy2: 0<k4_next_y B (k4_next_x B x y) (k4_next_y B x y)).
  { eapply k4_pair_live_successor_y; eauto. }
  destruct (k4_nested_absorb B (u+4) _ _ (A+2) A HB Hpair2
    Hy2 HA2 PA2) as [PA2f HOK].
  destruct (k4_nested_absorb B (u+4) _ _ (A+4) A HB Hpair2
    Hy2 HA2 PA4) as [PA4f HOK4].
  destruct (k4_nested_absorb B (u+4) _ _ (A+5) A HB Hpair2
    Hy2 HA2 PA5) as [PA5f HOK5].
  assert (PT: K4TopParticle P (u+4) (A+1) A).
  { exists 7,13. repeat split; try assumption; lia. }
  destruct (k4_top_nested_absorb B (u+4) _ _ (A+1) A Hpair2 HA2 PT)
    as [PTf HTOK].
  assert (RT3n: K4Row P B true (u+6)
      (k4_next_x B (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)))) by
    (applys_eq RT3; lia).
  assert (RF3n: K4Row P B false (u+7)
      (k4_next_y B (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)))) by
    (applys_eq RF3; lia).
  assert (PA2n: K4Particle P (u+6) (A+2)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1)) by
    (applys_eq PA2f; lia).
  assert (PA4n: K4Particle P (u+6) (A+4)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1)) by
    (applys_eq PA4f; lia).
  assert (PA5n: K4Particle P (u+6) (A+5)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1)) by
    (applys_eq PA5f; lia).
  assert (PTn: K4TopParticle P (u+6) (A+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq PTf; lia).
  assert (Hgen2: P (A+6) 0 (A-1) 18).
  { apply k4_second_generator; [exact HApos|exact HZ]. }
  exists (k4_follow B
        (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B x y-1)),
    (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1),
    (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)).
  repeat split; try assumption; try lia.
Qed.

End K4PhaseProbe.
