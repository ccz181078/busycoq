Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles
  BusyCoq.CounterClass1.CounterClass1K5Common.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Section K5Scan.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K5Rules P.
Let Q:=K5Q P.
Let C:=k5_q_core_rules P R.

Lemma k5_pointer_low_follow B u x y n:
  K4PointerTrace B u x y n -> K4FollowTrace B u x y y n.
Proof.
  intros HT. induction HT.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma k5_nested_absorb B u x y A D:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> 0<y ->
  K4Particle Q u D y -> K4Particle Q u A D ->
  K4Particle Q (u+2) A (y-1) /\
  K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y) (y-1).
Proof.
  intros HB Hxy Hy [bd [dd [HDw [Hyw HD]]]]
    [b [d [HAw [HDw' HA]]]].
  unfold Q,K5Q in *.
  assert (Hd:d=bd+4) by lia. subst d. split.
  - exists (b+2),(dd+4). repeat split; try lia.
    applys_eq (k5_rov' R A b D bd (y-1) (1+dd)); try lia.
    + applys_eq HA; lia.
    + applys_eq HD; lia.
  - apply k4_synced_decrement_ok; assumption.
Qed.

Lemma k5_top_nested_absorb B u x y A D:
  y<=x<=S y ->
  K4Particle Q u D y -> K4TopParticle Q u A D ->
  K4TopParticle Q (u+2) A y /\
  K4TopFollowerOK B (k4_next_x B x y) (k4_next_y B x y) y.
Proof.
  intros Hxy [bd [dd [HDw [Hyw HD]]]]
    [b [d [HAw [HDw' HA]]]].
  unfold Q,K5Q in *.
  assert (Hd:d=bd+3) by lia. subst d. split.
  - exists (b+2),(dd+1). repeat split; try lia.
    applys_eq (k5_rov R A b D bd y (1+dd)); try lia.
    + applys_eq HA; lia.
    + applys_eq HD; lia.
  - assert (x=y \/ x=S y) by lia. destruct H as [E|E]; subst x.
    + unfold K4TopFollowerOK,k4_next_x,k4_next_y.
      destruct (nth y B false) eqn:EY; cbn.
      * destruct y.
        -- left. reflexivity.
        -- unfold k4_next_x. rewrite EY. cbn.
           right; left. repeat split; try lia.
      * left. reflexivity.
    + unfold K4TopFollowerOK,k4_next_x,k4_next_y.
      destruct (nth (S y) B false),(nth y B false); cbn; left; lia.
Qed.

Lemma k5_top_particle_step B u x y z a:
  K4Row Q B true u x -> K4Row Q B false (u+1) y ->
  z<length B -> (nth z B false=true -> 0<x) ->
  2*length B<=u+2 -> K4TopParticle Q u a z ->
  K4TopParticle Q (u+2) a (k4_top_follow B x y z).
Proof.
  intros [dt [Hdt RT]] [df [Hdf RF]] Hzl Hz0 Hlen
    [b [d [Hab [Hzd HP]]]].
  unfold Q,K5Q in *.
  destruct (nth z B false) eqn:Hz.
  - assert (Hx:0<x) by (apply Hz0; reflexivity).
    exists (b+2),(4+dt). split; [lia|]. split.
    + unfold k4_top_follow. rewrite Hz. cbn. lia.
    + unfold k4_top_follow. rewrite Hz. cbn.
      applys_eq (k5_rov' R a b z (d-4) (x-1) (1+dt)); try lia.
      * applys_eq HP; lia.
      * applys_eq (RT z (d-4)); try assumption; lia.
  - exists (b+2),(1+df). split; [lia|]. split.
    + unfold k4_top_follow. rewrite Hz. cbn. lia.
    + unfold k4_top_follow. rewrite Hz. cbn.
      applys_eq (k5_rov R a b z (d-3) y (1+df)); try lia.
      * applys_eq HP; lia.
      * applys_eq (RF z (d-3)); try assumption; lia.
Qed.

Lemma k5_pointer_prefix_top_synced B u x y n xf yf a:
  K4PointerPrefix B u x y n xf yf ->
  K4Row Q B true u x -> K4Row Q B false (u+1) y ->
  K4TopParticle Q u a x -> K4TopParticle Q (u+2*n) a xf.
Proof.
  intros HP. induction HP; intros RT RF HA.
  - cbn. applys_eq HA; lia.
  - destruct (k4_rows_step Q C B u x y RT RF H H0 H1 H2 H3 H4 H5)
      as [RT1 RF1].
    assert (RF1':K4Row Q B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF1; lia).
    assert (HA1:K4TopParticle Q (u+2) a (k4_next_x B x y)).
    { applys_eq (k5_top_particle_step B u x y x a RT RF H H1 H5 HA);
        unfold k4_top_follow,k4_next_x; reflexivity || lia. }
    applys_eq (IHHP RT1 RF1' HA1); lia.
Qed.

Lemma k5_pointer_prefix_live_top B u x y n xf yf z a:
  y<=x<=S y -> K4PointerPrefix B u x y (2+n) xf yf ->
  K4Row Q B true u x -> K4Row Q B false (u+1) y ->
  K4TopFollowerOK B x y z -> K4TopParticle Q u a z ->
  K4TopParticle Q (u+2*(2+n)) a xf.
Proof.
  intros Hxy HP RT RF HOK HA.
  destruct (k4_pointer_prefix_uncons B u x y (1+n) xf yf HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step Q C B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
    as [RT1 RF1].
  assert (RF1':K4Row Q B false (u+2+1) (k4_next_y B x y)) by
    (applys_eq RF1; lia).
  destruct (k4_top_follower_ok_step B x y z Hnz Hxy HOK) as [Hz0 HOK1].
  assert (Hzl:z<length B) by
    exact (k4_top_follower_ok_bound B x y z Hxl Hyl HOK).
  assert (HA1:K4TopParticle Q (u+2) a (k4_top_follow B x y z)).
  { exact (k5_top_particle_step B u x y z a RT RF Hzl Hz0 Hlen HA). }
  destruct (k4_pointer_pair_step B x y Hxy) as [Hlow Hpair].
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) n xf yf HP1) as
    (Hxl1&Hyl1&Hx01&Hy01&Hxu1&Hyu1&Hlen1&Hnz1&HP2).
  destruct (k4_rows_step Q C B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) RT1 RF1' Hxl1 Hyl1 Hx01 Hy01
      Hxu1 Hyu1 Hlen1) as [RT2 RF2].
  assert (RF2':K4Row Q B false (u+4+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RF2; lia).
  destruct (k4_top_follower_ok_step B _ _ _ Hnz1 Hpair HOK1)
    as [Hz01 HOK2].
  assert (Hzl1:k4_top_follow B x y z<length B) by
    exact (k4_top_follower_ok_bound B _ _ _ Hxl1 Hyl1 HOK1).
  assert (HA2:K4TopParticle Q (u+4) a
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))).
  { rewrite <- (k4_top_follower_two B x y z Hxy HOK).
    applys_eq (k5_top_particle_step B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_top_follow B x y z) a
      RT1 RF1' Hzl1 Hz01 Hlen1 HA1); lia. }
  assert (HP2':K4PointerPrefix B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)) n xf yf) by
    (applys_eq HP2; lia).
  assert (RT2':K4Row Q B true (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RT2; lia).
  applys_eq (k5_pointer_prefix_top_synced B (u+4) _ _ n xf yf a
    HP2' RT2' RF2' HA2); lia.
Qed.

(* The six old boundary columns point only at [H] or [H-1].  Both join the
   low pointer after at most one row; the sole asymmetric case is the top
   column of a T4 phase. *)
Lemma k5_tail_follow kind B u H n z:
  2<=H -> nth H B false=true -> nth (H-1) B false=true ->
  (nth 0 B false=true \/ nth 1 B false=true) ->
  K4PointerTrace B u H (k5_scan_y kind H) n ->
  (z=H \/ z=H-1) ->
  K4FollowTrace B u H (k5_scan_y kind H) z n.
Proof.
  intros HH BH BHm Hbase HT [E|E]; subst z; destruct kind; cbn in *.
  - destruct (k4_pointer_trace_uncons B u H (H-1) n ltac:(lia) HT)
      as (m&->&Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&HT').
    eapply K4FollowMore.
    + exact Hxl.
    + rewrite BH. discriminate.
    + exact Hxl.
    + exact Hyl.
    + exact Hx0.
    + exact Hy0.
    + exact Hxu.
    + exact Hyu.
    + exact Hlen.
    + unfold k4_follow. rewrite BH. cbn.
      unfold k4_next_y in HT' |- *. rewrite BHm in HT' |- *. cbn in HT' |- *.
      unfold k4_next_x in HT' |- *. rewrite BH in HT' |- *. cbn in HT' |- *.
      apply k5_pointer_low_follow. exact HT'.
  - eapply k4_pointer_follow_ok; [exact Hbase|exact HT|].
    left. auto.
  - eapply k4_pointer_follow_ok; [exact Hbase|exact HT|].
    right; left. split; [lia|]. split; [reflexivity|]. left; lia.
  - eapply k4_pointer_follow_ok; [exact Hbase|exact HT|].
    right; right; right. repeat split; try assumption; lia.
Qed.

(* The major zero-axis fact starts a fixed three-row gadget.  Its five
   emitted columns either join the current low pointer immediately or become
   a certified follower; the sixth column remains the decreasing endpoint
   consumed by the rest of the scan. *)
Lemma k5_second_generator_start B u x y A xf yf:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=Datatypes.S y -> 2<=A -> 2*A+5=u ->
  K4PointerPrefix B u x y 3 xf yf ->
  (xf<>0 \/ yf<>0) ->
  K4Row Q B true u x -> K4Row Q B false (u+1) y ->
  (forall j, j<=1 -> K4Particle Q u (A-j) y) ->
  P A 0 0 (2*A+5) ->
  exists z z4 zt,
    K4Row Q B true (u+6) xf /\
    K4Row Q B false (u+7) yf /\
    yf<=xf<=Datatypes.S yf /\
    K4FollowerOK B xf yf z /\
    K4Particle Q (u+6) (A+2) z /\
    K4Particle Q (u+6) (A+3) z /\
    K4Particle Q (u+6) (A+5) z /\
    K4FollowerOK B xf yf z4 /\
    K4Particle Q (u+6) (A+4) z4 /\
    K4TopFollowerOK B xf yf zt /\
    K4TopParticle Q (u+6) (A+1) zt /\
    P (A+6) 0 (A-2) 21.
Proof.
  intros Hbase Hpair HA Huw HP Hlive RT RF HD HZ.
  destruct (k4_pointer_prefix_uncons B u x y 2 xf yf HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step Q C B u x y RT RF Hxl Hyl Hx0 Hy0
      Hxu Hyu Hlen) as [RT1 RF1].
  assert (RF1':K4Row Q B false (u+2+1) (k4_next_y B x y)) by
    (applys_eq RF1; lia).
  destruct (k4_pointer_pair_step B x y Hpair) as [Hlow1 Hpair1].
  assert (HA0:K4Particle Q u A y) by
    (applys_eq (HD 0 ltac:(lia)); lia).
  assert (HAm0:K4Particle Q u (A-1) y) by
    (applys_eq (HD 1 ltac:(lia)); lia).
  assert (HA1:K4Particle Q (u+2) A (k4_next_y B x y)).
  { applys_eq (k4_particle_step Q C B u x y y A RT1 RF
      Hyl Hy0 Hlen HA0);
      unfold k4_follow,k4_next_y; reflexivity || lia. }
  assert (HAm1:K4Particle Q (u+2) (A-1) (k4_next_y B x y)).
  { applys_eq (k4_particle_step Q C B u x y y (A-1) RT1 RF
      Hyl Hy0 Hlen HAm0);
      unfold k4_follow,k4_next_y; reflexivity || lia. }
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) 1 xf yf HP1) as
    (Hxl1&Hyl1&Hx01&Hy01&Hxu1&Hyu1&Hlen1&Hnz1&HP2).
  destruct (k4_rows_step Q C B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) RT1 RF1' Hxl1 Hyl1 Hx01 Hy01
      Hxu1 Hyu1 Hlen1) as [RT2 RF2].
  assert (RF2':K4Row Q B false (u+4+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RF2; lia).
  destruct (k4_pointer_pair_step B (k4_next_x B x y)
      (k4_next_y B x y) Hpair1) as [Hlow2 Hpair2].
  assert (HA2:K4Particle Q (u+4) A
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))).
  { applys_eq (k4_particle_step Q C B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_next_y B x y) A RT2 RF1'
      Hyl1 Hy01 Hlen1 HA1);
      unfold k4_follow,k4_next_y; reflexivity || lia. }
  assert (HAm2:K4Particle Q (u+4) (A-1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))).
  { applys_eq (k4_particle_step Q C B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_next_y B x y) (A-1) RT2 RF1'
      Hyl1 Hy01 Hlen1 HAm1);
      unfold k4_follow,k4_next_y; reflexivity || lia. }
  assert (HP2':K4PointerPrefix B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      1 xf yf) by (applys_eq HP2; lia).
  assert (RT2':K4Row Q B true (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RT2; lia).
  destruct (k4_pointer_prefix_uncons B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      0 xf yf HP2') as
    (Hxl2&Hyl2&Hx02&Hy02&Hxu2&Hyu2&Hlen2&Hnz2&HP3).
  destruct (k4_rows_step Q C B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      RT2' RF2' Hxl2 Hyl2 Hx02 Hy02 Hxu2 Hyu2 Hlen2) as [RT3 RF3].
  inversion HP3; subst xf yf.
  destruct (k4_pointer_pair_step B
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)) Hpair2)
    as [Hlow3 Hpair3].

  assert (G1:P (A+1) 3 (A+2) 6).
  { applys_eq (k5_lov2 R A (A+2)); try lia. applys_eq HZ; lia. }
  assert (G2:P (A+2) 2 (A+1) 9).
  { applys_eq (k5_lov3 R A (A+1)); try lia. applys_eq HZ; lia. }
  assert (G3:P (A+3) 0 (A+1) 9).
  { applys_eq (k5_lov1 R A (A+1)); try lia. applys_eq HZ; lia. }
  assert (G4:P (A+1) 5 (A+1) 10).
  { applys_eq (k5_rov R (A+1) 3 (A+2) 2 (A+1) 9);
      try lia; assumption. }
  assert (G5:P (A+1) 7 A 14).
  { applys_eq (k5_rov' R (A+1) 5 (A+1) 5 A 10);
      try lia; applys_eq G4; lia. }
  assert (G24:P (A+2) 4 (A+1) 11).
  { applys_eq (k5_rov R (A+2) 2 (A+1) 5 (A+1) 10);
      try lia; assumption. }
  assert (G26:P (A+2) 6 A 15).
  { applys_eq (k5_rov R (A+2) 4 (A+1) 7 A 14);
      try lia; assumption. }
  assert (G32:P (A+3) 2 (A+1) 11).
  { applys_eq (k5_rov R (A+3) 0 (A+1) 5 (A+1) 10);
      try lia; assumption. }
  assert (G34:P (A+3) 4 A 15).
  { applys_eq (k5_rov R (A+3) 2 (A+1) 7 A 14);
      try lia; assumption. }
  assert (G40:P (A+4) 0 A 13).
  { applys_eq (k5_inc01 R (A+3) A 9); try lia. applys_eq G3; lia. }
  assert (G50:P (A+5) 0 (A-1) 17).
  { applys_eq (k5_inc01 R (A+4) (A-1) 13); try lia.
    applys_eq G40; lia. }
  assert (G60:P (A+6) 0 (A-2) 21).
  { applys_eq (k5_inc01 R (A+5) (A-2) 17); try lia.
    applys_eq G50; lia. }

  assert (PT:K4TopParticle Q (u+4) (A+1) A).
  { exists 7,13. unfold Q,K5Q. repeat split; try assumption; lia. }
  destruct (k5_top_nested_absorb B (u+4) _ _ (A+1) A
      Hpair2 HA2 PT) as [PTf HTOK].
  assert (P2:K4Particle Q (u+4) (A+2) A).
  { exists 6,14. unfold Q,K5Q. repeat split; try assumption; lia. }
  assert (P3:K4Particle Q (u+4) (A+3) A).
  { exists 4,14. unfold Q,K5Q. repeat split; try assumption; lia. }
  assert (P5:K4Particle Q (u+4) (A+5) (A-1)).
  { exists 0,16. unfold Q,K5Q. repeat split; try assumption; lia. }
  assert (Hy1:0<k4_next_y B x y).
  { eapply k4_pair_live_successor_y; eauto. }
  assert (Hy2:0<k4_next_y B (k4_next_x B x y) (k4_next_y B x y)).
  { eapply k4_pair_live_successor_y; eauto. }
  destruct (k5_nested_absorb B (u+4) _ _ (A+2) A Hbase
      Hpair2 Hy2 HA2 P2)
    as [P2f HOK].
  destruct (k5_nested_absorb B (u+4) _ _ (A+3) A Hbase
      Hpair2 Hy2 HA2 P3)
    as [P3f HOK3].
  destruct (k5_nested_absorb B (u+4) _ _ (A+5) (A-1) Hbase
      Hpair2 Hy2 HAm2 P5)
    as [P5f HOK5].
  assert (P4:K4Particle Q (u+2) (A+4) A).
  { exists 0,12. unfold Q,K5Q. repeat split; try assumption; lia. }
  destruct (k5_nested_absorb B (u+2) _ _ (A+4) A Hbase
      Hpair1 Hy1 HA1 P4)
    as [P4m HOK4].
  destruct (k4_follower_ok_step B _ _ _ Hbase Hnz2 HOK4)
    as [P40 HOK4f].
  assert (P4l:k4_next_y B x y-1<length B).
  { unfold K4FollowerOK in HOK4.
    destruct HOK4 as [[E F]|[[E [F G]]|[[E [F [G I]]]|[E [F G]]]]]; lia. }
  assert (P4mn:K4Particle Q (u+4) (A+4) (k4_next_y B x y-1)) by
    (applys_eq P4m; lia).
  assert (P4f:K4Particle Q (u+6) (A+4)
      (k4_follow B
        (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B x y-1))).
  { applys_eq (k4_particle_step Q C B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B x y-1) (A+4) RT3 RF2' P4l P40 Hlen2 P4mn); lia. }
  assert (RT3n:K4Row Q B true (u+6)
      (k4_next_x B (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)))) by
    (applys_eq RT3; lia).
  assert (RF3n:K4Row Q B false (u+7)
      (k4_next_y B (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
        (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)))) by
    (applys_eq RF3; lia).
  assert (P2n:K4Particle Q (u+6) (A+2)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1)) by
    (applys_eq P2f; lia).
  assert (P3n:K4Particle Q (u+6) (A+3)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1)) by
    (applys_eq P3f; lia).
  assert (P5n:K4Particle Q (u+6) (A+5)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1)) by
    (applys_eq P5f; lia).
  assert (PTn:K4TopParticle Q (u+6) (A+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq PTf; lia).
  exists (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)-1),
    (k4_follow B
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B x y-1)),
    (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)).
  repeat split; try assumption; try lia.
Qed.

Definition K5SecondGen (B:list bool) (H S D k:nat) : Prop :=
  let A:=H+D+2 in
  let Sp:=2*S+k+4 in
  let W:=2*(2*H+k+7)-1 in
  exists xb yb,
    K4PointerPrefix B (2*A+11) xb yb ((Sp-7)+2) 0 0 /\
    K4Row Q B true (2*A+11) xb /\
    K4Row Q B false (2*A+12) yb /\
    yb<=xb<=Datatypes.S yb /\
    (forall j, j<=Sp-5 -> K4Particle Q (2*A+11) (A-2-j) yb) /\
    P (A+6) 0 (A-2) 21 /\
    (forall a, A+2<=a<=A+5 -> K4Particle Q W a 0) /\
    K4TopParticle Q W (A+1) 0.

Lemma k5_scan_second kind runs B H S D k:
  K5ScanStart P kind runs B H S D k ->
  K5FirstGen P kind B H S D k -> K5SecondGen B H S D k.
Proof.
  intros HS0 HF.
  unfold K5ScanStart,K5ScanPayload in HS0.
  destruct HS0 as [Hshape [Hbits [Hhead
    [Hheads [Hdrop [R0 [R1 [Htail Hex]]]]]]]].
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk HS]]]]]]] eqn:Eshape.
  assert (Hbase:nth 0 B false=true \/ nth 1 B false=true).
  { destruct kind; cbn [K4HeadBits] in Hheads;
      destruct Hheads as [B0 [B1 B2]]; auto. }
  set (u:=2*H+13).
  set (q:=D-5).
  set (e:=H+7).
  set (A:=H+D+2).
  set (Sp:=2*S+k+4).
  set (W:=2*(2*H+k+7)-1).
  unfold K5FirstGen in HF. fold u q e A Sp in HF.
  destruct HF as (xg&yg&HTg&RTg&RFg&Hpairg&Hgen&HZ).
  assert (HUA:2*A+5=u+2*(q+3)) by (unfold A,u,q; lia).
  destruct (k4_pointer_trace_split B (u+2*(q+3)) xg yg
      (Sp-2) 3) as (xb&yb&m&Hm&HPb&HTb); try assumption; try lia.
  assert (Hm':m=Sp-5) by lia. subst m.
  assert (Hliveb:xb<>0 \/ yb<>0).
  { inversion HTb; subst; [unfold Sp in *; lia|assumption]. }
  assert (HD:forall j, j<=1 -> K4Particle Q
      (u+2*(q+3)) (A-j) yg).
  { intros j Hj. replace (A-j) with (e+(q-j)) by
      (unfold A,e,q; lia). apply Hgen. lia. }
  destruct (k5_second_generator_start B (u+2*(q+3)) xg yg A xb yb
      Hbase Hpairg ltac:(unfold A; lia) HUA HPb Hliveb RTg RFg HD HZ)
    as (z&z4&zt&HRTb&HRFb&Hpairb&HOK&HPA2&HPA3&HPA5&HOK4&HPA4&HTOK&HPT&HE).
  assert (HPrem:K4PointerPrefix B (2*A+11) xb yb ((Sp-7)+2) 0 0).
  { applys_eq (k4_pointer_trace_prefix B
      (u+2*(q+3)+6) xb yb (Sp-5) HTb); lia. }
  assert (HPrem':K4PointerPrefix B (2*A+11) xb yb (2+(Sp-7)) 0 0) by
    (applys_eq HPrem; lia).
  assert (RTb:K4Row Q B true (2*A+11) xb) by
    (applys_eq HRTb; lia).
  assert (RFb:K4Row Q B false (2*A+12) yb) by
    (applys_eq HRFb; lia).
  assert (RFb':K4Row Q B false (2*A+11+1) yb) by
    (applys_eq RFb; lia).
  assert (HPA20:K4Particle Q (2*A+11) (A+2) z) by
    (applys_eq HPA2; lia).
  assert (HPA30:K4Particle Q (2*A+11) (A+3) z) by
    (applys_eq HPA3; lia).
  assert (HPA40:K4Particle Q (2*A+11) (A+4) z4) by
    (applys_eq HPA4; lia).
  assert (HPA50:K4Particle Q (2*A+11) (A+5) z) by
    (applys_eq HPA5; lia).
  assert (HPT0:K4TopParticle Q (2*A+11) (A+1) zt) by
    (applys_eq HPT; lia).
  assert (Hbridge:forall a, A+2<=a<=A+5 -> K4Particle Q W a 0).
  { intros a Ha.
    assert (E:a=A+2 \/ a=A+3 \/ a=A+4 \/ a=A+5) by lia.
    destruct E as [E|[E|[E|E]]]; subst a.
    - applys_eq (k4_pointer_prefix_live_particle Q C B (2*A+11)
        xb yb (Sp-7) 0 0 z (A+2) Hbase HPrem' RTb RFb' HOK HPA20);
        unfold W; lia.
    - applys_eq (k4_pointer_prefix_live_particle Q C B (2*A+11)
        xb yb (Sp-7) 0 0 z (A+3) Hbase HPrem' RTb RFb' HOK HPA30);
        unfold W; lia.
    - applys_eq (k4_pointer_prefix_live_particle Q C B (2*A+11)
        xb yb (Sp-7) 0 0 z4 (A+4) Hbase HPrem' RTb RFb' HOK4 HPA40);
        unfold W; lia.
    - applys_eq (k4_pointer_prefix_live_particle Q C B (2*A+11)
        xb yb (Sp-7) 0 0 z (A+5) Hbase HPrem' RTb RFb' HOK HPA50);
        unfold W; lia. }
  assert (HTop:K4TopParticle Q W (A+1) 0).
  { applys_eq (k5_pointer_prefix_live_top B (2*A+11)
      xb yb (Sp-7) 0 0 zt (A+1) Hpairb HPrem' RTb RFb' HTOK HPT0);
      unfold W; lia. }
  assert (Hdrivers:forall j, j<=Sp-5 ->
      K4Particle Q (2*A+11) (A-2-j) yb).
  { intros j Hj.
    assert (Hsrc:K4Particle Q (u+2*(q+3)) (A-2-j) yg).
    { replace (A-2-j) with (e+(A-2-j-e)) by lia.
      apply Hgen; unfold A,e,q,Sp in *; lia. }
    applys_eq (k4_pointer_prefix_synced_particle Q C B
      (u+2*(q+3)) xg yg 3 xb yb (A-2-j) HPb RTg RFg Hsrc); lia. }
  destruct Hpairb as [Hby Hxb].
  unfold K5SecondGen. fold A Sp W.
  exists xb,yb. repeat split; try assumption.
Qed.

Definition K5CoreEnd (B:list bool) (H S D k:nat) : Prop :=
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+4 in
  let Dp:=2*D-k-1 in
  let A:=H+D+2 in
  let W:=2*Hp-1 in
  exists x y,
    K4PointerPrefix B (W-4) x y 2 0 0 /\
    K4Row Q B true (W-4) x /\
    K4Row Q B false (W-3) y /\
    y<=x<=Datatypes.S y /\
    K4ReachPrefix B (W-4) x y /\
    (forall j, j<=2 -> K4Particle Q (W-4) (Dp+4-j) y) /\
    P (Hp-2) 0 (Dp+4) (4*Sp-7) /\
    (forall j, j<Sp-7 -> K4Particle Q W (A+6+j) 0) /\
    K4Row Q B true W 0 /\
    K4Row Q B false (W+1) 0 /\
    (forall a, H+1<=a<=A -> K4Particle Q W a 0) /\
    (forall a, A+2<=a<=A+5 -> K4Particle Q W a 0) /\
    K4TopParticle Q W (A+1) 0.

Lemma k5_scan_core kind runs B H S D k:
  K5ScanStart P kind runs B H S D k -> K5CoreEnd B H S D k.
Proof.
  intros HS0.
  pose proof (k5_scan_first P R kind runs B H S D k HS0) as HF.
  pose proof (k5_scan_second kind runs B H S D k HS0 HF) as HM.
  unfold K5ScanStart,K5ScanPayload in HS0.
  destruct HS0 as [Hshape [Hbits [Hhead
    [Hheads [Hdrop [R0 [R1 [Htail Hex]]]]]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk HS]]]]]]].
  assert (Hlen:length B=H+1) by
    (rewrite Hbits,k4_bits_length,Hsum; reflexivity).
  assert (Hbase:nth 0 B false=true \/ nth 1 B false=true).
  { destruct kind; cbn [K4HeadBits] in Hheads;
      destruct Hheads as [B0 [B1 B2]]; auto. }
  assert (BH:nth H B false=true).
  { eapply k5_bits_last_true; [exact Hshape0|exact Hbits|lia]. }
  assert (BHm:nth (H-1) B false=true).
  { eapply k5_bits_last_true; [exact Hshape0|exact Hbits|lia]. }
  set (u:=2*H+13).
  set (q:=D-5).
  set (e:=H+7).
  set (A:=H+D+2).
  set (Sp:=2*S+k+4).
  set (Dp:=2*D-k-1).
  set (Hp:=2*H+k+7).
  set (W:=2*Hp-1).
  assert (HT:K4PointerTrace B u H (k5_scan_y kind H) (H+k)).
  { eapply k5_pointer_trace; eauto; unfold u; lia. }
  assert (RT:K4Row Q B true u H) by
    (exists 17; unfold u; applys_eq R0; lia).
  assert (RF:K4Row Q B false (u+1) (k5_scan_y kind H)) by
    (exists (k5_row_false_d kind); unfold u; applys_eq R1; lia).
  destruct (k4_pointer_trace_rows Q C B u H (k5_scan_y kind H)
      (H+k) HT RT RF) as [RTW RFW].
  assert (Htot:u+2*(H+k)=W) by (unfold u,W,Hp; lia).
  assert (RTW':K4Row Q B true W 0) by (applys_eq RTW; lia).
  assert (RFW':K4Row Q B false (W+1) 0) by (applys_eq RFW; lia).
  assert (Hpair0:k5_scan_y kind H<=H<=Datatypes.S (k5_scan_y kind H)).
  { destruct kind; cbn [k5_scan_y]; lia. }
  assert (Hqy:q+2<=k5_scan_y kind H).
  { destruct kind; cbn [k5_scan_y]; unfold q; lia. }
  assert (HexQ:Q e 0 q (4*S+28)).
  { unfold Q,K5Q,e,q. applys_eq Hex; lia. }
  assert (Hew:2*e=u+1) by (unfold e,u; lia).
  assert (Heout:2*q+(4*S+28)=u+5) by (unfold q,u; lia).
  assert (Hmove:forall a b z d,
      2*a+b=u+1 -> 2*z+d=u+5 -> Q a b z d ->
      (z=H \/ z=H-1) -> K4Particle Q W a 0).
  { intros a b z d Haw Hzw HQ Hz.
    assert (HP:K4Particle Q u a z) by
      (exists b,d; repeat split; assumption).
    assert (HFT:K4FollowTrace B u H (k5_scan_y kind H) z (H+k)).
    { eapply k5_tail_follow; eauto; lia. }
    applys_eq (k4_follow_trace_particle Q C B u H
      (k5_scan_y kind H) z (H+k) HFT RT RF a HP); lia. }
  unfold K5Tail in Htail.
  destruct Htail as [T1 [T2 [T3 [T4 [T5 T6]]]]].
  assert (Hfirst:forall a, H+1<=a<=A -> K4Particle Q W a 0).
  { intros a Ha. destruct (Compare_dec.le_lt_dec e a) as [Hea|Hae].
    - replace a with (e+(a-e)) by lia.
      applys_eq (k4_generated_particles Q C B u H
        (k5_scan_y kind H) q (H+k) e (4*S+28)
        Hbase Hpair0 Hqy HT RT RF HexQ Hew Heout (a-e)); lia.
    - assert (E:a=H+1 \/ a=H+2 \/ a=H+3 \/
          a=H+4 \/ a=H+5 \/ a=H+6) by (unfold e in Hae; lia).
      destruct E as [E|[E|[E|[E|[E|E]]]]]; subst a.
      + eapply Hmove with (b:=12) (z:=H) (d:=18); try lia.
        * unfold Q,K5Q. applys_eq T1; lia.
      + eapply Hmove with (b:=10) (z:=H-1) (d:=20); try lia.
        * unfold Q,K5Q. applys_eq T2; lia.
      + eapply Hmove with (b:=8) (z:=H-1) (d:=20); try lia.
        * unfold Q,K5Q. applys_eq T3; lia.
      + eapply Hmove with (b:=6) (z:=H) (d:=18); try lia.
        * unfold Q,K5Q. applys_eq T4; lia.
      + eapply Hmove with (b:=4) (z:=H-1) (d:=20); try lia.
        * unfold Q,K5Q. applys_eq T5; lia.
      + eapply Hmove with (b:=2) (z:=H) (d:=18); try lia.
        * unfold Q,K5Q. applys_eq T6; lia.
        }
  unfold K5SecondGen in HM. fold A Sp W in HM.
  destruct HM as
    (xb&yb&HPearly&RTb&RFb&Hpairb&Hdrivers&HE&Hbridge&HTop).
  assert (HEQ:Q (A+6) 0 (A-2) 20).
  { unfold Q,K5Q. applys_eq HE; lia. }
  assert (HDearly:forall j, j<=Sp-7+2 ->
      K4Particle Q (2*A+11) (A-2-j) yb).
  { intros j Hj. apply Hdrivers. lia. }
  destruct (k4_endpoint_early Q C B (2*A+11) xb yb (Sp-7)
      (A+6) (A-2) 20 Hbase Hpairb ltac:(lia) ltac:(lia)
      HPearly RTb ltac:(applys_eq RFb; lia) HDearly HEQ
      ltac:(lia) ltac:(lia)) as
    (xt&yt&Hreach&HPt&RTt&RFt&Hpairt&HDt&HEt&Hzeros).
  assert (Hterminal:2*A+11+2*(Sp-7)=W-4) by
    (unfold A,Sp,W,Hp; lia).
  assert (Hzero:2*A+11+2*((Sp-7)+2)=W) by
    (unfold A,Sp,W,Hp; lia).
  assert (Hhigh:K4ReachPrefix B (W-4) xt yt).
  { exists (2*A+11),xb,yb,(Sp-7). repeat split; try assumption; lia. }
  assert (HPtn:K4PointerPrefix B (W-4) xt yt 2 0 0) by
    (applys_eq HPt; lia).
  assert (RTtn:K4Row Q B true (W-4) xt) by (applys_eq RTt; lia).
  assert (RFtn:K4Row Q B false (W-3) yt) by (applys_eq RFt; lia).
  assert (HDtn:forall j, j<=2 ->
      K4Particle Q (W-4) (Dp+4-j) yt).
  { intros j Hj. applys_eq (HDt j Hj); unfold Dp,A,Sp; lia. }
  assert (HEtn:P (Hp-2) 0 (Dp+4) (4*Sp-7)).
  { unfold Q,K5Q in HEt. applys_eq HEt; unfold Hp,Dp,Sp,A; lia. }
  assert (Hzerosn:forall j, j<Sp-7 ->
      K4Particle Q W (A+6+j) 0).
  { intros j Hj. applys_eq (Hzeros j Hj); unfold W; lia. }
  destruct Hpairt as [Hyt Hxt].
  unfold K5CoreEnd. fold Hp Sp Dp A W.
  exists xt,yt.
  repeat split; try assumption.
Qed.

End K5Scan.
