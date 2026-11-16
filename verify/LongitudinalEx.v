From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Inductive signal :=
| headRL(hRL:DH0*DH0)
| blockR(b:list Sym)
| blockL(b:list Sym)
.

Inductive side_upds: TM -> (list signal) -> side -> side -> Prop :=
| side_upds_O tm r: side_upds tm [] r r
| side_upds_headRL tm hR hL h r r0 r1:
  sideRL tm hR hL r r0 ->
  side_upds tm h r0 r1 ->
  side_upds tm ((headRL (hR,hL))::h) r r1
| side_upds_blockR tm b h r r0:
  side_upds tm h (b*>r) r0 ->
  side_upds tm ((blockR b)::h) r r0
.

Local Hint Constructors side_upds: core.

Definition seg_upds(tm:TM)(h1 h2:list signal)(w1 w2:list Sym):Prop :=
  forall r1 r2,
  side_upds tm h2 r1 r2 ->
  side_upds tm h1 (w1*>r1) (w2*>r2).

Lemma seg_side_upds_concat tm h1 h2 w1 w2 r1 r2:
  seg_upds tm h1 h2 w1 w2 ->
  side_upds tm h2 r1 r2 ->
  side_upds tm h1 (w1*>r1) (w2*>r2).
Proof.
  unfold seg_upds.
  auto.
Qed.

Lemma seg_upds_concat tm h1 h2 h3 w1 w2 w3 w4:
  seg_upds tm h1 h2 w1 w2 ->
  seg_upds tm h2 h3 w3 w4 ->
  seg_upds tm h1 h3 (w1++w3) (w2++w4).
Proof.
  unfold seg_upds.
  intros.
  repeat rewrite Str_app_assoc.
  auto.
Qed.

Lemma side_upds_trans tm h1 h2 r1 r2 r3:
  side_upds tm h1 r1 r2 ->
  side_upds tm h2 r2 r3 ->
  side_upds tm (h1++h2) r1 r3.
Proof.
  intros H.
  gen h2 r3.
  induction H; intros; cbn; eauto.
Qed.

Lemma side_upds_split tm h1 h2 r1 r2:
  side_upds tm (h1++h2) r1 r2 ->
  exists r3, side_upds tm h1 r1 r3 /\ side_upds tm h2 r3 r2.
Proof.
  gen h2 r1 r2.
  induction h1; cbn; intros.
  - eauto.
  - inverts H.
    + eapply IHh1 in H6.
      destruct H6 as [r3 [I1 I2]].
      eauto.
    + eapply IHh1 in H5.
      destruct H5 as [r3 [I1 I2]].
      eauto.
Qed.

Lemma seg_upds_trans tm h1 h2 h3 h4 w1 w2 w3:
  seg_upds tm h1 h2 w1 w2 ->
  seg_upds tm h3 h4 w2 w3 ->
  seg_upds tm (h1++h3) (h2++h4) w1 w3.
Proof.
  unfold seg_upds.
  intros.
  apply side_upds_split in H1.
  destruct H1 as [r3 [I1 I2]].
  eapply side_upds_trans; eauto.
Qed.

Lemma side_upds_RLs tm h r1 r2:
  side_upds tm (map headRL h) r1 r2 ->
  sideRLs tm h r1 r2.
Proof.
  gen r1 r2.
  induction h; intros.
  - inverts H.
    constructor.
  - inverts H.
    econstructor; eauto.
Qed.


