From BusyCoq Require Import Individual62.

Lemma DH_tape_L_feq {f:TM->Q*tape->Q*tape->Prop} {tm l l0 q r r0 c}:
  l=l0 ->
  r=r0 ->
  f tm (l0 <{{ q }} r0) c ->
  f tm (l <{{ q }} r) c.
Proof.
  congruence.
Qed.

Lemma DH_tape_R_feq {f:TM->Q*tape->Q*tape->Prop} {tm l l0 q r r0 c}:
  r=r0 ->
  l=l0 ->
  f tm (l0 {{ q }}> r0) c ->
  f tm (l {{ q }}> r) c.
Proof.
  congruence.
Qed.

Lemma tape_feq {f:TM->Q*tape->Q*tape->Prop} {tm c1 c2 c}:
  c1 = c2 ->
  f tm c2 c ->
  f tm c1 c.
Proof.
  congruence.
Qed.

Lemma DH_L_def (q:Q) (l r:side) (m:Sym):
  (q,(l,m,r)) = (l<<m) <{{q}} r.
Proof.
  reflexivity.
Qed.

Lemma DH_R_def (q:Q) (l r:side) (m:Sym):
  (q,(l,m,r)) = l {{q}}> (m>>r).
Proof.
  reflexivity.
Qed.

Ltac fold_DH_L :=
  (
  match goal with
  | |- (?q,(?l,?m,?r)) = _ =>
    lazymatch m with
    | hd _ => reflexivity
    | _ => eapply DH_L_def
    end
  end).

Ltac fold_DH_R :=
  (
  match goal with
  | |- (?q,(?l,?m,?r)) = _ =>
    lazymatch m with
    | hd _ => reflexivity
    | _ => eapply DH_R_def
    end
  end).

Ltac rw_unrotate_0 :=
  (rewrite lpow_unrotate_1 ||
  rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 ||
  rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 ||
  rewrite lpow_unrotate_6).

Ltac sr_l :=
  eapply tape_feq;
  [ fold_DH_L | ];
  eapply DH_tape_L_feq;
  [ repeat rw_unrotate_0; reflexivity | | ];
  [ reflexivity | ];
  use_shift_rule.

Ltac sr_r :=
  eapply tape_feq;
  [ fold_DH_R | ];
  eapply DH_tape_R_feq;
  [ repeat rw_unrotate_0; reflexivity | | ];
  [ reflexivity | ];
  use_shift_rule.

Ltac es1 :=
  simpl_rotate; cbn;
  (apply evstep_refl ||
  sr_l ||
  sr_r ||
  step1).

Ltac es := intros; st; repeat es1.
Ltac es_r := es.

