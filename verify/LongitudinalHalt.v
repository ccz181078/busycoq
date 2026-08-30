From BusyCoq Require Import Individual62.

(** [sideRLs] only describes calls in which every signal returns.  This
    companion predicate describes a finite signal stream whose execution
    halts while processing one of its signals; the unused suffix is retained
    in the index but is deliberately unconstrained. *)
Inductive sideRLs_halt (tm : TM) : list (DH0 * DH0) -> side -> Prop :=
| sideRLs_halt_here hR hL hs r :
    (forall l, halts tm (l {{{ (hR,R) }}} r)) ->
    sideRLs_halt tm ((hR,hL)::hs) r
| sideRLs_halt_next hR hL hs r r' :
    sideRL tm hR hL r r' ->
    sideRLs_halt tm hs r' ->
    sideRLs_halt tm ((hR,hL)::hs) r.

#[export] Hint Constructors sideRLs_halt : core.

Lemma sideRLs_halt_app_left tm hs1 hs2 r :
  sideRLs_halt tm hs1 r ->
  sideRLs_halt tm (hs1 ++ hs2) r.
Proof.
  intros H.
  induction H; cbn; eauto.
Qed.

Lemma sideRLs_halt_app_right tm hs1 hs2 r r' :
  sideRLs tm hs1 r r' ->
  sideRLs_halt tm hs2 r' ->
  sideRLs_halt tm (hs1 ++ hs2) r.
Proof.
  intros H.
  induction H; cbn; eauto.
Qed.

Lemma sideRLs_halt_split tm hs1 hs2 r :
  sideRLs_halt tm (hs1 ++ hs2) r ->
  sideRLs_halt tm hs1 r \/
  exists r', sideRLs tm hs1 r r' /\ sideRLs_halt tm hs2 r'.
Proof.
  gen r.
  induction hs1 as [|[hR hL] hs1 IH]; cbn; intros r H.
  - right. exists r. split; [constructor|exact H].
  - inverts H.
    + left. constructor. exact H4.
    + specialize (IH _ H5).
      destruct IH as [IH|[r'' [IH1 IH2]]].
      * left. econstructor 2; eauto.
      * right. exists r''. split; [econstructor; eauto|exact IH2].
Qed.

(** A halting version of [sideRLs_segLRs_concat].  It is the extra case
    needed by the [segRLs_lrcons] constructor: after each returned right-side
    call, [segLRs] carries the head through the finite word to the next call. *)
Lemma sideRLs_halt_segLRs_concat tm hs h1 h2 w1 w2 r :
  segLRs tm hs w1 w2 ->
  sideRLs_halt tm (lrcons h1 hs h2) r ->
  forall l, halts tm (l <* w1 {{{ (h1,R) }}} r).
Proof.
  intros Hseg.
  gen h1 h2 r.
  induction Hseg; intros h1' h2' r Hhalt l.
  - cbn in Hhalt.
    inverts Hhalt; eauto.
    match goal with
    | Hnone : sideRLs_halt _ [] _ |- _ => inverts Hnone
    end.
  - cbn in Hhalt.
    inverts Hhalt.
    + eauto.
    + eapply halts_evstep.
      1: eapply IHHseg; eassumption.
      eapply progress_evstep.
      eapply progress_evstep_trans with
        (c' := (w1 *> l) {{{ (h1,L) }}} r').
      * apply H4.
      * apply H.
Qed.

(** If a segment emits a signal stream which later halts, then the input
    stream halts as well.  Unlike the extensional experiment in the old
    backup file, this theorem is proved by induction over the actual
    [segRLs] derivation, so the halting case cannot hold vacuously. *)
Lemma segRLs_sideRLs_halt_concat tm hs1 hs2 w1 w2 r :
  segRLs tm hs1 hs2 w1 w2 ->
  sideRLs_halt tm hs2 r ->
  sideRLs_halt tm hs1 (w1 *> r).
Proof.
  intros Hseg.
  gen r.
  induction Hseg; intros r Hhalt.
  - inverts Hhalt.
  - econstructor 2.
    + intros l. apply H.
    + eapply IHHseg. exact Hhalt.
  - apply sideRLs_halt_split in Hhalt.
    destruct Hhalt as [Hprefix|[r' [Hprefix Hsuffix]]].
    + constructor 1. intros l.
      eapply halts_evstep.
      1: eapply sideRLs_halt_segLRs_concat; eauto.
      apply H.
    + econstructor 2.
      * intros l.
        follow H.
        eapply progress_evstep_trans.
        2: apply H0.
        eapply sideRLs_segLRs_concat; eauto.
      * eapply IHHseg. exact Hsuffix.
Qed.

Lemma sideRLs_halt_single tm hR hL r :
  sideRLs_halt tm [(hR,hL)] r ->
  forall l, halts tm (l {{{ (hR,R) }}} r).
Proof.
  intros H l. inverts H; eauto.
  match goal with
  | Hnone : sideRLs_halt _ [] _ |- _ => inverts Hnone
  end.
Qed.
