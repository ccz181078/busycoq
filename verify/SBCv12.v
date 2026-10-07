From BusyCoq Require Import Individual62 ES_v3.
From Coq Require Import List String Lia ZifyNat.
Import ListNotations.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC0RF_1RD0LC_1LE0RA_1LE1LC_---0RE").
Notation "c -->* d" := (c -[tm]->* d) (at level 40).
Notation "c -->+ d" := (c -[tm]->+ d) (at level 40).
Notation hf := ((A,<[0]):DH0).
Notation hh := ((B,<[0;1]):DH0).
Notation ht := ((E,<[0;1;0;0]):DH0).
Notation hl := ((C,[]):DH0).
Local Ltac es_v3_pre ::= cbn [to_DH_config]; repeat rewrite Str_app_assoc.

(* A single right call, including the possibility that it never returns. *)
Definition Result h r (P : side -> Prop) :=
  (exists r', sideRL tm h hl r r' /\ P r') \/
  (forall l, ~halts tm (l {{{(h,R)}}} r)).

Lemma result_mono h r P Q : Result h r P ->
  (forall r', P r' -> Q r') -> Result h r Q.
Proof.
  intros [[r' [H HP]]|H] HQ; [left; exists r'; auto|right; exact H].
Qed.

Lemma result_return h w w' r P : segRL tm h hl w w' ->
  P (w'*>r) -> Result h (w*>r) P.
Proof. intros H HP; left; exists (w'*>r); split; [intro l; apply H|exact HP]. Qed.
Arguments result_return {h w w' r P}.

(* The outward/return pair retains the divergent case, unlike a bare
   implication between two finite-return sideRL statements. *)
Definition Calls h h' w w' := exists v,
  segRR tm h h' w v /\ segLL tm hl hl v w'.

Lemma result_call h h' w w' r P Q : Calls h h' w w' ->
  Result h' r P -> (forall r', P r' -> Q (w'*>r')) ->
  Result h (w*>r) Q.
Proof.
  intros [v [Hf Hb]] [[r' [Hr HP]]|Hn] HQ.
  - left; exists (w'*>r'); split; [|auto].
    intro l; eapply evstep_progress_trans; [apply Hf|].
    eapply progress_evstep_trans; [apply Hr|apply Hb].
  - right; intro l; eapply multistep_nonhalt; [apply Hf|apply Hn].
Qed.
Arguments result_call {h h' w w' r P Q}.

Lemma f_zero : segRL tm hf hl [0] [0;0].
Proof. intros l r; es' & l r. Qed.
Lemma h_zero : segRL tm hh hl [0;0;0] [1;1;0;1;1].
Proof. intros l r; es' & l r. Qed.
Lemma h_one : segRL tm hh hl [0;1] [1;1;0;0].
Proof. intros l r; es' & l r. Qed.

Lemma t_zeros n : Calls ht ht ([0]^^n) ([0]^^n).
Proof.
  exists ([1]^^n); split; intros l r; es' n & l r.
Qed.
Lemma t_four q : Calls ht ht ([1]^^(4+q*4)) ([1]^^(4+q*4)).
Proof.
  exists (<[0;1;0;1]^^(1+q)); split; intros l r; es' q & l r.
Qed.
Lemma t_one q : Calls ht hf ([1]^^(1+q*4)) ([1]^^(4+q*4)).
Proof.
  exists (<[0;1;0;1]^^(1+q)); split; intros l r; es' q & l r.
Qed.
Lemma t_two q : Calls ht hh ([1]^^(2+q*4)) ([1]^^(4+q*4)).
Proof.
  exists (<[0;1;0;1]^^(1+q)); split; intros l r; es' q & l r.
Qed.
Lemma h_two_one q : Calls hh hf ([0;0]++[1]^^(1+q*4))
  ([1;1;0;0]++[1]^^(q*4)).
Proof.
  exists (<[0;1;0;1]^^q++<[0;1;1;1]); split;
    intros l r; es' q & l r.
Qed.
Lemma h_two_four q : Calls hh ht ([0;0]++[1]^^(4+q*4))
  ([1;1;0;0]++[1]^^(q*4)).
Proof.
  exists (<[0;1;0;1]^^q++<[0;1;1;1]); split;
    intros l r; es' q & l r.
Qed.
Lemma h_two : Calls hh ht [1;1] [].
Proof. exists ([]:list sym); split; intros l r; es' & l r. Qed.

Lemma t_blank l : ~halts tm (l {{{(ht,R)}}} 0inf).
Proof.
  apply (progress_nonhalt_simple tm side (fun l => l {{{(ht,R)}}} 0inf) l).
  intro l'; exists (l' << 1); es' & l'.
Qed.

Lemma calls_app h1 h2 h3 w1 w2 w3 w4 :
  Calls h1 h2 w1 w2 -> Calls h2 h3 w3 w4 ->
  Calls h1 h3 (w1++w3) (w2++w4).
Proof.
  intros [v1 [H1 H2]] [v2 [H3 H4]]; exists (v2++v1).
  split; intros l r; repeat rewrite Str_app_assoc.
  - eapply evstep_trans; [apply H1|apply H3].
  - eapply evstep_trans; [apply H4|apply H2].
Qed.
Arguments calls_app {h1 h2 h3 w1 w2 w3 w4}.

(* false/true index G_0/G_1. Run residues are encoded by constructors. *)
Inductive G : bool -> side -> Prop :=
| G_blank p : G p 0inf
| G_four p n q r : G false r ->
    G p ([0]^^((if p then 2 else 3)+n*3)*>[1]^^(4+q*4)*>r)
| G_one p n q r : G true r ->
    G p ([0]^^((if p then 2 else 3)+n*3)*>[1]^^(1+q*4)*>r)
| G_two p n q r : G true r ->
    G p ([0]^^((if p then 1 else 2)+n*3)*>[1]^^(2+q*4)*>r).

Lemma G_zero r : G true r -> G false (0>>r).
Proof.
  intro H; inverts H.
  - rewrite <-const_unfold; apply G_blank.
  - apply (G_four false n q _ H0).
  - apply (G_one false n q _ H0).
  - apply (G_two false n q _ H0).
Qed.

Lemma G_twozeros r : G false r -> G true ([0;0]*>r).
Proof.
  intro H; inverts H.
  - cbn [Str_app]; repeat rewrite <-const_unfold; constructor.
  - applys_eq (G_four true (1+n) q _ H0); flia.
  - applys_eq (G_one true (1+n) q _ H0); flia.
  - applys_eq (G_two true (1+n) q _ H0); flia.
Qed.

Lemma G_twoblocks q r : G false r -> G true ([0;0]*>[1]^^(q*4)*>r).
Proof.
  destruct q as [|q]; intro H; [apply G_twozeros, H|].
  apply (G_four true 0 q r H).
Qed.

Lemma G_mark r : G true r -> G true ([0;1;1]*>r).
Proof. apply (G_two true 0 0 r). Qed.

Lemma f_G r : G true r -> Result hf r (G false).
Proof.
  intro H; assert (exists u, r=0>>u) as [u ->] by
    (inverts H; [exists (0inf:side); apply const_unfold|
      eexists; reflexivity|eexists; reflexivity|eexists; reflexivity]).
  eapply (result_return f_zero); apply G_zero, H.
Qed.

Definition Mark r := exists u, G true u /\ r=[1;1]*>u.

Lemma h_big r : G true r -> Result hh ([0;0;0]*>r) Mark.
Proof.
  intro H; eapply (result_return h_zero).
  exists ([0;1;1]*>r); split; [apply G_mark, H|reflexivity].
Qed.

Lemma G_calls p r : G p r ->
  Result ht r (G p) /\ (p=true -> Result hh r Mark).
Proof.
  intro H; induction H as [p|p n q r H [IT IH]|p n q r H [IT IH]|p n q r H [IT IH]].
  - split; [right; apply t_blank|].
    intros ->; replace (0inf:side) with ([0;0;0]*>0inf) by
      (cbn [Str_app]; repeat rewrite <-const_unfold; reflexivity).
    apply h_big; constructor.
  - split.
    + rewrite <-Str_app_assoc.
      eapply (result_call (calls_app (t_zeros _) (t_four q))); [exact IT|].
      intros u Hu; rewrite Str_app_assoc; apply G_four, Hu.
    + intros ->; destruct n as [|n].
      * change (Result hh (([0;0]++[1]^^(4+q*4))*>r) Mark).
        eapply (result_call (h_two_four q)); [exact IT|].
        intros u Hu; exists ([0;0]*>[1]^^(q*4)*>u); split;
          [apply G_twoblocks, Hu|rewrite Str_app_assoc; reflexivity].
      * applys_eq (h_big _ (G_four true n q r H)); flia.
  - split.
    + rewrite <-Str_app_assoc.
      eapply (result_call (calls_app (t_zeros _) (t_one q))); [apply f_G, H|].
      intros u Hu; rewrite Str_app_assoc; apply G_four, Hu.
    + intros ->; destruct n as [|n].
      * change (Result hh (([0;0]++[1]^^(1+q*4))*>r) Mark).
        eapply (result_call (h_two_one q)); [apply f_G, H|].
        intros u Hu; exists ([0;0]*>[1]^^(q*4)*>u); split;
          [apply G_twoblocks, Hu|rewrite Str_app_assoc; reflexivity].
      * applys_eq (h_big _ (G_one true n q r H)); flia.
  - split.
    + rewrite <-Str_app_assoc.
      eapply (result_call (calls_app (t_zeros _) (t_two q))); [apply IH; reflexivity|].
      intros v [u [Hu ->]]; rewrite Str_app_assoc.
      change (G p ([0]^^((if p then 1 else 2)+n*3)*>
        [1]^^(4+q*4)*>[1]^^2*>u)).
      rewrite <-(Str_app_assoc ([1]^^(4+q*4)) ([1]^^2) u), <-lpow_add.
      applys_eq (G_two p n (1+q) u Hu); flia.
    + intros ->; destruct n as [|n].
      * change (Result hh ([0;1]*>[1]^^(1+q*4)*>r) Mark).
        eapply (result_return h_one).
        exists ([0;0]*>[1]^^(1+q*4)*>r); split;
          [apply (G_one true 0 q r H)|reflexivity].
      * applys_eq (h_big _ (G_two true n q r H)); flia.
Qed.

Definition Safe r := G true r \/ Mark r.

Lemma safe_step r : Safe r -> Result hh r Safe.
Proof.
  intros [H|[u [H ->]]].
  - eapply result_mono; [apply (proj2 (G_calls _ _ H)); reflexivity|].
    intros u Hu; right; exact Hu.
  - eapply (result_call h_two); [apply (proj1 (G_calls _ _ H))|].
    intros v Hv; left; exact Hv.
Qed.

Definition cfg r := (0inf << 1) {{{(hh,R)}}} r.

Lemma left_return r : (0inf << 1) <{{C}} r -->+ cfg r.
Proof. unfold cfg; es' & r. Qed.

Lemma safe_nonhalt r : Safe r -> ~halts tm (cfg r).
Proof.
  intros Hr HH.
  eapply (progress_nonhalt tm
    (fun c => halts tm c /\ exists r, Safe r /\ c=cfg r) (cfg r)).
  - intros c [Hc [u [Hu ->]]].
    destruct (safe_step _ Hu) as [[v [Hstep Hv]]|Hn].
    + assert (cfg u -->+ cfg v) as Hrun.
      { eapply progress_trans; [apply Hstep|apply left_return]. }
      exists (cfg v); split; [split|exact Hrun].
      * exact (proj1 (halts_evstep_iff tm _ _ (progress_evstep _ _ _ Hrun)) Hc).
      * exists v; auto.
    + exfalso; exact (Hn (0inf << 1) Hc).
  - split; [exact HH|exists r; auto].
  - exact HH.
Qed.

Lemma init : c0 -->* cfg 0inf.
Proof.
  change (0inf {{A}}> 0inf -->* (0inf << 1) <* <[0;1] {{B}}> 0inf).
  es'.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|apply safe_nonhalt; left; constructor].
Qed.

End TM1.
