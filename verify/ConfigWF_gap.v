(** * Closing the Config_WF gap in busycoq's extracted `decider`.

    [decide_hlin_nonhalt_spec_1] guarantees non-halting only under the
    hypothesis [Config_WF tm cfg]. The binary never checks that, so the chain
    from "decider printed nonhalting" to the theorem had an unverified link.
    This file removes it. *)

From Coq Require Import List NArith Bool. Import ListNotations.
Require Import BusyCoq.Inductive_inf.

(** ** 1. Which config updates can disturb Config_WF

    [Config_WF tm x := Forall (ExtraRules_WF tm) x.(ex_rules)]  (Inductive.v:2043)
    so only the two setters that write [ex_rules] can matter. *)

Definition touches_ex_rules (s : SetConfig) : bool :=
  match s with
  | set_ex_rules _ | add_ex_rules _ => true
  | _ => false
  end.

Definition safe (ls : list SetConfig) : bool :=
  forallb (fun s => negb (touches_ex_rules s)) ls.

Lemma get_ex_rules_preserved : forall ls v0,
  safe ls = true -> get_ex_rules ls v0 = v0.
Proof.
  induction ls as [|s ls IH]; intros v0 H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    destruct s; simpl in H1; try discriminate; apply IH; exact H2.
Qed.

Lemma upd_config_ex_rules : forall ls c,
  safe ls = true -> ex_rules (upd_config ls c) = ex_rules c.
Proof. intros ls c H. unfold upd_config; cbn. apply get_ex_rules_preserved, H. Qed.

(** ** 2. Every config reachable in parse_args (Inductive_inf.v:115-133).
    The "--maxT", bare-TM and [] branches pass cfg through unchanged. *)

Inductive reachable_cfg : Config -> Prop :=
| rc_default : reachable_cfg default_config
| rc_upd : forall ls c, reachable_cfg c -> safe ls = true ->
    reachable_cfg (upd_config ls c)
| rc_exp : forall c, reachable_cfg c -> reachable_cfg (config_exploop c).

Lemma reachable_ex_rules : forall c, reachable_cfg c -> ex_rules c = [].
Proof.
  induction 1.
  - reflexivity.
  - rewrite upd_config_ex_rules by assumption. assumption.
  - unfold config_exploop. rewrite upd_config_ex_rules by reflexivity. assumption.
Qed.

(** Each setter list parse_args actually uses is [safe] -- by computation,
    so no transcription of the argument *values* is being trusted. *)
Lemma safe_max_repeater_len  : forall n, safe [set_max_repeater_len n] = true.
Proof. reflexivity. Qed.
Lemma safe_max_repeater_size : forall n, safe [set_max_repeater_size n] = true.
Proof. reflexivity. Qed.
Lemma safe_block_size : forall a b c,
  safe [set_max_repeater_size a; set_max_repeater_len b; set_fixed_block_size c] = true.
Proof. reflexivity. Qed.
Lemma safe_arithseq : forall b, safe [set_enable_arithseq b] = true.
Proof. reflexivity. Qed.
(* and the UBRRBA entry point's config, for completeness *)
Lemma ubrrba_ex_rules : forall bsz, ex_rules (config_ubrrba bsz) = [].
Proof. reflexivity. Qed.

(** ** 3. The branch of parse_args that prints "nonhalting"
    (Inductive_inf.v:144-146), and the fact that it *is* the decider the
    soundness theorem talks about -- checked by computation, not by eye. *)

Definition prints_nonhalting (tm : TM) (cfg : Config) (T : N) : bool :=
  match hlin_layers_steps tm cfg T with
  | inr ((_, (_, w0), _) :: _) => check_nonhalt (fst w0)
  | _ => false
  end.

Lemma prints_nonhalting_is_decider : forall tm cfg T,
  prints_nonhalting tm cfg T = decide_hlin_nonhalt tm cfg T.
Proof. reflexivity. Qed.

(** ** 4. The gap, closed: no Config_WF hypothesis remains. *)

Theorem exec_nonhalting_sound : forall tm cfg T,
  reachable_cfg cfg ->
  prints_nonhalting tm cfg T = true ->
  ~ halts tm c0.
Proof.
  intros tm cfg T Hr Hp.
  rewrite prints_nonhalting_is_decider in Hp.
  eapply decide_hlin_nonhalt_spec_1; [| exact Hp].
  apply Config_WF_simple, reachable_ex_rules, Hr.
Qed.

Print Assumptions exec_nonhalting_sound.
