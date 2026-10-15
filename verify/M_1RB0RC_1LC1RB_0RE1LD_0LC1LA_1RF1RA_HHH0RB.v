(** * 1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB never halts

    Machine: 1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB ("Bell eats counter").
    Adapted from verify/BECv5.v, Module TM1: the one-lemma-per-rule layout.  New here: the left side is a stack of frames
    00 (10)^p 1 (one per nested level), the right side is a bell (10)^q followed by a
    counter zone with bits 3 cells apart, and non-halting is a bounded induction on the
    number of steps (U_all), with the arithmetic carried by invariants of a phase that every
    round preserves.  The informal proof is the accompanying write-up (1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB_writeup.md).

    Formalized with Claude Code (AI-assisted).
    Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
    Print Assumptions nonhalt: Closed under the global context.
*)

From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Low-level rules (proof.md 3.1).  Left-side lists are written outward from the head. *)

Lemma BR k: forall l r, l {{B}}> [1]^^k *> r -->* [1]^^k *> l {{B}}> r.
Proof. es. Qed.

Lemma SW k: forall l r, [1;0]^^k *> l <{{C}} r -->* l <{{C}} [0;1]^^k *> r.
Proof. es. Qed.

Lemma TT j: forall l r, [1;1;1]^^j *> l <{{C}} r -->* l <{{C}} [0;1;1]^^j *> r.
Proof. es. Qed.

Lemma PS b: forall l r, [1;1;0] *> l {{B}}> [1;0]^^b *> r -->* [1;1] *> [0;1]^^b *> [0] *> l {{B}}> r.
Proof. es. Qed.

(** The round W, PS^(q-3), ZA, in three cases by f mod 3 (f = 3j+2, 3j+4, 3j+3). *)
Lemma RND2 q j: forall l r,
  l {{C}}> [0;0] *> [1;0]^^(q+3) *> [1;1;1]^^j *> [1;1;0] *> r -->+
  [1;0;1;0] *> l {{C}}> [0;0] *> [1;0]^^(q+1) *> [1;1;0]^^j *> [1;1;1] *> r.
Proof. es. Qed.

Lemma RND1 q j: forall l r,
  l {{C}}> [0;0] *> [1;0]^^(q+3) *> [1;1;1]^^j *> [1;1;1;1;0] *> r -->+
  [1;0;1;0] *> l {{C}}> [0;0] *> [1;0]^^(q+1) *> [1;1;1;1] *> [0;1;1]^^j *> [1] *> r.
Proof. es. Qed.

Lemma RND0 q j: forall l r,
  l {{C}}> [0;0] *> [1;0]^^(q+3) *> [1;1;1]^^j *> [1;1;1;0] *> r -->+
  [1;0;1;0] *> l {{C}}> [0;0] *> [1;0]^^q *> [1;1;1;1;1] *> [0;1;1]^^j *> [1] *> r.
Proof. es. Qed.

(** PUSH k: the bite at q = 2 (B2 for k = 0, the nested bite N for k >= 1). *)
Lemma PUSH k: forall l r,
  l {{C}}> [0;0] *> [1;0]^^2 *> [1;1;0]^^k *> [1;1;1] *> r -->+
  [1;0;0]^^k *> [1;0;1;0] *> l {{C}}> [0;0] *> [1;0] *> [1] *> r.
Proof. es. Qed.

(** Ending bites B1, B0, B0c: they read the left part (10)^p 1 and the 00 left of it. *)
Lemma BITE1 p: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;0] *> [1;1] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+3) *> [1] *> r.
Proof. es. Qed.

Lemma BITE0 p j: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;1;1]^^j *> [1;1;0] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+2) *> [1] *> [0;1;1]^^j *> [1] *> r.
Proof. es. Qed.

Lemma BITE0c p j: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;1;1]^^j *> [1;1;1;1;1;1;0] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+2) *> [1;1;1] *> [1;1;0]^^j *> [1;1;1] *> r.
Proof. es. Qed.

Lemma BITE0c3 p: forall l r,
  [1] *> [0;1]^^p *> [0;0] *> l {{C}}> [0;0] *> [1;1;1;0;0] *> r -->+
  l {{C}}> [0;0] *> [1;0]^^(p+1) *> [1;1;1;1;1;1] *> r.
Proof. es. Qed.

(** ** The counter zone: zone r L v = 1^r (1 1 c_0) ... (1 1 c_(L-1)) 1 1 1, width 3L+3+r,
    c_b = 0 iff bit b of v is set (proof.md 2: the lattice of a width-w zone). *)

Definition bitc (v : nat) : sym := if Nat.odd v then 0 else 1.

Fixpoint dg (L v : nat) : list sym :=
  match L with
  | O => []
  | S L' => [1;1;bitc v] ++ dg L' (Nat.div2 v)
  end.

Definition zone (r L v : nat) : list sym := [1]^^r ++ dg L v ++ [1;1;1].

Lemma bitc_even v: bitc (2*v) = 1.
Proof. unfold bitc. rewrite Nat.odd_mul. reflexivity. Qed.

Lemma bitc_odd v: bitc (2*v+1) = 0.
Proof. unfold bitc. rewrite Nat.add_1_r, Nat.odd_succ, Nat.even_mul. reflexivity. Qed.

Lemma div2_even v: Nat.div2 (2*v) = v.
Proof. apply Nat.div2_double. Qed.

Lemma div2_odd v: Nat.div2 (2*v+1) = v.
Proof. rewrite Nat.add_1_r. apply Nat.div2_succ_double. Qed.

Lemma dg_even L v: dg (S L) (2*v) = [1;1;1] ++ dg L v.
Proof. cbn [dg]. rewrite bitc_even, div2_even. reflexivity. Qed.

Lemma dg_odd L v: dg (S L) (2*v+1) = [1;1;0] ++ dg L v.
Proof. cbn [dg]. rewrite bitc_odd, div2_odd. reflexivity. Qed.

Lemma pow_pos P: 1 <= 2^P.
Proof. pose proof (Nat.pow_nonzero 2 P). lia. Qed.

Lemma dg_zero L: dg L 0 = [1;1;1]^^L.
Proof.
  induction L as [|L IH]; [reflexivity|].
  change (dg (S L) 0) with ([1;1;1] ++ dg L 0). rewrite IH. reflexivity.
Qed.

Lemma dg_full L: dg L (2^L - 1) = [1;1;0]^^L.
Proof.
  induction L as [|L IH]; [reflexivity|].
  replace (2^(S L) - 1) with (2*(2^L-1)+1) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos L); lia).
  rewrite dg_odd, IH. reflexivity.
Qed.

Lemma dg_low b L o: dg (b + S L) (2^b*(2*o+1)) = [1;1;1]^^b ++ [1;1;0] ++ dg L o.
Proof.
  induction b as [|b IH].
  - replace (2^0*(2*o+1)) with (2*o+1) by (cbn; lia). apply dg_odd.
  - replace (2^(S b)*(2*o+1)) with (2*(2^b*(2*o+1))) by (rewrite Nat.pow_succ_r'; lia).
    cbn [Nat.add]. rewrite dg_even, IH. reflexivity.
Qed.

Lemma dg_lowones k L o: dg (k + S L) (2^k - 1 + 2^(S k)*o) = [1;1;0]^^k ++ [1;1;1] ++ dg L o.
Proof.
  induction k as [|k IH].
  - replace (2^0 - 1 + 2^1*o) with (2*o) by (cbn; lia). apply dg_even.
  - replace (2^(S k) - 1 + 2^(S (S k))*o) with (2*(2^k - 1 + 2^(S k)*o)+1)
      by (rewrite !Nat.pow_succ_r'; pose proof (pow_pos k); lia).
    cbn [Nat.add]. rewrite dg_odd, IH. reflexivity.
Qed.

Lemma lowbit (x:nat): x <> 0%nat -> exists P o, x = 2^P*(2*o+1).
Proof.
  induction x as [x IH] using lt_wf_ind. intros Hx.
  destruct (Nat.Even_or_Odd x) as [[x' Hx']|[x' Hx']]; subst x.
  - destruct (IH x') as [P [o Ho]]; [lia|lia|].
    exists (S P), o. rewrite Nat.pow_succ_r'. lia.
  - exists 0%nat, x'. cbn. lia.
Qed.

Lemma lowbit_lt b o L: 2^b*(2*o+1) < 2^L -> b < L /\ o < 2^(L-b-1).
Proof.
  intros H.
  assert (Hb: b < L).
  { apply (Nat.pow_lt_mono_r_iff 2); [lia|]. pose proof (pow_pos b). nia. }
  split; [exact Hb|].
  replace L with (b + S (L-b-1)) in H by lia.
  rewrite Nat.pow_add_r, Nat.pow_succ_r' in H.
  pose proof (pow_pos b). nia.
Qed.

Lemma ones_comm b: [1;1] ++ [1;1;1]^^b = [1;1;1]^^b ++ [1;1].
Proof. induction b as [|b IH]; [reflexivity|]. cbn [lpow]. rewrite <-List.app_assoc, <-IH. reflexivity. Qed.

Lemma one_comm b: [1] ++ [1;1;1]^^b = [1;1;1]^^b ++ [1].
Proof. induction b as [|b IH]; [reflexivity|]. cbn [lpow]. rewrite <-List.app_assoc, <-IH. reflexivity. Qed.

Lemma sh110 b: [1;1] ++ [0;1;1]^^b = [1;1;0]^^b ++ [1;1].
Proof. induction b as [|b IH]; [reflexivity|]. cbn [lpow]. rewrite <-List.app_assoc, <-IH. reflexivity. Qed.

Lemma S_ones2 b s: [1;1] *> [1;1;1]^^b *> s = [1;1;1]^^b *> [1;1] *> s.
Proof. rewrite <-!Str_app_assoc, ones_comm. reflexivity. Qed.

Lemma S_ones1 b s: [1] *> [1;1;1]^^b *> s = [1;1;1]^^b *> [1] *> s.
Proof. rewrite <-!Str_app_assoc, one_comm. reflexivity. Qed.

Lemma S_sh110 b s: [1;1] *> [0;1;1]^^b *> s = [1;1;0]^^b *> [1;1] *> s.
Proof. rewrite <-!Str_app_assoc, sh110. reflexivity. Qed.

(** ** Counter forms of the round (proof.md 3.2), for any left side l *)

Definition RT (l : side) (q : nat) (Z : list sym) : Q * tape := l {{C}}> [0;0] *> [1;0]^^q *> Z *> const 0.

Lemma R1z l q L v: 1 <= v -> v < 2^L ->
  RT l (q+3) (zone 0 L v) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 0 L (v-1)).
Proof.
  intros H1 H2. destruct (lowbit v) as [b [o ->]]; [lia|].
  destruct (lowbit_lt _ _ _ H2) as [Hb Ho].
  remember (L-b-1) as L'. replace L with (b + S L') by lia.
  replace (2^b*(2*o+1) - 1) with (2^b - 1 + 2^(S b)*o) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos b); nia).
  unfold RT, zone. rewrite dg_low, dg_lowones. cbn [lpow app].
  rewrite !Str_app_assoc. apply RND2.
Qed.

Lemma R1t l q L v: 1 <= v -> v < 2^L ->
  RT l (q+3) (zone 2 L v) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 2 L (v-1)).
Proof.
  intros H1 H2. destruct (lowbit v) as [b [o ->]]; [lia|].
  destruct (lowbit_lt _ _ _ H2) as [Hb Ho].
  remember (L-b-1) as L'. replace L with (b + S L') by lia.
  replace (2^b*(2*o+1) - 1) with (2^b - 1 + 2^(S b)*o) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos b); nia).
  unfold RT, zone. rewrite dg_low, dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^2) with [1;1]. rewrite S_ones2.
  change ([1;1] *> [1;1;0] *> ?Y) with ([1;1;1;1;0] *> Y).
  eapply progress_evstep_trans. 1: apply RND1. apply evstep_refl'.
  change ([1;1;1;1] *> ?X) with ([1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Lemma R2r l q L v: 1 <= v -> v < 2^L ->
  RT l (q+3) (zone 1 L v) -->+ RT ([1;0;1;0] *> l) q (zone 0 (S L) (2*v-2)).
Proof.
  intros H1 H2. destruct (lowbit v) as [b [o ->]]; [lia|].
  destruct (lowbit_lt _ _ _ H2) as [Hb Ho].
  remember (L-b-1) as L'. replace L with (b + S L') by lia.
  replace (2*(2^b*(2*o+1))-2) with (2*(2^b - 1 + 2^(S b)*o)) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos b); nia).
  unfold RT, zone. rewrite dg_low, dg_even, dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^1) with [1]. rewrite S_ones1.
  change ([1] *> [1;1;0] *> ?Y) with ([1;1;1;0] *> Y).
  eapply progress_evstep_trans. 1: apply RND0. apply evstep_refl'.
  change ([1;1;1;1;1] *> ?X) with ([1;1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Lemma O2r l q L:
  RT l (q+3) (zone 2 L 0) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 0 (S L) (2^(S L)-1)).
Proof.
  unfold RT, zone. rewrite dg_zero, dg_full. rewrite !Str_app_assoc.
  change ([1]^^2) with [1;1]. change ([1]^^0 *> ?X) with X.
  assert (E: [1;1] *> [1;1;1]^^L *> [1;1;1] *> const 0 = [1;1;1]^^(S L) *> [1;1;0] *> const 0).
  { rewrite S_ones2, lpow_S, Str_app_assoc, <-lpow_shift'. f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. apply RND2.
Qed.

Lemma O1r l q L:
  RT l (q+3) (zone 1 L 0) -->+ RT ([1;0;1;0] *> l) (q+1) (zone 2 L (2^L-1)).
Proof.
  unfold RT, zone. rewrite dg_zero, dg_full. rewrite !Str_app_assoc.
  change ([1]^^2) with [1;1]. change ([1]^^1) with [1].
  assert (E: [1] *> [1;1;1]^^L *> [1;1;1] *> const 0 = [1;1;1]^^L *> [1;1;1;1;0] *> const 0).
  { rewrite S_ones1. f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. eapply progress_evstep_trans. 1: apply RND1. apply evstep_refl'.
  change ([1;1;1;1] *> ?X) with ([1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

Lemma O0r l q L:
  RT l (q+3) (zone 0 L 0) -->+ RT ([1;0;1;0] *> l) q (zone 0 (S L) (2^(S L)-2)).
Proof.
  replace (2^(S L)-2) with (2*(2^L-1)) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos L); lia).
  unfold RT, zone. rewrite dg_zero, dg_even, dg_full. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X.
  assert (E: [1;1;1]^^L *> [1;1;1] *> const 0 = [1;1;1]^^L *> [1;1;1;0] *> const 0).
  { f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. eapply progress_evstep_trans. 1: apply RND0. apply evstep_refl'.
  change ([1;1;1;1;1] *> ?X) with ([1;1;1] *> [1;1] *> X). rewrite S_sh110. reflexivity.
Qed.

(** ** Counter forms of the bites (proof.md 3.3).  FR p l is the frame 00 (10)^p 1 on top of l. *)

Definition FR (p : nat) (l : side) : side := [1] *> [0;1]^^p *> [0;0] *> l.

Lemma PUSHr l k L o:
  RT l 2 (zone 0 (k + S L) (2^k - 1 + 2^(S k)*o)) -->+ RT ([1;0;0]^^k *> [1;0;1;0] *> l) 1 (zone 1 L o).
Proof.
  unfold RT, zone. rewrite dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X.
  eapply progress_evstep_trans. 1: apply PUSH. apply evstep_refl'. reflexivity.
Qed.

Lemma B1z0 p l L v: RT (FR p l) 1 (zone 0 (S L) (2*v)) -->+ RT l (p+3) (zone 2 L v).
Proof.
  unfold RT, FR, zone. rewrite dg_even. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^1 *> [1;1;1] *> ?X) with ([1;0] *> [1;1] *> [1] *> X).
  eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
Qed.

Lemma B1z1 p l L v: RT (FR p l) 1 (zone 0 (S L) (2*v+1)) -->+ RT l (p+4) (zone 0 L v).
Proof.
  unfold RT, FR, zone. rewrite dg_odd. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^1 *> [1;1;0] *> ?X) with ([1;0] *> [1;1] *> [0] *> X).
  eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'.
  replace (p+4) with (S (p+3)) by lia. rewrite lpow_S, Str_app_assoc, <-lpow_shift'. reflexivity.
Qed.

Lemma B1o p l L v: RT (FR p l) 1 (zone 1 L v) -->+ RT l (p+3) (zone 0 L v).
Proof.
  unfold RT, FR, zone. destruct L as [|L].
  - cbn [dg]. change ([1;0]^^1 *> ([1]^^1 ++ [] ++ [1;1;1]) *> ?X) with ([1;0] *> [1;1] *> [1;1] *> X).
    eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
  - cbn [dg]. rewrite !Str_app_assoc.
    change ([1;0]^^1 *> [1]^^1 *> [1;1;bitc v] *> ?X) with ([1;0] *> [1;1] *> [1;bitc v] *> X).
    eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
Qed.

Lemma B1t p l L v: RT (FR p l) 1 (zone 2 L v) -->+ RT l (p+3) (zone 1 L v).
Proof.
  unfold RT, FR, zone. rewrite !Str_app_assoc.
  change ([1;0]^^1 *> [1]^^2 *> ?X) with ([1;0] *> [1;1] *> X).
  eapply progress_evstep_trans. 1: apply BITE1. apply evstep_refl'. reflexivity.
Qed.

Lemma B0r p l b L o:
  RT (FR p l) 0 (zone 0 (S b + S L) (2^(S b)*(2*o+1))) -->+ RT l (p+3) (zone 0 (b + S L) (2^b - 1 + 2^(S b)*o)).
Proof.
  unfold RT, FR, zone. rewrite dg_low, dg_lowones. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^0 *> ?X) with X.
  eapply progress_evstep_trans. 1: apply BITE0. apply evstep_refl'.
  rewrite lpow_S, Str_app_assoc.
  change ([1] *> [0;1;1] *> ?X) with ([1;0] *> [1;1] *> X). rewrite S_sh110.
  replace (p+3) with (S (p+2)) by lia. rewrite (lpow_S (p+2)), Str_app_assoc, <-lpow_shift'. reflexivity.
Qed.

Lemma B0cr p l L: RT (FR p l) 0 (zone 0 (S L) 0) -->+ RT l (p+2) (zone 0 (S L) (2^(S L)-2)).
Proof.
  replace (2^(S L)-2) with (2*(2^L-1)) by (rewrite Nat.pow_succ_r'; pose proof (pow_pos L); lia).
  unfold RT, FR, zone. rewrite dg_zero, dg_even, dg_full. rewrite !Str_app_assoc.
  change ([1]^^0 *> ?X) with X. change ([1;0]^^0 *> ?X) with X.
  assert (E: [1;1;1]^^(S L) *> [1;1;1] *> const 0 = [1;1;1]^^L *> [1;1;1;1;1;1;0] *> const 0).
  { rewrite lpow_S, Str_app_assoc, <-lpow_shift'. f_equal. cbn. repeat f_equal. apply const_unfold. }
  rewrite E. apply BITE0c.
Qed.

Lemma B0c3r p l: RT (FR p l) 0 (zone 0 0 0) -->+ RT l (p+1) (zone 0 1 0).
Proof.
  unfold RT, FR, zone. cbn [dg lpow app].
  assert (E: [1;1;1] *> const 0 = [1;1;1;0;0] *> const 0).
  { cbn. rewrite <-!const_unfold. reflexivity. }
  change ([1;0]^^0 *> ?X) with X. rewrite E.
  eapply progress_evstep_trans. 1: apply BITE0c3. apply evstep_refl'. reflexivity.
Qed.

(** ** Frames *)

Lemma FR_round p l: [1;0;1;0] *> FR p l = FR (p+2) l.
Proof.
  unfold FR. replace (p+2) with (S (S p)) by lia.
  cbn [lpow]. rewrite !Str_app_assoc. reflexivity.
Qed.

(** ** Initial segment (proof.md 7): c0 -->(327) R(-1, 6, 11111) = (6,5,0) *)

Lemma init: c0 -->* RT (const 0) 6 (zone 2 0 0).
Proof. unfold RT, zone. cbn. solve_init. Qed.

(** ** Levels.  lev P l is the top frame in shifted coordinates P = p+1; P = 0 is the cycle
    start (no frame), used only over the blank left side. *)

Definition lev (P : nat) (l : side) : side :=
  match P with
  | O => l
  | S p => FR p l
  end.

Definition okL (P : nat) (l : side) : Prop := P = 0%nat -> l = const 0.

Lemma lev_round P l: okL P l -> [1;0;1;0] *> lev P l = lev (P+2) l.
Proof.
  unfold okL. destruct P as [|P]; intros H.
  - rewrite H by reflexivity. cbn. repeat f_equal. apply const_unfold.
  - cbn [lev]. replace (S P + 2) with (S (P+2)) by lia. apply FR_round.
Qed.

Lemma okL_S P l: okL (S P) l.
Proof. unfold okL. intros H. discriminate H. Qed.

(** The abstract round (proof.md 3.2 counter form): (q, r, L, v) -> (q', r', L', v'). *)
Inductive Rnd : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| RR1z q L v: 1 <= v -> Rnd (q+3) 0 L v (q+1) 0 L (v-1)
| RR1t q L v: 1 <= v -> Rnd (q+3) 2 L v (q+1) 2 L (v-1)
| RR2 q L v: 1 <= v -> Rnd (q+3) 1 L v q 0 (S L) (2*v-2)
| RO2 q L: Rnd (q+3) 2 L 0 (q+1) 0 (S L) (2^(S L)-1)
| RO1 q L: Rnd (q+3) 1 L 0 (q+1) 2 L (2^L-1)
| RO0 q L: Rnd (q+3) 0 L 0 q 0 (S L) (2^(S L)-2).

Lemma Rnd_tape q r L v q' r' L' v' P l:
  Rnd q r L v q' r' L' v' -> v < 2^L -> okL P l ->
  RT (lev P l) q (zone r L v) -->+ RT (lev (P+2) l) q' (zone r' L' v').
Proof.
  intros H Hv Hl. rewrite <-(lev_round P l Hl).
  destruct H.
  - apply R1z; lia.
  - apply R1t; lia.
  - apply R2r; lia.
  - apply O2r.
  - apply O1r.
  - apply O0r.
Qed.

Lemma Rnd_valid q r L v q' r' L' v':
  Rnd q r L v q' r' L' v' -> v < 2^L -> r < 3 -> v' < 2^L' /\ r' < 3.
Proof.
  intros H Hv Hr. destruct H; rewrite ?Nat.pow_succ_r' in *; pose proof (pow_pos L); lia.
Qed.

Lemma Rnd_exists q r L v: 3 <= q -> r < 3 -> exists q' r' L' v', Rnd q r L v q' r' L' v'.
Proof.
  intros Hq Hr. replace q with ((q-3)+3) by lia.
  destruct (Nat.eq_dec v 0) as [->|Hv].
  - destruct r as [|[|[|]]]; [| | |lia]; eexists _, _, _, _.
    + apply RO0.
    + apply RO1.
    + apply RO2.
  - destruct r as [|[|[|]]]; [| | |lia]; eexists _, _, _, _.
    + apply RR1z; lia.
    + apply RR2; lia.
    + apply RR1t; lia.
Qed.

Lemma okL_ge P l: 1 <= P -> okL P l.
Proof. intros H. destruct P; [lia|apply okL_S]. Qed.

(** ** The invariant (proof.md 5.1) on cycle starts t = (n, r, L, v): width w = 3L+3+r *)

Definition cap (r L : nat) : nat := L + (if Nat.eqb r 1 then 1 else 0).

(** K: d = n - 2^(cap+1) >= 2 *)
Definition Kst (n r L : nat) : Prop := 2^(S (cap r L)) + 2 <= n.

(** J: n >= 3, n odd when w = 1, 2 mod 3 *)
Definition Jst (n r : nat) : Prop := 3 <= n /\ (r <> 0%nat -> n mod 2 = 1%nat).

(** M (mod 3): n + 2v - 2^(cap+2) (w = 0, 2), n + v - 2^(cap+2) (w = 1); -x is written 2x *)
Definition Mv (n r L v : nat) : nat :=
  (n + (if Nat.eqb r 1 then v else 2*v) + 2 * 2^(cap r L + 2)) mod 3.

(** The sign-law quantity Q of a frame (proof.md 5.4), P = p+1: Q = M - P = M + 2P (mod 3) *)
Definition Qv (P q r L v : nat) : nat := (Mv q r L v + 2*P) mod 3.

Definition Ist (n r L v : nat) : Prop :=
  r < 3 /\ v < 2^L /\ Kst n r L /\ Mv n r L v <> 0%nat /\ ~ (n = 6 /\ r = 1 /\ L = 0 /\ v = 0)%nat.

Lemma init_I: Ist 6 2 0 0.
Proof. unfold Ist, Kst, Mv, cap. cbn. repeat split; lia. Qed.

Lemma Rnd_sign P q r L v q' r' L' v':
  Rnd q r L v q' r' L' v' -> Qv P q r L v = Qv (P+2) q' r' L' v'.
Proof.
  intros H. unfold Qv, Mv, cap.
  destruct H as [q L v Hv|q L v Hv|q L v Hv|q L|q L|q L]; pose proof (pow_pos L);
    cbn [Nat.eqb]; rewrite ?Nat.pow_add_r; cbn [Nat.pow]; lia.
Qed.

(** ** Ending bites as one relation: from frame P = p+1 the pop is RT l (P + e) (zone r' L' v') *)

Inductive EB : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| EB1z0 L v: EB 1 0 (S L) (2*v) 2 2 L v
| EB1z1 L v: EB 1 0 (S L) (2*v+1) 3 0 L v
| EB1o L v: EB 1 1 L v 2 0 L v
| EB1t L v: EB 1 2 L v 2 1 L v
| EB0 b L o: EB 0 0 (S b + S L) (2^(S b)*(2*o+1)) 2 0 (b + S L) (2^b - 1 + 2^(S b)*o)
| EB0c L: EB 0 0 (S L) 0 1 0 (S L) (2^(S L)-2)
| EB0c3: EB 0 0 0 0 0 0 1 0.

Lemma EB_tape q r L v e r' L' v' p l:
  EB q r L v e r' L' v' -> RT (FR p l) q (zone r L v) -->+ RT l (S p + e) (zone r' L' v').
Proof.
  intros H. destruct H.
  - replace (S p + 2) with (p+3) by lia. apply B1z0.
  - replace (S p + 3) with (p+4) by lia. apply B1z1.
  - replace (S p + 2) with (p+3) by lia. apply B1o.
  - replace (S p + 2) with (p+3) by lia. apply B1t.
  - replace (S p + 2) with (p+3) by lia. apply B0r.
  - replace (S p + 1) with (p+2) by lia. apply B0cr.
  - replace (S p + 0) with (p+1) by lia. apply B0c3r.
Qed.

(** Sign law for ending bites (proof.md 5.4): M(pop) = -Q(bite) (mod 3) *)
Lemma EB_sign q r L v e r' L' v' P:
  EB q r L v e r' L' v' -> (Mv (P + e) r' L' v' + Qv P q r L v) mod 3 = 0%nat.
Proof.
  intros H. unfold Qv, Mv, cap.
  destruct H as [L v|L v|L v|L v|b L o|L|]; cbn [Nat.eqb]; rewrite ?Nat.pow_add_r; cbn [Nat.pow].
  1-4,6: pose proof (pow_pos L); lia.
  - pose proof (pow_pos L). pose proof (pow_pos b). nia.
  - lia.
Qed.

(** ** The bite at q = 2 on a level: PUSH k leaves k pending inner levels (frames p = 0,
    i.e. lev 1) over the level's own frame, now at P+2 (proof.md 3.4, the stack). *)

Lemma iter_FR0 k X: [1;0;0]^^k *> X = Nat.iter k (FR 0) X.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite lpow_S, Str_app_assoc, IH. reflexivity.
Qed.

Lemma PUSH_lev k L o P l: okL P l ->
  RT (lev P l) 2 (zone 0 (k + S L) (2^k - 1 + 2^(S k)*o)) -->+
  RT (Nat.iter k (FR 0) (lev (P+2) l)) 1 (zone 1 L o).
Proof.
  intros Hl. rewrite <-(lev_round P l Hl), <-iter_FR0. apply PUSHr.
Qed.

(** The innermost level of a nested bite is a single B1 bite: it pops into the next level's
    start (lev 1 = the frame p = 0) with t_2 = (3, Y[3:]). *)
Lemma inner1 k L o X:
  RT (Nat.iter (S k) (FR 0) X) 1 (zone 1 L o) -->+ RT (Nat.iter k (FR 0) X) 3 (zone 0 L o).
Proof. cbn [Nat.iter]. apply (EB_tape 1 1 L o 2 0 L o 0). constructor. Qed.

(** ** Bounded safety (proof.md 6, route 3 of proof.md 9) *)

Definition safe (c : Q * tape) (N : nat) : Prop := forall M, M <= N -> ~ halts_in tm c M.

Lemma safe_mono c N N': safe c N -> N' <= N -> safe c N'.
Proof. intros H Hle M HM. apply H. lia. Qed.

Lemma safe_ev c c' N: c -->* c' -> safe c' N -> safe c N.
Proof.
  intros H HN M HM Hh. apply with_counter in H as [n Hn].
  destruct (Nat.leb_spec n M).
  - apply (HN (M - n)); [lia|]. eapply preceeds_halt; eauto.
  - eapply exceeds_halt; eauto.
Qed.

Lemma safe_prog c c' N: c -->+ c' -> safe c' (N - 1) -> safe c N.
Proof.
  intros H HN M HM Hh. apply progress_multistep in H as [n Hn].
  destruct (Nat.leb_spec (S n) M).
  - apply (HN (M - S n)); [lia|]. eapply preceeds_halt; eauto.
  - eapply exceeds_halt; eauto.
Qed.

Lemma safe_prog0 c c': c -->+ c' -> safe c 0.
Proof.
  intros H M HM Hh. apply progress_multistep in H as [n Hn].
  eapply exceeds_halt; [exact Hh | | exact Hn]. lia.
Qed.

Lemma safe_RT0 l q Z: safe (RT l q Z) 0.
Proof.
  intros M HM [ch [Hrun Hh]]. assert (M = 0%nat) by lia. subst M.
  inversion Hrun; subst. unfold RT in Hh. cbn in Hh. discriminate.
Qed.

(** ** The phase lemma: rounds from a phase start to its bite (q <= 2), carrying any
    invariant that every round preserves.  j is the frame offset from the level start. *)

Lemma phase (Inv : nat -> nat -> nat -> nat -> nat -> Prop):
  (forall j q r L v q' r' L' v', Rnd q r L v q' r' L' v' -> v < 2^L ->
     Inv j q r L v -> Inv (j+2) q' r' L' v') ->
  forall q j P l r L v, okL (P + j) l -> r < 3 -> v < 2^L -> Inv j q r L v ->
  exists j' q' r' L' v', q' <= 2 /\ r' < 3 /\ v' < 2^L' /\ Inv j' q' r' L' v' /\
    j <= j' /\ (3 <= q -> j + 2 <= j') /\
    RT (lev (P + j) l) q (zone r L v) -->* RT (lev (P + j') l) q' (zone r' L' v').
Proof.
  intros Hstep q. induction q as [q IH] using lt_wf_ind. intros j P l r L v Hl Hr Hv HI.
  destruct (Nat.le_gt_cases q 2) as [Hq|Hq].
  - exists j, q, r, L, v. repeat split; try assumption; try lia. apply evstep_refl.
  - destruct (Rnd_exists q r L v ltac:(lia) Hr) as [q' [r' [L' [v' HR]]]].
    assert (Hq': q' < q) by (destruct HR; lia).
    destruct (Rnd_valid _ _ _ _ _ _ _ _ HR Hv Hr) as [Hv' Hr'].
    assert (Hl': okL (P + (j+2)) l) by (apply okL_ge; lia).
    destruct (IH q' Hq' (j+2) P l r' L' v' Hl' Hr' Hv' (Hstep _ _ _ _ _ _ _ _ _ HR Hv HI))
      as [j2 [q2 [r2 [L2 [v2 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]].
    exists j2, q2, r2, L2, v2. repeat split; try assumption; try lia.
    eapply evstep_trans. 2: exact H7.
    apply progress_evstep. replace (P + (j+2)) with ((P+j)+2) by lia. apply Rnd_tape; assumption.
Qed.

(** ** Classes of level starts and the phase invariants (proof.md 5) *)

Lemma cap0 L: cap 0 L = L. Proof. unfold cap. cbn. lia. Qed.
Lemma cap1 L: cap 1 L = S L. Proof. unfold cap. cbn. lia. Qed.
Lemma cap2 L: cap 2 L = L. Proof. unfold cap. cbn. lia. Qed.

Ltac pw := rewrite ?Nat.pow_succ_r' in *.

Lemma pow0 L: L = 0%nat -> 2^L = 1%nat.
Proof. intros ->. reflexivity. Qed.

(** K' = K minus T_c and (6,4,0) *)
Definition Kx (n r L v : nat) : Prop :=
  Kst n r L /\ ~ (r = 2%nat /\ v = 2^L - 1 /\ n = 2^(S L) + 2) /\
  ~ (n = 6%nat /\ r = 1%nat /\ L = 0%nat /\ v = 0%nat).

Definition Pre (n r L v : nat) : Prop := Jst n r \/ Kx n r L v.

(** Safety along a phase (Lemma P): no H, and every bite has a rule. *)
Definition Saf (q r L v : nat) : Prop :=
  match r with
  | O => (L = 0%nat -> 3 <= q) /\ ~ (q = 2%nat /\ v = 2^L - 1) /\ (q = 0%nat -> v mod 2 = 0%nat)
  | 1%nat => 3 <= q /\ (v = 0%nat -> (q <= 2^(S L) + 2 -> q mod 2 = 1%nat) /\ q <> 2^(S L) + 4)
  | _ => (q <= 2*v + 2 -> q mod 2 = 1%nat) /\ q <> 2*v + 4
  end.

(** The K bound along a phase from K' (Lemma K, Lemma A1); j is the frame offset. *)
Definition KI (j q r L v : nat) : Prop :=
  match r with
  | O => 2^L <= j + q /\ (2^(S L) <= j + 2*v + 2 \/ 2^(S L) + 1 <= j + q) /\
         (q = 0%nat -> v <> 0%nat) /\ (L = 0%nat -> 4 <= q)
  | 1%nat => 2^(S (S L)) + 2 <= q /\ (v = 0%nat -> 2^(S L) + 5 <= q)
  | _ => 2^(S L) + 2 <= j + q /\ 2*v + 5 <= q
  end.

(** The overflow bound along a phase from a zone-dominated start (Lemma Z'), target cap C. *)
Definition ZI (C q r L v : nat) : Prop :=
  1 <= C /\
  match r with
  | O => L <= S C /\ q + 2^(S (S L)) + C <= 2*v + L + 2^(S (S (S C))) + 1 /\
         (q = 0%nat -> v = 0%nat -> L <= C)
  | 1%nat => S (S L) <= C /\ q <= 2^(S (S L)) + 1 /\ 3 <= q
  | _ => S L <= C /\ q <= 2*v + 2^(S L) + 1
  end.

Lemma Saf_step q r L v q' r' L' v': Rnd q r L v q' r' L' v' -> v < 2^L -> Saf q r L v -> Saf q' r' L' v'.
Proof.
  intros H Hv HS. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  destruct H; cbn [Saf] in *; pw; lia.
Qed.

Lemma KI_step j q r L v q' r' L' v': Rnd q r L v q' r' L' v' -> v < 2^L -> KI j q r L v -> KI (j+2) q' r' L' v'.
Proof.
  intros H Hv HK. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  destruct H; cbn [KI] in *.
  1-5: pw; lia.
  destruct L as [|L]; cbn [Nat.pow] in *; [lia|]. pose proof (pow_pos L). pw. lia.
Qed.

Lemma pow_mono a b: a <= b -> 2^a <= 2^b.
Proof. intros H. apply Nat.pow_le_mono_r; lia. Qed.

Lemma pow_lin a: S a <= 2^a.
Proof. pose proof (Nat.pow_gt_lin_r 2 a ltac:(lia)). lia. Qed.

Lemma ZI_step C q r L v q' r' L' v': Rnd q r L v q' r' L' v' -> v < 2^L -> ZI C q r L v -> ZI C q' r' L' v'.
Proof.
  intros H Hv [HC HZ]. split; [exact HC|]. pose proof (pow_pos L) as HL. pose proof (pow_lin C) as HlC.
  pose proof (pow0 L) as H0.
  destruct H; cbn [ZI] in *.
  - pw; lia.
  - pw; lia.
  - (* R2 *) pose proof (pow_mono (S (S L)) C ltac:(lia)). pw; lia.
  - (* O2 *) pose proof (pow_mono (S L) C ltac:(lia)). pw; lia.
  - (* O1 *) pw; lia.
  - (* O0 *) destruct (Nat.eq_dec L (S C)) as [E|E].
    + subst L. pw. lia.
    + destruct L as [|L]; cbn [Nat.pow] in *; [lia|]. pose proof (pow_pos L). pw. lia.
Qed.

(** The phase invariant of a level started at t = (n, r, L, v): sign law (Qv), the U5 bound,
    safety, the K bound (t in K') and the overflow bound (t in J, zone-dominated). *)
Definition PI (n r L v j q r' L' v' : nat) : Prop :=
  j mod 2 = 0%nat /\ Qv j q r' L' v' = Mv n r L v /\
  (r' = 1%nat -> j = 0%nat) /\ (r' = 2%nat -> L' = 0%nat -> j <= 2) /\
  Saf q r' L' v' /\ (Kx n r L v -> KI j q r' L' v') /\
  (Jst n r -> ~ Kst n r L -> ZI (S (cap r L)) q r' L' v').

Lemma PI_step n r L v j q r1 L1 v1 q' r' L' v':
  Rnd q r1 L1 v1 q' r' L' v' -> v1 < 2^L1 -> PI n r L v j q r1 L1 v1 -> PI n r L v (j+2) q' r' L' v'.
Proof.
  intros H Hv [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  split; [lia|]. split; [rewrite <-H2; symmetry; apply Rnd_sign; exact H|].
  split; [intros E; subst r'; inversion H|].
  split.
  { intros E1 E2. inversion H; subst; try discriminate.
    - cbn in Hv. lia.
    - specialize (H3 eq_refl). lia. }
  split; [eapply Saf_step; eauto|].
  split; [intros HK; eapply KI_step; eauto|].
  intros HJ HK. eapply ZI_step; eauto.
Qed.

Lemma Mv_lt3 n r L v: Mv n r L v < 3.
Proof. unfold Mv. apply Nat.mod_upper_bound. lia. Qed.

Lemma Qv0 q r L v: Qv 0 q r L v = Mv q r L v.
Proof. unfold Qv. rewrite Nat.mul_0_r, Nat.add_0_r. apply Nat.mod_small, Mv_lt3. Qed.

Lemma Pre_n3 n r L v: Pre n r L v -> 3 <= n.
Proof.
  intros [[H _]|[H _]]; [exact H|]. unfold Kst in H. pose proof (pow_pos (S (cap r L))). lia.
Qed.

Lemma Saf_start n r L v: r < 3 -> v < 2^L -> Pre n r L v -> Saf n r L v.
Proof.
  intros Hr Hv HP. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  destruct HP as [[Hn Hp]|[HK [HT H6]]].
  - destruct r as [|[|[|r]]]; cbn [Saf]; pw; lia.
  - unfold Kst in HK. destruct r as [|[|[|r]]]; cbn [Saf]; rewrite ?cap0, ?cap1, ?cap2 in HK; pw; try lia.
    destruct (Nat.eq_dec L 0) as [->|EL]; [cbn in *; lia|].
    assert (2 <= 2^L) by (destruct L; [lia|]; cbn [Nat.pow]; pose proof (pow_pos L); lia). lia.
Qed.

Lemma KI_start n r L v: r < 3 -> v < 2^L -> Kx n r L v -> KI 0 n r L v.
Proof.
  intros Hr Hv [HK [HT H6]]. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  unfold Kst in HK. destruct r as [|[|[|r]]]; cbn [KI]; rewrite ?cap0, ?cap1, ?cap2 in HK; pw; try lia.
  destruct (Nat.eq_dec L 0) as [->|EL]; [cbn in *; lia|].
  assert (2 <= 2^L) by (destruct L; [lia|]; cbn [Nat.pow]; pose proof (pow_pos L); lia). lia.
Qed.

Lemma ZI_start n r L v: r < 3 -> v < 2^L -> Jst n r -> ~ Kst n r L -> ZI (S (cap r L)) n r L v.
Proof.
  intros Hr Hv [Hn Hp] HK. pose proof (pow_pos L) as HL. pose proof (pow0 L) as H0.
  unfold Kst in HK. split; [lia|].
  destruct r as [|[|[|r]]]; cbn [ZI]; rewrite ?cap0, ?cap1, ?cap2 in *; pw; lia.
Qed.

Lemma PI_start n r L v: r < 3 -> v < 2^L -> Pre n r L v -> PI n r L v 0 n r L v.
Proof.
  intros Hr Hv HP. split; [reflexivity|]. split; [apply Qv0|].
  split; [reflexivity|]. split; [lia|]. split; [apply Saf_start; assumption|].
  split; [intros HK; apply KI_start; assumption|].
  intros HJ HK. apply ZI_start; assumption.
Qed.

(** ** What a level guarantees about its pop (proof.md 6, U1-U4, plus the (6,4,0) bound U5).
    A level from t = (n, r, L, v) at frame P pops at RT l (P + n') (zone r' L' v'). *)
Definition Post (n r L v n' r' L' v' : nat) : Prop :=
  r' < 3 /\ v' < 2^L' /\
  (Jst n r -> Jst (S n') r') /\
  (Kx n r L v -> Kst n' r' L') /\
  (Jst n r -> ~ Kst n r L -> Kst (S n') r' L' \/ cap r' L' <= S (cap r L)) /\
  (Mv n' r' L' v' + Mv n r L v) mod 3 = 0%nat /\
  (r' = 1%nat -> L' = 0%nat -> v' = 0%nat -> n' = 4%nat \/ 8 <= n').

Definition U (N : nat) : Prop :=
  forall P l n r L v, okL P l -> r < 3 -> v < 2^L -> Pre n r L v ->
  (forall n' r' L' v', Post n r L v n' r' L' v' -> safe (RT l (P + n') (zone r' L' v')) (N - 1)) ->
  safe (RT (lev P l) n (zone r L v)) N.

(** ** Bites (proof.md 3.3, Lemma P3) *)

Lemma lowones L: forall v, v < 2^L -> v <> 2^L - 1 ->
  exists k L' o, L = k + S L' /\ v = 2^k - 1 + 2^(S k) * o /\ o < 2^L'.
Proof.
  induction L as [|L IH]; intros v Hv Hne.
  - cbn in *. lia.
  - rewrite Nat.pow_succ_r' in Hv, Hne.
    destruct (Nat.Even_or_Odd v) as [[o Ho]|[v' Hv']].
    + exists 0%nat, L, o. cbn. lia.
    + destruct (IH v') as [k [L' [o [E1 [E2 E3]]]]]; [lia|lia|].
      exists (S k), L', o. split; [lia|]. split; [|exact E3].
      subst v v'. pose proof (pow_pos k). pw. lia.
Qed.

Lemma bite_shape j qb rb Lb vb: qb <= 2 -> rb < 3 -> vb < 2^Lb -> Saf qb rb Lb vb -> 2 <= j ->
  (rb = 1%nat -> j = 0%nat) ->
  (exists e r' L' v', EB qb rb Lb vb e r' L' v') \/
  (qb = 2%nat /\ rb = 0%nat /\ exists k L' o, Lb = k + S L' /\ vb = 2^k - 1 + 2^(S k) * o /\ o < 2^L').
Proof.
  intros Hq Hr Hv HS Hj H1.
  destruct rb as [|[|[|rb]]]; [| lia | | lia]; cbn [Saf] in HS.
  - destruct HS as [HS1 [HS2 HS3]].
    destruct qb as [|[|[|qb]]]; [| | |lia].
    + destruct Lb as [|Lb]; [lia|]. left.
      destruct (Nat.eq_dec vb 0) as [->|Hne].
      * eexists _, _, _, _. apply EB0c.
      * destruct (lowbit vb Hne) as [b [o ->]].
        destruct b as [|b]; [rewrite Nat.pow_0_r, Nat.mul_1_l in HS3; lia|].
        destruct (lowbit_lt _ _ _ Hv) as [Hb Ho].
        replace (S Lb) with (S b + S (Lb - b - 1)) by lia.
        eexists _, _, _, _. apply EB0.
    + destruct Lb as [|Lb]; [lia|]. left.
      destruct (Nat.Even_or_Odd vb) as [[w ->]|[w ->]]; eexists _, _, _, _; [apply EB1z0|apply EB1z1].
    + right. split; [reflexivity|]. split; [reflexivity|]. apply lowones; [exact Hv|]. tauto.
  - destruct HS as [HS1 HS2]. assert (qb = 1%nat) as -> by lia.
    left. eexists _, _, _, _. apply EB1t.
Qed.

Lemma EB_valid q r L v e r' L' v': EB q r L v e r' L' v' -> v < 2^L -> r' < 3 /\ v' < 2^L'.
Proof.
  intros H Hv. destruct H; (split; [lia|]).
  - pw. lia.
  - pw. lia.
  - exact Hv.
  - exact Hv.
  - rewrite Nat.pow_add_r in *. pw. pose proof (pow_pos b). pose proof (pow_pos L).
    assert (o < 2^L) by nia. nia.
  - pose proof (pow_pos L). pw. lia.
  - cbn. lia.
Qed.

Lemma EB_lev q r L v e r' L' v' P l: 1 <= P -> EB q r L v e r' L' v' ->
  RT (lev P l) q (zone r L v) -->+ RT l (P + e) (zone r' L' v').
Proof. intros HP H. destruct P as [|p]; [lia|]. cbn [lev]. apply EB_tape. exact H. Qed.

Lemma Kst_mono n n' r L: Kst n r L -> n <= n' -> Kst n' r L.
Proof. unfold Kst. lia. Qed.

(** A plain end: the first bite of the level is an ending bite (proof.md 5.5, 5.7 plain cases). *)
Lemma ending n r L v j qb rb Lb vb e r' L' v':
  EB qb rb Lb vb e r' L' v' -> PI n r L v j qb rb Lb vb -> 2 <= j -> vb < 2^Lb ->
  Post n r L v (j + e) r' L' v'.
Proof.
  intros H [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hj Hvb.
  destruct (EB_valid _ _ _ _ _ _ _ _ H Hvb) as [Hr' Hv'].
  pose proof (EB_sign _ _ _ _ _ _ _ _ j H) as HS. rewrite H2 in HS.
  split; [exact Hr'|]. split; [exact Hv'|].
  split.
  { intros _. unfold Jst. destruct H; split; lia. }
  split.
  { intros HK. specialize (H6 HK). unfold Kst.
    destruct H; cbn [KI] in H6; rewrite ?cap0, ?cap1, ?cap2; cbn [Nat.add] in *; pw; lia. }
  split.
  { intros HJ HK. destruct (H7 HJ HK) as [HC7 HZ7]. right.
    destruct H; cbn [ZI] in HZ7; rewrite ?cap0, ?cap1, ?cap2; cbn [Nat.add] in *; lia. }
  split; [exact HS|].
  intros E1 E2 E3. destruct H; try discriminate E1. subst. left. specialize (H4 eq_refl eq_refl). lia.
Qed.

(** B2 then B1 (PUSH with k = 0, then the B1 of zone 1). *)
Lemma ending_B2 n r L v j L' o:
  PI n r L v j 2 0 (0 + S L') (2^0 - 1 + 2^1 * o) -> 2 <= j -> o < 2^L' ->
  Post n r L v (j + 4) 0 L' o.
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hj Ho. cbn [Nat.add Nat.pow Nat.sub] in *.
  split; [lia|]. split; [exact Ho|].
  split; [intros _; unfold Jst; lia|].
  split.
  { intros HK. specialize (H6 HK). unfold Kst. cbn [KI] in H6. rewrite cap0. pw. lia. }
  split.
  { intros HJ HK. destruct (H7 HJ HK) as [HC7 HZ7]. right. cbn [ZI] in HZ7. rewrite cap0. lia. }
  split.
  { rewrite <-H2. unfold Qv, Mv, cap. cbn [Nat.eqb]. rewrite !Nat.pow_add_r. cbn [Nat.pow].
    pose proof (pow_pos L'). lia. }
  intros E. discriminate E.
Qed.

(** ** The stack of a nested bite (proof.md 3.4): budget and sign along the inner levels *)

(** Budget(t, C): d(t) >= 2, or cap(t) <= C (Lemmas Kp and Z' carry it from level to level). *)
Definition Budget (n r L C : nat) : Prop := Kst n r L \/ cap r L <= C.

(** Sign relation after j levels: X - 1 alternates in sign (proof.md 5.4, rule N). *)
Definition SR (j a b : nat) : Prop :=
  (j mod 2 = 0%nat -> b = a) /\ (j mod 2 = 1%nat -> (a + b + 2) mod 3 = 0%nat).

Lemma JK n r L v: Jst n r -> Kst n r L -> Kx n r L v.
Proof.
  intros [Hn Hp] HK. split; [exact HK|]. split.
  - intros [-> [_ ->]]. pw. specialize (Hp ltac:(lia)). lia.
  - intros [-> [-> _]]. specialize (Hp ltac:(lia)). lia.
Qed.

Lemma Budget_step n r L v C n' r' L' v': Jst n r -> Budget n r L C -> Post n r L v n' r' L' v' ->
  Budget (S n') r' L' (S C).
Proof.
  intros HJ HB [_ [_ [_ [HU2 [HU3 _]]]]].
  destruct (Nat.le_gt_cases (2^(S (cap r L)) + 2) n) as [HK|HK].
  - left. apply (Kst_mono n'); [apply HU2, JK; assumption | lia].
  - destruct HB as [HB|HB]; [unfold Kst in HB; lia|].
    destruct (HU3 HJ ltac:(unfold Kst; lia)) as [H|H]; [left; exact H | right; lia].
Qed.

Lemma Mv_shift a n r L v: Mv (a + n) r L v = (Mv n r L v + a) mod 3.
Proof. unfold Mv. generalize (if Nat.eqb r 1 then v else 2*v) (2 * 2^(cap r L + 2)). intros x y. lia. Qed.

Lemma SR_step j n r L v n' r' L' v' b: b < 3 -> Post n r L v n' r' L' v' -> SR j (Mv (S n') r' L' v') b ->
  SR (S j) (Mv n r L v) b.
Proof.
  intros Hb [_ [_ [_ [_ [_ [HU4 _]]]]]] [HE HO].
  change (S n') with (1 + n') in HE, HO. rewrite Mv_shift in HE, HO.
  pose proof (Mv_lt3 n r L v). pose proof (Mv_lt3 n' r' L' v').
  split; intros Hj; lia.
Qed.

Lemma pow2_mod3 k: exists x, 2^k = 3*x + 1 + k mod 2.
Proof.
  induction k as [|k [x Hx]]; [exists 0%nat; reflexivity|].
  exists (2*x + k mod 2). rewrite Nat.pow_succ_r', Hx. pose proof (Nat.mod_upper_bound k 2). lia.
Qed.

(** The sign of the bite zone (110)^k 111 Y against the zone of t_2 (proof.md 5.4, N row). *)
Lemma QvN j k L o:
  (k mod 2 = 0%nat -> Qv j 2 0 (S k + S L) (2^(S k) - 1 + 2^(S (S k)) * o) = (Mv 3 0 L o + 1 + 2*j) mod 3) /\
  (k mod 2 = 1%nat -> Qv j 2 0 (S k + S L) (2^(S k) - 1 + 2^(S (S k)) * o) = (2 * (Mv 3 0 L o + 1) + 2*j) mod 3).
Proof.
  destruct (pow2_mod3 k) as [x Hx]. pose proof (pow_pos L).
  unfold Qv, Mv, cap. cbn [Nat.eqb]. rewrite !Nat.pow_add_r. cbn [Nat.pow]. rewrite Hx.
  split; intros Hk; rewrite Hk; lia.
Qed.

(** The composite form of a level with a nested bite (proof.md 3.4, 5.7): the outer level
    resumes at t_(k+1) and its pop is that of the resumed phase, shifted by j + 2. *)
Lemma compose n r L v j k L' o n1 r1 L1 v1 n3 r3 L3 v3:
  PI n r L v j 2 0 (S k + S L') (2^(S k) - 1 + 2^(S (S k)) * o) -> 2 <= j ->
  Jst n1 r1 -> Budget n1 r1 L1 (L' + k) -> SR k (Mv 3 0 L' o) (Mv n1 r1 L1 v1) ->
  Post n1 r1 L1 v1 n3 r3 L3 v3 -> Post n r L v (j + 2 + n3) r3 L3 v3.
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hj HJ1 HB1 HSR HP.
  pose proof (Budget_step _ _ _ _ _ _ _ _ _ HJ1 HB1 HP) as HB3.
  destruct HP as [Hr3 [Hv3 [HU1 [HU2 [HU3 [HU4 HU5]]]]]].
  destruct (HU1 HJ1) as [Hn3 Hp3].
  split; [exact Hr3|]. split; [exact Hv3|].
  split.
  { intros _. split; [lia|]. intros E. specialize (Hp3 E). lia. }
  split.
  { intros HK. specialize (H6 HK). cbn [KI] in H6. unfold Kst.
    destruct HB3 as [HB3|HB3]; [unfold Kst in HB3; lia|].
    pose proof (pow_mono (S (cap r3 L3)) (S k + S L') ltac:(lia)). lia. }
  split.
  { intros HJ HK. destruct (H7 HJ HK) as [HC7 HZ7]. cbn [ZI] in HZ7.
    destruct HB3 as [HB3|HB3]; [left; apply (Kst_mono (S n3)); [exact HB3|lia] | right; lia]. }
  split.
  { rewrite (Mv_shift (j + 2) n3). destruct HSR as [HE HO]. destruct (QvN j k L' o) as [QE QO].
    pose proof (Mv_lt3 n3 r3 L3 v3). pose proof (Mv_lt3 n1 r1 L1 v1). pose proof (Mv_lt3 3 0 L' o).
    pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
    rewrite <-H2.
    destruct (Nat.eq_dec (k mod 2) 0) as [Ek|Ek].
    - rewrite (QE Ek). specialize (HE Ek). lia.
    - assert (Ek1: k mod 2 = 1%nat) by lia. rewrite (QO Ek1). specialize (HO Ek1). lia. }
  intros E1 E2 E3. right. destruct (HU5 E1 E2 E3); lia.
Qed.

Lemma STK: forall j B, (forall B', B' <= B -> U B') -> forall n r L v C X,
  Jst n r -> Budget n r L C -> r < 3 -> v < 2^L ->
  (forall n1 r1 L1 v1, Jst n1 r1 -> Budget n1 r1 L1 (C + j) -> r1 < 3 -> v1 < 2^L1 ->
     SR j (Mv n r L v) (Mv n1 r1 L1 v1) -> safe (RT X n1 (zone r1 L1 v1)) (B - j)) ->
  safe (RT (Nat.iter j (FR 0) X) n (zone r L v)) B.
Proof.
  induction j as [|j IH]; intros B HU n r L v C X HJ HB Hr Hv Hk.
  - cbn [Nat.iter].
    pose proof (Hk n r L v HJ ltac:(rewrite Nat.add_0_r; exact HB) Hr Hv
                  ltac:(split; intros; [reflexivity|lia])) as H.
    rewrite Nat.sub_0_r in H. exact H.
  - change (Nat.iter (S j) (FR 0) X) with (lev 1 (Nat.iter j (FR 0) X)).
    apply (HU B (le_n B) 1%nat (Nat.iter j (FR 0) X) n r L v (okL_S 0 _) Hr Hv (or_introl HJ)).
    intros n' r' L' v' HP.
    change (1 + n') with (S n').
    pose proof HP as [Hr' [Hv' [HU1 _]]].
    apply (IH (B - 1) (fun B' HB' => HU B' ltac:(lia)) (S n') r' L' v' (S C) X (HU1 HJ)
             (Budget_step _ _ _ _ _ _ _ _ _ HJ HB HP) Hr' Hv').
    intros n1 r1 L1 v1 HJ1 HB1 Hr1 Hv1 HS1.
    replace (B - 1 - j) with (B - S j) by lia.
    apply Hk; try assumption.
    + replace (C + S j) with (S C + j) by lia. exact HB1.
    + eapply SR_step; [apply Mv_lt3 | eassumption | eassumption].
Qed.

(** ** U(N) for every N (proof.md 6): strong induction on the number of steps *)

Lemma U_all: forall N, U N.
Proof.
  intros N. induction N as [N IH] using strong_induction.
  intros P l n r L v Hl Hr Hv Hpre Hk.
  pose proof (Pre_n3 _ _ _ _ Hpre) as Hn.
  destruct N as [|N'].
  { destruct (Rnd_exists n r L v Hn Hr) as [q' [r' [L' [v' HR]]]].
    eapply safe_prog0. eapply Rnd_tape; eassumption. }
  destruct (phase (PI n r L v) (PI_step n r L v) n 0 P l r L v)
    as [j [qb [rb [Lb [vb [Hqb [Hrb [Hvb [HI [_ [Hj Hrun]]]]]]]]]]].
  { rewrite Nat.add_0_r. exact Hl. }
  { exact Hr. } { exact Hv. } { apply PI_start; assumption. }
  specialize (Hj Hn). rewrite Nat.add_0_r in Hrun. cbn [Nat.add] in Hj.
  eapply safe_ev; [exact Hrun|].
  assert (HlP: okL (P + j) l) by (apply okL_ge; lia).
  pose proof HI as [_ [_ [HI3 [_ [HI5 _]]]]].
  destruct (bite_shape j qb rb Lb vb Hqb Hrb Hvb HI5 Hj HI3)
    as [[e [r' [L' [v' HE]]]] | [Eq [Er [k [L' [o [EL [Ev Ho]]]]]]]].
  - (* an ending bite: the pop *)
    eapply safe_prog. { apply EB_lev; [lia | exact HE]. }
    replace (P + j + e) with (P + (j + e)) by lia.
    apply Hk. eapply ending; eassumption.
  - subst qb rb Lb vb. destruct k as [|k].
    + (* B2, then B1 *)
      eapply safe_prog.
      { eapply progress_trans. { apply (PUSH_lev 0 L' o (P + j) l HlP). }
        cbn [Nat.iter]. apply (EB_lev 1 1 L' o 2 0 L' o (P + j + 2) l); [lia | constructor]. }
      replace (P + j + 2 + 2) with (P + (j + 4)) by lia.
      apply Hk. apply ending_B2; assumption.
    + (* the nested bite N: PUSH, the innermost B1, the stack, then the rest of the level *)
      assert (Hpush: RT (lev (P + j) l) 2 (zone 0 (S k + S L') (2^(S k) - 1 + 2^(S (S k)) * o)) -->+
                     RT (Nat.iter k (FR 0) (lev (P + j + 2) l)) 3 (zone 0 L' o)).
      { eapply progress_trans. { apply (PUSH_lev (S k) L' o (P + j) l HlP). } apply inner1. }
      eapply safe_prog; [exact Hpush|].
      replace (S N' - 1) with N' by lia.
      apply (STK k N' (fun B HB => IH B ltac:(lia)) 3 0 L' o L' (lev (P + j + 2) l)).
      * split; [lia|]. intros E; lia.
      * right. rewrite cap0. lia.
      * lia.
      * exact Ho.
      * intros n1 r1 L1 v1 HJ1 HB1 Hr1 Hv1 HS1.
        apply (IH (N' - k) ltac:(lia) (P + j + 2) l n1 r1 L1 v1 (okL_ge (P + j + 2) l ltac:(lia)) Hr1 Hv1 (or_introl HJ1)).
        intros n3 r3 L3 v3 HP3.
        replace (P + j + 2 + n3) with (P + (j + 2 + n3)) by lia.
        apply (safe_mono _ (S N' - 1)); [| lia].
        apply Hk. eapply compose; eassumption.
Qed.

(** ** Cycles from I (proof.md 5.8) and the main theorem *)

Lemma Ist_Kx n r L v: Ist n r L v -> Kx n r L v.
Proof.
  unfold Ist, Kx. intros [Hr [Hv [HK [HM H6]]]]. split; [exact HK|]. split; [|exact H6].
  intros [-> [-> ->]]. apply HM. unfold Mv, cap. cbn [Nat.eqb]. rewrite !Nat.pow_add_r. cbn [Nat.pow].
  pose proof (pow_pos L). lia.
Qed.

Lemma cycles N: forall n r L v, Ist n r L v -> safe (RT (const 0) n (zone r L v)) N.
Proof.
  induction N as [N IH] using strong_induction. intros n r L v HI.
  pose proof (Ist_Kx _ _ _ _ HI) as HK. destruct HI as [Hr [Hv [HKs [HM H6]]]].
  apply (U_all N 0%nat (const 0) n r L v); [intros _; reflexivity | exact Hr | exact Hv | right; exact HK |].
  intros n' r' L' v' [Hr' [Hv' [_ [HU2 [_ [HU4 HU5]]]]]].
  destruct N as [|N']; [apply safe_RT0|].
  replace (S N' - 1) with N' by lia.
  change (0 + n')%nat with n'. apply IH; [lia|]. unfold Ist. split; [exact Hr'|]. split; [exact Hv'|]. split; [apply HU2, HK|].
  pose proof (Mv_lt3 n r L v). pose proof (Mv_lt3 n' r' L' v'). split; [lia|].
  intros [E1 [E2 [E3 E4]]]. destruct (HU5 E2 E3 E4); lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  intros [N HN].
  exact (safe_ev c0 _ N init (cycles N 6 2 0 0 init_I) N (le_n N) HN).
Qed.

(*
1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_---0RB  (only F0 is undefined)

zone(r,L,v) = 1^r (1 1 c_0) ... (1 1 c_(L-1)) 1 1 1,  c_b = 0 iff bit b of v is set   (width 3L+3+r)
frame p     = 0 0 (10)^p 1;   RT l q Z = l C> 0 0 (10)^q Z 0^inf
lev P l     = frame P-1 on top of l (P >= 1);  lev 0 l = l = 0^inf (the cycle start)

R1  q -> q-2,  v -> v-1                            q >= 3, v >= 1, r = 0, 2
R2  q -> q-3,  zone(1,L,v) -> zone(0,L+1,2v-2)     q >= 3, v >= 1
O2  q -> q-2,  zone(2,L,0) -> zone(0,L+1,2^(L+1)-1)
O1  q -> q-2,  zone(1,L,0) -> zone(2,L,2^L-1)
O0  q -> q-3,  zone(0,L,0) -> zone(0,L+1,2^(L+1)-2)          (every round: P -> P+2)
PUSH q = 2, zone(0,k+1+L, 2^k-1 + 2^(k+1) o) -> k new frames 0 over P+2, q = 1, zone(1,L,o)
     (k = 0: B2;  k >= 1: nested levels;  all bits set: halts)
B1  q = 1: pop frame p, q -> p+3 (+1 if bit 0 set), zone loses its first cell
B0  q = 0, bit 0 clear: pop, q -> p+3;   B0c  q = 0, v = 0: pop, q -> p+2 (p+1 on 111)

level starts t = (n,r,L,v):  cap = L + [r = 1],  K: n >= 2^(cap+1) + 2,  J: n >= 3, n odd if r <> 0
  K' = K minus (2^(L+1)+2, 2, L, 2^L-1) and (6, 1, 0, 0);   M = n + (r = 1 ? v : 2v) + 2^(cap+3) mod 3
phase invariants, kept by every round:  Saf (no halt, every bite has a rule),  KI (start in K'),
  ZI (start in J with n < 2^(cap+1) + 2),  Qv = M + 2P mod 3 (sign law)
U(N): a level from t in J or K' at any frame does not halt within N steps if every pop t' with
  U1-U5 is safe for N-1 steps;  the inner levels of a nested bite and the rest of the level after
  it use U at fewer steps (STK, compose)
I = K' with M <> 0 is closed under cycles;  start: c0 -->(327) q = 6, zone(2,0,0) = 11111, no frame
*)
