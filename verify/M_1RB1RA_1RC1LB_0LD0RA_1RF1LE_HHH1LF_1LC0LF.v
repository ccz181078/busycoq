(* 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF never halts. *)

From Coq Require Import Arith Lia ZifyNat PeanoNat Bool String Lists.Streams List.
From BusyCoq Require Import Individual62.
Import ListNotations.

Open Scope list_scope.
Open Scope sym_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Set Default Goal Selector "!".

Definition tm := Eval compute in
  (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF").

Definition config := (Q * tape)%type.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* ========================================================================= *)
(* Section 1: Step-budget calculus (`leads`, `advances`, `LeadsUpTo`)        *)
(* ========================================================================= *)

Lemma ptrans {c1 c2 c3 : config} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma pe_trans {c1 c2 c3 : config} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma ep_trans {c1 c2 c3 : config} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : config} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : config} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Definition leads (c : config) (P : config -> Prop) : Prop :=
  forall n, halts_in tm c n ->
  exists m d, m <= n /\ P d /\ halts_in tm d m.

Definition advances (c : config) (P : config -> Prop) : Prop :=
  forall n, halts_in tm c n ->
  exists m d, m < n /\ P d /\ halts_in tm d m.

Definition LeadsUpTo (N : nat) (c : config) (P : config -> Prop) : Prop :=
  forall n, n <= N -> halts_in tm c n ->
  exists m d, m <= n /\ P d /\ halts_in tm d m.

Lemma reduce_evstep {c d : config} {n : nat} :
  c -->* d -> halts_in tm c n -> exists m, m <= n /\ halts_in tm d m.
Proof.
  intros Hr Hh. destruct (with_counter Hr) as [k Hk].
  assert (Hkn : k <= n) by (eapply within_halt; eauto).
  exists (n - k). split; [lia | eapply preceeds_halt; eauto].
Qed.

Lemma reduce_progress {c d : config} {n : nat} :
  c -->+ d -> halts_in tm c n -> exists m, m < n /\ halts_in tm d m.
Proof.
  intros Hr Hh. destruct (progress_multistep _ _ _ Hr) as [k Hk].
  assert (Hkn : S k <= n) by (eapply within_halt; eauto).
  exists (n - S k). split; [lia | eapply preceeds_halt; eauto].
Qed.

Lemma leads_here {c : config} {P : config -> Prop} (HP : P c) : leads c P.
Proof. intros n Hh. exists n, c. auto. Qed.

Lemma leads_trans {c : config} {P Qp : config -> Prop}
  (H1 : leads c P) (H2 : forall d, P d -> leads d Qp) : leads c Qp.
Proof.
  intros n Hh. destruct (H1 n Hh) as [m [d [Hmn [HP Hm]]]].
  destruct (H2 d HP m Hm) as [k [e [Hkm [HQ Hk]]]].
  exists k, e. repeat split; auto; lia.
Qed.

Lemma advances_of_stepPlus {c1 c2 : config} {P : config -> Prop}
  (H1 : c1 -->+ c2) (H2 : P c2) : advances c1 P.
Proof.
  intros n Hh. destruct (reduce_progress H1 Hh) as [m [Hmn Hm]].
  exists m, c2. auto.
Qed.

Lemma advances_to_leads {c : config} {P : config -> Prop}
  (H : advances c P) : leads c P.
Proof.
  intros n Hh. destruct (H n Hh) as [m [d [Hmn Hrest]]].
  exists m, d. split; [lia | exact Hrest].
Qed.

Lemma advances_of_stepPlus_leads {c1 c2 : config} {P : config -> Prop}
  (H1 : c1 -->+ c2) (H2 : leads c2 P) : advances c1 P.
Proof.
  intros n Hh. destruct (reduce_progress H1 Hh) as [m [Hmn Hm]].
  destruct (H2 m Hm) as [k [e [Hkm Hrest]]].
  exists k, e. split; [lia | exact Hrest].
Qed.

Lemma leads_of_stepPlus_leads {c1 c2 : config} {P : config -> Prop}
  (H1 : c1 -->+ c2) (H2 : leads c2 P) : leads c1 P.
Proof.
  apply advances_to_leads. eapply advances_of_stepPlus_leads; eauto.
Qed.

Lemma leadsUpTo_here {N : nat} {c : config} {P : config -> Prop}
  (Hc : P c) : LeadsUpTo N c P.
Proof.
  intros n _ Hn. exists n, c. auto.
Qed.

Lemma leadsUpTo_mono {N : nat} {c : config} {P Qp : config -> Prop}
  (H1 : LeadsUpTo N c P) (H2 : forall d, P d -> Qp d) : LeadsUpTo N c Qp.
Proof.
  intros n HnN Hn. destruct (H1 n HnN Hn) as [m [d [Hmn [HPd Hm]]]].
  exists m, d. repeat split; auto.
Qed.

Lemma leadsUpTo_trans {N : nat} {c : config} {P Qp : config -> Prop}
  (H1 : LeadsUpTo N c P) (H2 : forall d, P d -> LeadsUpTo N d Qp) : LeadsUpTo N c Qp.
Proof.
  intros n HnN Hn. destruct (H1 n HnN Hn) as [m [d [Hmn [HPd Hm]]]].
  assert (HmN : m <= N) by lia.
  destruct (H2 d HPd m HmN Hm) as [k [e [Hkm [HQe Hk]]]].
  exists k, e. repeat split; auto; lia.
Qed.

Lemma leadsUpTo_stepPlus {N : nat} {c1 c2 : config} {P : config -> Prop}
  (H1 : c1 -->+ c2) (H2 : forall m, m < N -> LeadsUpTo m c2 P) : LeadsUpTo N c1 P.
Proof.
  intros n HnN Hn. destruct (reduce_progress H1 Hn) as [m [Hmn Hm]].
  assert (HmN : m < N) by lia.
  destruct (H2 m HmN m (Nat.le_refl m) Hm) as [k [d [Hkm [HPd Hk]]]].
  exists k, d. repeat split; auto; lia.
Qed.

Lemma decreasing_halt_budget (P : config -> Prop) :
  (forall c, P c -> advances c P) -> forall c, P c -> ~ halts tm c.
Proof.
  intros Hadv c HP [n Hn]. revert c HP Hn.
  induction n using strong_induction. intros c HP Hn.
  destruct (Hadv c HP n Hn) as [m [d [Hmn [Hd Hm]]]].
  eapply H; eauto.
Qed.

(* ========================================================================= *)
(* Section 2: Elementary tape runs & bounce lemmas                           *)
(* ========================================================================= *)

(* Mirror-renaming twin coordinates corresponding to #177's (qA..qF, L, h, R):
   tape reflection L <-> R and state permutation (A,B,C,D,E,F) -> (F,C,D,A,B,E). *)
Definition qA : Q := F.
Definition qB : Q := C.
Definition qC : Q := D.
Definition qD : Q := A.
Definition qE : Q := B.
Definition qF : Q := E.

Definition K (q : Q) (L : side) (h : Sym) (R : side) : config :=
  (q, (R, h, L)).

Lemma z_cons_def : 0%sym >> 0inf%sym = 0inf%sym.
Proof. symmetry. apply const_unfold. Qed.

Lemma pow1_succ (x : Sym) (n : nat) (s : side) :
  [x] ^^ (n + 1) *> s = x >> ([x] ^^ n *> s).
Proof. replace (n + 1) with (S n) by lia. reflexivity. Qed.

Lemma pow1_succ' (x : Sym) (n : nat) (s : side) :
  [x] ^^ (n + 1) *> s = [x] ^^ n *> (x >> s).
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma pow1_add (x : Sym) (a b : nat) (s : side) :
  [x] ^^ (a + b) *> s = [x] ^^ a *> ([x] ^^ b *> s).
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma pow_blk_succ (u : list Sym) (n : nat) (s : side) :
  u ^^ (n + 1) *> s = u *> (u ^^ n *> s).
Proof.
  replace (n + 1) with (S n) by lia.
  cbn [lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma pow_blk_succ' (u : list Sym) (n : nat) (s : side) :
  u ^^ (n + 1) *> s = u ^^ n *> (u *> s).
Proof.
  rewrite lpow_add, Str_app_assoc.
  cbn [lpow List.app]. rewrite List.app_nil_r. reflexivity.
Qed.

Lemma pow_blk_add (u : list Sym) (a b : nat) (s : side) :
  u ^^ (a + b) *> s = u ^^ a *> (u ^^ b *> s).
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma zeros_default (n : nat) : [0]%sym ^^ n *> 0inf%sym = 0inf%sym.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [lpow List.app Str_app]. rewrite IH, z_cons_def. reflexivity.
Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app lpow List.app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  lazymatch goal with
  | |- (?q1, _) -->* (?q2, _) =>
    constr_eq q1 q2;
    apply evstep_refl';
    cbn [Str_app lpow List.app];
    repeat rewrite <- const_unfold;
    reflexivity
  end.

Ltac run_prog :=
  unfold K, qA, qB, qC, qD, qE, qF;
  cbn [Str_app lpow List.app];
  repeat rewrite <- const_unfold;
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

Lemma a1_run (k : nat) : forall (L R : side),
  K qA L 1%sym ([1]%sym ^^ k *> (0%sym >> R)) -->+
  K qA ([0]%sym ^^ (k + 1) *> L) 0%sym R.
Proof.
  induction k as [| k IH]; intros L R.
  - run_prog.
  - assert (H1 :
      K qA L 1%sym ([1]%sym ^^ (S k) *> (0%sym >> R)) -->+
      K qA (0%sym >> L) 1%sym ([1]%sym ^^ k *> (0%sym >> R))) by run_prog.
    eapply ptrans; [exact H1 |].
    pose proof (IH (0%sym >> L) R) as H2.
    rewrite <- pow1_succ' in H2.
    replace (S k + 1) with (k + 1 + 1) by lia.
    exact H2.
Qed.

Lemma d1_run (k : nat) : forall (L R : side) (s : Sym),
  K qD ([1]%sym ^^ k *> (s >> L)) 1%sym R -->+
  K qD L s ([1]%sym ^^ (k + 1) *> R).
Proof.
  induction k as [| k IH]; intros L R s.
  - run_prog.
  - assert (H1 :
      K qD ([1]%sym ^^ (S k) *> (s >> L)) 1%sym R -->+
      K qD ([1]%sym ^^ k *> (s >> L)) 1%sym (1%sym >> R)) by run_prog.
    eapply ptrans; [exact H1 |].
    pose proof (IH L (1%sym >> R) s) as H2.
    rewrite <- pow1_succ' in H2.
    replace (S k + 1) with (k + 1 + 1) by lia.
    exact H2.
Qed.

Lemma e1_run (k : nat) : forall (L R : side),
  K qE L 1%sym ([1]%sym ^^ k *> (0%sym >> R)) -->+
  K qE ([1]%sym ^^ (k + 1) *> L) 0%sym R.
Proof.
  induction k as [| k IH]; intros L R.
  - run_prog.
  - assert (H1 :
      K qE L 1%sym ([1]%sym ^^ (S k) *> (0%sym >> R)) -->+
      K qE (1%sym >> L) 1%sym ([1]%sym ^^ k *> (0%sym >> R))) by run_prog.
    eapply ptrans; [exact H1 |].
    pose proof (IH (1%sym >> L) R) as H2.
    rewrite <- pow1_succ' in H2.
    replace (S k + 1) with (k + 1 + 1) by lia.
    exact H2.
Qed.

Lemma b1_walk (a : nat) (s : Sym) (L R : side) :
  K qB ([1]%sym ^^ a *> (s >> L)) 1%sym R -->+
  K qD L s ([1]%sym ^^ a *> (0%sym >> R)).
Proof.
  destruct a as [| a].
  - run_prog.
  - assert (H1 :
      K qB ([1]%sym ^^ (S a) *> (s >> L)) 1%sym R -->+
      K qD ([1]%sym ^^ a *> (s >> L)) 1%sym (0%sym >> R)) by run_prog.
    eapply ptrans; [exact H1 |].
    replace (S a) with (a + 1) by lia.
    exact (d1_run a L (0%sym >> R) s).
Qed.

Lemma b1_zero_one (a : nat) (Rest R : side) :
  K qB ([1]%sym ^^ a *> (0%sym >> 1%sym >> Rest)) 1%sym R -->+
  K qB ([1]%sym ^^ (a + 1) *> Rest) 1%sym (1%sym >> R).
Proof.
  eapply ptrans; [exact (b1_walk a 0%sym (1%sym >> Rest) R) |].
  assert (H1 :
    K qD (1%sym >> Rest) 0%sym ([1]%sym ^^ a *> (0%sym >> R)) -->+
    K qE Rest 1%sym ([1]%sym ^^ (a + 1) *> (0%sym >> R))).
  { replace (a + 1) with (S a) by lia. run_prog. }
  eapply ptrans; [exact H1 |].
  eapply ptrans; [exact (e1_run (a + 1) Rest R) |].
  rewrite (pow1_succ 1%sym (a + 1)).
  run_prog.
Qed.

Lemma b1_two_zeros_one (a : nat) (Rest R : side) :
  K qB ([1]%sym ^^ a *> (0%sym >> 0%sym >> 1%sym >> Rest)) 1%sym R -->+
  K qB Rest 1%sym ([1]%sym ^^ (a + 2) *> (0%sym >> R)).
Proof.
  eapply ptrans; [exact (b1_walk a 0%sym (0%sym >> 1%sym >> Rest) R) |].
  replace (a + 2) with (S (S a)) by lia.
  run_prog.
Qed.

Lemma b1_three_zeros (a : nat) (Rest R : side) :
  K qB ([1]%sym ^^ (a + 1) *> (0%sym >> 0%sym >> 0%sym >> Rest)) 1%sym R -->+
  K qA ([0]%sym ^^ (a + 1) *> (1%sym >> 1%sym >> 0%sym >> Rest)) 0%sym R.
Proof.
  eapply ptrans; [exact (b1_walk (a + 1) 0%sym (0%sym >> 0%sym >> Rest) R) |].
  assert (H1 :
    K qD (0%sym >> 0%sym >> Rest) 0%sym ([1]%sym ^^ (a + 1) *> (0%sym >> R)) -->+
    K qA (1%sym >> 1%sym >> 0%sym >> Rest) 1%sym ([1]%sym ^^ a *> (0%sym >> R))).
  { rewrite (pow1_succ 1%sym a). run_prog. }
  eapply ptrans; [exact H1 |].
  exact (a1_run a (1%sym >> 1%sym >> 0%sym >> Rest) R).
Qed.

Lemma a0_zero_R (c : nat) (L R : side) :
  K qA L 0%sym (0%sym >> ([1]%sym ^^ (c + 3) *> (0%sym >> R))) -->+
  K qA ([0]%sym ^^ (c + 1) *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> L)) 0%sym R.
Proof.
  assert (H1 :
    K qA L 0%sym (0%sym >> ([1]%sym ^^ (c + 3) *> (0%sym >> R))) -->+
    K qA (1%sym >> 1%sym >> 0%sym >> 1%sym >> L) 1%sym ([1]%sym ^^ c *> (0%sym >> R))).
  { replace (c + 3) with (3 + c) by lia. run_prog. }
  eapply ptrans; [exact H1 |].
  exact (a1_run c (1%sym >> 1%sym >> 0%sym >> 1%sym >> L) R).
Qed.

Lemma a0_step (L R : side) :
  K qA L 0%sym (1%sym >> R) -->+ K qB (1%sym >> L) 1%sym R.
Proof. run_prog. Qed.

Definition EBounce (j : nat) (s : Sym) (L' R' : side) : config :=
  K qE L' s ([1]%sym ^^ (2 * j + 2) *> (0%sym >> ([1]%sym ^^ j *> R'))).

Lemma ebounce_to_B1 (j : nat) (L' R' : side) :
  EBounce j 1%sym L' R' -->+
  K qB ([1]%sym ^^ (2 * j + 2) *> L') 1%sym ([1]%sym ^^ (j + 1) *> R').
Proof.
  unfold EBounce.
  eapply ptrans; [exact (e1_run (2 * j + 2) L' ([1]%sym ^^ j *> R')) |].
  rewrite (pow1_succ 1%sym (2 * j + 2)), (pow1_succ 1%sym j).
  run_prog.
Qed.

Lemma ebounce_one (j : nat) (s : Sym) (L' R' : side) :
  EBounce j 1%sym (1%sym >> 0%sym >> s >> L') R' -->+ EBounce (j + 1) s L' R'.
Proof.
  eapply ptrans; [exact (ebounce_to_B1 j (1%sym >> 0%sym >> s >> L') R') |].
  rewrite <- pow1_succ'.
  replace (2 * j + 2 + 1) with (2 * j + 3) by lia.
  eapply ptrans; [exact (b1_walk (2 * j + 3) 0%sym (s >> L') ([1]%sym ^^ (j + 1) *> R')) |].
  unfold EBounce.
  replace (2 * (j + 1) + 2) with ((2 * j + 3) + 1) by lia.
  rewrite (pow1_succ 1%sym (2 * j + 3)).
  run_prog.
Qed.

Lemma ebounce_zero (j : nat) (L0 R' : side) :
  EBounce j 0%sym (0%sym >> L0) R' -->+
  K qA ([0]%sym ^^ (2 * j + 1) *> (1%sym >> 1%sym >> 0%sym >> L0)) 0%sym ([1]%sym ^^ j *> R').
Proof.
  unfold EBounce.
  assert (H1 :
    K qE (0%sym >> L0) 0%sym ([1]%sym ^^ (2 * j + 2) *> (0%sym >> ([1]%sym ^^ j *> R'))) -->+
    K qA (1%sym >> 1%sym >> 0%sym >> L0) 1%sym ([1]%sym ^^ (2 * j) *> (0%sym >> ([1]%sym ^^ j *> R')))).
  { replace (2 * j + 2) with (2 + 2 * j) by lia. run_prog. }
  eapply ptrans; [exact H1 |].
  exact (a1_run (2 * j) (1%sym >> 1%sym >> 0%sym >> L0) ([1]%sym ^^ j *> R')).
Qed.

Lemma e0_to_B1 (j : nat) (L' R' : side) :
  EBounce j 0%sym (1%sym >> L') R' -->+
  K qB L' 1%sym ([1]%sym ^^ (2 * j + 3) *> (0%sym >> ([1]%sym ^^ j *> R'))).
Proof.
  unfold EBounce.
  replace (2 * j + 3) with ((2 * j + 2) + 1) by lia.
  rewrite (pow1_succ 1%sym (2 * j + 2)).
  run_prog.
Qed.

Lemma a0_odd_zeros (j : nat) : forall (s : Sym) (L' R' : side),
  K qA ([0]%sym ^^ (2 * j + 1) *> (s >> L')) 0%sym ([1]%sym ^^ (j + 1) *> R') -->+
  EBounce j s L' R'.
Proof.
  induction j as [| j IH]; intros s L' R'.
  - unfold EBounce. run_prog.
  - replace (S j) with (j + 1) by lia.
    replace (2 * (j + 1) + 1) with (((2 * j + 1) + 1) + 1) by lia.
    rewrite (pow1_succ' 0%sym ((2 * j + 1) + 1)).
    rewrite (pow1_succ' 0%sym (2 * j + 1)).
    rewrite (pow1_succ' 1%sym (j + 1)).
    eapply ptrans; [exact (IH 0%sym (0%sym >> s >> L') (1%sym >> R')) |].
    eapply ptrans; [exact (ebounce_zero j (s >> L') (1%sym >> R')) |].
    rewrite <- (pow1_succ' 1%sym j).
    eapply ptrans; [exact (IH 1%sym (1%sym >> 0%sym >> s >> L') R') |].
    exact (ebounce_one j s L' R').
Qed.

Lemma a0_cascade (k : nat) : forall (Lrem R' : side),
  K qA ([0]%sym ^^ (2 * k + 1) *> (1%sym >> 1%sym >> Lrem)) 0%sym ([1]%sym ^^ k *> R') -->*
  K qA ([0; 1; 1]%sym ^^ (k + 1) *> Lrem) 0%sym R'.
Proof.
  induction k as [| k IH]; intros Lrem R'.
  - apply evstep_refl'; reflexivity.
  - replace (S k) with (k + 1) by lia.
    replace (2 * (k + 1) + 1) with (((2 * k + 1) + 1) + 1) by lia.
    rewrite (pow1_succ' 0%sym ((2 * k + 1) + 1)).
    rewrite (pow1_succ' 0%sym (2 * k + 1)).
    eapply etrans;
      [exact (pev (a0_odd_zeros k 0%sym (0%sym >> 1%sym >> 1%sym >> Lrem) R')) |].
    eapply etrans;
      [exact (pev (ebounce_zero k (1%sym >> 1%sym >> Lrem) R')) |].
    pose proof (IH (0%sym >> 1%sym >> 1%sym >> Lrem) R') as H.
    rewrite (pow_blk_succ' [0; 1; 1]%sym (k + 1)).
    exact H.
Qed.

Lemma b1_zero_one_run (w : nat) : forall (a m : nat) (Rest R' : side),
  K qB ([1]%sym ^^ (a + 1) *> ([0; 1; 1]%sym ^^ w *> Rest)) 1%sym ([1]%sym ^^ m *> R') -->*
  K qB ([1]%sym ^^ (a + 2 * w + 1) *> Rest) 1%sym ([1]%sym ^^ (m + w) *> R').
Proof.
  induction w as [| w IH]; intros a m Rest R'.
  - apply evstep_refl'. f_equal; f_equal; lia_refl.
  - replace (S w) with (w + 1) by lia.
    rewrite (pow_blk_succ [0; 1; 1]%sym w).
    cbn [Str_app].
    eapply etrans;
      [exact (pev (b1_zero_one (a + 1) (1%sym >> ([0; 1; 1]%sym ^^ w *> Rest)) ([1]%sym ^^ m *> R'))) |].
    rewrite <- (pow1_succ' 1%sym (a + 1 + 1)).
    rewrite <- (pow1_succ 1%sym m).
    pose proof (IH (a + 2) (m + 1) Rest R') as H.
    replace (a + 2 + 1) with (a + 1 + 1 + 1) in H by lia.
    replace (a + 2 + 2 * w + 1) with (a + 2 * (w + 1) + 1) in H by lia.
    replace (m + 1 + w) with (m + (w + 1)) in H by lia.
    exact H.
Qed.

Lemma m_round (j : nat) (L R : side) :
  K qB ([1]%sym ^^ (2 * j + 1) *> (0%sym >> 0%sym >> 0%sym >> L)) 1%sym ([1]%sym ^^ (j + 1) *> R) -->+
  K qB ([1]%sym ^^ (2 * j + 3) *> (0%sym >> L)) 1%sym ([1]%sym ^^ (j + 1) *> R).
Proof.
  eapply ptrans; [exact (b1_three_zeros (2 * j) L ([1]%sym ^^ (j + 1) *> R)) |].
  eapply ptrans; [exact (a0_odd_zeros j 1%sym (1%sym >> 0%sym >> L) R) |].
  pose proof (ebounce_to_B1 j (1%sym >> 0%sym >> L) R) as H.
  rewrite <- (pow1_succ' 1%sym (2 * j + 2)) in H.
  replace (2 * j + 2 + 1) with (2 * j + 3) in H by lia.
  exact H.
Qed.

Lemma m_rounds (n : nat) : forall (j : nat) (L R : side),
  K qB ([1]%sym ^^ (2 * j + 1) *> ([0]%sym ^^ (2 * n + 2) *> L)) 1%sym ([1]%sym ^^ (j + n) *> R) -->*
  K qB ([1]%sym ^^ (2 * j + 2 * n + 1) *> (0%sym >> 0%sym >> L)) 1%sym ([1]%sym ^^ (j + n) *> R).
Proof.
  induction n as [| n IH]; intros j L R.
  - apply evstep_refl'.
    replace (2 * 0 + 2) with 2 by lia.
    replace (2 * j + 2 * 0 + 1) with (2 * j + 1) by lia.
    reflexivity.
  - replace (S n) with (n + 1) by lia.
    replace (2 * (n + 1) + 2) with ((((2 * n + 1) + 1) + 1) + 1) by lia.
    rewrite (pow1_succ 0%sym (((2 * n + 1) + 1) + 1)).
    rewrite (pow1_succ 0%sym ((2 * n + 1) + 1)).
    rewrite (pow1_succ 0%sym (2 * n + 1)).
    replace (j + (n + 1)) with ((j + 1) + n) by lia.
    rewrite (pow1_add 1%sym (j + 1) n).
    eapply etrans;
      [exact (pev (m_round j ([0]%sym ^^ (2 * n + 1) *> L) ([1]%sym ^^ n *> R))) |].
    pose proof (IH (j + 1) L R) as H.
    replace (2 * (j + 1) + 1) with (2 * j + 3) in H by lia.
    replace (2 * (j + 1) + 2 * n + 1) with (2 * j + 2 * (n + 1) + 1) in H by lia.
    replace (2 * n + 2) with ((2 * n + 1) + 1) in H by lia.
    rewrite (pow1_succ 0%sym (2 * n + 1)) in H.
    rewrite (pow1_add 1%sym (j + 1) n) in H.
    exact H.
Qed.

Lemma fixed89 (Lrem : side) :
  K qA ([0; 1; 1]%sym ^^ 5 *> Lrem) 0%sym 0inf%sym -->+
  K qB ([1]%sym ^^ 12 *> Lrem) 1%sym ([1]%sym ^^ 5 *> 0inf%sym).
Proof. run_prog. Qed.

Lemma fixed23 (Rest : side) :
  K qA (0%sym >> 0%sym >> 0%sym >> Rest) 0%sym 0inf%sym -->+
  K qB (1%sym >> 0%sym >> Rest) 1%sym ([1]%sym ^^ 4 *> 0inf%sym).
Proof. run_prog. Qed.

(* ========================================================================= *)
(* Section 3: Two-stack configuration family & 17 macro rules (`R1`..`R15`)  *)
(* ========================================================================= *)

Fixpoint encL (l : list (nat * nat)) : side :=
  match l with
  | [] => 0inf%sym
  | (z, w) :: l' =>
    [0]%sym ^^ (z + 1) *>
      (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l'))
  end.

Fixpoint encS (s : list nat) : side :=
  match s with
  | [] => 0inf%sym
  | b :: s' => 0%sym >> ([1]%sym ^^ b *> encS s')
  end.

Lemma encL_nil : encL [] = 0inf%sym.
Proof. reflexivity. Qed.

Lemma encL_cons (z w : nat) (l : list (nat * nat)) :
  encL ((z, w) :: l) =
    [0]%sym ^^ (z + 1) *>
      (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l)).
Proof. reflexivity. Qed.

Lemma encS_nil : encS [] = 0inf%sym.
Proof. reflexivity. Qed.

Lemma encS_cons (b : nat) (s : list nat) :
  encS (b :: s) = 0%sym >> ([1]%sym ^^ b *> encS s).
Proof. reflexivity. Qed.

Definition Beq (m : nat) (l : list (nat * nat)) : config :=
  K qB ([1]%sym ^^ (2 * m + 2) *> encL l) 1%sym ([1]%sym ^^ m *> 0inf%sym).

Definition Bev (j : nat) (l : list (nat * nat)) (m : nat) (s : list nat) : config :=
  K qB ([1]%sym ^^ (2 * j + 1) *> encL l) 1%sym ([1]%sym ^^ m *> encS s).

Definition Bodd (k : nat) (l : list (nat * nat)) (m : nat) (s : list nat) : config :=
  K qB ([1]%sym ^^ (2 * k + 10) *> encL l) 1%sym ([1]%sym ^^ m *> encS s).

Definition Amega (z w : nat) (l : list (nat * nat)) (m : nat) (s : list nat) : config :=
  K qA (encL ((z, w) :: l)) 0%sym ([1]%sym ^^ m *> encS s).

Definition Bounce (w : nat) (l : list (nat * nat)) (s : list nat) : config :=
  K qA ([0; 1; 1]%sym ^^ (w + 5) *> encL l) 0%sym (encS s).

Lemma default3 : 0inf%sym = 0%sym >> 0%sym >> 0%sym >> 0inf%sym.
Proof. symmetry. repeat rewrite z_cons_def. reflexivity. Qed.

Lemma zeros3 (n : nat) (X : side) :
  [0]%sym ^^ (n + 3) *> X = 0%sym >> 0%sym >> 0%sym >> ([0]%sym ^^ n *> X).
Proof. replace (n + 3) with (3 + n) by lia. reflexivity. Qed.

Lemma zeros3' (n : nat) (X : side) :
  [0]%sym ^^ (n + 3) *> X = [0]%sym ^^ n *> (0%sym >> 0%sym >> 0%sym >> X).
Proof. rewrite pow1_add. reflexivity. Qed.

Lemma zeros2 (n : nat) (X : side) :
  [0]%sym ^^ (n + 2) *> X = 0%sym >> 0%sym >> ([0]%sym ^^ n *> X).
Proof. replace (n + 2) with (2 + n) by lia. reflexivity. Qed.

Lemma zeros1 (n : nat) (X : side) :
  [0]%sym ^^ (n + 1) *> X = 0%sym >> ([0]%sym ^^ n *> X).
Proof. replace (n + 1) with (1 + n) by lia. reflexivity. Qed.

Lemma ones1 (n : nat) (X : side) :
  [1]%sym ^^ (n + 1) *> X = 1%sym >> ([1]%sym ^^ n *> X).
Proof. replace (n + 1) with (1 + n) by lia. reflexivity. Qed.

Lemma ones1' (n : nat) (X : side) :
  [1]%sym ^^ (n + 1) *> X = [1]%sym ^^ n *> (1%sym >> X).
Proof. exact (pow1_succ' 1%sym n X). Qed.

Lemma ones_one (X : side) : [1]%sym ^^ 1 *> X = 1%sym >> X.
Proof. reflexivity. Qed.

Lemma ones_add (a b : nat) (X : side) :
  [1]%sym ^^ (a + b) *> X = [1]%sym ^^ a *> ([1]%sym ^^ b *> X).
Proof. exact (pow1_add 1%sym a b X). Qed.

Lemma blk_add (a b : nat) (X : side) :
  [0; 1; 1]%sym ^^ (a + b) *> X = [0; 1; 1]%sym ^^ a *> ([0; 1; 1]%sym ^^ b *> X).
Proof. exact (pow_blk_add [0; 1; 1]%sym a b X). Qed.

Theorem R4 (j r z w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bev j ((z + 2, w) :: l') (j + 1 + r) s -->+ Bev (j + 1) ((z, w) :: l') (j + 1 + r) s.
Proof.
  unfold Bev.
  rewrite encL_cons, encL_cons.
  replace (z + 2 + 1) with (z + 3) by lia.
  rewrite zeros3, zeros1, (ones_add (j + 1) r).
  replace (2 * (j + 1) + 1) with (2 * j + 3) by lia.
  exact (m_round j
    ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l')))
    ([1]%sym ^^ r *> encS s)).
Qed.

Theorem R4nil (j r : nat) (s : list nat) :
  Bev j [] (j + 1 + r) s -->+ Bev (j + 1) [] (j + 1 + r) s.
Proof.
  unfold Bev.
  rewrite encL_nil, (ones_add (j + 1) r).
  replace (2 * (j + 1) + 1) with (2 * j + 3) by lia.
  pose proof (m_round j 0inf%sym ([1]%sym ^^ r *> encS s)) as H.
  repeat rewrite z_cons_def in H.
  repeat rewrite z_cons_def.
  exact H.
Qed.

Theorem R5 (m z w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bev (m + 4) ((z + 2, w) :: l') (m + 4) s -->+ Bounce m ((z, w) :: l') s.
Proof.
  unfold Bev, Bounce.
  rewrite encL_cons, encL_cons.
  replace (z + 2 + 1) with (z + 3) by lia.
  rewrite zeros3, zeros1.
  eapply pe_trans; [exact (b1_three_zeros (2 * (m + 4)) _ _) |].
  pose proof (a0_cascade (m + 4)
    (0%sym >> ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l'))))
    (encS s)) as H.
  replace (m + 4 + 1) with (m + 5) in H by lia.
  exact H.
Qed.

Theorem R5nil (m : nat) (s : list nat) :
  Bev (m + 4) [] (m + 4) s -->+ Bounce m [] s.
Proof.
  unfold Bev, Bounce.
  rewrite encL_nil.
  rewrite default3 at 1.
  eapply pe_trans; [exact (b1_three_zeros (2 * (m + 4)) 0inf%sym ([1]%sym ^^ (m + 4) *> encS s)) |].
  pose proof (a0_cascade (m + 4) (0%sym >> 0inf%sym) (encS s)) as H.
  replace (m + 4 + 1) with (m + 5) in H by lia.
  repeat rewrite z_cons_def in H.
  repeat rewrite z_cons_def.
  exact H.
Qed.

Lemma pop_frame0 (a m w : nat) (l' : list (nat * nat)) (R' : side) :
  K qB ([1]%sym ^^ a *> encL ((0, w) :: l')) 1%sym ([1]%sym ^^ m *> R') -->+
  K qB ([1]%sym ^^ (a + 2 * w + 13) *> encL l') 1%sym ([1]%sym ^^ (m + w + 7) *> R').
Proof.
  rewrite encL_cons.
  cbn [Nat.add lpow List.app Str_app].
  eapply ptrans; [exact (b1_zero_one a _ _) |].
  rewrite <- (ones1' (a + 1)).
  replace (a + 1 + 1) with (a + 2) by lia.
  eapply pe_trans; [exact (b1_zero_one (a + 2) _ _) |].
  rewrite <- (ones1 m).
  rewrite <- (ones1 (m + 1)).
  pose proof (b1_zero_one_run (w + 5) (a + 2) (m + 1 + 1) (encL l') R') as H.
  replace (a + 2 + 2 * (w + 5) + 1) with (a + 2 * w + 13) in H by lia.
  replace (m + 1 + 1 + (w + 5)) with (m + w + 7) in H by lia.
  exact H.
Qed.

Lemma pop_frame1 (a m w : nat) (l' : list (nat * nat)) (R' : side) :
  K qB ([1]%sym ^^ a *> encL ((1, w) :: l')) 1%sym ([1]%sym ^^ m *> R') -->+
  K qB ([1]%sym ^^ (2 * w + 12) *> encL l') 1%sym
    ([1]%sym ^^ (a + w + 8) *> (0%sym >> ([1]%sym ^^ m *> R'))).
Proof.
  rewrite encL_cons.
  cbn [Nat.add lpow List.app Str_app].
  eapply ptrans; [exact (b1_two_zeros_one a _ _) |].
  pose proof (b1_zero_one 1
    ([0; 1; 1]%sym ^^ (w + 5) *> encL l')
    ([1]%sym ^^ (a + 2) *> (0%sym >> ([1]%sym ^^ m *> R')))) as H1.
  rewrite ones_one in H1.
  eapply pe_trans; [exact H1 |].
  rewrite <- (ones1 (a + 2)).
  pose proof (b1_zero_one_run (w + 5) 1 (a + 2 + 1) (encL l')
    (0%sym >> ([1]%sym ^^ m *> R'))) as H.
  replace (1 + 2 * (w + 5) + 1) with (2 * w + 12) in H by lia.
  replace (a + 2 + 1 + (w + 5)) with (a + w + 8) in H by lia.
  exact H.
Qed.

Theorem R2 (m w : nat) (l' : list (nat * nat)) :
  Beq m ((0, w) :: l') -->+ Bev (m + w + 7) l' (m + w + 7) [].
Proof.
  unfold Beq, Bev.
  pose proof (pop_frame0 (2 * m + 2) m w l' 0inf%sym) as H.
  replace (2 * m + 2 + 2 * w + 13) with (2 * (m + w + 7) + 1) in H by lia.
  rewrite encS_nil.
  exact H.
Qed.

Theorem R3 (m w : nat) (l' : list (nat * nat)) :
  Beq m ((1, w) :: l') -->+ Bodd (w + 1) l' (2 * m + w + 10) [m].
Proof.
  unfold Beq, Bodd.
  pose proof (pop_frame1 (2 * m + 2) m w l' 0inf%sym) as H.
  replace (2 * m + 2 + w + 8) with (2 * m + w + 10) in H by lia.
  replace (2 * w + 12) with (2 * (w + 1) + 10) in H by lia.
  rewrite encS_cons, encS_nil.
  exact H.
Qed.

Theorem R6 (j m w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bev j ((0, w) :: l') m s -->+ Bodd (j + w + 2) l' (m + w + 7) s.
Proof.
  unfold Bev, Bodd.
  pose proof (pop_frame0 (2 * j + 1) m w l' (encS s)) as H.
  replace (2 * j + 1 + 2 * w + 13) with (2 * (j + w + 2) + 10) in H by lia.
  exact H.
Qed.

Theorem R7 (j m w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bev j ((1, w) :: l') m s -->+ Bodd (w + 1) l' (2 * j + w + 9) (m :: s).
Proof.
  unfold Bev, Bodd.
  pose proof (pop_frame1 (2 * j + 1) m w l' (encS s)) as H.
  replace (2 * j + 1 + w + 8) with (2 * j + w + 9) in H by lia.
  replace (2 * w + 12) with (2 * (w + 1) + 10) in H by lia.
  rewrite encS_cons.
  exact H.
Qed.

Theorem R8a (k m w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bodd k ((0, w) :: l') m s -->+ Bev (k + w + 11) l' (m + w + 7) s.
Proof.
  unfold Bodd, Bev.
  pose proof (pop_frame0 (2 * k + 10) m w l' (encS s)) as H.
  replace (2 * k + 10 + 2 * w + 13) with (2 * (k + w + 11) + 1) in H by lia.
  exact H.
Qed.

Theorem R8b (k m w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bodd k ((1, w) :: l') m s -->+ Bodd (w + 1) l' (2 * k + w + 18) (m :: s).
Proof.
  unfold Bodd.
  pose proof (pop_frame1 (2 * k + 10) m w l' (encS s)) as H.
  replace (2 * k + 10 + w + 8) with (2 * k + w + 18) in H by lia.
  replace (2 * w + 12) with (2 * (w + 1) + 10) in H by lia.
  rewrite encS_cons.
  exact H.
Qed.

Theorem R8 (k r z w : nat) (l' : list (nat * nat)) (s : list nat) :
  Bodd k ((z + 2, w) :: l') (k + 5 + r) s -->+
  Bev 0 ((z, w) :: l') (2 * k + 11) ((k + 4 + r) :: s).
Proof.
  unfold Bodd, Bev.
  rewrite encL_cons, encL_cons, encS_cons.
  replace (z + 2 + 1) with (z + 3) by lia.
  rewrite zeros3, zeros1.
  replace (2 * k + 10) with ((2 * k + 9) + 1) by lia.
  eapply ptrans; [exact (b1_three_zeros (2 * k + 9) _ _) |].
  replace (k + 5 + r) with ((k + 4 + r) + 1) by lia.
  rewrite (ones1 (k + 4 + r)).
  eapply ep_trans; [exact (pev (a0_step _ _)) |].
  replace (2 * k + 9 + 1) with (2 * (k + 4) + 2) by lia.
  pose proof (m_rounds (k + 4) 0
    (1%sym >> 1%sym >> 0%sym >> ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l'))))
    ([1]%sym ^^ r *> encS s)) as Hr.
  rewrite <- (ones_add (0 + (k + 4)) r) in Hr.
  cbn [Nat.add Nat.mul] in Hr.
  rewrite ones_one in Hr.
  replace (0 + (k + 4) + r) with (k + 4 + r) in Hr by lia.
  eapply ep_trans; [exact Hr |].
  pose proof (b1_two_zeros_one (2 * (k + 4) + 1)
    (1%sym >> 0%sym >> ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l'))))
    ([1]%sym ^^ (k + 4 + r) *> encS s)) as H.
  replace (2 * (k + 4) + 1 + 2) with (2 * k + 11) in H by lia.
  change (2 * 0 + 1) with 1.
  rewrite ones_one.
  exact H.
Qed.

Theorem R8nil (k r : nat) (s : list nat) :
  Bodd k [] (k + 5 + r) s -->+ Bev 0 [] (2 * k + 11) ((k + 4 + r) :: s).
Proof.
  unfold Bodd, Bev.
  rewrite encL_nil, encS_cons.
  rewrite default3 at 1.
  replace (2 * k + 10) with ((2 * k + 9) + 1) by lia.
  eapply ptrans; [exact (b1_three_zeros (2 * k + 9) 0inf%sym ([1]%sym ^^ (k + 5 + r) *> encS s)) |].
  replace (k + 5 + r) with ((k + 4 + r) + 1) by lia.
  rewrite (ones1 (k + 4 + r)).
  eapply ep_trans; [exact (pev (a0_step _ _)) |].
  replace (2 * k + 9 + 1) with (2 * (k + 4) + 2) by lia.
  pose proof (m_rounds (k + 4) 0
    (1%sym >> 1%sym >> 0%sym >> 0inf%sym)
    ([1]%sym ^^ r *> encS s)) as Hr.
  rewrite <- (ones_add (0 + (k + 4)) r) in Hr.
  cbn [Nat.add Nat.mul] in Hr.
  rewrite ones_one in Hr.
  replace (0 + (k + 4) + r) with (k + 4 + r) in Hr by lia.
  eapply ep_trans; [exact Hr |].
  pose proof (b1_two_zeros_one (2 * (k + 4) + 1)
    (1%sym >> 0%sym >> 0inf%sym)
    ([1]%sym ^^ (k + 4 + r) *> encS s)) as H.
  replace (2 * (k + 4) + 1 + 2) with (2 * k + 11) in H by lia.
  change (2 * 0 + 1) with 1.
  rewrite ones_one.
  repeat rewrite z_cons_def in H.
  repeat rewrite z_cons_def.
  exact H.
Qed.

Theorem R1 (m z w : nat) (l' : list (nat * nat)) :
  Beq (m + 5) ((z + 2, w) :: l') -->+ Bev 0 ((z, w) :: l') (2 * (m + 5) + 4) [m + 5].
Proof.
  unfold Beq, Bev.
  rewrite encL_cons, encL_cons, encS_cons, encS_nil.
  replace (z + 2 + 1) with (z + 3) by lia.
  rewrite zeros3, zeros1.
  replace (2 * (m + 5) + 2) with ((2 * m + 11) + 1) by lia.
  eapply ptrans; [exact (b1_three_zeros (2 * m + 11) _ _) |].
  replace (2 * m + 11 + 1) with ((2 * (m + 4) + 1) + 3) by lia.
  rewrite zeros3'.
  replace (m + 5) with ((m + 4) + 1) at 1 by lia.
  set (Y := 1%sym >> 1%sym >> 0%sym >>
    ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l')))).
  eapply ptrans; [exact (a0_odd_zeros (m + 4) 0%sym (0%sym >> 0%sym >> Y) 0inf%sym) |].
  eapply ptrans; [exact (ebounce_zero (m + 4) (0%sym >> Y) 0inf%sym) |].
  eapply ep_trans; [exact (a0_cascade (m + 4) (0%sym >> 0%sym >> Y) 0inf%sym) |].
  replace (m + 4 + 1) with (5 + m) by lia.
  rewrite (blk_add 5 m).
  eapply ep_trans; [exact (pev (fixed89 _)) |].
  replace 12 with (11 + 1) by lia.
  eapply ep_trans; [exact (b1_zero_one_run m 11 5 (0%sym >> 0%sym >> Y) 0inf%sym) |].
  subst Y.
  pose proof (b1_two_zeros_one (11 + 2 * m + 1)
    (1%sym >> 0%sym >> ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l'))))
    ([1]%sym ^^ (5 + m) *> 0inf%sym)) as H.
  replace (11 + 2 * m + 1 + 2) with (2 * (m + 5) + 4) in H by lia.
  replace (5 + m) with (m + 5) in H by lia.
  replace (5 + m) with (m + 5) by lia.
  change (2 * 0 + 1) with 1.
  rewrite ones_one.
  exact H.
Qed.

Theorem R1nil (m : nat) :
  Beq (m + 5) [] -->+ Bev 0 [] (2 * (m + 5) + 4) [m + 5].
Proof.
  unfold Beq, Bev.
  rewrite encL_nil, encS_cons, encS_nil.
  rewrite default3 at 1.
  replace (2 * (m + 5) + 2) with ((2 * m + 11) + 1) by lia.
  eapply ptrans; [exact (b1_three_zeros (2 * m + 11) 0inf%sym ([1]%sym ^^ (m + 5) *> 0inf%sym)) |].
  replace (2 * m + 11 + 1) with ((2 * (m + 4) + 1) + 3) by lia.
  rewrite zeros3'.
  replace (m + 5) with ((m + 4) + 1) at 1 by lia.
  set (Y := 1%sym >> 1%sym >> 0%sym >> 0inf%sym).
  eapply ptrans; [exact (a0_odd_zeros (m + 4) 0%sym (0%sym >> 0%sym >> Y) 0inf%sym) |].
  eapply ptrans; [exact (ebounce_zero (m + 4) (0%sym >> Y) 0inf%sym) |].
  eapply ep_trans; [exact (a0_cascade (m + 4) (0%sym >> 0%sym >> Y) 0inf%sym) |].
  replace (m + 4 + 1) with (5 + m) by lia.
  rewrite (blk_add 5 m).
  eapply ep_trans; [exact (pev (fixed89 _)) |].
  replace 12 with (11 + 1) by lia.
  eapply ep_trans; [exact (b1_zero_one_run m 11 5 (0%sym >> 0%sym >> Y) 0inf%sym) |].
  subst Y.
  pose proof (b1_two_zeros_one (11 + 2 * m + 1)
    (1%sym >> 0%sym >> 0inf%sym)
    ([1]%sym ^^ (5 + m) *> 0inf%sym)) as H.
  replace (11 + 2 * m + 1 + 2) with (2 * (m + 5) + 4) in H by lia.
  replace (5 + m) with (m + 5) in H by lia.
  replace (5 + m) with (m + 5) by lia.
  change (2 * 0 + 1) with 1.
  rewrite ones_one.
  repeat rewrite z_cons_def in H.
  repeat rewrite z_cons_def.
  exact H.
Qed.

Theorem R9 (m z' w : nat) (l : list (nat * nat)) (s : list nat) :
  Amega (2 * (m + 5) + z') w l (m + 5) s -->+ Bounce m ((z', w) :: l) s.
Proof.
  unfold Amega, Bounce.
  rewrite encL_cons, encL_cons.
  replace (2 * (m + 5) + z' + 1) with ((2 * (m + 4) + 1) + (z' + 2)) by lia.
  rewrite (pow1_add 0%sym (2 * (m + 4) + 1) (z' + 2)).
  rewrite (zeros2 z'), (zeros1 z').
  replace (m + 5) with ((m + 4) + 1) by lia.
  set (Z := [0]%sym ^^ z' *>
    (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l))).
  eapply ptrans; [exact (a0_odd_zeros (m + 4) 0%sym (0%sym >> Z) (encS s)) |].
  eapply pe_trans; [exact (ebounce_zero (m + 4) Z (encS s)) |].
  exact (a0_cascade (m + 4) (0%sym >> Z) (encS s)).
Qed.

Theorem R10 (k r w : nat) (l : list (nat * nat)) (s : list nat) :
  Amega (2 * k) w l (k + 1 + r) s -->+ Bodd (k + w + 2) l (k + 1 + r + w + 6) s.
Proof.
  unfold Amega, Bodd.
  rewrite encL_cons, (ones_add (k + 1) r).
  eapply ptrans; [exact (a0_odd_zeros k 1%sym _ _) |].
  eapply ptrans; [exact (ebounce_to_B1 k _ _) |].
  rewrite <- (ones1' (2 * k + 2)).
  replace (2 * k + 2 + 1) with (2 * k + 3) by lia.
  eapply pe_trans; [exact (b1_zero_one (2 * k + 3) _ _) |].
  rewrite <- (ones_add (k + 1) r).
  rewrite <- (ones1 (k + 1 + r)).
  pose proof (b1_zero_one_run (w + 5) (2 * k + 3) (k + 1 + r + 1) (encL l) (encS s)) as H.
  replace (2 * k + 3 + 2 * (w + 5) + 1) with (2 * (k + w + 2) + 10) in H by lia.
  replace (k + 1 + r + 1 + (w + 5)) with (k + 1 + r + w + 6) in H by lia.
  exact H.
Qed.

Theorem R11 (k r w : nat) (l : list (nat * nat)) (s : list nat) :
  Amega (2 * k + 1) w l (k + 1 + r) s -->+ Bodd (w + 1) l (2 * k + w + 9) ((k + r) :: s).
Proof.
  unfold Amega, Bodd.
  rewrite encL_cons, (pow1_succ' 0%sym (2 * k + 1)), (ones_add (k + 1) r), encS_cons.
  eapply ptrans; [exact (a0_odd_zeros k 0%sym _ _) |].
  eapply ptrans; [exact (e0_to_B1 k _ _) |].
  rewrite <- (ones_add k r).
  pose proof (b1_zero_one 1
    ([0; 1; 1]%sym ^^ (w + 5) *> encL l)
    ([1]%sym ^^ (2 * k + 3) *> (0%sym >> ([1]%sym ^^ (k + r) *> encS s)))) as H1.
  rewrite ones_one in H1.
  eapply pe_trans; [exact H1 |].
  rewrite <- (ones1 (2 * k + 3)).
  pose proof (b1_zero_one_run (w + 5) 1 (2 * k + 3 + 1) (encL l)
    (0%sym >> ([1]%sym ^^ (k + r) *> encS s))) as H.
  replace (1 + 2 * (w + 5) + 1) with (2 * (w + 1) + 10) in H by lia.
  replace (2 * k + 3 + 1 + (w + 5)) with (2 * k + w + 9) in H by lia.
  exact H.
Qed.

Theorem R12 (w : nat) (l : list (nat * nat)) :
  Bounce w l [] -->+ Beq (w + 5) l.
Proof.
  unfold Bounce, Beq.
  rewrite encS_nil.
  replace (w + 5) with (5 + w) by lia.
  rewrite (blk_add 5 w).
  eapply pe_trans; [exact (fixed89 _) |].
  replace 12 with (11 + 1) by lia.
  pose proof (b1_zero_one_run w 11 5 (encL l) 0inf%sym) as H.
  replace (11 + 2 * w + 1) with (2 * (5 + w) + 2) in H by lia.
  exact H.
Qed.

Theorem R13 (w : nat) (l : list (nat * nat)) :
  Bounce w l [5] -->+ Bodd (w + 2) l (w + 11) [].
Proof.
  unfold Bounce, Bodd.
  rewrite encS_cons, encS_nil.
  assert (Hz : [1]%sym ^^ 5 *> 0inf%sym = [1]%sym ^^ (2 + 3) *> (0%sym >> 0inf%sym)).
  { cbn [Nat.add]. rewrite z_cons_def. reflexivity. }
  rewrite Hz.
  eapply ptrans; [exact (a0_zero_R 2 _ 0inf%sym) |].
  cbn [Nat.add lpow List.app Str_app].
  eapply ep_trans; [exact (pev (fixed23 _)) |].
  pose proof (b1_zero_one 1
    (1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l))
    ([1]%sym ^^ 4 *> 0inf%sym)) as H1.
  rewrite ones_one in H1.
  eapply ptrans; [exact H1 |].
  change (1 + 1) with 2.
  rewrite <- (ones1' 2), <- (ones1 4).
  change (2 + 1) with 3.
  change (4 + 1) with 5.
  eapply pe_trans; [exact (b1_zero_one 3 _ _) |].
  rewrite <- (ones1 5).
  pose proof (b1_zero_one_run (w + 5) 3 (5 + 1) (encL l) 0inf%sym) as H.
  replace (3 + 2 * (w + 5) + 1) with (2 * (w + 2) + 10) in H by lia.
  replace (5 + 1 + (w + 5)) with (w + 11) in H by lia.
  exact H.
Qed.

Theorem R14 (w b' : nat) (l : list (nat * nat)) :
  Bounce w l [b' + 15] -->+ Beq 5 ((b', w) :: l).
Proof.
  unfold Bounce, Beq.
  rewrite encS_cons, encS_nil, encL_cons.
  set (X := 1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l)).
  assert (Hz :
    [1]%sym ^^ (b' + 15) *> 0inf%sym =
    [1]%sym ^^ ((b' + 12) + 3) *> (0%sym >> 0inf%sym)).
  { replace ((b' + 12) + 3) with (b' + 15) by lia. rewrite z_cons_def. reflexivity. }
  rewrite Hz.
  eapply ptrans; [exact (a0_zero_R (b' + 12) _ 0inf%sym) |].
  replace (b' + 12 + 1) with ((b' + 10) + 3) by lia.
  rewrite zeros3.
  eapply ep_trans; [exact (pev (fixed23 _)) |].
  pose proof (m_rounds 4 0 ([0]%sym ^^ (b' + 1) *> X) 0inf%sym) as Hr.
  cbn [Nat.mul Nat.add] in Hr.
  rewrite ones_one in Hr.
  rewrite <- (pow1_add 0%sym 10 (b' + 1)) in Hr.
  replace (10 + (b' + 1)) with ((b' + 10) + 1) in Hr by lia.
  rewrite (zeros1 (b' + 10)) in Hr.
  eapply ep_trans; [exact Hr |].
  rewrite (zeros1 b').
  replace 9 with (8 + 1) by lia.
  eapply pe_trans; [exact (b1_three_zeros 8 _ _) |].
  replace (8 + 1) with (2 * 4 + 1) by lia.
  eapply etrans; [exact (a0_cascade 4 (0%sym >> ([0]%sym ^^ b' *> X)) 0inf%sym) |].
  exact (pev (fixed89 _)).
Qed.

Theorem R15 (w b1 b2 : nat) (l : list (nat * nat)) (s' : list nat) :
  Bounce w l ((b1 + 3) :: b2 :: s') -->+ Amega b1 w l b2 s'.
Proof.
  unfold Bounce, Amega.
  rewrite encS_cons, encS_cons, encL_cons.
  exact (a0_zero_R b1 _ _).
Qed.

Lemma R4_iter (d : nat) : forall (j r z w : nat) (l' : list (nat * nat)) (s : list nat),
  Bev j ((z + 2 * d, w) :: l') (j + d + r) s -->*
  Bev (j + d) ((z, w) :: l') (j + d + r) s.
Proof.
  induction d as [| d IH]; intros j r z w l' s.
  - apply evstep_refl'. f_equal; lia_refl.
  - replace (S d) with (d + 1) by lia.
    pose proof (pev (R4 j (d + r) (z + 2 * d) w l' s)) as Hstep.
    replace (z + 2 * d + 2) with (z + 2 * (d + 1)) in Hstep by lia.
    replace (j + 1 + (d + r)) with (j + (d + 1) + r) in Hstep by lia.
    eapply etrans; [exact Hstep |].
    pose proof (IH (j + 1) r z w l' s) as H2.
    replace (j + 1 + d) with (j + (d + 1)) in H2 by lia.
    exact H2.
Qed.

Lemma R4nil_iter (d : nat) : forall (j r : nat) (s : list nat),
  Bev j [] (j + d + r) s -->* Bev (j + d) [] (j + d + r) s.
Proof.
  induction d as [| d IH]; intros j r s.
  - apply evstep_refl'. f_equal; lia_refl.
  - replace (S d) with (d + 1) by lia.
    pose proof (pev (R4nil j (d + r) s)) as Hstep.
    replace (j + 1 + (d + r)) with (j + (d + 1) + r) in Hstep by lia.
    eapply etrans; [exact Hstep |].
    pose proof (IH (j + 1) r s) as H2.
    replace (j + 1 + d) with (j + (d + 1)) in H2 by lia.
    exact H2.
Qed.

Lemma bev0_nil_bounce (m' : nat) (s : list nat) :
  Bev 0 [] (m' + 4) s -->+ Bounce m' [] s.
Proof.
  pose proof (R4nil_iter (m' + 4) 0 0 s) as H1.
  replace (0 + (m' + 4) + 0) with (m' + 4) in H1 by lia.
  replace (0 + (m' + 4)) with (m' + 4) in H1 by lia.
  exact (ep_trans H1 (R5nil m' s)).
Qed.

(* ========================================================================= *)
(* Section 4: Stack-polymorphic linear excursion calculus                    *)
(* ========================================================================= *)

Definition ValidL (l : list (nat * nat)) : Prop :=
  forall p, In p l -> 27 <= snd p.

Lemma validL_nil : ValidL [].
Proof. intros p Hp. inversion Hp. Qed.

Lemma validL_cons {z w : nat} {l : list (nat * nat)}
  (Hw : 27 <= w) (Hl : ValidL l) : ValidL ((z, w) :: l).
Proof.
  intros p [Heq | Hin].
  - subst p. exact Hw.
  - exact (Hl p Hin).
Qed.

Lemma validL_head {z w : nat} {l : list (nat * nat)}
  (Hl : ValidL ((z, w) :: l)) : 27 <= w.
Proof. exact (Hl (z, w) (or_introl eq_refl)). Qed.

Lemma validL_tail {z w : nat} {l : list (nat * nat)}
  (Hl : ValidL ((z, w) :: l)) : ValidL l.
Proof. intros p Hp. exact (Hl p (or_intror Hp)). Qed.

Definition bx (j m : nat) : nat := m - (5 * m - (4 * j + 165)) / 60 - 1.
Definition bdw (j m : nat) : nat := bx j m - 5.
Definition bxw (j m : nat) : nat := m + j / 15 + 27.
Definition ox (k M : nat) : nat := M - (5 * M - (4 * k + 30)) / 60 - 2.
Definition odw (k M : nat) : nat := ox k M - 5.
Definition oxw (k M : nat) : nat := M + k / 15 + 55.

Lemma mod2 (n : nat) : (exists a, n = a * 2) \/ (exists a, n = 1 + a * 2).
Proof.
  pose proof (Nat.div_mod_eq n 2) as Hdm.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hlt.
  destruct (n mod 2) as [| r]; [left | right]; exists (n / 2); lia.
Qed.

Lemma div15_spec (n : nat) :
  exists q r : nat, r < 15 /\ n = 15 * q + r /\ n / 15 = q.
Proof.
  exists (n / 15), (n mod 15).
  pose proof (Nat.div_mod_eq n 15).
  pose proof (Nat.mod_upper_bound n 15 ltac:(lia)).
  lia.
Qed.

Lemma bx_spec (j m : nat) :
  exists bxv : nat, bx j m = bxv /\ bdw j m = bxv - 5 /\
    ((5 * m <= 4 * j + 165 /\ bxv = m - 1) \/
     (exists q r : nat, r < 60 /\ 5 * m = 4 * j + 165 + 60 * q + r /\ bxv = m - q - 1)).
Proof.
  exists (bx j m). repeat split; try reflexivity.
  unfold bx.
  destruct (le_lt_dec (5 * m) (4 * j + 165)) as [Hle | Hgt].
  - left. replace (5 * m - (4 * j + 165)) with 0 by lia. cbn. lia.
  - right. set (d := 5 * m - (4 * j + 165)).
    exists (d / 60), (d mod 60).
    pose proof (Nat.div_mod_eq d 60).
    pose proof (Nat.mod_upper_bound d 60 ltac:(lia)).
    subst d. lia.
Qed.

Lemma ox_spec (k M : nat) :
  exists oxv : nat, ox k M = oxv /\ odw k M = oxv - 5 /\
    ((5 * M <= 4 * k + 30 /\ oxv = M - 2) \/
     (exists q r : nat, r < 60 /\ 5 * M = 4 * k + 30 + 60 * q + r /\ oxv = M - q - 2)).
Proof.
  exists (ox k M). repeat split; try reflexivity.
  unfold ox.
  destruct (le_lt_dec (5 * M) (4 * k + 30)) as [Hle | Hgt].
  - left. replace (5 * M - (4 * k + 30)) with 0 by lia. cbn. lia.
  - right. set (d := 5 * M - (4 * k + 30)).
    exists (d / 60), (d mod 60).
    pose proof (Nat.div_mod_eq d 60).
    pose proof (Nat.mod_upper_bound d 60 ltac:(lia)).
    subst d. lia.
Qed.

Ltac rew_div E :=
  try rewrite E;
  repeat match goal with
  | H : _ <= _ |- _ => progress rewrite E in H
  end.

Ltac elim_one_div :=
  match goal with
  | |- context [bx ?j ?m] =>
    let v := fresh "bxv" in let E := fresh "Ebx" in
    destruct (bx_spec j m) as [v [E [_ [[? ->] | [? [? [? [? ->]]]]]]]];
    rew_div E
  | H : _ <= _ |- _ =>
    match type of H with
    | context [bx ?j ?m] =>
      let v := fresh "bxv" in let E := fresh "Ebx" in
      destruct (bx_spec j m) as [v [E [_ [[? ->] | [? [? [? [? ->]]]]]]]];
      rew_div E
    end
  | |- context [ox ?k ?M] =>
    let v := fresh "oxv" in let E := fresh "Eox" in
    destruct (ox_spec k M) as [v [E [_ [[? ->] | [? [? [? [? ->]]]]]]]];
    rew_div E
  | H : _ <= _ |- _ =>
    match type of H with
    | context [ox ?k ?M] =>
      let v := fresh "oxv" in let E := fresh "Eox" in
      destruct (ox_spec k M) as [v [E [_ [[? ->] | [? [? [? [? ->]]]]]]]];
      rew_div E
    end
  | |- context [?n / 15] =>
    let q := fresh "qd" in let r := fresh "rd" in let E := fresh "Ediv" in
    destruct (div15_spec n) as [q [r [? [? E]]]];
    rew_div E
  | H : _ <= _ |- _ =>
    match type of H with
    | context [?n / 15] =>
      let q := fresh "qd" in let r := fresh "rd" in let E := fresh "Ediv" in
      destruct (div15_spec n) as [q [r [? [? E]]]];
      rew_div E
    end
  end.

Ltac lin_omega :=
  unfold bdw, bxw, odw, oxw;
  repeat match goal with H : _ <= _ |- _ => progress unfold bdw, bxw, odw, oxw in H end;
  repeat change (0 / 15) with 0;
  repeat match goal with H : _ <= _ |- _ => progress change (0 / 15) with 0 in H end;
  repeat elim_one_div;
  lia.

Definition Exit (tx tdw txw : nat) (S : list nat) (c : config) : Prop :=
  (exists (w : nat) (l : list (nat * nat)),
    ValidL l /\ 27 <= w /\ tdw <= w /\ c = Bounce w l S) \/
  (exists (x w : nat) (l : list (nat * nat)),
    ValidL l /\ 27 <= w /\ tx <= x /\ txw <= x + w /\ c = Bounce w l (x :: S)).

Lemma exit_mono {tx1 tdw1 txw1 tx2 tdw2 txw2 : nat} {S : list nat} {c : config}
  (H : Exit tx2 tdw2 txw2 S c)
  (H1 : tx1 <= tx2) (H2 : tdw1 <= tdw2) (H3 : txw1 <= txw2) :
  Exit tx1 tdw1 txw1 S c.
Proof.
  destruct H as [[w [l [Hl [Hw [Htdw ->]]]]] | [x [w [l [Hl [Hw [Htx [Htxw ->]]]]]]]].
  - left. exists w, l. repeat split; auto; lia.
  - right. exists x, w, l. repeat split; auto; lia.
Qed.

Definition BevBound (N : nat) : Prop :=
  forall j l m S, ValidL l -> j <= m -> 35 <= m ->
    LeadsUpTo N (Bev j l m S) (Exit (bx j m) (bdw j m) (bxw j m) S).

Definition BoddBound (N : nat) : Prop :=
  forall k l M S, ValidL l -> 28 <= k -> k + 5 <= M -> 36 <= M ->
    LeadsUpTo N (Bodd k l M S) (Exit (ox k M) (odw k M) (oxw k M) S).

Definition LoopBound (N : nat) : Prop :=
  forall kc lc Mc x tx tdw txw S,
    ValidL lc -> 28 <= kc -> kc + 5 <= Mc -> 36 <= Mc ->
    34 <= tx -> tdw = tx - 5 -> tx <= x ->
    695 * tx + 27 <= 11 * (Mc + 61 * x) ->
    60 * tx <= 2 * Mc + 55 * x + 200 ->
    12 * txw + 72 <= 11 * Mc + 12 * x ->
    30 * txw <= Mc + 30 * x + 1700 ->
    LeadsUpTo N (Bodd kc lc Mc (x :: S)) (Exit tx tdw txw S).

Lemma amega_bounce_step {N : nat}
  (IH : forall m, m < N -> BevBound m /\ BoddBound m /\ LoopBound m)
  {z0 w1 x tx tdw txw : nat} {l1 : list (nat * nat)} {S : list nat}
  (Hl1 : ValidL l1) (Hw1 : 27 <= w1) (Hz0_ge3 : 3 <= z0)
  (Htx34 : 34 <= tx) (Htdw : tdw = tx - 5) (Htxx : tx <= x)
  (Hr10_tx : forall kp, z0 = 3 + kp * 2 -> kp + 1 <= x -> tx <= ox (kp + w1 + 2) (x + w1 + 6))
  (Hr10_txw : forall kp, z0 = 3 + kp * 2 -> kp + 1 <= x -> txw <= oxw (kp + w1 + 2) (x + w1 + 6))
  (Hr11_x : forall kp, z0 = 4 + kp * 2 -> kp + 1 <= x -> tx <= x - 1)
  (Hr11_i1 : forall kp, z0 = 4 + kp * 2 -> kp + 1 <= x -> 695 * tx + 27 <= 11 * ((2 * kp + w1 + 9) + 61 * (x - 1)))
  (Hr11_i2 : forall kp, z0 = 4 + kp * 2 -> kp + 1 <= x -> 60 * tx <= 2 * (2 * kp + w1 + 9) + 55 * (x - 1) + 200)
  (Hr11_i3 : forall kp, z0 = 4 + kp * 2 -> kp + 1 <= x -> 12 * txw + 72 <= 11 * (2 * kp + w1 + 9) + 12 * (x - 1))
  (Hr11_i4 : forall kp, z0 = 4 + kp * 2 -> kp + 1 <= x -> 30 * txw <= (2 * kp + w1 + 9) + 30 * (x - 1) + 1700) :
  LeadsUpTo N (Bounce w1 l1 (z0 :: x :: S)) (Exit tx tdw txw S).
Proof.
  destruct (lt_dec (z0 - 3) (2 * x)) as [Hlt | Hge].
  - destruct (mod2 (z0 - 3)) as [[kp Hkp] | [kp Hkp]].
    + assert (Hz_eq : z0 = 3 + kp * 2) by lia.
      assert (Hkpx : kp + 1 <= x) by lia.
      assert (Hstep : Bounce w1 l1 (z0 :: x :: S) -->+ Bodd (kp + w1 + 2) l1 (x + w1 + 6) S).
      { replace z0 with ((2 * kp) + 3) by lia.
        replace x with (kp + 1 + (x - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp) (kp + 1 + (x - (kp + 1))) l1 S)
          (R10 kp (x - (kp + 1)) w1 l1 S)) as H2.
        replace (kp + 1 + (x - (kp + 1)) + w1 + 6) with (x + w1 + 6) in H2 by lia.
        exact H2. }
      eapply leadsUpTo_stepPlus; [exact Hstep |].
      intros m Hm.
      destruct (IH m Hm) as [_ [Hbodd _]].
      eapply leadsUpTo_mono; [apply Hbodd; try exact Hl1; lia |].
      intros d Hd.
      pose proof (Hr10_tx kp Hz_eq Hkpx) as Htx'.
      pose proof (Hr10_txw kp Hz_eq Hkpx) as Htxw'.
      eapply exit_mono; [exact Hd | exact Htx' | unfold odw; lia | exact Htxw'].
    + assert (Hz_eq : z0 = 4 + kp * 2) by lia.
      assert (Hkpx : kp + 1 <= x) by lia.
      assert (Hstep : Bounce w1 l1 (z0 :: x :: S) -->+ Bodd (w1 + 1) l1 (2 * kp + w1 + 9) ((x - 1) :: S)).
      { replace z0 with ((2 * kp + 1) + 3) by lia.
        replace x with (kp + 1 + (x - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp + 1) (kp + 1 + (x - (kp + 1))) l1 S)
          (R11 kp (x - (kp + 1)) w1 l1 S)) as H2.
        replace (kp + (x - (kp + 1))) with (x - 1) in H2 by lia.
        exact H2. }
      eapply leadsUpTo_stepPlus; [exact Hstep |].
      intros m Hm.
      destruct (IH m Hm) as [_ [_ Hloop]].
      apply Hloop; try assumption; try lia.
      * exact (Hr11_x kp Hz_eq Hkpx).
      * exact (Hr11_i1 kp Hz_eq Hkpx).
      * exact (Hr11_i2 kp Hz_eq Hkpx).
      * exact (Hr11_i3 kp Hz_eq Hkpx).
      * exact (Hr11_i4 kp Hz_eq Hkpx).
  - assert (Hstep : Bounce w1 l1 (z0 :: x :: S) -->+ Bounce (x - 5) ((z0 - 3 - 2 * x, w1) :: l1) S).
    { pose proof (ptrans
        (R15 w1 (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) ((x - 5) + 5) l1 S)
        (R9 (x - 5) (z0 - 3 - 2 * x) w1 l1 S)) as H2.
      replace (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x) + 3) with z0 in H2 by lia.
      replace ((x - 5) + 5) with x in H2 by lia.
      exact H2. }
    eapply leadsUpTo_stepPlus; [exact Hstep |].
    intros m _.
    apply leadsUpTo_here.
    left. exists (x - 5), ((z0 - 3 - 2 * x, w1) :: l1).
    repeat split; try exact (validL_cons Hw1 Hl1); lia.
Qed.

Theorem excursion_bundle (N : nat) : BevBound N /\ BoddBound N /\ LoopBound N.
Proof.
  induction N as [N IH] using strong_induction.
  assert (H_bev : BevBound N).
  { intros j l m S Hl Hjm Hm35.
    destruct l as [| [z w] l'].
    - destruct (lt_dec j m) as [Hlt | Hge].
      + replace m with (j + 1 + (m - (j + 1))) at 1 by lia.
        eapply leadsUpTo_stepPlus; [exact (R4nil j (m - (j + 1)) S) |].
        intros n' Hn'.
        replace (j + 1 + (m - (j + 1))) with m by lia.
        destruct (IH n' Hn') as [Hbev' _].
        eapply leadsUpTo_mono; [apply Hbev'; try exact validL_nil; lia |].
        intros d Hd. eapply exit_mono; [exact Hd | lin_omega | lin_omega | lin_omega].
      + assert (Hjm_eq : j = m) by lia. subst m.
        replace j with ((j - 4) + 4) at 1 2 by lia.
        eapply leadsUpTo_stepPlus; [exact (R5nil (j - 4) S) |].
        intros m' _. apply leadsUpTo_here.
        left. exists (j - 4), (@nil (nat * nat)). repeat split; try exact validL_nil; lin_omega.
    - pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      + eapply leadsUpTo_stepPlus; [exact (R6 j m w l' S) |].
        intros n' Hm'.
        destruct (IH n' Hm') as [_ [Hbodd' _]].
        eapply leadsUpTo_mono; [apply Hbodd'; try exact Hl'; lia |].
        intros d Hd. eapply exit_mono; [exact Hd | lin_omega | lin_omega | lin_omega].
      + eapply leadsUpTo_stepPlus; [exact (R7 j m w l' S) |].
        intros n' Hn'.
        destruct (IH n' Hn') as [_ [_ Hloop']].
        apply Hloop'; try exact Hl'; lin_omega.
      + replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        destruct (lt_dec j m) as [Hlt | Hge].
        * replace m with (j + 1 + (m - (j + 1))) at 1 by lia.
          eapply leadsUpTo_stepPlus; [exact (R4 j (m - (j + 1)) z' w l' S) |].
          intros n' Hn'.
          replace (j + 1 + (m - (j + 1))) with m by lia.
          destruct (IH n' Hn') as [Hbev' _].
          eapply leadsUpTo_mono; [apply Hbev'; try exact (validL_cons Hw Hl'); lia |].
          intros d Hd. eapply exit_mono; [exact Hd | lin_omega | lin_omega | lin_omega].
        * assert (Hjm_eq : j = m) by lia. subst m.
          replace j with ((j - 4) + 4) at 1 2 by lia.
          eapply leadsUpTo_stepPlus; [exact (R5 (j - 4) z' w l' S) |].
          intros m' _. apply leadsUpTo_here.
          left. exists (j - 4), ((z', w) :: l').
          repeat split; try exact (validL_cons Hw Hl'); lin_omega. }
  assert (H_bodd : BoddBound N).
  { intros k l M S Hl Hk28 HkM HM36.
    assert (Hr8_post : forall (l'' : list (nat * nat)), ValidL l'' ->
      forall m', m' < N ->
      LeadsUpTo m' (Bev 0 l'' (2 * k + 11) ((M - 1) :: S)) (Exit (ox k M) (odw k M) (oxw k M) S)).
    { intros l'' Hl'' m' Hm'.
      destruct (IH m' Hm') as [Hbev' _].
      eapply leadsUpTo_trans; [apply Hbev'; try exact Hl''; lia |].
      intros d [[w1 [l1 [Hl1 [Hw1 [Hbdw ->]]]]] | [z0 [w1 [l1 [Hl1 [Hw1 [Hbx [Hbxw ->]]]]]]]].
      - apply leadsUpTo_here.
        right. exists (M - 1), w1, l1. repeat split; auto; lin_omega.
      - assert (Hz3 : 3 <= z0) by (clear Hbxw; lin_omega).
        assert (Hox34 : 34 <= ox k M) by (clear Hbx Hbxw; lin_omega).
        assert (HoxM : ox k M <= M - 1) by (clear Hbx Hbxw; lin_omega).
        eapply (amega_bounce_step (fun m'' Hm'' => IH m'' (Nat.lt_trans _ _ _ Hm'' Hm'))
          Hl1 Hw1 Hz3 Hox34 eq_refl HoxM); intros kp Hz Hkpx.
        + lin_omega.
        + clear Hbx; lin_omega.
        + clear Hbxw; lin_omega.
        + clear Hbx; lin_omega.
        + clear Hbx; lin_omega.
        + clear Hbx; lin_omega.
        + clear Hbx; lin_omega. }
    destruct l as [| [z w] l'].
    - replace M with (k + 5 + (M - (k + 5))) at 1 by lia.
      eapply leadsUpTo_stepPlus; [exact (R8nil k (M - (k + 5)) S) |].
      intros m' Hm'.
      replace (k + 4 + (M - (k + 5))) with (M - 1) by lia.
      exact (Hr8_post [] validL_nil m' Hm').
    - pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      + eapply leadsUpTo_stepPlus; [exact (R8a k M w l' S) |].
        intros m' Hm'.
        destruct (IH m' Hm') as [Hbev' _].
        eapply leadsUpTo_mono; [apply Hbev'; try exact Hl'; lia |].
        intros d Hd. eapply exit_mono; [exact Hd | lin_omega | lin_omega | lin_omega].
      + eapply leadsUpTo_stepPlus; [exact (R8b k M w l' S) |].
        intros m' Hm'.
        destruct (IH m' Hm') as [_ [_ Hloop']].
        apply Hloop'; try exact Hl'; lin_omega.
      + replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        replace M with (k + 5 + (M - (k + 5))) at 1 by lia.
        eapply leadsUpTo_stepPlus; [exact (R8 k (M - (k + 5)) z' w l' S) |].
        intros m' Hm'.
        replace (k + 4 + (M - (k + 5))) with (M - 1) by lia.
        exact (Hr8_post ((z', w) :: l') (validL_cons Hw Hl') m' Hm'). }
  assert (H_loop : LoopBound N).
  { intros kc lc Mc x tx tdw txw S Hlc Hkc28 HkcMc HMc36 Htx34 Htdw Htxx Hi1 Hi2 Hi3 Hi4.
    eapply leadsUpTo_trans; [exact (H_bodd kc lc Mc (x :: S) Hlc Hkc28 HkcMc HMc36) |].
    intros d [[w1 [l1 [Hl1 [Hw1 [Hodw ->]]]]] | [z0 [w1 [l1 [Hl1 [Hw1 [Hox [Hoxw ->]]]]]]]].
    - apply leadsUpTo_here.
      right. exists x, w1, l1. repeat split; auto; lin_omega.
    - assert (Hz3 : 3 <= z0) by (clear Hoxw; lin_omega).
      eapply (amega_bounce_step IH Hl1 Hw1 Hz3 Htx34 Htdw Htxx); intros kp Hz Hkpx.
      + lin_omega.
      + clear Hox; lin_omega.
      + clear Hoxw; lin_omega.
      + clear Hox; lin_omega.
      + clear Hox; lin_omega.
      + clear Hox; lin_omega.
      + clear Hox; lin_omega. }
  exact (conj H_bev (conj H_bodd H_loop)).
Qed.

Lemma bev_leads {j m : nat} {l : list (nat * nat)} {S : list nat}
  (Hl : ValidL l) (Hjm : j <= m) (Hm35 : 35 <= m) :
  leads (Bev j l m S) (Exit (bx j m) (bdw j m) (bxw j m) S).
Proof.
  intros n Hn.
  exact (proj1 (excursion_bundle n) j l m S Hl Hjm Hm35 n (Nat.le_refl n) Hn).
Qed.

Lemma bodd_leads {k M : nat} {l : list (nat * nat)} {S : list nat}
  (Hl : ValidL l) (Hk28 : 28 <= k) (HkM : k + 5 <= M) (HM36 : 36 <= M) :
  leads (Bodd k l M S) (Exit (ox k M) (odw k M) (oxw k M) S).
Proof.
  intros n Hn.
  exact (proj1 (proj2 (excursion_bundle n)) k l M S Hl Hk28 HkM HM36 n (Nat.le_refl n) Hn).
Qed.

Lemma loop_leads (tx tdw txw : nat) {kc Mc x : nat} {lc : list (nat * nat)} {S : list nat}
  (Hlc : ValidL lc) (Hkc28 : 28 <= kc) (HkcMc : kc + 5 <= Mc) (HMc36 : 36 <= Mc)
  (Htx34 : 34 <= tx) (Htdw : tdw = tx - 5) (Htxx : tx <= x)
  (Hi1 : 695 * tx + 27 <= 11 * (Mc + 61 * x))
  (Hi2 : 60 * tx <= 2 * Mc + 55 * x + 200)
  (Hi3 : 12 * txw + 72 <= 11 * Mc + 12 * x)
  (Hi4 : 30 * txw <= Mc + 30 * x + 1700) :
  leads (Bodd kc lc Mc (x :: S)) (Exit tx tdw txw S).
Proof.
  intros n Hn.
  exact (proj2 (proj2 (excursion_bundle n)) kc lc Mc x tx tdw txw S
    Hlc Hkc28 HkcMc HMc36 Htx34 Htdw Htxx Hi1 Hi2 Hi3 Hi4 n (Nat.le_refl n) Hn).
Qed.

(* ========================================================================= *)
(* Section 5: Root invariant closure (`RootInv`, `root_advances`)            *)
(* ========================================================================= *)

Definition RootInv (c : config) : Prop :=
  exists M l, (M = 5 \/ 18 <= M) /\ ValidL l /\ c = Beq M l.

Lemma root_of_5 {l : list (nat * nat)} (Hl : ValidL l) : RootInv (Beq 5 l).
Proof. exists 5, l. repeat split; auto. Qed.

Lemma root_of_ge18 {M : nat} {l : list (nat * nat)}
  (HM : 18 <= M) (Hl : ValidL l) : RootInv (Beq M l).
Proof. exists M, l. repeat split; auto. Qed.

Lemma exit_nil_leads_root {tx tdw txw : nat} (Htx : 15 <= tx) {c : config}
  (Hc : Exit tx tdw txw [] c) : leads c RootInv.
Proof.
  destruct Hc as [[w [l [Hl [Hw [_ ->]]]]] | [x [w [l [Hl [Hw [Hxx [_ ->]]]]]]]].
  - apply advances_to_leads.
    eapply advances_of_stepPlus; [exact (R12 w l) |].
    apply root_of_ge18; [lia | exact Hl].
  - replace x with ((x - 15) + 15) by lia.
    apply advances_to_leads.
    eapply advances_of_stepPlus; [exact (R14 w (x - 15) l) |].
    exact (root_of_5 (validL_cons Hw Hl)).
Qed.

Lemma bev_nil_leads_root {j m : nat} {l : list (nat * nat)}
  (Hl : ValidL l) (Hjm : j <= m) (Hm35 : 35 <= m) :
  leads (Bev j l m []) RootInv.
Proof.
  eapply leads_trans; [exact (bev_leads Hl Hjm Hm35) |].
  intros d Hd. refine (exit_nil_leads_root _ Hd); lin_omega.
Qed.

Lemma bodd_nil_leads_root {k M : nat} {l : list (nat * nat)}
  (Hl : ValidL l) (Hk28 : 28 <= k) (HkM : k + 5 <= M) (HM36 : 36 <= M) :
  leads (Bodd k l M []) RootInv.
Proof.
  eapply leads_trans; [exact (bodd_leads Hl Hk28 HkM HM36) |].
  intros d Hd. refine (exit_nil_leads_root _ Hd); lin_omega.
Qed.

Lemma exit_single_forced_r9 {tx tdw txw x : nat}
  (Hx18 : 18 <= x) (Htx_r9 : 2 * x + 3 <= tx) {c : config}
  (Hc : Exit tx tdw txw [x] c) : leads c RootInv.
Proof.
  destruct Hc as [[w [l [Hl [Hw [_ ->]]]]] | [z0 [w [l [Hl [Hw [Hz0 [_ ->]]]]]]]].
  - replace x with ((x - 15) + 15) by lia.
    apply advances_to_leads.
    eapply advances_of_stepPlus; [exact (R14 w (x - 15) l) |].
    exact (root_of_5 (validL_cons Hw Hl)).
  - pose proof (ptrans
      (ptrans (R15 w (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) ((x - 5) + 5) l [])
        (R9 (x - 5) (z0 - 3 - 2 * x) w l []))
      (R12 (x - 5) ((z0 - 3 - 2 * x, w) :: l))) as Hstep.
    replace (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x) + 3) with z0 in Hstep by lia.
    replace ((x - 5) + 5) with x in Hstep by lia.
    apply advances_to_leads.
    eapply advances_of_stepPlus; [exact Hstep |].
    exact (root_of_ge18 Hx18 (validL_cons Hw Hl)).
Qed.

Lemma exit_5_leads_root {tx tdw txw : nat} (Htx : 13 <= tx) {c : config}
  (Hc : Exit tx tdw txw [5] c) : leads c RootInv.
Proof.
  destruct Hc as [[w [l [Hl [Hw [_ ->]]]]] | [z0 [w [l [Hl [Hw [Hz0 [_ ->]]]]]]]].
  - eapply leads_of_stepPlus_leads; [exact (R13 w l) |].
    apply bodd_nil_leads_root; try exact Hl; lia.
  - replace z0 with ((2 * (0 + 5) + (z0 - 13)) + 3) by lia.
    change [((2 * (0 + 5) + (z0 - 13)) + 3); 5] with
      (((2 * (0 + 5) + (z0 - 13)) + 3) :: (0 + 5) :: []).
    pose proof (ptrans
      (ptrans (R15 w (2 * (0 + 5) + (z0 - 13)) (0 + 5) l [])
        (R9 0 (z0 - 13) w l []))
      (R12 0 ((z0 - 13, w) :: l))) as Hstep.
    apply advances_to_leads.
    eapply advances_of_stepPlus; [exact Hstep |].
    exact (root_of_5 (validL_cons Hw Hl)).
Qed.

Lemma bev0_35_20_leads_root {l : list (nat * nat)} (Hl : ValidL l) :
  leads (Bev 0 l 35 [20]) RootInv.
Proof.
  eapply leads_trans; [apply bev_leads; try exact Hl; lia |].
  intros d [[w1 [l1 [Hl1 [Hw1 [_ ->]]]]] | [z0 [w1 [l1 [Hl1 [Hw1 [Hz0 [Hzw ->]]]]]]]].
  - apply advances_to_leads.
    eapply advances_of_stepPlus; [exact (R14 w1 5 l1) |].
    exact (root_of_5 (validL_cons Hw1 Hl1)).
  - assert (Hz34 : 34 <= z0) by lin_omega.
    assert (Hzw62 : 62 <= z0 + w1) by lin_omega.
    destruct (lt_dec (z0 - 3) 40) as [Hlt | Hge].
    + destruct (mod2 (z0 - 3)) as [[kp Hkp] | [kp Hkp]].
      * replace z0 with ((2 * kp) + 3) by lia.
        replace 20 with (kp + 1 + (20 - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp) (kp + 1 + (20 - (kp + 1))) l1 [])
          (R10 kp (20 - (kp + 1)) w1 l1 [])) as Hstep.
        replace (kp + 1 + (20 - (kp + 1)) + w1 + 6) with (w1 + 26) in Hstep by lia.
        eapply leads_of_stepPlus_leads; [exact Hstep |].
        apply bodd_nil_leads_root; try exact Hl1; lia.
      * replace z0 with ((2 * kp + 1) + 3) by lia.
        replace 20 with (kp + 1 + (20 - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp + 1) (kp + 1 + (20 - (kp + 1))) l1 [])
          (R11 kp (20 - (kp + 1)) w1 l1 [])) as Hstep.
        replace (kp + (20 - (kp + 1))) with 19 in Hstep by lia.
        eapply leads_of_stepPlus_leads; [exact Hstep |].
        eapply leads_trans; [apply bodd_leads; try exact Hl1; lia |].
        intros d2 Hd2. refine (exit_single_forced_r9 _ _ Hd2); [lia | lin_omega].
    + replace z0 with ((2 * (15 + 5) + (z0 - 43)) + 3) by lia.
      change [((2 * (15 + 5) + (z0 - 43)) + 3); 20] with
        (((2 * (15 + 5) + (z0 - 43)) + 3) :: (15 + 5) :: []).
      pose proof (ptrans
        (ptrans (R15 w1 (2 * (15 + 5) + (z0 - 43)) (15 + 5) l1 [])
          (R9 15 (z0 - 43) w1 l1 []))
        (R12 15 ((z0 - 43, w1) :: l1))) as Hstep.
      apply advances_to_leads.
      eapply advances_of_stepPlus; [exact Hstep |].
      apply root_of_ge18; [lia | exact (validL_cons Hw1 Hl1)].
Qed.

Lemma bodd12_21_leads_root {l : list (nat * nat)} (Hl : ValidL l) :
  leads (Bodd 12 l 21 []) RootInv.
Proof.
  destruct l as [| [z w] l'].
  - eapply leads_of_stepPlus_leads; [exact (R8nil 12 4 []) |].
    exact (bev0_35_20_leads_root validL_nil).
  - pose proof (validL_head Hl) as Hw.
    pose proof (validL_tail Hl) as Hl'.
    destruct z as [| [| z']].
    + eapply leads_of_stepPlus_leads; [exact (R8a 12 21 w l' []) |].
      apply bev_nil_leads_root; try exact Hl'; lia.
    + eapply leads_of_stepPlus_leads; [exact (R8b 12 21 w l' []) |].
      eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
      intros d Hd. refine (exit_single_forced_r9 _ _ Hd); [lia | lin_omega].
    + replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
      eapply leads_of_stepPlus_leads; [exact (R8 12 4 z' w l' []) |].
      exact (bev0_35_20_leads_root (validL_cons Hw Hl')).
Qed.

Lemma r7_33_19_leads_root {j w : nat} {l' : list (nat * nat)}
  (Hj : j <= 33) (Hw : 27 <= w) (Hl' : ValidL l') :
  leads (Bev j ((1, w) :: l') 33 [19]) RootInv.
Proof.
  eapply leads_of_stepPlus_leads; [exact (R7 j 33 w l' [19]) |].
  eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
  intros d [[w1 [l1 [Hl1 [Hw1 [_ ->]]]]] | [z0 [w1 [l1 [Hl1 [Hw1 [Hz0 [Hzw ->]]]]]]]].
  - pose proof (ptrans (R15 w1 30 19 l1 []) (R10 15 3 w1 l1 [])) as Hstep.
    eapply leads_of_stepPlus_leads; [exact Hstep |].
    apply bodd_nil_leads_root; try exact Hl1; lia.
  - assert (Hz34 : 34 <= z0) by lin_omega.
    assert (Hzw92 : 92 <= z0 + w1) by lin_omega.
    destruct (lt_dec (z0 - 3) 66) as [Hlt | Hge].
    + destruct (mod2 (z0 - 3)) as [[kp Hkp] | [kp Hkp]].
      * replace z0 with ((2 * kp) + 3) by lia.
        replace 33 with (kp + 1 + (33 - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp) (kp + 1 + (33 - (kp + 1))) l1 [19])
          (R10 kp (33 - (kp + 1)) w1 l1 [19])) as Hstep.
        replace (kp + 1 + (33 - (kp + 1)) + w1 + 6) with (w1 + 39) in Hstep by lia.
        eapply leads_of_stepPlus_leads; [exact Hstep |].
        eapply leads_trans; [apply bodd_leads; try exact Hl1; lia |].
        intros d2 Hd2. refine (exit_single_forced_r9 _ _ Hd2); [lia | lin_omega].
      * replace z0 with ((2 * kp + 1) + 3) by lia.
        replace 33 with (kp + 1 + (33 - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp + 1) (kp + 1 + (33 - (kp + 1))) l1 [19])
          (R11 kp (33 - (kp + 1)) w1 l1 [19])) as Hstep.
        replace (kp + (33 - (kp + 1))) with 32 in Hstep by lia.
        eapply leads_of_stepPlus_leads; [exact Hstep |].
        eapply leads_trans; [apply bodd_leads; try exact Hl1; lia |].
        intros d2 [[w2 [l2 [Hl2 [Hw2 [Hodw2 ->]]]]] | [z2 [w2 [l2 [Hl2 [Hw2 [Hz2 [_ ->]]]]]]]].
        -- assert (Hw85 : 85 <= w2) by lin_omega.
           pose proof (ptrans (R15 w2 29 19 l2 []) (R11 14 4 w2 l2 [])) as Hs2.
           eapply leads_of_stepPlus_leads; [exact Hs2 |].
           eapply leads_trans; [apply bodd_leads; try exact Hl2; lia |].
           intros d3 Hd3. refine (exit_single_forced_r9 _ _ Hd3); [lia | lin_omega].
        -- assert (Hz90 : 90 <= z2) by lin_omega.
           replace z2 with ((2 * (27 + 5) + (z2 - 67)) + 3) by lia.
           change [((2 * (27 + 5) + (z2 - 67)) + 3); 32; 19] with
             (((2 * (27 + 5) + (z2 - 67)) + 3) :: (27 + 5) :: [19]).
           pose proof (ptrans
             (ptrans (R15 w2 (2 * (27 + 5) + (z2 - 67)) (27 + 5) l2 [19])
               (R9 27 (z2 - 67) w2 l2 [19]))
             (R14 27 4 ((z2 - 67, w2) :: l2))) as Hs2.
           apply advances_to_leads.
           eapply advances_of_stepPlus; [exact Hs2 |].
           apply root_of_5. apply validL_cons; [lia | exact (validL_cons Hw2 Hl2)].
    + replace z0 with ((2 * (28 + 5) + (z0 - 69)) + 3) by lia.
      change [((2 * (28 + 5) + (z0 - 69)) + 3); 33; 19] with
        (((2 * (28 + 5) + (z0 - 69)) + 3) :: (28 + 5) :: [19]).
      pose proof (ptrans
        (ptrans (R15 w1 (2 * (28 + 5) + (z0 - 69)) (28 + 5) l1 [19])
          (R9 28 (z0 - 69) w1 l1 [19]))
        (R14 28 4 ((z0 - 69, w1) :: l1))) as Hstep.
      apply advances_to_leads.
      eapply advances_of_stepPlus; [exact Hstep |].
      apply root_of_5. apply validL_cons; [lia | exact (validL_cons Hw1 Hl1)].
Qed.

Lemma bev_33_19_walk (rem : nat) : forall (j : nat) (l : list (nat * nat)),
  rem = 33 - j -> j <= 33 -> ValidL l -> leads (Bev j l 33 [19]) RootInv.
Proof.
  induction rem as [| rem IH]; intros j l Hrem Hj Hl.
  - assert (Hj33 : j = 33) by lia. subst j.
    destruct l as [| [z w] l'].
    + apply advances_to_leads.
      eapply advances_of_stepPlus; [exact (ptrans (R5nil 29 [19]) (R14 29 4 [])) |].
      apply root_of_5. apply validL_cons; [lia | exact validL_nil].
    + pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      * eapply leads_of_stepPlus_leads; [exact (R6 33 33 w l' [19]) |].
        eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
        intros d Hd. refine (exit_single_forced_r9 _ _ Hd); [lia | lin_omega].
      * exact (r7_33_19_leads_root Hj Hw Hl').
      * replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        apply advances_to_leads.
        eapply advances_of_stepPlus;
          [exact (ptrans (R5 29 z' w l' [19]) (R14 29 4 ((z', w) :: l'))) |].
        apply root_of_5. apply validL_cons; [lia | exact (validL_cons Hw Hl')].
  - destruct l as [| [z w] l'].
    + replace 33 with (j + 1 + (32 - j)) at 1 by lia.
      eapply leads_of_stepPlus_leads; [exact (R4nil j (32 - j) [19]) |].
      replace (j + 1 + (32 - j)) with 33 by lia.
      apply IH; [lia | lia | exact validL_nil].
    + pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      * eapply leads_of_stepPlus_leads; [exact (R6 j 33 w l' [19]) |].
        eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
        intros d Hd. refine (exit_single_forced_r9 _ _ Hd); [lia | lin_omega].
      * exact (r7_33_19_leads_root Hj Hw Hl').
      * replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        replace 33 with (j + 1 + (32 - j)) at 1 by lia.
        eapply leads_of_stepPlus_leads; [exact (R4 j (32 - j) z' w l' [19]) |].
        replace (j + 1 + (32 - j)) with 33 by lia.
        apply IH; [lia | lia | exact (validL_cons Hw Hl')].
Qed.

Lemma bodd11_20_leads_root {l : list (nat * nat)} (Hl : ValidL l) :
  leads (Bodd 11 l 20 []) RootInv.
Proof.
  destruct l as [| [z w] l'].
  - eapply leads_of_stepPlus_leads; [exact (R8nil 11 4 []) |].
    apply (bev_33_19_walk 33 0 []); [reflexivity | lia | exact validL_nil].
  - pose proof (validL_head Hl) as Hw.
    pose proof (validL_tail Hl) as Hl'.
    destruct z as [| [| z']].
    + eapply leads_of_stepPlus_leads; [exact (R8a 11 20 w l' []) |].
      apply bev_nil_leads_root; try exact Hl'; lia.
    + eapply leads_of_stepPlus_leads; [exact (R8b 11 20 w l' []) |].
      eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
      intros d Hd. refine (exit_single_forced_r9 _ _ Hd); [lia | lin_omega].
    + replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
      eapply leads_of_stepPlus_leads; [exact (R8 11 4 z' w l' []) |].
      apply (bev_33_19_walk 33 0 ((z', w) :: l')); [reflexivity | lia | exact (validL_cons Hw Hl')].
Qed.

Lemma r7_14_5_leads_root {j w : nat} {l' : list (nat * nat)}
  (Hj : j <= 14) (Hw : 27 <= w) (Hl' : ValidL l') :
  leads (Bev j ((1, w) :: l') 14 [5]) RootInv.
Proof.
  eapply leads_of_stepPlus_leads; [exact (R7 j 14 w l' [5]) |].
  eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
  intros d [[w1 [l1 [Hl1 [Hw1 [_ ->]]]]] | [z0 [w1 [l1 [Hl1 [Hw1 [Hz0 [_ ->]]]]]]]].
  - pose proof (ptrans (ptrans (R15 w1 11 5 l1 []) (R9 0 1 w1 l1 []))
      (R12 0 ((1, w1) :: l1))) as Hstep.
    apply advances_to_leads.
    eapply advances_of_stepPlus; [exact Hstep |].
    exact (root_of_5 (validL_cons Hw1 Hl1)).
  - assert (Hz34 : 34 <= z0) by lin_omega.
    replace z0 with ((2 * (9 + 5) + (z0 - 31)) + 3) by lia.
    change [((2 * (9 + 5) + (z0 - 31)) + 3); 14; 5] with
      (((2 * (9 + 5) + (z0 - 31)) + 3) :: (9 + 5) :: [5]).
    pose proof (ptrans
      (ptrans (R15 w1 (2 * (9 + 5) + (z0 - 31)) (9 + 5) l1 [5])
        (R9 9 (z0 - 31) w1 l1 [5]))
      (R13 9 ((z0 - 31, w1) :: l1))) as Hstep.
    eapply leads_of_stepPlus_leads; [exact Hstep |].
    exact (bodd11_20_leads_root (validL_cons Hw1 Hl1)).
Qed.

Lemma bev_14_5_walk (rem : nat) : forall (j : nat) (l : list (nat * nat)),
  rem = 14 - j -> j <= 14 -> ValidL l -> leads (Bev j l 14 [5]) RootInv.
Proof.
  induction rem as [| rem IH]; intros j l Hrem Hj Hl.
  - assert (Hj14 : j = 14) by lia. subst j.
    destruct l as [| [z w] l'].
    + eapply leads_of_stepPlus_leads;
        [exact (ptrans (R5nil 10 [5]) (R13 10 [])) |].
      exact (bodd12_21_leads_root validL_nil).
    + pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      * eapply leads_of_stepPlus_leads; [exact (R6 14 14 w l' [5]) |].
        eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
        intros d Hd. refine (exit_5_leads_root _ Hd); lin_omega.
      * exact (r7_14_5_leads_root Hj Hw Hl').
      * replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        eapply leads_of_stepPlus_leads;
          [exact (ptrans (R5 10 z' w l' [5]) (R13 10 ((z', w) :: l'))) |].
        exact (bodd12_21_leads_root (validL_cons Hw Hl')).
  - destruct l as [| [z w] l'].
    + replace 14 with (j + 1 + (13 - j)) at 1 by lia.
      eapply leads_of_stepPlus_leads; [exact (R4nil j (13 - j) [5]) |].
      replace (j + 1 + (13 - j)) with 14 by lia.
      apply IH; [lia | lia | exact validL_nil].
    + pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      * eapply leads_of_stepPlus_leads; [exact (R6 j 14 w l' [5]) |].
        eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
        intros d Hd. refine (exit_5_leads_root _ Hd); lin_omega.
      * exact (r7_14_5_leads_root Hj Hw Hl').
      * replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        replace 14 with (j + 1 + (13 - j)) at 1 by lia.
        eapply leads_of_stepPlus_leads; [exact (R4 j (13 - j) z' w l' [5]) |].
        replace (j + 1 + (13 - j)) with 14 by lia.
        apply IH; [lia | lia | exact (validL_cons Hw Hl')].
Qed.

Lemma bev0_ge18_leads_root {M : nat} {l : list (nat * nat)}
  (HM18 : 18 <= M) (Hl : ValidL l) :
  leads (Bev 0 l (2 * M + 4) [M]) RootInv.
Proof.
  eapply leads_trans; [apply bev_leads; try exact Hl; lia |].
  intros d [[w1 [l1 [Hl1 [Hw1 [_ ->]]]]] | [z0 [w1 [l1 [Hl1 [Hw1 [Hz0 [Hzw ->]]]]]]]].
  - replace M with ((M - 15) + 15) by lia.
    apply advances_to_leads.
    eapply advances_of_stepPlus; [exact (R14 w1 (M - 15) l1) |].
    exact (root_of_5 (validL_cons Hw1 Hl1)).
  - assert (Hz34 : 34 <= z0) by lin_omega.
    destruct (lt_dec (z0 - 3) (2 * M)) as [Hlt | Hge].
    + destruct (mod2 (z0 - 3)) as [[kp Hkp] | [kp Hkp]].
      * replace z0 with ((2 * kp) + 3) by lia.
        replace M with (kp + 1 + (M - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp) (kp + 1 + (M - (kp + 1))) l1 [])
          (R10 kp (M - (kp + 1)) w1 l1 [])) as Hstep.
        replace (kp + 1 + (M - (kp + 1)) + w1 + 6) with (M + w1 + 6) in Hstep by lia.
        eapply leads_of_stepPlus_leads; [exact Hstep |].
        apply bodd_nil_leads_root; try exact Hl1; lia.
      * assert (HM21 : 21 <= M) by lin_omega.
        replace z0 with ((2 * kp + 1) + 3) by lia.
        replace M with (kp + 1 + (M - (kp + 1))) at 1 by lia.
        pose proof (ptrans (R15 w1 (2 * kp + 1) (kp + 1 + (M - (kp + 1))) l1 [])
          (R11 kp (M - (kp + 1)) w1 l1 [])) as Hstep.
        replace (kp + (M - (kp + 1))) with (M - 1) in Hstep by lia.
        eapply leads_of_stepPlus_leads; [exact Hstep |].
        destruct (lt_dec M 35) as [Hsmall | Hbig].
        -- eapply leads_trans; [apply bodd_leads; try exact Hl1; lia |].
           intros d2 Hd2. refine (exit_single_forced_r9 _ _ Hd2); [lia | lin_omega].
        -- eapply leads_trans;
             [apply (loop_leads 34 29 63);
               try exact Hl1; lin_omega |].
           intros d2 Hd2. refine (exit_nil_leads_root _ Hd2); lia.
    + pose proof (ptrans
        (ptrans (R15 w1 (2 * ((M - 5) + 5) + (z0 - 3 - 2 * M)) ((M - 5) + 5) l1 [])
          (R9 (M - 5) (z0 - 3 - 2 * M) w1 l1 []))
        (R12 (M - 5) ((z0 - 3 - 2 * M, w1) :: l1))) as Hstep.
      replace (2 * ((M - 5) + 5) + (z0 - 3 - 2 * M) + 3) with z0 in Hstep by lia.
      replace ((M - 5) + 5) with M in Hstep by lia.
      apply advances_to_leads.
      eapply advances_of_stepPlus; [exact Hstep |].
      exact (root_of_ge18 HM18 (validL_cons Hw1 Hl1)).
Qed.

Theorem root_advances : forall c, RootInv c -> advances c RootInv.
Proof.
  intros c [M [l [[-> | HM18] [Hl ->]]]].
  - destruct l as [| [z w] l'].
    + assert (Hstep : Beq 5 [] -->+ Beq 5 [(5, 31)]).
      { eapply ptrans; [exact (R1nil 0) |].
        eapply ptrans; [exact (bev0_nil_bounce 10 [5]) |].
        eapply ptrans; [exact (R13 10 []) |].
        eapply ptrans; [exact (R8nil 12 4 []) |].
        eapply ptrans; [exact (bev0_nil_bounce 31 [20]) |].
        exact (R14 31 5 []). }
      eapply advances_of_stepPlus; [exact Hstep |].
      apply root_of_5. apply validL_cons; [lia | exact validL_nil].
    + pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      * eapply advances_of_stepPlus_leads; [exact (R2 5 w l') |].
        apply bev_nil_leads_root; try exact Hl'; lia.
      * eapply advances_of_stepPlus_leads; [exact (R3 5 w l') |].
        eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
        intros d Hd. refine (exit_5_leads_root _ Hd); lin_omega.
      * replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        eapply advances_of_stepPlus_leads; [exact (R1 0 z' w l') |].
        apply (bev_14_5_walk 14 0 ((z', w) :: l')); [reflexivity | lia | exact (validL_cons Hw Hl')].
  - destruct l as [| [z w] l'].
    + replace M with ((M - 5) + 5) by lia.
      eapply advances_of_stepPlus_leads; [exact (R1nil (M - 5)) |].
      replace ((M - 5) + 5) with M by lia.
      exact (bev0_ge18_leads_root HM18 validL_nil).
    + pose proof (validL_head Hl) as Hw.
      pose proof (validL_tail Hl) as Hl'.
      destruct z as [| [| z']].
      * eapply advances_of_stepPlus_leads; [exact (R2 M w l') |].
        apply bev_nil_leads_root; try exact Hl'; lia.
      * eapply advances_of_stepPlus_leads; [exact (R3 M w l') |].
        destruct (lt_dec M 35) as [Hsmall | Hbig].
        -- eapply leads_trans; [apply bodd_leads; try exact Hl'; lia |].
           intros d Hd. refine (exit_single_forced_r9 _ _ Hd); [exact HM18 | lin_omega].
        -- eapply leads_trans;
             [apply (loop_leads 34 29 63);
               try exact Hl'; lia |].
           intros d Hd. refine (exit_nil_leads_root _ Hd); lia.
      * replace (Datatypes.S (Datatypes.S z')) with (z' + 2) by lia.
        replace M with ((M - 5) + 5) by lia.
        eapply advances_of_stepPlus_leads; [exact (R1 (M - 5) z' w l') |].
        replace ((M - 5) + 5) with M by lia.
        exact (bev0_ge18_leads_root HM18 (validL_cons Hw Hl')).
Qed.

(* ========================================================================= *)
(* Section 6: Blank-tape entry & top-level `nonhalt`                         *)
(* ========================================================================= *)

Lemma fixed64 (Lrem : side) :
  K qA ([0; 1; 1]%sym ^^ 4 *> Lrem) 0%sym 0inf%sym -->+
  K qB ([1]%sym ^^ 10 *> Lrem) 1%sym ([1]%sym ^^ 4 *> 0inf%sym).
Proof. run_prog. Qed.

Lemma bev3_nil_to_bodd0 :
  Bev 3 [] 3 [4] -->+ Bodd 0 [] 9 [].
Proof.
  unfold Bev, Bodd.
  rewrite encL_nil.
  rewrite default3 at 1.
  eapply ptrans; [exact (b1_three_zeros 6 0inf%sym ([1]%sym ^^ 3 *> encS [4])) |].
  eapply ep_trans; [exact (a0_cascade 3 (0%sym >> 0inf%sym) (encS [4])) |].
  repeat rewrite z_cons_def.
  rewrite encS_cons, encS_nil.
  run_prog.
Qed.

Lemma bounce7_to_beq0 :
  Bounce 7 [] [8] -->+ Beq 0 [(5, 7)].
Proof.
  unfold Bounce, Beq.
  rewrite encL_nil, encL_cons, encL_nil, encS_cons, encS_nil.
  run_prog.
Qed.

Lemma beq0_to_bev0 :
  Beq 0 [(5, 7)] -->+ Bev 0 [(3, 7)] 4 [].
Proof.
  unfold Beq, Bev.
  rewrite encL_cons, encL_cons, encL_nil, encS_nil.
  run_prog.
Qed.

Lemma amega_to_bev0 (z w : nat) (l : list (nat * nat)) :
  Amega z w l 4 [] -->+ Bev 0 ((z, w) :: l) 3 [].
Proof.
  unfold Amega, Bev.
  rewrite encS_nil.
  exact (a0_step (encL ((z, w) :: l)) ([1]%sym ^^ 3 *> 0inf%sym)).
Qed.

Lemma bev3_to_beq4 (z w : nat) (l' : list (nat * nat)) :
  Bev 3 ((z + 2, w) :: l') 3 [] -->+ Beq 4 ((z, w) :: l').
Proof.
  unfold Bev, Beq.
  rewrite encL_cons, encL_cons, encS_nil.
  replace (z + 2 + 1) with (z + 3) by lia.
  rewrite zeros3, zeros1.
  eapply ptrans; [exact (b1_three_zeros 6 _ _) |].
  eapply ep_trans; [exact (a0_cascade 3 _ 0inf%sym) |].
  exact (fixed64 _).
Qed.

Lemma beq4_to_bev0 (z w : nat) (l' : list (nat * nat)) :
  Beq 4 ((z + 2, w) :: l') -->+ Bev 0 ((z, w) :: l') 12 [4].
Proof.
  unfold Beq, Bev.
  rewrite encL_cons, encL_cons, encS_cons, encS_nil.
  replace (z + 2 + 1) with (z + 3) by lia.
  rewrite zeros3, zeros1.
  change (2 * 4 + 2) with (9 + 1).
  eapply ptrans; [exact (b1_three_zeros 9 _ _) |].
  change (9 + 1) with ((2 * 3 + 1) + 3).
  rewrite zeros3'.
  replace ([1]%sym ^^ 4 *> 0inf%sym) with ([1]%sym ^^ (3 + 1) *> 0inf%sym) at 1 by reflexivity.
  set (Y := 1%sym >> 1%sym >> 0%sym >>
    ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l')))).
  eapply ptrans; [exact (a0_odd_zeros 3 0%sym (0%sym >> 0%sym >> Y) 0inf%sym) |].
  eapply ptrans; [exact (ebounce_zero 3 (0%sym >> Y) 0inf%sym) |].
  eapply ep_trans; [exact (a0_cascade 3 (0%sym >> 0%sym >> Y) 0inf%sym) |].
  eapply ep_trans; [exact (pev (fixed64 _)) |].
  subst Y.
  pose proof (b1_two_zeros_one 10
    (1%sym >> 0%sym >> ([0]%sym ^^ z *> (1%sym >> 1%sym >> 0%sym >> 1%sym >> ([0; 1; 1]%sym ^^ (w + 5) *> encL l'))))
    ([1]%sym ^^ 4 *> 0inf%sym)) as H.
  change (2 * 0 + 1) with 1.
  rewrite ones_one.
  exact H.
Qed.

Lemma bounce8_to_beq0 (l : list (nat * nat)) :
  Bounce 8 l [4] -->+ Beq 0 ((1, 8) :: l).
Proof.
  unfold Bounce, Beq.
  rewrite encL_cons, encS_cons, encS_nil.
  run_prog.
Qed.

Lemma bodd_s0_eq_nil (k : nat) (l : list (nat * nat)) (m : nat) :
  Bodd k l m [0] = Bodd k l m [].
Proof.
  unfold Bodd.
  rewrite encS_cons, encS_nil.
  cbn [lpow Str_app].
  rewrite z_cons_def.
  reflexivity.
Qed.

Theorem entry_part1 : c0 -->+ Bodd 8 [] 18 [4].
Proof.
  assert (H50 : c0 -->+ Bev 0 [] 3 [4]).
  { unfold c0, tape0, q0, s0, Bev, encL, encS. run_prog. }
  eapply ptrans; [exact H50 |].
  eapply ep_trans; [exact (R4nil_iter 3 0 0 [4]) |].
  eapply ptrans; [exact bev3_nil_to_bodd0 |].
  eapply ptrans; [exact (R8nil 0 4 []) |].
  eapply ptrans; [exact (bev0_nil_bounce 7 [8]) |].
  eapply ptrans; [exact bounce7_to_beq0 |].
  eapply ptrans; [exact beq0_to_bev0 |].
  eapply ptrans; [exact (R4 0 3 1 7 [] []) |].
  exact (R7 1 4 7 [] []).
Qed.

Theorem entry_part2 : Bodd 8 [] 18 [4] -->+ Bodd 27 [] 42 [4].
Proof.
  eapply ptrans; [exact (R8nil 8 5 [4]) |].
  eapply ptrans; [exact (bev0_nil_bounce 23 [17; 4]) |].
  eapply ptrans; [exact (R15 23 14 4 [] []) |].
  eapply ptrans; [exact (amega_to_bev0 14 23 []) |].
  eapply ep_trans; [exact (R4_iter 3 0 0 8 23 [] []) |].
  eapply ptrans; [exact (bev3_to_beq4 6 23 []) |].
  eapply ptrans; [exact (beq4_to_bev0 4 23 []) |].
  eapply ep_trans; [exact (R4_iter 2 0 10 0 23 [] [4]) |].
  exact (R6 2 12 23 [] [4]).
Qed.

Theorem entry_part3 : Bodd 27 [] 42 [4] -->+ Bodd 9 [(2, 61)] 18 [].
Proof.
  eapply ptrans; [exact (R8nil 27 10 [4]) |].
  eapply ptrans; [exact (bev0_nil_bounce 61 [41; 4]) |].
  eapply ptrans; [exact (R15 61 38 4 [] []) |].
  eapply ptrans; [exact (amega_to_bev0 38 61 []) |].
  eapply ep_trans; [exact (R4_iter 3 0 0 32 61 [] []) |].
  eapply ptrans; [exact (bev3_to_beq4 30 61 []) |].
  eapply ptrans; [exact (beq4_to_bev0 28 61 []) |].
  eapply ep_trans; [exact (R4_iter 12 0 0 4 61 [] [4]) |].
  eapply ptrans; [exact (R5 8 2 61 [] [4]) |].
  eapply ptrans; [exact (bounce8_to_beq0 [(2, 61)]) |].
  rewrite <- (bodd_s0_eq_nil 9 [(2, 61)] 18).
  exact (R3 0 8 [(2, 61)]).
Qed.

Theorem entry_part4 : Bodd 9 [(2, 61)] 18 [] -->+ Beq 5 [(2, 33); (118, 275)].
Proof.
  eapply ptrans; [exact (R8 9 4 0 61 [] []) |].
  eapply ptrans; [exact (R6 0 29 61 [] [17]) |].
  eapply ptrans; [exact (R8nil 63 29 [17]) |].
  eapply ptrans; [exact (bev0_nil_bounce 133 [96; 17]) |].
  eapply ptrans; [exact (R15 133 93 17 [] []) |].
  eapply ptrans; [exact (R9 12 59 133 [] []) |].
  eapply ptrans; [exact (R12 12 [(59, 133)]) |].
  eapply ptrans; [exact (R1 12 57 133 []) |].
  eapply ep_trans; [exact (R4_iter 28 0 10 1 133 [] [17]) |].
  eapply ptrans; [exact (R7 28 38 133 [] [17]) |].
  eapply ptrans; [exact (R8nil 134 59 [38; 17]) |].
  eapply ptrans; [exact (bev0_nil_bounce 275 [197; 38; 17]) |].
  eapply ptrans; [exact (R15 275 194 38 [] [17]) |].
  eapply ptrans; [exact (R9 33 118 275 [] [17]) |].
  exact (R14 33 2 [(118, 275)]).
Qed.

Theorem entry : c0 -->+ Beq 5 [(2, 33); (118, 275)].
Proof.
  exact (ptrans entry_part1 (ptrans entry_part2 (ptrans entry_part3 entry_part4))).
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact (pev entry).
  - eapply (decreasing_halt_budget RootInv root_advances).
    apply root_of_5.
    apply validL_cons; [lia |].
    apply validL_cons; [lia | exact validL_nil].
Qed.
