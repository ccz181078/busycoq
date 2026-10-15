(** * 1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA never halts

    Machine: 1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA.  Its table is the table of
    1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF (tmP below, a bouncer whose right part
    is a four-particle system with a closed double-cycle law) with its states
    renamed by sigma = A->E, B->C, C->D, D->F, E->A, F->B (no mirror).  It starts in
    sigma(E) = A, so its run is tmP's run from E;; tape0 with every state renamed.
    The informal proof is the accompanying write-up (1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA_writeup.md): its section 1 is the
    relation, section 2 the opening and section 3 the domain of the double cycle;
    the macro rules and the double cycle are those of tmP's own write-up.

    Adapted from the proof for tmP, which follows verify/TranslatedBellv5.v, Module TM1:
    block macro rules proved by ES_v3's es', iterated by induction and chained with
    follow, ending with progress_nonhalt_simple as in verify/Bouncer_v2.v, Module TM1.
    The direct opening runs busycoq's list configurations (cconfig_step) with nested
    step counters as in verify/Bouncer_v3.v's multistep_c', cut into ten pieces.
    The renaming bridge (Perm tm tmP phi, perm_halts) is busycoq's Permute.v, as used
    in verify/Skelet15.v.
    The lemmas on tmP are stated on half-length parameters:
      Kr n a b c d = K(2n+1, 2a, 2b, 2c+1, 2d),     Ev N X = Even(2N+1, 8X+52).
    es' proves each macro rule for its whole domain by symbolic execution.

    Formalized with Claude Code (AI-assisted).
    Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
    Print Assumptions nonhalt: Closed under the global context.
*)

From BusyCoq Require Import Individual62.

Require Import ZArith Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import ES_v3.

Definition tm := Eval compute in (TM_from_str "1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA").

(** tmP: the parent table.  All configurations below are tmP's, in its coordinates. *)
Definition tmP := Eval compute in (TM_from_str "1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF").

Notation "c -->* c'" := (c -[ tmP ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tmP ]->+ c') (at level 40).

(** G: the fixed 43-cell gadget at the left end.
    Kr n a b c d = K(2n+1, 2a, 2b, 2c+1, 2d): F reads the 0 just left of G. *)
Definition G : list sym :=
  [0;0;1;1;0;1;1;1;1;0;1;1;0;1;1;1;1;1;1;0;1;1;0;1;1;1;1;1;0;0;1;1;0;1;1;1;1;1;0;1;1;0;0].

Definition Kr n a b c d :=
  0inf <{{F}} G *> [1] *> [1;1]^^n *> [0] *> [1;1]^^a *> [0;1;1;0] *> [1;1]^^b
    *> [0;0;0;0;0;0] *> [1] *> [1;1]^^c *> [0;1;1;0;1;1;1;1;0;0;0;0;0;0] *> [1;1]^^d
    *> [0;1;1;0;0;1;1;0;1;1;1] *> 0inf.

Ltac ES_v3.es_v3_pre ::= unfold Kr, G.

(** ** Macro rules (write-up 3.3, 3.4)

    S (12 trips):  K(n,a,b,c,d) -> K(n+48, a-8, b+4, c, d+4),
    n odd, a even >= 10, b even >= 6, c odd >= 7, d even >= 2. *)
Lemma S_step n a b c d:
  Kr n (5+a) (3+b) (3+c) (1+d) -->+ Kr (24+n) (1+a) (5+b) (3+c) (3+d).
Proof.
  es' n a b c d.
Qed.

(** TE (138 trips):  K(n,4,b,35,d) -> K(n+556, b-86, 82, d+51, 18),  b even >= 88, d even >= 20. *)
Lemma TE n b d:
  Kr n 2 (44+b) 17 (10+d) -->+ Kr (278+n) (1+b) 41 (35+d) 9.
Proof.
  es' n b d.
Qed.

(** TO (147 trips):  K(n,2,b,c,d) -> K(n+588, b+c-91, d+62, 35, 18),  b even >= 82, c odd >= 37, d even >= 18. *)
Lemma TO n b c d:
  Kr n 1 (41+b) (18+c) (9+d) -->+ Kr (294+n) (14+b+c) (40+d) 17 9.
Proof.
  es' n b c d.
Qed.

(** T6 (147 trips):  K(n,6,b,c,d) -> K(n+592, b+c-91, d+62, 35, 18),  b even >= 82, c odd >= 35, d even >= 18. *)
Lemma T6 n b c d:
  Kr n 3 (41+b) (17+c) (9+d) -->+ Kr (296+n) (13+b+c) (40+d) 17 9.
Proof.
  es' n b c d.
Qed.

(** T8 (135 trips):  K(n,8,b,35,d) -> K(n+540, b-74, 86, d+47, 18),  b even >= 88, d even >= 20. *)
Lemma T8 n b d:
  Kr n 4 (44+b) 17 (10+d) -->+ Kr (270+n) (7+b) 43 (33+d) 9.
Proof.
  es' n b d.
Qed.

Lemma S_step' n a b c d:
  Kr n (5+a) (3+b) (3+c) (1+d) -->* Kr (24+n) (1+a) (5+b) (3+c) (3+d).
Proof. apply progress_evstep, S_step. Qed.

Lemma TE' n b d:
  Kr n 2 (44+b) 17 (10+d) -->* Kr (278+n) (1+b) 41 (35+d) 9.
Proof. apply progress_evstep, TE. Qed.

Lemma TO' n b c d:
  Kr n 1 (41+b) (18+c) (9+d) -->* Kr (294+n) (14+b+c) (40+d) 17 9.
Proof. apply progress_evstep, TO. Qed.

Lemma T6' n b c d:
  Kr n 3 (41+b) (17+c) (9+d) -->* Kr (296+n) (13+b+c) (40+d) 17 9.
Proof. apply progress_evstep, T6. Qed.

Lemma T8' n b d:
  Kr n 4 (44+b) 17 (10+d) -->* Kr (270+n) (7+b) 43 (33+d) 9.
Proof. apply progress_evstep, T8. Qed.

(** S applied k times. *)
Lemma S_iter k: forall n a b c d,
  Kr n (4*k+1+a) (3+b) (3+c) (1+d) -->* Kr (24*k+n) (1+a) (2*k+3+b) (3+c) (2*k+1+d).
Proof.
  induction k; intros.
  - finish.
  - follow (S_step' n (4*k+a) b c d).
    follow (IHk (24+n) a (2+b) c (2+d)).
    finish.
Qed.

(** ** The double cycle (write-up 4)

    Ev N X = Even(2N+1, 8X+52), where Even(n,x) = K(n, x, (x+76)/2, 35, 18).
    DC: Even(n,x) -> Even(n+12x+808, x+32) by S^((x-4)/8), TE, S^((x-52)/8), TO. *)
Definition Ev N X := Kr N (4*X+26) (2*X+32) 17 9.

Lemma prog_eq c1 c2 c1' c2':
  c1 -->+ c2 -> c1 = c1' -> c2 = c2' -> c1' -->+ c2'.
Proof. intros H E1 E2. subst. exact H. Qed.

Lemma DC N X:
  Ev N X -->+ Ev (48*X+716+N) (4+X).
Proof.
  unfold Ev.
  follow (S_iter (X+6) N 1 (2*X+29) 14 8).
  follow (TE' (24*(X+6)+N) (4*X) (2*X+11)).
  follow (S_iter X (278+(24*(X+6)+N)) 0 38 (2*X+43) 8).
  eapply prog_eq.
  1: apply (TO (24*X+(278+(24*(X+6)+N))) (2*X) (2*X+28) (2*X)).
  all: lia_refl.
Qed.

(** ** Opening (write-up 2)

    tmP from E;; tape0: 6,950,830 steps to K(2583,70,76,43,18) = Kr 1291 35 38 21 9,
    then 18 macro steps to Even(13299,220) = Ev 6649 21 (its own chain, write-up 2.2).

    The direct run is cut at nine left records (where the tape is short in run-length
    form), so that no single computation is too large for the kernel.  cc_steps runs
    busycoq's list configurations (cconfig_step); cc_steps' nests two counters as
    multistep_c' does in verify/Bouncer_v3.v. *)
Fixpoint cc_steps (n:nat) (x:cconfig) : option cconfig :=
match n with
| O => Some x
| S n0 =>
  match cconfig_step tmP x with
  | Some x0 => cc_steps n0 x0
  | None => None
  end
end.

Lemma cc_steps_spec n x y:
  cc_steps n x = Some y -> cconfig_to_config x -->* cconfig_to_config y.
Proof.
  gen x.
  induction n; cbn[cc_steps]; intros x H.
  - inverts H. apply evstep_refl.
  - pose proof (cconfig_step_spec tmP x) as HE.
    destruct (cconfig_step tmP x) as [x0|]. 2: congruence.
    eapply evstep_step; eauto.
Qed.

Fixpoint cc_steps' (n1 n2 n3:nat) (x:cconfig) : option cconfig :=
match n1 with
| O => cc_steps n3 x
| S n1 =>
  match cc_steps n2 x with
  | Some x0 => cc_steps' n1 n2 n3 x0
  | None => None
  end
end.

Lemma cc_steps'_spec n1 n2 n3 x y:
  cc_steps' n1 n2 n3 x = Some y -> cconfig_to_config x -->* cconfig_to_config y.
Proof.
  gen x.
  induction n1; cbn[cc_steps']; intros x H.
  - exact (cc_steps_spec _ _ _ H).
  - destruct (cc_steps n2 x) as [x0|] eqn:E. 2: congruence.
    eapply evstep_trans.
    + exact (cc_steps_spec _ _ _ E).
    + apply IHn1, H.
Qed.

(** Run-length words: rl [(z1,o1); (z2,o2); ...] = 0^z1 1^o1 0^z2 1^o2 ... *)
Fixpoint rl (xs : list (nat*nat)) : list sym :=
match xs with
| [] => []
| (z,o)::t => [0]^^z ++ [1]^^o ++ rl t
end.

(** Left records: F reads the leftmost visited cell (a 0), and the word right of it. *)
Definition LR (xs : list (nat*nat)) : Q * tape := cconfig_to_config ([], rl xs, 0, F).

Definition Kr_list n a b c d : list sym :=
  G ++ [1] ++ [1;1]^^n ++ [0] ++ [1;1]^^a ++ [0;1;1;0] ++ [1;1]^^b
    ++ [0;0;0;0;0;0] ++ [1] ++ [1;1]^^c ++ [0;1;1;0;1;1;1;1;0;0;0;0;0;0] ++ [1;1]^^d
    ++ [0;1;1;0;0;1;1;0;1;1;1].

Lemma Kr_cc n a b c d:
  Kr n a b c d = cconfig_to_config ([], Kr_list n a b c d, 0, F).
Proof.
  unfold Kr, Kr_list, cconfig_to_config.
  cbn [Str_app]. rewrite !Str_app_assoc. reflexivity.
Qed.

(** Left record at step 694,787. *)
Definition W1 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,750);(1,2);(2,18);(2,34);(2,6);(1,2);(1,18);(1,2);(1,20)])%nat.

(** Left record at step 1,378,765. *)
Definition W2 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1094);(3,50);(2,4);(1,49);(1,20)])%nat.

(** Left record at step 2,077,151. *)
Definition W3 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1362);(1,2);(2,4);(2,4);(6,71);(1,2);(1,54);(2,20);(1,2);(1,4);(1,2);(3,4);(1,2)])%nat.

(** Left record at step 2,768,045. *)
Definition W4 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1586);(3,48);(2,4);(1,103);(1,29);(1,2);(1,7)])%nat.

(** Left record at step 3,469,055. *)
Definition W5 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1787);(2,14);(2,126);(2,58);(1,2);(1,4);(1,2);(1,4);(6,4);(11,4);(1,2)])%nat.

(** Left record at step 4,155,515. *)
Definition W6 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,1971);(2,170);(2,4);(6,19);(1,6);(1,2);(2,2);(2,8);(1,2)])%nat.

(** Left record at step 4,854,845. *)
Definition W7 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,2139);(2,142);(2,44);(2,26);(1,2);(1,7)])%nat.

(** Left record at step 5,552,637. *)
Definition W8 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,2295);(1,118);(1,2);(1,52);(6,43);(1,2);(1,4);(6,4);(11,4);(1,2)])%nat.

(** Left record at step 6,254,851. *)
Definition W9 : list (nat*nat) :=
  ([(2,2);(5,2);(6,4);(6,4);(1,2);(1,4);(1,2);(2,2442);(3,92);(6,62);(2,2);(2,46);(3,2);(2,2);(2,10);(1,2);(1,6);(2,2);(2,4);(1,2)])%nat.

Lemma init1:
  E;; tape0 -->* LR W1.
Proof.
  change (E;; tape0) with (cconfig_to_config ([], [], 0, E)).
  unfold LR.
  apply (cc_steps'_spec 694 1000 787).
  vm_compute.
  reflexivity.
Qed.

Lemma init2:
  LR W1 -->* LR W2.
Proof.
  unfold LR.
  apply (cc_steps'_spec 683 1000 978).
  vm_compute.
  reflexivity.
Qed.

Lemma init3:
  LR W2 -->* LR W3.
Proof.
  unfold LR.
  apply (cc_steps'_spec 698 1000 386).
  vm_compute.
  reflexivity.
Qed.

Lemma init4:
  LR W3 -->* LR W4.
Proof.
  unfold LR.
  apply (cc_steps'_spec 690 1000 894).
  vm_compute.
  reflexivity.
Qed.

Lemma init5:
  LR W4 -->* LR W5.
Proof.
  unfold LR.
  apply (cc_steps'_spec 701 1000 10).
  vm_compute.
  reflexivity.
Qed.

Lemma init6:
  LR W5 -->* LR W6.
Proof.
  unfold LR.
  apply (cc_steps'_spec 686 1000 460).
  vm_compute.
  reflexivity.
Qed.

Lemma init7:
  LR W6 -->* LR W7.
Proof.
  unfold LR.
  apply (cc_steps'_spec 699 1000 330).
  vm_compute.
  reflexivity.
Qed.

Lemma init8:
  LR W7 -->* LR W8.
Proof.
  unfold LR.
  apply (cc_steps'_spec 697 1000 792).
  vm_compute.
  reflexivity.
Qed.

Lemma init9:
  LR W8 -->* LR W9.
Proof.
  unfold LR.
  apply (cc_steps'_spec 702 1000 214).
  vm_compute.
  reflexivity.
Qed.

Lemma init10:
  LR W9 -->* Kr 1291 35 38 21 9.
Proof.
  unfold LR.
  rewrite Kr_cc.
  apply (cc_steps'_spec 695 1000 979).
  vm_compute.
  reflexivity.
Qed.

Lemma init:
  E;; tape0 -->* Kr 1291 35 38 21 9.
Proof.
  follow init1.
  follow init2.
  follow init3.
  follow init4.
  follow init5.
  follow init6.
  follow init7.
  follow init8.
  follow init9.
  apply init10.
Qed.

Lemma opening:
  Kr 1291 35 38 21 9 -->* Ev 6649 21.
Proof.
  unfold Ev.
  follow (S_iter 8 1291 2 35 18 8).
  follow (T6' 1483 13 4 16).
  follow (S_iter 7 1779 1 53 14 8).
  follow (TE' 1947 26 13).
  follow (S_iter 6 2225 2 38 45 8).
  follow (T6' 2369 12 31 12).
  follow (S_iter 13 2665 3 49 14 8).
  follow (T8' 2977 34 25).
  follow (S_iter 10 3247 0 40 55 8).
  follow (TO' 3487 22 40 20).
  follow (S_iter 18 3781 3 57 14 8).
  follow (T8' 4213 52 35).
  follow (S_iter 14 4483 2 40 65 8).
  follow (T6' 4819 30 51 28).
  follow (S_iter 23 5115 1 65 14 8).
  follow (TE' 5667 70 45).
  follow (S_iter 17 5945 2 38 77 8).
  follow (T6' 6353 34 63 34).
  finish.
Qed.

Lemma nonhaltP: ~halts tmP (E;; tape0).
Proof.
  eapply multistep_nonhalt.
  1: { follow init. apply opening. }
  apply (progress_nonhalt_simple tmP (nat*nat) (fun p => Ev (fst p) (snd p)) (6649,21)).
  intros [N X].
  exists (48*X+716+N, 4+X).
  apply DC.
Qed.

(** ** The relation (write-up 1)

    phi = sigma^-1 maps this machine's states to tmP's.  Every cell (q, s) of tm is
    tmP's cell (phi q, s) with every target state t replaced by phi t (same symbol,
    same move), so tm and tmP are equal up to renaming, and phi A = E. *)
Definition phi (q : Q) : Q :=
  match q with
  | A => E | B => F | C => B | D => C | E => A | F => D
  end.

Lemma perm: Perm tm tmP phi.
Proof.
  split.
  - intros [] [] H; cbn in *; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in *; inversion H; subst; reflexivity.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  intros H.
  change (halts tm (A;; tape0)) in H.
  exact (nonhaltP (perm_halts _ _ _ _ _ perm H)).
Qed.

(*
1RB0RD_0RC0LB_0RD1RD_1LE1RA_1RC1LF_---1LA        (only F0 undefined; F is entered only by E1 = 1LF)
  = tmP 1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF with its states renamed (no mirror)
    sigma = A->E, B->C, C->D, D->F, E->A, F->B (phi = sigma^-1); start A = sigma(E)

relation  c --tmP--> c'  iff  sigma c --tm--> sigma c'      (same tape and head, state q -> sigma q)
          sigma (E;; tape0) = c0, so tm's run is sigma of tmP's run from E;; tape0

below, configurations are tmP's (left records); tm sees the same tapes with state sigma q (K: B instead of F)

G            = 0^2 1^2 0 1^4 0 1^2 0 1^6 0 1^2 0 1^5 0^2 1^2 0 1^5 0 1^2 0^2          (43 cells)
K(n,a,b,c,d) = 0^inf <F G 1^n 0 1^a 0110 1^b 0^6 1^c 0110 1111 0^6 1^d 0110 0110 111 0^inf
sigma K      = 0^inf <B G 1^n 0 1^a 0110 1^b 0^6 1^c 0110 1111 0^6 1^d 0110 0110 111 0^inf
Even(n,x)    = K(n, x, (x+76)/2, 35, 18)
Kr n a b c d = K(2n+1, 2a, 2b, 2c+1, 2d)          Ev N X = Even(2N+1, 8X+52)

tmP's rules (tmP's coordinates):
R1   C> 1 1         --> 1 0 C>             2 steps    C1 E1
R2b  0 1 0 B> 0 0 0 --> 0 B> 0 0 0 1 1     12 steps   B0 C0 A0 B1 C0 A1 D1 E0 F1 F1 F1 F0
     k-fold:  C> 1^(2k) --> (10)^k C>   (2k steps);   0 (10)^k B> 000 --> 0 B> 000 1^(2k)   (12k steps)

rule  from            to                            domain                                          steps                          trips
S     K(n,a,b,c,d) -> K(n+48,a-8,b+4,c,d+4)         n odd, a even >= 10, b even >= 6, c odd >= 7, d even >= 2   84n+84a+77b+70c+63d+13628   12
TE    K(n,4,b,35,d) -> K(n+556,b-86,82,d+51,18)     n odd, b even >= 88, d even >= 20                         966n+952b+812d+455332        138
TO    K(n,2,b,c,d) -> K(n+588,b+c-91,d+62,35,18)    n odd, b even >= 82, c odd >= 37, d even >= 18            1029n+1001b+987c+882d+458476 147
T6    K(n,6,b,c,d) -> K(n+592,b+c-91,d+62,35,18)    n odd, b even >= 82, c odd >= 35, d even >= 18            1029n+1008b+987c+882d+462814 147
T8    K(n,8,b,35,d) -> K(n+540,b-74,86,d+47,18)     n odd, b even >= 88, d even >= 20                         945n+938b+784d+446893        135

DC    Even(n,x) --S^((x-4)/8)--> K(.,4,x+36,35,(x+32)/2) --TE--> K(.,x-50,82,(x+134)/2,18)
                --S^((x-52)/8)--> K(.,2,(x+112)/2,(x+134)/2,(x-16)/2) --TO--> Even(n+12x+808, x+32)
      n odd, x = 4 mod 8, x >= 52; 3x+201 trips
      (Rocq: Ev N X -->+ Ev (48X+716+N) (X+4))

start E;; tape0 -(6,950,830)-> K(2583,70,76,43,18) --(S^8 T6 S^7 TE S^6 T6 S^13 T8 S^10 TO S^18 T8 S^14 T6 S^23 TE S^17 T6)-->
      Even(13299,220) at step 163,638,058;  then DC forever (x = 220, 252, 284, ...)
      (the same for tm from c0, through sigma)
*)
