(* 1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF does not halt from the blank tape.

   The tape at the right end of a sweep ([A] marks the head in state A, on the cell to its right):
     0^inf ... 1^b2 0^z2 1^b1 0^z1 1^(2K) [A] 0^inf
   A token is a block with the zeros to its right, (b, z). A word is a list of tokens, nearest the head first. How a token acts depends only on the parity of its block and its zeros; sizes only go into later sizes and K:
     tZ (even, 3), tO (odd, 2), tA (odd, 3), tB (even, 2), tC (even, 1), tD (odd, 1).

   One macro step ([mstep], proved for all words by [step_ok]) sends one carry into the word:
     tZ becomes tO and tA becomes tB (the carry bounces); tO becomes tZ and the carry goes on to the next token;
     tB stops the carry, becomes tZ, and the next token y becomes tA tB (y = tZ), tA tD (tO), tA tO (tA), tA tC (tB), tA (tC), tZ (tD), see [ins];
     [inn] is undefined at tC and tD: on the machine, a carry reaching one of them is the halt.
   So tZ, tO are the bits 0, 1 of a binary counter, low bit first, with stoppers among them.

   [super] goes from one anchor (blocks 30 and 14, K = 4j - 12, then a word w) to the next. In between the only changes to w are the carries, one change of size in its low token if j is odd, and at the end one new head:
     j even: N j = 3j carries, next j = 3j/2 + 1. j odd: N j = 6j + 2 carries, next j = (3j + 3)/2. New head: tZ x :: y :: r -> tZ (x + 3) :: ins y r.
   The low blocks and K are exact functions of j. Of the sequence of j the proof only uses the parity at each step and these bounds on its growth.

   A head moves left through the bits. Leaving out the bits it has passed: tA tB, tB tB, tA tC, tB tC, tA, tB, and then with the next token y: a bit 0 starts over at tA tB, a bit 1 gives tA tD, tB tD and the head is gone.
   One round adds 3 tokens on its right and takes 1 on its left, so carries to it get 8 times rarer each round. A head that came next to an older head in state tA tC or tA tD could lead to a halt.

   The invariant [Inv]: w = T ++ P, nothing in P is ever read, and
     [Good]: T is bits and heads; a head with n tokens before it and g bits after it has K + phase <= n + 3g, where 8j <= 2^K (this K belongs to [Inv] and is not the K of the tape; heads tA tD, tB tD have no bound). A round keeps n + 3g - phase. A super-era adds a token before all old heads and the next j is at most 2j, so K can grow by 1 ([inv_S]). When a carry reaches tB tC with no bit after it, the tA it leaves is too far out to get another carry, and it goes to P with all that lies beyond it ([arrive], [inv_arr]).
     [V]: a value of T with V T + 2M + 48j <= 2^(|T|+1), M the carries left in this super-era. A carry adds at most 2 to it, scaled to the new length of T. So no carry leaves T, and this survives a super-era.
     [psi]: a measure of the k bits before the first head that grows by at least 1 per carry and is below 4 * 2^k. So at the end of a super-era 4 * 2^k > N j, and the new head has k - 2 bits after it ([inv_S]).
   From the blank tape the machine is run for 861 macro steps, to j = 46 ([run0], [inv0]).

   The macro cycle, the block rewrite laws, the binary counter with carries, the heads, the super-eras with blocks 30 and 14, the recurrence for their R0 = 8j + 4 (the block next to the head 14 macro steps before an anchor) and the collision to avoid come from the analysis of this machine by garrincha, https://github.com/juaansanchiis/bb6-holdouts-research (01-tm-1965-ctl-proof). The law for every word with its count of carries, the invariant and this proof are new here. *)
From BusyCoq Require Import Individual62.
From Coq Require Import Lia PeanoNat String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* 1^(2n), (01)^n and (10)^n. *)
Fixpoint oo (n : nat) : list Sym :=
  match n with
  | O => []
  | S n' => S1 :: S1 :: oo n'
  end.

Fixpoint pr (n : nat) : list Sym :=
  match n with
  | O => []
  | S n' => S0 :: S1 :: pr n'
  end.

Fixpoint tn (n : nat) : list Sym :=
  match n with
  | O => []
  | S n' => S1 :: S0 :: tn n'
  end.

Lemma oo_shift : forall n (s : side), oo n *> S1 >> s = S1 >> oo n *> s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma pr_tn : forall n (s : side), pr n *> S0 >> s = S0 >> tn n *> s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma pr_S : forall n (s : side), pr n *> S0 >> S1 >> s = S0 >> S1 >> pr n *> s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma pr_add : forall a b (s : side), pr a *> pr b *> s = pr (a + b) *> s.
Proof.
  induction a as [|a IH]; intros b s; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

(* The leftward sweep: 4 steps per two cells. *)
Lemma sweep : forall m l r, oo m *> l <{{C}} r -->* l <{{C}} pr m *> r.
Proof.
  induction m as [|m IH]; intros l r.
  - finish.
  - simpl. do 4 step.
    follow IH.
    rewrite pr_S. finish.
Qed.

(* The rightward run through (10)^k. *)
Lemma aloop : forall k l r, l {{A}}> tn k *> r -->* oo k *> l {{A}}> r.
Proof.
  induction k as [|k IH]; intros l r.
  - finish.
  - simpl. do 2 step.
    follow IH.
    rewrite !oo_shift. finish.
Qed.

Lemma ruleA : forall k L z,
  L {{A}}> pr (S (S k)) *> S0 >> z -->* oo k *> S0 >> S0 >> S0 >> S1 >> S1 >> L {{A}}> z.
Proof.
  intros k L z. simpl. do 4 step.
  rewrite pr_tn. step.
  follow aloop. finish.
Qed.

Lemma ruleB : forall k L z,
  L {{A}}> S0 >> S1 >> S0 >> pr k *> S0 >> z -->* oo k *> S0 >> S0 >> S1 >> S1 >> L {{A}}> z.
Proof.
  intros k L z. do 3 step.
  rewrite pr_tn. step.
  follow aloop. finish.
Qed.

(* Tokens: a block of ones and the zeros to its right, by parity of the block and number of zeros. *)
Inductive tok : Type :=
  | tZ (n : nat)   (* 2n+2 ones, 3 zeros *)
  | tO (n : nat)   (* 2n+3 ones, 2 zeros *)
  | tA (n : nat)   (* 2n+3 ones, 3 zeros *)
  | tB (n : nat)   (* 2n+2 ones, 2 zeros *)
  | tC (n : nat)   (* 2n+2 ones, 1 zero *)
  | tD (n : nat).  (* 2n+3 ones, 1 zero *)

(* The left side of the tape, read away from the head. Lists of tokens start at the head. *)
Fixpoint el (w : list tok) : side :=
  match w with
  | [] => const S0
  | tZ n :: r => S0 >> S0 >> S0 >> S1 >> S1 >> oo n *> el r
  | tO n :: r => S0 >> S0 >> S1 >> S1 >> S1 >> oo n *> el r
  | tA n :: r => S0 >> S0 >> S0 >> S1 >> S1 >> S1 >> oo n *> el r
  | tB n :: r => S0 >> S0 >> S1 >> S1 >> oo n *> el r
  | tC n :: r => S0 >> S1 >> S1 >> oo n *> el r
  | tD n :: r => S0 >> S1 >> S1 >> S1 >> oo n *> el r
  end.

(* A macro configuration: 1^(2K) to the left of the head, in state A, and blanks to the right. *)
Definition enc (w : list tok) (K : nat) : Q * tape :=
  oo K *> el w {{A}}> const S0.

Definition ins (y : tok) (r : list tok) : list tok :=
  match y with
  | tZ n => tA 0 :: tB n :: r
  | tO n => tA 0 :: tD n :: r
  | tA n => tA 0 :: tO n :: r
  | tB n => tA 0 :: tC n :: r
  | tC n => tA (S n) :: r
  | tD n => tZ (S (S n)) :: r
  end.

Inductive res : Type :=
  | Bnc (l : list tok)
  | Stp (l : list tok) (q : nat).

(* One carry arriving from the right at the token at the head of w. *)
Fixpoint inn (w : list tok) : option res :=
  match w with
  | [] => Some (Bnc [tO 0])
  | tZ n :: r => Some (Bnc (tO (S n) :: r))
  | tA n :: r => Some (Bnc (tB (S (S n)) :: r))
  | tB e :: [] => Some (Stp [tA 0] e)
  | tB e :: y :: r => Some (Stp (ins y r) e)
  | tO c :: r =>
    match inn r with
    | Some (Bnc l) => Some (Stp l (S (S c)))
    | Some (Stp l q) => Some (Stp (tZ q :: l) c)
    | None => None
    end
  | _ => None
  end.

Definition mstep (w : list tok) (K : nat) : option (list tok * nat) :=
  match inn w with
  | None => None
  | Some (Bnc l) => Some (l, K)
  | Some (Stp l q) =>
    match K with
    | O => Some (l, q)
    | S O => Some (tB q :: l, O)
    | S (S K') => Some (tZ q :: l, K')
    end
  end.

Definition X (m : nat) (w : list tok) (r : side) : Q * tape :=
  oo m *> S1 >> el w <{{C}} r.

Lemma cross3 : forall m L r,
  oo m *> S1 >> S0 >> S0 >> S0 >> L <{{C}} r -->+ S1 >> L {{A}}> S0 >> S1 >> S0 >> pr m *> r.
Proof.
  intros m L r.
  eapply evstep_progress_trans; [apply sweep|].
  eapply progress_intro; [prove_step|simpl_tape].
  execute.
Qed.

Lemma cross2 : forall m L r,
  oo m *> S1 >> S0 >> S0 >> L <{{C}} r -->+ L <{{C}} S0 >> S1 >> S0 >> pr m *> r.
Proof.
  intros m L r.
  eapply evstep_progress_trans; [apply sweep|].
  eapply progress_intro; [prove_step|simpl_tape].
  do 2 step. finish.
Qed.

Lemma stop_even : forall e y r m rho,
  oo m *> S1 >> S0 >> S0 >> S1 >> S1 >> oo e *> el (y :: r) <{{C}} rho -->+
  oo e *> el (ins y r) {{A}}> pr m *> rho.
Proof.
  intros e y r m rho.
  eapply progress_evstep_trans; [apply cross2|].
  change (S1 >> S1 >> oo e *> el (y :: r)) with (oo (S e) *> el (y :: r)).
  follow sweep.
  rewrite pr_S.
  destruct y as [n|n|n|n|n|n]; simpl el; step; simpl ins;
    (eapply evstep_trans; [apply (ruleA e)|]); finish.
Qed.


Lemma cross_blank : forall m r,
  oo m *> S1 >> const S0 <{{C}} r -->+ S1 >> const S0 {{A}}> S0 >> S1 >> S0 >> pr m *> r.
Proof.
  intros m r. pose proof (cross3 m (const S0) r) as H.
  rewrite <- !const_unfold in H. exact H.
Qed.

Lemma stop_blank : forall e m rho,
  oo m *> S1 >> S0 >> S0 >> S1 >> S1 >> oo e *> const S0 <{{C}} rho -->+
  oo e *> S0 >> S0 >> S0 >> S1 >> S1 >> S1 >> const S0 {{A}}> pr m *> rho.
Proof.
  intros e m rho.
  eapply progress_evstep_trans; [apply cross2|].
  change (S1 >> S1 >> oo e *> const S0) with (oo (S e) *> const S0).
  follow sweep.
  rewrite pr_S.
  step.
  eapply evstep_trans; [apply (ruleA e)|]. finish.
Qed.

Lemma inn_ok : forall w,
  (forall l, inn w = Some (Bnc l) -> forall m k z, X m w (pr k *> S0 >> z) -->+ oo (m + k) *> el l {{A}}> z) /\
  (forall l q, inn w = Some (Stp l q) -> forall m r, X m w r -->+ oo q *> el l {{A}}> pr m *> r).
Proof.
  induction w as [|t w [IHb IHs]].
  - split.
    + intros l H. injection H as <-. intros m k z. unfold X. simpl el.
      eapply progress_evstep_trans; [apply cross_blank|].
      rewrite pr_add.
      eapply evstep_trans; [apply ruleB|]. finish.
    + intros l q H. discriminate.
  - destruct t as [n|c|n|e|n|n]; simpl inn; split; intros l.
    + intros H. injection H as <-. intros m k z. unfold X. simpl el.
      eapply progress_evstep_trans; [apply cross3|].
      rewrite pr_add.
      eapply evstep_trans; [apply ruleB|]. finish.
    + intros q H. discriminate.
    + intros H m k z. destruct (inn w) as [[l1|l1 q1]|]; discriminate.
    + intros q H m r. unfold X. simpl el.
      eapply progress_trans; [apply cross2|].
      assert (E : S1 >> S1 >> S1 >> oo c *> el w = oo (S c) *> S1 >> el w).
      { simpl. rewrite oo_shift. reflexivity. }
      rewrite E. clear E.
      destruct (inn w) as [[l1|l1 q1]|]; [| |discriminate]; injection H as <- <-.
      * pose proof (IHb l1 eq_refl (S c) 1%nat (pr m *> r)) as H. unfold X in H.
        replace (S c + 1) with (S (S c)) in H by lia.
        exact H.
      * eapply progress_evstep_trans; [apply (IHs l1 q1 eq_refl (S c))|].
        change (pr (S c) *> S0 >> S1 >> S0 >> pr m *> r) with (S0 >> S1 >> pr c *> S0 >> S1 >> S0 >> pr m *> r).
        rewrite pr_S.
        change (S0 >> S1 >> S0 >> S1 >> pr c *> S0 >> pr m *> r) with (pr (S (S c)) *> S0 >> pr m *> r).
        eapply evstep_trans; [apply ruleA|]. finish.
    + intros H. injection H as <-. intros m k z. unfold X. simpl el.
      eapply progress_evstep_trans; [apply cross3|].
      rewrite pr_add.
      eapply evstep_trans; [apply ruleB|]. finish.
    + intros q H. discriminate.
    + destruct w; discriminate.
    + intros q H m r. unfold X. simpl el.
      destruct w as [|y w'].
      * injection H as <- <-. apply stop_blank.
      * injection H as <- <-. apply stop_even.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
Qed.

Lemma enc_X : forall w K, enc w K -->+ X K w (const S0).
Proof.
  intros w K. unfold enc, X.
  eapply progress_intro; [prove_step|simpl_tape].
  rewrite oo_shift.
  step. finish.
Qed.

(* One macro step is at least one machine step. The rest of the file does not look at the tape. *)
Theorem step_ok : forall w K w' K', mstep w K = Some (w', K') -> enc w K -->+ enc w' K'.
Proof.
  intros w K w' K' H. unfold mstep in H.
  destruct (inn_ok w) as [Hb Hs].
  eapply progress_trans; [apply enc_X|].
  destruct (inn w) as [[l|l q]|]; [| |discriminate].
  - injection H as <- <-.
    pose proof (Hb l eq_refl K 0%nat (const S0)) as H1.
    rewrite Nat.add_0_r in H1.
    change (pr 0 *> S0 >> const S0) with (S0 >> const S0) in H1.
    rewrite <- const_unfold in H1. exact H1.
  - pose proof (Hs l q eq_refl K (const S0)) as H1.
    eapply progress_evstep_trans; [exact H1|].
    destruct K as [|[|K2]]; injection H as <- <-.
    + finish.
    + unfold enc. simpl. execute.
    + pose proof (ruleA K2 (oo q *> el l) (const S0)) as HA.
      rewrite <- const_unfold in HA. exact HA.
Qed.

(* From here on the proof only works with lists of tokens. [arr] is the carry alone, without K. *)

Definition arr (w : list tok) : option (list tok) :=
  match inn w with
  | None => None
  | Some (Bnc l) => Some l
  | Some (Stp l q) => Some (tZ q :: l)
  end.

Fixpoint gapl (T : list tok) : nat :=
  match T with
  | tZ _ :: r => S (gapl r)
  | tO _ :: r => S (gapl r)
  | _ => 0
  end.

(* Bits and heads; a head has a first token tA or tB and one more token, or tA or tB alone before a bit.
   Heads are tA tB, tB tB (phase 0), tA tC, tB tC (phase 1), tA, tB (phase 2), tA tD, tB tD (they end soon, no bound).
   Position n: tokens before it. Bound: K + phase <= n + 3 g, g bits after the head. *)
Fixpoint Good (K n : nat) (T : list tok) {struct T} : Prop :=
  match T with
  | [] => True
  | tZ _ :: r => Good K (S n) r
  | tO _ :: r => Good K (S n) r
  | tC _ :: _ => False
  | tD _ :: _ => False
  | _ :: [] => False
  | _ :: tA _ :: _ => False
  | _ :: tB _ :: r => K <= n + 3 * gapl r /\ Good K (S (S n)) r
  | _ :: tC _ :: r => S K <= n + 3 * gapl r /\ Good K (S (S n)) r
  | _ :: tD _ :: r => Good K (S (S n)) r
  | _ :: tZ x :: r => S (S K) <= n + 3 * S (gapl r) /\ Good K (S (S n)) r
  | _ :: tO x :: r => S (S K) <= n + 3 * S (gapl r) /\ Good K (S (S n)) r
  end.

(* The value of T, low token first. *)
Definition dg (t : tok) : nat :=
  match t with
  | tZ _ => 0
  | tO _ => 2
  | tA _ => 1
  | tB _ => 1
  | tC _ => 0
  | tD _ => 0
  end.

Fixpoint V (T : list tok) : nat :=
  match T with
  | [] => 0
  | t :: r => dg t + 2 * V r
  end.

(* The bits before the first head, plus 2 or 3 times 2^k. *)
Fixpoint psi (T : list tok) : nat :=
  match T with
  | tZ _ :: r => 2 * psi r
  | tO _ :: r => 1 + 2 * psi r
  | tA _ :: _ => 2
  | _ => 3
  end.

Lemma Good_mono : forall T K n K' n', Good K n T -> K' + n <= K + n' -> Good K' n' T.
Proof.
  fix IH 1.
  intros T K n K' n' H Hle.
  destruct T as [|t r]; [exact I|].
  destruct t as [x|x|x|x|x|x]; simpl in *.
  - apply (IH r K (S n)); [exact H|lia].
  - apply (IH r K (S n)); [exact H|lia].
  - destruct r as [|y r']; [exact H|].
    destruct y as [z|z|z|z|z|z]; simpl in *; try exact H;
      try (destruct H as [H1 H2]; split; [lia|apply (IH r' K (S (S n))); [exact H2|lia]]);
      apply (IH r' K (S (S n))); [exact H|lia].
  - destruct r as [|y r']; [exact H|].
    destruct y as [z|z|z|z|z|z]; simpl in *; try exact H;
      try (destruct H as [H1 H2]; split; [lia|apply (IH r' K (S (S n))); [exact H2|lia]]);
      apply (IH r' K (S (S n))); [exact H|lia].
  - exact H.
  - exact H.
Qed.

Lemma psi_pos : forall T, 1 <= psi T.
Proof.
  induction T as [|t r IH]; [simpl; lia|].
  destruct t; simpl; lia.
Qed.

Lemma psi_lt : forall T, psi T + 1 <= 4 * 2 ^ gapl T.
Proof.
  induction T as [|t r IH]; [simpl; lia|].
  destruct t; simpl; try lia.
Qed.


Definition low (T : list tok) : nat :=
  match T with
  | tZ _ :: _ => 0
  | tO _ :: _ => 1
  | _ => 2
  end.

(* What one arrival does to the part T of the word; P1 is what leaves T when a head freezes. *)
Definition Stepd (K n : nat) (T T1 P1 : list tok) : Prop :=
  psi T + 1 <= psi T1 /\ Good K n T1 /\
  ( (P1 = [] /\ exists d, length T1 = length T + d /\ V T1 <= (V T + 2) * 2 ^ d)
    \/ (V T1 = 0 /\ K + 2 <= n + length T1) ).

Lemma arr_tO : forall c w l, arr w = Some l -> exists c', arr (tO c :: w) = Some (tZ c' :: l).
Proof.
  intros c w l H. unfold arr in *. simpl.
  destruct (inn w) as [[l1|l1 q1]|]; [| |discriminate]; injection H as <-; eexists; reflexivity.
Qed.

Local Ltac low_tac := split; simpl; intros; try discriminate; reflexivity.
Local Ltac keep_tac d := left; split; [reflexivity | exists d; simpl; split; lia].

(* The hardest lemma: one arrival keeps Good, and bounds V and psi. *)
Lemma arrive : forall T P K n, Good K n T -> V T + 2 < 2 ^ S (length T) ->
  exists T1 P1, arr (T ++ P) = Some (T1 ++ P1 ++ P) /\ Stepd K n T T1 P1 /\
    (low T = 0 -> low T1 = 1) /\ (low T = 1 -> low T1 = 0).
Proof.
  induction T as [|t T' IH]; intros P K n HG HV.
  - simpl in HV. lia.
  - destruct t as [x|x|x|x|x|x].
    + (* bit 0 becomes bit 1 *)
      exists (tO (S x) :: T'), (@nil tok). split; [reflexivity|]. split; [|low_tac].
      split; [simpl; lia|]. split; [exact HG|]. keep_tac 0.
    + (* bit 1 is crossed *)
      simpl in HG.
      assert (HV' : V T' + 2 < 2 ^ S (length T')).
      { cbn [length V dg] in HV. rewrite Nat.pow_succ_r' in HV. lia. }
      destruct (IH P K (S n) HG HV') as [T1 [P1 [Ha [[Hp [Hg Hr]] _]]]].
      destruct (arr_tO x _ _ Ha) as [c' Hc].
      exists (tZ c' :: T1), P1. split; [exact Hc|]. split; [|low_tac].
      split; [simpl; lia|]. split; [exact Hg|].
      destruct Hr as [[HP1 [d [Hl Hv]]]|[Hv Hk]].
      * left. split; [exact HP1|]. exists d. simpl. split; [lia|].
        nia.
      * right. simpl. split; lia.
    + (* a becomes b; the head stays where it is *)
      destruct T' as [|y T2]; [destruct HG|].
      exists (tB (S (S x)) :: y :: T2), (@nil tok). split; [reflexivity|]. split; [|low_tac].
      split; [simpl; lia|]. split; [exact HG|]. keep_tac 0.
    + (* b stops the carry and changes the token to its left *)
      destruct T' as [|y T2]; [destruct HG|].
      destruct y as [z|z|z|z|z|z].
      * destruct HG as [H1 H2].
        exists (tZ x :: tA 0 :: tB z :: T2), (@nil tok). split; [reflexivity|]. split; [|low_tac].
        split; [simpl; lia|]. split.
        -- simpl. split; [lia|]. apply (Good_mono T2 K (S (S n))); [exact H2|lia].
        -- keep_tac 1.
      * destruct HG as [H1 H2].
        exists (tZ x :: tA 0 :: tD z :: T2), (@nil tok). split; [reflexivity|]. split; [|low_tac].
        split; [simpl; lia|]. split.
        -- simpl. apply (Good_mono T2 K (S (S n))); [exact H2|lia].
        -- keep_tac 1.
      * destruct HG.
      * destruct HG as [H1 H2].
        exists (tZ x :: tA 0 :: tC z :: T2), (@nil tok). split; [reflexivity|]. split; [|low_tac].
        split; [simpl; lia|]. split.
        -- simpl. split; [lia|]. apply (Good_mono T2 K (S (S n))); [exact H2|lia].
        -- keep_tac 1.
      * destruct HG as [H1 H2].
        (* no bit after this head: it can get no more carries, and everything from it on leaves T *)
        assert (Hsh : gapl T2 = 0 -> exists T1 P1, arr ((tB x :: tC z :: T2) ++ P) = Some (T1 ++ P1 ++ P) /\
          Stepd K n (tB x :: tC z :: T2) T1 P1 /\
          (low (tB x :: tC z :: T2) = 0 -> low T1 = 1) /\ (low (tB x :: tC z :: T2) = 1 -> low T1 = 0)).
        { intros E0. exists [tZ x], (tA (S z) :: T2). split; [reflexivity|]. split; [|low_tac].
          split; [simpl; lia|]. split; [exact I|]. right. rewrite E0 in H1. simpl. split; lia. }
        destruct T2 as [|[u|u|u|u|u|u] T3]; try (apply Hsh; reflexivity).
        -- exists (tZ x :: tA (S z) :: tZ u :: T3), (@nil tok). split; [reflexivity|]. split; [|low_tac].
           split; [simpl; lia|]. split.
           ++ simpl in *. split; [lia|exact H2].
           ++ keep_tac 0.
        -- exists (tZ x :: tA (S z) :: tO u :: T3), (@nil tok). split; [reflexivity|]. split; [|low_tac].
           split; [simpl; lia|]. split.
           ++ simpl in *. split; [lia|exact H2].
           ++ keep_tac 0.
      * exists (tZ x :: tZ (S (S z)) :: T2), (@nil tok). split; [reflexivity|]. split; [|low_tac].
        pose proof (psi_pos T2) as HP.
        split; [simpl; lia|]. split; [exact HG|]. keep_tac 0.
    + destruct HG.
    + destruct HG.
Qed.

(* Carries in a super-era and the next j. *)
Definition N (j : nat) : nat := if Nat.even j then 3 * j else 6 * j + 2.
Definition nj (j : nat) : nat := if Nat.even j then 3 * Nat.div2 j + 1 else 3 * Nat.div2 j + 3.

Lemma ev_or : forall j,
  (exists i, j = 2 * i /\ N j = 6 * i /\ nj j = 3 * i + 1) \/
  (exists i, j = 2 * i + 1 /\ N j = 12 * i + 8 /\ nj j = 3 * i + 3).
Proof.
  intros j. destruct (Nat.Even_or_Odd j) as [[i Hi]|[i Hi]].
  - left. exists i. subst j. unfold N, nj.
    assert (E : Nat.even (2 * i) = true) by (apply Nat.even_spec; exists i; reflexivity).
    rewrite E, Nat.div2_double. split; [reflexivity|split; lia].
  - right. exists i. subst j. unfold N, nj.
    assert (E : Nat.even (2 * i + 1) = false).
    { rewrite <- Nat.negb_odd. assert (E' : Nat.odd (2 * i + 1) = true) by (apply Nat.odd_spec; exists i; reflexivity).
      rewrite E'. reflexivity. }
    rewrite E. replace (2 * i + 1) with (S (2 * i)) by lia. rewrite Nat.div2_succ_double.
    split; [reflexivity|split; lia].
Qed.

Lemma N_even : forall j, Nat.even (N j) = true.
Proof.
  intros j. apply Nat.even_spec. destruct (ev_or j) as [[i [_ [E _]]]|[i [_ [E _]]]]; rewrite E.
  - exists (3 * i). lia.
  - exists (6 * i + 4). lia.
Qed.

(* M carries are left in this super-era. The low token of T is tZ for M even, tO for M odd. *)
Definition Inv (j M : nat) (w : list tok) : Prop :=
  exists T P K, w = T ++ P /\ Good K 0 T /\ V T + 2 * M + 48 * j <= 2 ^ S (length T) /\
    N j <= psi T + M /\ M <= N j /\ 8 * j <= 2 ^ K /\ low T = (if Nat.even M then 0 else 1).

Lemma pow2_pos : forall d, 1 <= 2 ^ d.
Proof. intros d. pose proof (Nat.pow_nonzero 2 d) as H. lia. Qed.

Lemma inv_arr : forall j M w, 1 <= j -> Inv j (S M) w -> exists w', arr w = Some w' /\ Inv j M w'.
Proof.
  intros j M w Hj [T [P [K [-> [HG [HF [Hpsi [HM [HK Hlow]]]]]]]]].
  destruct (arrive T P K 0 HG) as [T1 [P1 [Ha [[Hp [Hg Hr]] [H0 H1]]]]]; [lia|].
  exists (T1 ++ P1 ++ P). split; [exact Ha|].
  assert (Hlow1 : low T1 = if Nat.even M then 0 else 1).
  { rewrite Nat.even_succ, <- Nat.negb_even in Hlow.
    destruct (Nat.even M); simpl in Hlow; auto. }
  pose proof (ev_or j) as Hj2.
  assert (HN : N j <= 6 * j + 2) by (destruct Hj2 as [[i [? [? _]]]|[i [? [? _]]]]; lia).
  destruct Hr as [[-> [d [Hl Hv]]]|[Hv Hk]].
  - exists T1, P, K. split; [reflexivity|]. split; [exact Hg|]. split.
    + replace (S (length T1)) with (S (length T) + d) by lia.
      rewrite Nat.pow_add_r.
      pose proof (pow2_pos d) as Hd.
      assert (E : (V T + 2 * S M + 48 * j) * 2 ^ d <= 2 ^ S (length T) * 2 ^ d)
        by (apply Nat.mul_le_mono_r; exact HF).
      nia.
    + repeat split; try lia.
  - exists T1, (P1 ++ P), K. split; [reflexivity|]. split; [exact Hg|]. split.
    + rewrite Hv.
      assert (E : 2 ^ (K + 3) <= 2 ^ S (length T1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite Nat.pow_add_r in E. simpl (2 ^ 3) in E. lia.
    + repeat split; try lia.
Qed.

Lemma inv_low : forall j M w, Inv j M w -> low w = (if Nat.even M then 0 else 1).
Proof.
  intros j M w [T [P [K [-> [_ [_ [_ [_ [_ Hlow]]]]]]]]].
  rewrite <- Hlow. destruct T as [|[x|x|x|x|x|x] T']; try reflexivity;
    simpl in Hlow; destruct (Nat.even M); discriminate.
Qed.

Lemma inv_payload : forall j M x x' r, Inv j M (tO x :: r) -> Inv j M (tO x' :: r).
Proof.
  intros j M x x' r [T [P [K [E [HG [HF [Hpsi [HM [HK Hlow]]]]]]]]].
  destruct T as [|[y|y|y|y|y|y] T'];
    try (simpl in Hlow; destruct (Nat.even M); discriminate);
    try discriminate.
  injection E as <- ->.
  exists (tO x' :: T'), P, K. split; [reflexivity|]. split; [exact HG|]. exact (conj HF (conj Hpsi (conj HM (conj HK Hlow)))).
Qed.

(* The word after the carry, and what the next block gains (half of it) in the low groups below. *)
Definition nl (r : res) : list tok :=
  match r with
  | Bnc l => l
  | Stp l q => tZ q :: l
  end.

Definition dc (r : res) : nat :=
  match r with
  | Bnc _ => 3
  | Stp _ _ => 1
  end.

(* A bit 1 at the low end: the arrival is a stop. *)
Lemma inv_last : forall j M w, 1 <= j -> Inv j (S M) w -> Nat.even (S M) = false ->
  exists l q, inn w = Some (Stp l q) /\ Inv j M (tZ q :: l).
Proof.
  intros j M w Hj H He.
  pose proof (inv_low _ _ _ H) as Hl. rewrite He in Hl.
  destruct (inv_arr _ _ _ Hj H) as [w1 [Ha Hi]].
  destruct w as [|[x|x|x|x|x|x] w0]; try discriminate.
  unfold arr in Ha. simpl in Ha.
  destruct (inn w0) as [[l|l q]|] eqn:E0; [| |discriminate]; injection Ha as <-.
  - exists l, (S (S x)). split; [simpl; rewrite E0; reflexivity|exact Hi].
  - exists (tZ q :: l), x. split; [simpl; rewrite E0; reflexivity|exact Hi].
Qed.

(* A bit 0 at the low end: the arrival is a bounce. *)
Lemma inv_first : forall j M w, 1 <= j -> Inv j (S M) w -> Nat.even (S M) = true ->
  exists x w0, w = tZ x :: w0 /\ Inv j M (tO (S x) :: w0).
Proof.
  intros j M w Hj H He.
  pose proof (inv_low _ _ _ H) as Hl. rewrite He in Hl.
  destruct (inv_arr _ _ _ Hj H) as [w1 [Ha Hi]].
  destruct w as [|[x|x|x|x|x|x] w0]; try discriminate.
  injection Ha as <-. exists x, w0. split; [reflexivity|exact Hi].
Qed.

Lemma inv_two : forall j M w, 1 <= j -> Inv j (S (S M)) w ->
  exists r1 r2, inn w = Some r1 /\ inn (nl r1) = Some r2 /\ dc r1 + dc r2 = 4 /\ Inv j M (nl r2).
Proof.
  intros j M w Hj H.
  destruct (Nat.even (S (S M))) eqn:He.
  - destruct (inv_first _ _ _ Hj H He) as [x [w0 [-> Hi]]].
    assert (He2 : Nat.even (S M) = false).
    { rewrite Nat.even_succ_succ in He. rewrite Nat.even_succ, <- Nat.negb_even, He. reflexivity. }
    destruct (inv_last _ _ _ Hj Hi He2) as [l [q [El Hi2]]].
    exists (Bnc (tO (S x) :: w0)), (Stp l q). split; [reflexivity|]. split; [exact El|]. split; [reflexivity|exact Hi2].
  - destruct (inv_last _ _ _ Hj H He) as [l [q [El Hi]]].
    assert (He2 : Nat.even (S M) = true).
    { rewrite Nat.even_succ_succ in He. rewrite Nat.even_succ, <- Nat.negb_even, He. reflexivity. }
    destruct (inv_first _ _ _ Hj Hi He2) as [x [w0 [E Hi2]]].
    injection E as <- <-.
    exists (Stp l q), (Bnc (tO (S q) :: l)). split; [exact El|]. split; [reflexivity|]. split; [reflexivity|exact Hi2].
Qed.

Lemma pow_3 : forall k, 2 ^ (3 * k + 1) = 2 * (2 ^ k * (2 ^ k * 2 ^ k)).
Proof.
  intros k. rewrite Nat.add_1_r. rewrite Nat.pow_succ_r'. f_equal.
  replace (3 * k) with (k + (k + k)) by lia. rewrite !Nat.pow_add_r. reflexivity.
Qed.

(* A new head is born: there are more than log2 N - 2 bits before the first head, so its gap is long. *)
Lemma inv_S : forall j x w0, 46 <= j -> Inv j 0 (tZ x :: w0) ->
  exists y r, w0 = y :: r /\ Inv (nj j) (N (nj j)) (tZ (S (S (S x))) :: ins y r).
Proof.
  intros j x w0 Hj [T [P [K [E [HG [HF [Hpsi [_ [HK Hlow]]]]]]]]].
  destruct T as [|[y0|y0|y0|y0|y0|y0] T']; try discriminate.
  injection E as <- ->.
  assert (HN3 : 3 * j <= N j) by (destruct (ev_or j) as [[i [? [? _]]]|[i [? [? _]]]]; lia).
  assert (Hnx : 2 * nj j <= 3 * j + 3) by (destruct (ev_or j) as [[i [? [_ ?]]]|[i [? [_ ?]]]]; lia).
  assert (HN2 : N (nj j) <= 6 * nj j + 2) by (destruct (ev_or (nj j)) as [[i [? [? _]]]|[i [? [? _]]]]; lia).
  assert (Hlt : 3 * j + 1 <= 4 * 2 ^ gapl (tZ x :: T')) by (pose proof (psi_lt (tZ x :: T')); lia).
  (* the second token is a bit, since the psi bound says there are at least 2 leading bits *)
  destruct T' as [|[z|z|z|z|z|z] T2]; try (simpl in Hlt; lia).
  - (* a bit 0: a live head with a long gap *)
    exists (tZ z), (T2 ++ P). split; [reflexivity|].
    cbn [gapl] in Hlt. rewrite !Nat.pow_succ_r' in Hlt.
    set (k2 := gapl T2) in *.
    set (K' := Nat.min (S K) (3 * k2 + 1)).
    assert (HK' : 8 * nj j <= 2 ^ K').
    { unfold K'. destruct (Nat.min_spec (S K) (3 * k2 + 1)) as [[_ ->]|[_ ->]].
      - rewrite Nat.pow_succ_r'. lia.
      - rewrite pow_3.
        set (Y := 2 ^ k2) in *.
        assert (HY : 9 <= Y) by lia.
        assert (HY2 : 81 <= Y * Y) by nia.
        assert (HY3 : 81 * Y <= Y * (Y * Y)) by nia.
        lia. }
    exists (tZ (S (S (S x))) :: tA 0 :: tB z :: T2), P, K'.
    split; [reflexivity|]. split.
    + simpl. split.
      * unfold K'. pose proof (Nat.le_min_r (S K) (3 * k2 + 1)). lia.
      * apply (Good_mono T2 K 2); [exact HG|].
        unfold K'. pose proof (Nat.le_min_l (S K) (3 * k2 + 1)). lia.
    + split.
      * cbn [length V dg] in HF |- *. rewrite Nat.pow_succ_r'. lia.
      * rewrite N_even. repeat split; try lia.
  - (* a bit 1: this head dies soon *)
    exists (tO z), (T2 ++ P). split; [reflexivity|].
    exists (tZ (S (S (S x))) :: tA 0 :: tD z :: T2), P, (S K).
    split; [reflexivity|]. split.
    + simpl. apply (Good_mono T2 K 2); [exact HG|lia].
    + split.
      * cbn [length V dg] in HF |- *. rewrite Nat.pow_succ_r'. lia.
      * rewrite N_even. repeat split; try lia. rewrite Nat.pow_succ_r'. lia.
Qed.

(* Groups of macro steps at the low end of the word. *)
Local Ltac one := eapply progress_trans; [apply step_ok; reflexivity|].
Local Ltac last_one := apply step_ok; reflexivity.

Lemma tick4 : forall b a w K r, inn w = Some r ->
  enc (tZ b :: tZ a :: w) (S (S (S (S K)))) -->+ enc (tZ (S (S (S (S b)))) :: tZ (dc r + a) :: nl r) K.
Proof.
  intros b a w K r H.
  one. one. one.
  apply step_ok. unfold mstep. simpl. rewrite H. destruct r; reflexivity.
Qed.

Lemma tick2O : forall c w K r, inn w = Some r ->
  enc (tO c :: w) (S (S K)) -->+ enc (tO (dc r + c) :: nl r) K.
Proof.
  intros c w K r H.
  destruct r as [l|l q];
    (eapply progress_trans; [apply step_ok; unfold mstep; simpl; rewrite H; reflexivity|last_one]).
Qed.

Lemma tick2Z : forall c w K r, inn w = Some r ->
  enc (tZ c :: w) (S (S K)) -->+ enc (tZ (dc r + c) :: nl r) K.
Proof.
  intros c w K r H.
  one.
  apply step_ok. unfold mstep. simpl. rewrite H. destruct r; reflexivity.
Qed.

Lemma era1end : forall b a w,
  enc (tZ b :: tZ a :: w) 0 -->+ enc (tO (S a) :: w) (S (S (S b))).
Proof. intros. one. last_one. Qed.

Lemma stage1 : forall B y r K,
  enc (tA 0 :: tB B :: y :: r) (14 + K) -->+ enc (tZ 14 :: tZ 6 :: tZ (S (S (S B))) :: ins y r) K.
Proof.
  intros. do 13 one. last_one.
Qed.

Lemma end2O : forall c w l q, inn w = Some (Stp l q) ->
  enc (tO c :: w) 1 -->+ enc (tA 0 :: tB q :: l) c.
Proof.
  intros c w l q H.
  eapply progress_trans.
  - apply step_ok. unfold mstep. simpl. rewrite H. reflexivity.
  - last_one.
Qed.

Lemma end2Z : forall c x w0,
  enc (tO c :: tZ x :: w0) 1 -->+ enc (tA 0 :: tD (S x) :: w0) (S (S c)).
Proof. intros. one. last_one. Qed.

Lemma era3start : forall x w0 K,
  enc (tA 0 :: tD x :: w0) (S (S (S (S K)))) -->+ enc (tZ 5 :: tO (S (S (S x))) :: w0) K.
Proof. intros. one. one. one. last_one. Qed.

Lemma end3 : forall c w l q, inn w = Some (Stp l q) ->
  enc (tZ c :: w) 1 -->+ enc (tA 0 :: tB q :: l) (S c).
Proof.
  intros c w l q H.
  one.
  eapply progress_trans.
  - apply step_ok. unfold mstep. simpl. rewrite H. reflexivity.
  - last_one.
Qed.

Lemma era1 : forall p j M w a b K, 1 <= j -> Inv j (2 * p + M) w ->
  exists w', enc (tZ b :: tZ a :: w) (8 * p + K) -->* enc (tZ (8 * p + b) :: tZ (4 * p + a) :: w') K /\ Inv j M w'.
Proof.
  induction p as [|p IH]; intros j M w a b K Hj H.
  - exists w. split; [apply evstep_refl|exact H].
  - replace (2 * S p + M) with (S (S (2 * p + M))) in H by lia.
    destruct (inv_two _ _ _ Hj H) as [r1 [r2 [E1 [E2 [E3 Hi]]]]].
    destruct (IH j M (nl r2) (dc r2 + (dc r1 + a)) (S (S (S (S (S (S (S (S b)))))))) K Hj Hi) as [w' [Hrun Hw']].
    exists w'. split; [|exact Hw'].
    replace (8 * S p + K) with (S (S (S (S (S (S (S (S (8 * p + K))))))))) by lia.
    eapply evstep_trans.
    + apply progress_evstep. eapply progress_trans; [apply (tick4 _ _ _ _ _ E1)|apply (tick4 _ _ _ _ _ E2)].
    + eapply evstep_trans; [exact Hrun|]. finish.
Qed.

Lemma era2 : forall p j M w c K, 1 <= j -> Inv j (2 * p + M) w ->
  exists w', enc (tO c :: w) (4 * p + K) -->* enc (tO (4 * p + c) :: w') K /\ Inv j M w'.
Proof.
  induction p as [|p IH]; intros j M w c K Hj H.
  - exists w. split; [apply evstep_refl|exact H].
  - replace (2 * S p + M) with (S (S (2 * p + M))) in H by lia.
    destruct (inv_two _ _ _ Hj H) as [r1 [r2 [E1 [E2 [E3 Hi]]]]].
    destruct (IH j M (nl r2) (dc r2 + (dc r1 + c)) K Hj Hi) as [w' [Hrun Hw']].
    exists w'. split; [|exact Hw'].
    replace (4 * S p + K) with (S (S (S (S (4 * p + K))))) by lia.
    eapply evstep_trans.
    + apply progress_evstep. eapply progress_trans; [apply (tick2O _ _ _ _ E1)|apply (tick2O _ _ _ _ E2)].
    + eapply evstep_trans; [exact Hrun|]. finish.
Qed.

Lemma era3 : forall p j M w c K, 1 <= j -> Inv j (2 * p + M) w ->
  exists w', enc (tZ c :: w) (4 * p + K) -->* enc (tZ (4 * p + c) :: w') K /\ Inv j M w'.
Proof.
  induction p as [|p IH]; intros j M w c K Hj H.
  - exists w. split; [apply evstep_refl|exact H].
  - replace (2 * S p + M) with (S (S (2 * p + M))) in H by lia.
    destruct (inv_two _ _ _ Hj H) as [r1 [r2 [E1 [E2 [E3 Hi]]]]].
    destruct (IH j M (nl r2) (dc r2 + (dc r1 + c)) K Hj Hi) as [w' [Hrun Hw']].
    exists w'. split; [|exact Hw'].
    replace (4 * S p + K) with (S (S (S (S (4 * p + K))))) by lia.
    eapply evstep_trans.
    + apply progress_evstep. eapply progress_trans; [apply (tick2Z _ _ _ _ E1)|apply (tick2Z _ _ _ _ E2)].
    + eapply evstep_trans; [exact Hrun|]. finish.
Qed.

Lemma even_2 : forall n, Nat.even (2 * n) = true.
Proof. intros n. apply Nat.even_spec. exists n. reflexivity. Qed.

(* One super-era, from one anchor to the next. *)
(* Anchors: blocks 30, 14, then the word. *)
Definition C (i : list tok * nat) : Q * tape :=
  enc (tZ 14 :: tZ 6 :: fst i) (4 * snd i - 12).

Definition PP (i : list tok * nat) : Prop :=
  46 <= snd i /\ Inv (snd i) (N (snd i)) (fst i).

Lemma nj_ge : forall j, j <= nj j.
Proof. intros j. destruct (ev_or j) as [[i [? [_ ?]]]|[i [? [_ ?]]]]; lia. Qed.

Lemma super : forall i, PP i -> exists i', C i -->+ C i' /\ PP i'.
Proof.
  intros [w j] [Hj H]. simpl in Hj, H. unfold C. simpl fst. simpl snd.
  assert (Hj1 : 1 <= j) by lia.
  destruct (ev_or j) as [[i [Ej [EN En]]]|[i [Ej [EN En]]]]; rewrite EN in H.
  - (* j even, two eras *)
    assert (HK0 : 4 * j - 12 = 8 * (i - 2) + 4) by lia.
    assert (HM0 : 6 * i = 2 * (i - 2) + (4 * (i - 2) + 12)) by lia.
    rewrite HM0 in H. rewrite HK0.
    destruct (era1 _ _ _ _ 6 14 4 Hj1 H) as [w1 [R1 H1]].
    set (M1 := 4 * (i - 2) + 11) in *.
    assert (HM1 : 4 * (i - 2) + 12 = S M1) by (unfold M1; lia).
    rewrite HM1 in H1.
    assert (He1 : Nat.even (S M1) = true).
    { rewrite <- HM1. replace (4 * (i - 2) + 12) with (2 * (2 * (i - 2) + 6)) by lia. apply even_2. }
    destruct (inv_first _ _ _ Hj1 H1 He1) as [x [w10 [-> H2]]].
    set (b1 := 8 * (i - 2) + 14) in *. set (a1 := 4 * (i - 2) + 6) in *.
    assert (R2 : enc (tZ b1 :: tZ a1 :: tZ x :: w10) 4 -->+ enc (tO (S (3 + a1)) :: tO (S x) :: w10) (S (S (S (S (S (S (S b1)))))))).
    { eapply progress_trans.
      - apply (tick4 b1 a1 (tZ x :: w10) 0 (Bnc (tO (S x) :: w10)) eq_refl).
      - apply era1end. }
    assert (HK2 : S (S (S (S (S (S (S b1)))))) = 4 * (2 * (i - 2) + 5) + 1) by (unfold b1; lia).
    rewrite HK2 in R2.
    assert (HM2 : M1 = 2 * (2 * (i - 2) + 5) + 1) by (unfold M1; lia).
    rewrite HM2 in H2.
    destruct (era2 _ _ _ _ (S (3 + a1)) 1 Hj1 H2) as [w3 [R3 H3]].
    replace 1 with (S 0) in H3 by reflexivity.
    assert (He3 : Nat.even (S 0) = false) by reflexivity.
    destruct (inv_last _ _ _ Hj1 H3 He3) as [l [q [El H4]]].
    destruct (inv_S _ _ _ Hj H4) as [y [r [-> H5]]].
    exists (tZ (S (S (S q))) :: ins y r, nj j). split.
    + eapply evstep_progress_trans; [exact R1|].
      eapply progress_trans; [exact R2|].
      eapply evstep_progress_trans; [exact R3|].
      eapply progress_trans; [apply (end2O _ _ _ _ El)|].
      simpl fst. simpl snd.
      replace (4 * (2 * (i - 2) + 5) + S (3 + a1)) with (14 + (4 * nj j - 12)) by (unfold a1; lia).
      apply stage1.
    + split; [simpl; pose proof (nj_ge j); lia|exact H5].
  - (* j odd, three eras *)
    assert (HK0 : 4 * j - 12 = 8 * (i - 1) + 0) by lia.
    assert (HM0 : 12 * i + 8 = 2 * (i - 1) + (10 * (i - 1) + 20)) by lia.
    rewrite HM0 in H. rewrite HK0.
    destruct (era1 _ _ _ _ 6 14 0 Hj1 H) as [w1 [R1 H1]].
    set (b1 := 8 * (i - 1) + 14) in *. set (a1 := 4 * (i - 1) + 6) in *.
    pose proof (era1end b1 a1 w1) as R2.
    assert (HK2 : S (S (S b1)) = 4 * (2 * (i - 1) + 4) + 1) by (unfold b1; lia).
    rewrite HK2 in R2.
    assert (HM2 : 10 * (i - 1) + 20 = 2 * (2 * (i - 1) + 4) + (6 * (i - 1) + 12)) by lia.
    rewrite HM2 in H1.
    destruct (era2 _ _ _ _ (S a1) 1 Hj1 H1) as [w2 [R3 H2]].
    set (M2 := 6 * (i - 1) + 11) in *.
    assert (HM3 : 6 * (i - 1) + 12 = S M2) by (unfold M2; lia).
    rewrite HM3 in H2.
    assert (He2 : Nat.even (S M2) = true).
    { rewrite <- HM3. replace (6 * (i - 1) + 12) with (2 * (3 * (i - 1) + 6)) by lia. apply even_2. }
    destruct (inv_first _ _ _ Hj1 H2 He2) as [x [w20 [-> H3]]].
    set (c2 := 4 * (2 * (i - 1) + 4) + S a1) in *.
    assert (R4 : enc (tO c2 :: tZ x :: w20) 1 -->+ enc (tZ 5 :: tO (S (S (S (S x)))) :: w20) (4 * (3 * (i - 1) + 5) + 1)).
    { eapply progress_trans; [apply end2Z|].
      replace (S (S c2)) with (S (S (S (S (4 * (3 * (i - 1) + 5) + 1))))) by (unfold c2, a1; lia).
      apply era3start. }
    pose proof (inv_payload _ _ _ (S (S (S (S x)))) _ H3) as H4.
    assert (HM4 : M2 = 2 * (3 * (i - 1) + 5) + 1) by (unfold M2; lia).
    rewrite HM4 in H4.
    destruct (era3 _ _ _ _ 5 1 Hj1 H4) as [w4 [R5 H5]].
    replace 1 with (S 0) in H5 by reflexivity.
    assert (He5 : Nat.even (S 0) = false) by reflexivity.
    destruct (inv_last _ _ _ Hj1 H5 He5) as [l [q [El H6]]].
    destruct (inv_S _ _ _ Hj H6) as [y [r [-> H7]]].
    exists (tZ (S (S (S q))) :: ins y r, nj j). split.
    + eapply evstep_progress_trans; [exact R1|].
      eapply progress_trans; [exact R2|].
      eapply evstep_progress_trans; [exact R3|].
      eapply progress_trans; [exact R4|].
      eapply evstep_progress_trans; [exact R5|].
      eapply progress_trans; [apply (end3 _ _ _ _ El)|].
      simpl fst. simpl snd.
      replace (S (4 * (3 * (i - 1) + 5) + 5)) with (14 + (4 * nj j - 12)) by lia.
      apply stage1.
    + split; [simpl; pose proof (nj_ge j); lia|exact H7].
Qed.

(* The start: 861 macro steps from the blank tape reach the anchor with j = 46, the first the proof uses (j = 4, 7, 12, 19, 30 come before it). *)
Fixpoint runm (n : nat) (w : list tok) (K : nat) : option (list tok * nat) :=
  match n with
  | O => Some (w, K)
  | S n' =>
    match mstep w K with
    | None => None
    | Some (w1, K1) => runm n' w1 K1
    end
  end.

Lemma runm_ok : forall n w K w' K', runm (S n) w K = Some (w', K') -> enc w K -->+ enc w' K'.
Proof.
  induction n as [|n IH]; intros w K w' K' H.
  - simpl in H. destruct (mstep w K) as [[w1 K1]|] eqn:E; [|discriminate].
    injection H as <- <-. apply step_ok. exact E.
  - remember (S n) as n1. simpl in H. subst n1.
    destruct (mstep w K) as [[w1 K1]|] eqn:E; [|discriminate].
    eapply progress_trans; [apply step_ok; exact E|].
    apply (IH _ _ _ _ H).
Qed.

Definition T0 : list tok :=
  [tZ 340; tA 0; tD 46; tO 22; tO 69; tO 3; tA 0; tC 29; tO 33; tO 6; tB 2; tC 9].
Definition P0 : list tok :=
  [tO 26; tA 0; tB 10; tZ 12; tB 2; tB 10; tZ 3; tZ 2; tO 0].

Lemma run0 : runm 861 [] 0 = Some (tZ 14 :: tZ 6 :: T0 ++ P0, 4 * 46 - 12).
Proof. reflexivity. Qed.

Lemma inv0 : PP (T0 ++ P0, 46).
Proof.
  split; [simpl; lia|].
  exists T0, P0, 9. split; [reflexivity|]. split.
  - simpl. repeat split; lia.
  - split; [|split; [|split; [|split]]].
    + apply Nat.leb_le. reflexivity.
    + simpl. lia.
    + apply Nat.leb_le. reflexivity.
    + apply Nat.leb_le. reflexivity.
    + reflexivity.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (c' := C (T0 ++ P0, 46)).
  - apply progress_evstep. apply (runm_ok 860 [] 0). exact run0.
  - apply (progress_nonhalt_cond tm _ _ C PP).
    + exact super.
    + exact inv0.
Qed.

End TM1.

Print Assumptions TM1.nonhalt.
