(* 1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA--- does not halt from the blank tape.

   A visit ([Vis]): the head enters a stream s from the left in state C (the cell left of it is 0) and comes back in state A one cell left of that 0, with s changed to s'.
     visit(0 x) = 1 x,  visit(100 x) = 000 visit(x),  visit(1010 x) = 1010 visit(visit(x)),  visit(1011 x) = 0001 x,  visit(110 x) = 001 x,  111 would halt.
   A round ([round_step]) pushes 1 0 on the stream at the left end and makes one visit.

   Tokens ([tk]): L = 1010, H = 100, Z = 000. n visits of L make 2 n visits below it; H and Z are one binary digit, carry to the digit below. A pushed 1 0 is a pending piece of stream ([pd]) that re-reads the tokens, one token for one token ([xstep]):
     pending 10: Z -> H, pending 00; H -> L, pending 0; L -> L.
     pending 00: Z -> Z; H -> L, pending 0, after 1 visit; L -> L, pending 10, after 1 visit.
     pending 0:  Z -> Z; H -> L, nothing pending, after 3 visits; L -> Z, pending 10, after 4 visits.
   Once nothing is pending the tokens only take the count. So a round is one left to right scan with a count ([xscan], exact). [sstep] and [spass] are the same scan for a count 2^a x - c with x unknown; they fail if a digit would depend on x ([PassP]).

   The run. [xrun] goes from the blank tape to round 26128, where the tape is L^k A C E T^v 0^inf with T = H Z Z Z, and on to round 33824.
   For every t, [sw] is the tape L^(k + 3848 t) A B^t C D^t E T^(v + 962 t) 0^inf. B is a block of 18552 tokens that gets 2^4536 times the visits, D a block of 4536 digits.
   In every round, for every t ([round_ok]), the count crosses B^t C D^t as nested pairs ([zone]): 2^64 x - c in, 2^b x - e out, for every x and t ([zone_ok]), because one layer B ... D maps that form to itself, which [core] checks. Then it goes through E, and T^v gets the exact power of 2 that adds one more T at the end ([VS_T]). [ycut] and [ucut] move a few tokens between the zones as the point that absorbs the pending piece moves on; they are identities of streams.
   [check] runs 7696 rounds in the VM, for all t at once, and finds the same zones with one more layer ([closure]), so the tape repeats for ever with a larger t. A, C, E are read off the exact run at round 26128, B and D at round 33824; they are not data in this file. *)
From BusyCoq Require Import Individual62.
From Coq Require Import NArith Lia String PeanoNat.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* The visit law. *)
Definition Vis (s s' : side) : Prop :=
  forall x l, S0 >> x >> l {{C}}> s -->+ l {{A}}> x >> S0 >> s'.

Lemma vis_0 : forall r, Vis (S0 >> r) (S1 >> r).
Proof. intros r x l. execute. Qed.

Lemma vis_H : forall r r', Vis r r' -> Vis (S1 >> S0 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Proof.
  intros r r' H x l.
  eapply progress_intro; [prove_step|simpl_tape].
  do 4 step.
  eapply evstep_trans; [apply progress_evstep; apply H|].
  execute.
Qed.

Lemma vis_L : forall r r1 r2, Vis r r1 -> Vis r1 r2 ->
  Vis (S1 >> S0 >> S1 >> S0 >> r) (S1 >> S0 >> S1 >> S0 >> r2).
Proof.
  intros r r1 r2 H1 H2 x l.
  eapply progress_intro; [prove_step|simpl_tape].
  do 3 step.
  eapply evstep_trans; [apply progress_evstep; apply H1|].
  do 2 step.
  eapply evstep_trans; [apply progress_evstep; apply H2|].
  execute.
Qed.

Lemma vis_b : forall r, Vis (S1 >> S0 >> S1 >> S1 >> r) (S0 >> S0 >> S0 >> S1 >> r).
Proof. intros r x l. execute. Qed.

Lemma vis_c : forall r, Vis (S1 >> S1 >> S0 >> r) (S0 >> S0 >> S1 >> r).
Proof. intros r x l. execute. Qed.

(* One round at the left end. *)
Definition LE (s : side) : Q * tape := const S0 {{A}}> S1 >> S0 >> s.

Lemma round_step : forall s s', Vis (S1 >> S0 >> s) s' -> LE s -->+ LE s'.
Proof.
  intros s s' H. unfold LE.
  eapply progress_intro; [prove_step|simpl_tape].
  do 5 step.
  apply progress_evstep. apply H.
Qed.

Lemma blank_start : c0 -->+ LE (S1 >> const S0).
Proof.
  unfold c0, LE, tape0.
  eapply progress_intro; [prove_step|simpl_tape].
  do 3 step. finish.
Qed.

(* n visits in a row. *)
Inductive VS : N -> side -> side -> Prop :=
  | VS_0 : forall s, VS 0 s s
  | VS_S : forall n s s1 s2, Vis s s1 -> VS n s1 s2 -> VS (N.succ n) s s2.

Lemma VS_1 : forall s s', Vis s s' -> VS 1 s s'.
Proof. intros s s' H. apply (VS_S 0 s s' s'); [exact H|apply VS_0]. Qed.

Lemma VS_add : forall a b s s1 s2, VS a s s1 -> VS b s1 s2 -> VS (a + b) s s2.
Proof.
  intros a b s s1 s2 H1. revert b s2. induction H1 as [s|n s s3 s1 HV _ IH]; intros b s2 H2.
  - exact H2.
  - replace (N.succ n + b)%N with (N.succ (n + b))%N by lia.
    eapply VS_S; [exact HV|]. apply IH. exact H2.
Qed.

Lemma VS_inv : forall n s s', VS (N.succ n) s s' -> exists s1, Vis s s1 /\ VS n s1 s'.
Proof.
  intros n s s' H. inversion H as [s0 E1 E2 E3|n0 s0 s1 s2 HV HR E1 E2 E3]; subst.
  - lia.
  - apply N.succ_inj in E1. subst. exists s1. split; assumption.
Qed.

Lemma VS_inv0 : forall s s', VS 0 s s' -> s = s'.
Proof.
  intros s s' H. inversion H as [s0 E1 E2|n0 s0 s1 s2 HV HR E1 E2 E3]; subst.
  - reflexivity.
  - lia.
Qed.

Notation Lt r := (S1 >> S0 >> S1 >> S0 >> r).
Notation Ht r := (S1 >> S0 >> S0 >> r).
Notation Zt r := (S0 >> S0 >> S0 >> r).

Lemma VS_L : forall n r r', VS (2 * n) r r' -> VS n (Lt r) (Lt r').
Proof.
  induction n as [|n IH] using N.peano_ind; intros r r' H.
  - replace (2 * 0)%N with 0%N in H by lia. rewrite (VS_inv0 _ _ H). apply VS_0.
  - replace (2 * N.succ n)%N with (N.succ (N.succ (2 * n)))%N in H by lia.
    destruct (VS_inv _ _ _ H) as [r1 [H1 H2]].
    destruct (VS_inv _ _ _ H2) as [r2 [H3 H4]].
    eapply VS_S; [eapply vis_L; eassumption | apply IH; exact H4].
Qed.

Lemma VS_ZZ : forall n r r', VS n r r' -> VS (2 * n) (Zt r) (Zt r').
Proof.
  intros n r r' H. induction H as [r|n r r1 r' HV _ IH].
  - apply VS_0.
  - replace (2 * N.succ n)%N with (N.succ (N.succ (2 * n)))%N by lia.
    eapply VS_S; [apply vis_0|].
    eapply VS_S; [apply vis_H; exact HV|exact IH].
Qed.

Lemma VS_HH : forall n r r', VS n r r' -> VS (2 * n) (Ht r) (Ht r').
Proof.
  intros n r r' H. induction H as [r|n r r1 r' HV _ IH].
  - apply VS_0.
  - replace (2 * N.succ n)%N with (N.succ (N.succ (2 * n)))%N by lia.
    eapply VS_S; [apply vis_H; exact HV|].
    eapply VS_S; [apply vis_0|exact IH].
Qed.

Lemma VS_ZH : forall n r r', VS n r r' -> VS (2 * n + 1) (Zt r) (Ht r').
Proof.
  intros n r r' H.
  eapply VS_add; [apply VS_ZZ; exact H|].
  apply VS_1. apply vis_0.
Qed.

Lemma VS_HZ : forall n r r', VS (N.succ n) r r' -> VS (2 * n + 1) (Ht r) (Zt r').
Proof.
  intros n r r' H.
  destruct (VS_inv _ _ _ H) as [r1 [H1 H2]].
  replace (2 * n + 1)%N with (1 + 2 * n)%N by lia.
  eapply VS_add; [apply VS_1; apply vis_H; exact H1|].
  apply VS_ZZ. exact H2.
Qed.

(* Tokens and pending pieces. *)
Inductive Tok := tZ | tH | tL.

Definition tk (t : Tok) (r : side) : side :=
  match t with
  | tZ => Zt r
  | tH => Ht r
  | tL => Lt r
  end.

Fixpoint tks (w : list Tok) (r : side) : side :=
  match w with
  | [] => r
  | t :: w' => tk t (tks w' r)
  end.

Lemma tks_app : forall a b r, tks (a ++ b) r = tks a (tks b r).
Proof. induction a as [|t a IH]; intros b r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Inductive Pd := P10 | P00 | P0 | PE.

Definition pd (p : Pd) (r : side) : side :=
  match p with
  | P10 => S1 >> S0 >> r
  | P00 => S0 >> S0 >> r
  | P0 => S0 >> r
  | PE => r
  end.

(* Parity. *)
Local Open Scope N_scope.

Lemma double_or v : exists m, v = N.double m \/ v = N.succ_double m.
Proof.
  destruct v as [|[p|p|]].
  - exists 0. left. reflexivity.
  - exists (Npos p). right. reflexivity.
  - exists (Npos p). left. reflexivity.
  - exists 0. right. reflexivity.
Qed.

Lemma odd_double m : N.odd (N.double m) = false.
Proof. destruct m; reflexivity. Qed.
Lemma odd_succ_double m : N.odd (N.succ_double m) = true.
Proof. destruct m; reflexivity. Qed.
Lemma div2_double m : N.div2 (N.double m) = m.
Proof. destruct m; reflexivity. Qed.
Lemma div2_succ_double m : N.div2 (N.succ_double m) = m.
Proof. destruct m; reflexivity. Qed.
Lemma succ_double_S m : N.succ (N.double m) = N.succ_double m.
Proof. rewrite N.double_spec, N.succ_double_spec. lia. Qed.
Lemma succ_succ_double m : N.succ (N.succ_double m) = N.double (N.succ m).
Proof. rewrite N.double_spec, N.succ_double_spec. lia. Qed.

Lemma law_Z0 : forall n r r', N.odd n = false -> VS (N.div2 n) r r' -> VS n (tk tZ r) (tk tZ r').
Proof.
  intros n r r' E H. destruct (double_or n) as [m [-> | ->]].
  - rewrite div2_double in H. rewrite N.double_spec. exact (VS_ZZ _ _ _ H).
  - rewrite odd_succ_double in E. discriminate.
Qed.

Lemma law_Z1 : forall n r r', N.odd n = true -> VS (N.div2 n) r r' -> VS n (tk tZ r) (tk tH r').
Proof.
  intros n r r' E H. destruct (double_or n) as [m [-> | ->]].
  - rewrite odd_double in E. discriminate.
  - rewrite div2_succ_double in H. rewrite N.succ_double_spec. exact (VS_ZH _ _ _ H).
Qed.

Lemma law_H0 : forall n r r', N.odd n = false -> VS (N.div2 n) r r' -> VS n (tk tH r) (tk tH r').
Proof.
  intros n r r' E H. destruct (double_or n) as [m [-> | ->]].
  - rewrite div2_double in H. rewrite N.double_spec. exact (VS_HH _ _ _ H).
  - rewrite odd_succ_double in E. discriminate.
Qed.

Lemma law_H1 : forall n r r', N.odd n = true -> VS (N.div2 (N.succ n)) r r' -> VS n (tk tH r) (tk tZ r').
Proof.
  intros n r r' E H. destruct (double_or n) as [m [-> | ->]].
  - rewrite odd_double in E. discriminate.
  - rewrite succ_succ_double, div2_double in H. rewrite N.succ_double_spec. exact (VS_HZ _ _ _ H).
Qed.

(* One token, exact count. *)
Definition xstep (p : Pd) (t : Tok) (n : N) : option (Tok * Pd * N) :=
  match p, t with
  | P10, tZ => if N.odd n then Some (tZ, P00, N.div2 (N.succ n)) else Some (tH, P00, N.div2 n)
  | P10, tH => Some (tL, P0, N.double n)
  | P10, tL => Some (tL, P10, N.double n)
  | P00, tZ => if N.odd n then Some (tH, P00, N.div2 n) else Some (tZ, P00, N.div2 n)
  | P00, tH => if N.leb 1 n then Some (tL, P0, N.double (N.pred n)) else None
  | P00, tL => if N.leb 1 n then Some (tL, P10, N.double (N.pred n)) else None
  | P0, tZ => if N.odd n then Some (tH, P0, N.div2 n) else Some (tZ, P0, N.div2 n)
  | P0, tH => if N.leb 3 n then Some (tL, PE, N.double (n - 3)) else None
  | P0, tL => if N.leb 4 n then
                (if N.odd (n - 4) then Some (tH, P10, N.div2 (n - 4)) else Some (tZ, P10, N.div2 (n - 4)))
              else None
  | PE, tZ => if N.odd n then Some (tH, PE, N.div2 n) else Some (tZ, PE, N.div2 n)
  | PE, tH => if N.odd n then Some (tZ, PE, N.div2 (N.succ n)) else Some (tH, PE, N.div2 n)
  | PE, tL => Some (tL, PE, N.double n)
  end.

Lemma VS_Ld : forall n r r', VS (N.double n) r r' -> VS n (Lt r) (Lt r').
Proof. intros n r r' H. apply VS_L. rewrite <- N.double_spec. exact H. Qed.

Lemma xstep_ok : forall p t n t' p' n', xstep p t n = Some (t', p', n') ->
  forall r r', VS n' (pd p' r) r' -> VS n (pd p (tk t r)) (tk t' r').
Proof.
  intros p t n t' p' n' H r r' HV.
  destruct p, t; cbn [xstep] in H.
  - destruct (N.odd n) eqn:E; injection H as <- <- <-.
    + exact (law_H1 n (pd P00 r) r' E HV).
    + exact (law_H0 n (pd P00 r) r' E HV).
  - injection H as <- <- <-. exact (VS_Ld n (pd P0 r) r' HV).
  - injection H as <- <- <-. exact (VS_Ld n (pd P10 r) r' HV).
  - destruct (N.odd n) eqn:E; injection H as <- <- <-.
    + exact (law_Z1 n (pd P00 r) r' E HV).
    + exact (law_Z0 n (pd P00 r) r' E HV).
  - destruct (N.leb 1 n) eqn:E; [|discriminate]. injection H as <- <- <-.
    apply N.leb_le in E.
    replace n with (N.succ (N.pred n)) by lia.
    eapply VS_S; [apply vis_0|].
    exact (VS_Ld (N.pred n) (pd P0 r) r' HV).
  - destruct (N.leb 1 n) eqn:E; [|discriminate]. injection H as <- <- <-.
    apply N.leb_le in E.
    replace n with (N.succ (N.pred n)) by lia.
    eapply VS_S; [apply vis_0|].
    exact (VS_Ld (N.pred n) (pd P10 r) r' HV).
  - destruct (N.odd n) eqn:E; injection H as <- <- <-.
    + exact (law_Z1 n (pd P0 r) r' E HV).
    + exact (law_Z0 n (pd P0 r) r' E HV).
  - destruct (N.leb 3 n) eqn:E; [|discriminate]. injection H as <- <- <-.
    apply N.leb_le in E.
    replace n with (N.succ (N.succ (N.succ (n - 3)))) by lia.
    eapply VS_S; [apply vis_0|].
    eapply VS_S; [apply vis_c|].
    eapply VS_S; [apply vis_0|].
    exact (VS_Ld (n - 3) (pd PE r) r' HV).
  - destruct (N.leb 4 n) eqn:E; [|discriminate]. apply N.leb_le in E.
    assert (Hn : n = N.succ (N.succ (N.succ (N.succ (n - 4))))) by lia.
    destruct (N.odd (n - 4)) eqn:E2; injection H as <- <- <-; rewrite Hn;
      (eapply VS_S; [apply vis_0|]);
      (eapply VS_S; [apply vis_c|]);
      (eapply VS_S; [apply vis_0|]);
      (eapply VS_S; [apply vis_b|]).
    + exact (law_Z1 (n - 4) (pd P10 r) r' E2 HV).
    + exact (law_Z0 (n - 4) (pd P10 r) r' E2 HV).
  - destruct (N.odd n) eqn:E; injection H as <- <- <-.
    + exact (law_Z1 n r r' E HV).
    + exact (law_Z0 n r r' E HV).
  - destruct (N.odd n) eqn:E; injection H as <- <- <-.
    + exact (law_H1 n r r' E HV).
    + exact (law_H0 n r r' E HV).
  - injection H as <- <- <-. exact (VS_Ld n r r' HV).
Qed.

(* The blank end. *)
Definition Zinf : side := const S0.

Lemma Zinf_unfold : Zinf = S0 >> Zinf.
Proof. apply const_unfold. Qed.

Fixpoint allz (w : list Tok) : bool :=
  match w with
  | [] => true
  | tZ :: w' => allz w'
  | _ :: _ => false
  end.

Lemma allz_ok : forall w, allz w = true -> tks w Zinf = Zinf.
Proof.
  induction w as [|t w IH]; intros H; [reflexivity|].
  destruct t; try discriminate. simpl in H. simpl. rewrite (IH H).
  rewrite <- !Zinf_unfold. reflexivity.
Qed.

Definition pad8 : list Tok := [tZ;tZ;tZ;tZ;tZ;tZ;tZ;tZ].

Definition pad (w : list Tok) : list Tok :=
  match w with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => w
  | _ => w ++ pad8
  end.

Lemma pad8_ok : tks pad8 Zinf = Zinf.
Proof. apply allz_ok. reflexivity. Qed.

Lemma pad_cases : forall w, pad w = w \/ pad w = w ++ pad8.
Proof.
  intros w. unfold pad.
  destruct w as [|a [|b [|c [|d [|e [|f [|g [|h w]]]]]]]];
    first [left; reflexivity | right; reflexivity].
Qed.

Lemma pad_ok : forall w, tks (pad w) Zinf = tks w Zinf.
Proof.
  intros w. destruct (pad_cases w) as [E|E]; rewrite E; [reflexivity|].
  rewrite tks_app, pad8_ok. reflexivity.
Qed.

Definition xfinish (p : Pd) (w acc : list Tok) : option (list Tok) :=
  match p with
  | PE => Some (rev_append acc (pad w))
  | P10 => if allz w then Some (rev_append acc (tH :: pad8)) else None
  | _ => if allz w then Some (rev_append acc pad8) else None
  end.

Lemma xfinish_ok : forall p w acc res, xfinish p w acc = Some res ->
  exists w', res = rev_append acc w' /\ VS 0 (pd p (tks w Zinf)) (tks w' Zinf).
Proof.
  intros p w acc res H. unfold xfinish in H.
  destruct p.
  - destruct (allz w) eqn:E; [|discriminate]. injection H as <-.
    exists (tH :: pad8). split; [reflexivity|].
    rewrite (allz_ok _ E).
    change (tks (tH :: pad8) Zinf) with (tk tH (tks pad8 Zinf)).
    rewrite pad8_ok.
    replace (tk tH Zinf) with (S1 >> S0 >> Zinf).
    + apply VS_0.
    + simpl. rewrite <- !Zinf_unfold. reflexivity.
  - destruct (allz w) eqn:E; [|discriminate]. injection H as <-.
    exists pad8. split; [reflexivity|].
    rewrite (allz_ok _ E), pad8_ok. cbn [pd]. rewrite <- !Zinf_unfold. apply VS_0.
  - destruct (allz w) eqn:E; [|discriminate]. injection H as <-.
    exists pad8. split; [reflexivity|].
    rewrite (allz_ok _ E), pad8_ok. cbn [pd]. rewrite <- Zinf_unfold. apply VS_0.
  - injection H as <-. exists (pad w). split; [reflexivity|].
    rewrite pad_ok. apply VS_0.
Qed.

(* One round, exact count, the same as xstep with the matches written out for the VM. *)
Fixpoint xscan (f : nat) (p : Pd) (n : N) (w acc : list Tok) {struct f} : option (list Tok) :=
  match f with
  | O => None
  | S f =>
    match n with
    | N0 => xfinish p w acc
    | Npos _ =>
      match w with
      | [] => None
      | t :: w1 =>
        match p with
        | P10 =>
          match t with
          | tZ => if N.odd n then xscan f P00 (N.div2 (N.succ n)) w1 (tZ :: acc)
                  else xscan f P00 (N.div2 n) w1 (tH :: acc)
          | tH => xscan f P0 (N.double n) w1 (tL :: acc)
          | tL => xscan f P10 (N.double n) w1 (tL :: acc)
          end
        | P00 =>
          match t with
          | tZ => if N.odd n then xscan f P00 (N.div2 n) w1 (tH :: acc)
                  else xscan f P00 (N.div2 n) w1 (tZ :: acc)
          | tH => if N.leb 1 n then xscan f P0 (N.double (N.pred n)) w1 (tL :: acc) else None
          | tL => if N.leb 1 n then xscan f P10 (N.double (N.pred n)) w1 (tL :: acc) else None
          end
        | P0 =>
          match t with
          | tZ => if N.odd n then xscan f P0 (N.div2 n) w1 (tH :: acc)
                  else xscan f P0 (N.div2 n) w1 (tZ :: acc)
          | tH => if N.leb 3 n then xscan f PE (N.double (n - 3)) w1 (tL :: acc) else None
          | tL => if N.leb 4 n then
                    (if N.odd (n - 4) then xscan f P10 (N.div2 (n - 4)) w1 (tH :: acc)
                     else xscan f P10 (N.div2 (n - 4)) w1 (tZ :: acc))
                  else None
          end
        | PE =>
          match t with
          | tZ => if N.odd n then xscan f PE (N.div2 n) w1 (tH :: acc)
                  else xscan f PE (N.div2 n) w1 (tZ :: acc)
          | tH => if N.odd n then xscan f PE (N.div2 (N.succ n)) w1 (tZ :: acc)
                  else xscan f PE (N.div2 n) w1 (tH :: acc)
          | tL => xscan f PE (N.double n) w1 (tL :: acc)
          end
        end
      end
    end
  end.

Lemma xscan_unfold : forall f p q t w1 acc,
  xscan (S f) p (Npos q) (t :: w1) acc =
  match xstep p t (Npos q) with
  | Some (t', p', n') => xscan f p' n' w1 (t' :: acc)
  | None => None
  end.
Proof.
  intros f p q t w1 acc. unfold xstep. cbn [xscan].
  destruct p, t;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    end; reflexivity.
Qed.

Lemma xscan_ok : forall f p n w acc res, xscan f p n w acc = Some res ->
  exists w', res = rev_append acc w' /\ VS n (pd p (tks w Zinf)) (tks w' Zinf).
Proof.
  induction f as [|f IH]; intros p n w acc res H; [discriminate|].
  destruct n as [|q].
  - cbn [xscan] in H. exact (xfinish_ok _ _ _ _ H).
  - destruct w as [|t w1]; [discriminate|].
    rewrite xscan_unfold in H.
    destruct (xstep p t (Npos q)) as [[[t' p'] n']|] eqn:Hx; [|discriminate].
    destruct (IH _ _ _ _ _ H) as [w2 [Hr HV]].
    exists (t' :: w2). split; [exact Hr|].
    exact (xstep_ok _ _ _ _ _ _ Hx _ _ HV).
Qed.

(* Repeats. *)
Fixpoint rep (w : list Tok) (n : nat) (r : side) : side :=
  match n with
  | O => r
  | S n' => tks w (rep w n' r)
  end.

Lemma rep_shift : forall w n r, rep w n (tks w r) = tks w (rep w n r).
Proof. intros w. induction n as [|n IH]; intros r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma rep_add : forall w a b r, rep w (a + b) r = rep w a (rep w b r).
Proof. intros w. induction a as [|a IH]; intros b r; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

(* Powers. *)
Definition pw (w : nat) : N := 2 ^ N.of_nat w.

Lemma pw_0 : pw 0 = 1.
Proof. reflexivity. Qed.

Lemma pw_S w : pw (S w) = 2 * pw w.
Proof. unfold pw. rewrite Nat2N.inj_succ, N.pow_succ_r'. reflexivity. Qed.

Lemma pw_pos w : 0 < pw w.
Proof. unfold pw. apply N.neq_0_lt_0. apply N.pow_nonzero. lia. Qed.

Lemma pw_add a b : pw (a + b) = pw a * pw b.
Proof. unfold pw. rewrite Nat2N.inj_add, N.pow_add_r. reflexivity. Qed.

Lemma VS_rep_L : forall k n r r', VS (pw k * n) (pd P10 r) r' ->
  VS n (pd P10 (rep [tL] k r)) (rep [tL] k r').
Proof.
  induction k as [|k IH]; intros n r r' H.
  - rewrite pw_0, N.mul_1_l in H. exact H.
  - change (rep [tL] (S k) r) with (tk tL (rep [tL] k r)).
    change (rep [tL] (S k) r') with (tk tL (rep [tL] k r')).
    apply VS_L. apply IH.
    rewrite pw_S in H.
    replace (pw k * (2 * n)) with (2 * pw k * n) by lia. exact H.
Qed.

Lemma VS1_round : forall s s', VS 1 (pd P10 s) s' -> LE s -->+ LE s'.
Proof.
  intros s s' H.
  change 1 with (N.succ 0) in H.
  destruct (VS_inv _ _ _ H) as [s1 [H1 H2]].
  rewrite <- (VS_inv0 _ _ H2).
  apply round_step. exact H1.
Qed.

(* Rounds from the blank tape. *)
Fixpoint dropk (k : nat) (nk : N) (w : list Tok) : nat * N * list Tok :=
  match w with
  | tL :: w' => dropk (S k) (N.double nk) w'
  | _ => (k, nk, w)
  end.

Lemma dropk_ok : forall w k nk k' nk' w', dropk k nk w = (k', nk', w') -> nk = pw k ->
  nk' = pw k' /\ forall r, rep [tL] k (tks w r) = rep [tL] k' (tks w' r).
Proof.
  induction w as [|t w IH]; intros k nk k' nk' w' H Hn.
  - injection H as <- <- <-. split; [exact Hn|intros r; reflexivity].
  - destruct t; simpl in H.
    + injection H as <- <- <-. split; [exact Hn|intros r; reflexivity].
    + injection H as <- <- <-. split; [exact Hn|intros r; reflexivity].
    + destruct (IH _ _ _ _ _ H) as [H1 H2].
      { rewrite pw_S, Hn, N.double_spec. reflexivity. }
      split; [exact H1|]. intros r. rewrite <- H2.
      change (rep [tL] (S k) (tks w r)) with (tk tL (rep [tL] k (tks w r))).
      change (tks (tL :: w) r) with (tks [tL] (tks w r)).
      rewrite rep_shift. reflexivity.
Qed.

Fixpoint xrun (f r : nat) (k : nat) (nk : N) (w : list Tok) : option (nat * N * list Tok) :=
  match r with
  | O => Some (k, nk, w)
  | S r' =>
    match xscan f P10 nk w [] with
    | Some w1 =>
      let '(k1, nk1, w2) := dropk k nk w1 in
      xrun f r' k1 nk1 w2
    | None => None
    end
  end.

Lemma xrun_ok : forall r f k nk w k' nk' w', xrun f r k nk w = Some (k', nk', w') -> nk = pw k ->
  nk' = pw k' /\ LE (rep [tL] k (tks w Zinf)) -->* LE (rep [tL] k' (tks w' Zinf)).
Proof.
  induction r as [|r IH]; intros f k nk w k' nk' w' H Hn.
  - injection H as <- <- <-. split; [exact Hn|apply evstep_refl].
  - cbn [xrun] in H.
    destruct (xscan f P10 nk w []) as [w1|] eqn:Hs; [|discriminate].
    destruct (dropk k nk w1) as [[k1 nk1] w2] eqn:Hd.
    destruct (xscan_ok _ _ _ _ _ _ Hs) as [w3 [Hr HV]].
    simpl rev_append in Hr. subst w1.
    destruct (dropk_ok _ _ _ _ _ _ Hd Hn) as [Hn1 He].
    destruct (IH _ _ _ _ _ _ _ H Hn1) as [H1 H2].
    split; [exact H1|].
    eapply evstep_trans; [|exact H2].
    rewrite <- He.
    apply progress_evstep. apply VS1_round.
    apply VS_rep_L. rewrite N.mul_1_r, <- Hn. exact HV.
Qed.

(* One token, count 2^a x - c with x unknown. *)
Definition sstep (p : Pd) (t : Tok) (a : nat) (c : N) : option (Tok * Pd * nat * N) :=
  match p, t with
  | P10, tZ => match a with
               | O => None
               | S a' => if N.odd c then Some (tZ, P00, a', N.div2 c) else Some (tH, P00, a', N.div2 c)
               end
  | P10, tH => Some (tL, P0, S a, N.double c)
  | P10, tL => Some (tL, P10, S a, N.double c)
  | P00, tZ => match a with
               | O => None
               | S a' => if N.odd c then Some (tH, P00, a', N.div2 (N.succ c)) else Some (tZ, P00, a', N.div2 c)
               end
  | P00, tH => Some (tL, P0, S a, N.double (N.succ c))
  | P00, tL => Some (tL, P10, S a, N.double (N.succ c))
  | P0, tZ => match a with
              | O => None
              | S a' => if N.odd c then Some (tH, P0, a', N.div2 (N.succ c)) else Some (tZ, P0, a', N.div2 c)
              end
  | P0, tH => Some (tL, PE, S a, N.double (c + 3))
  | P0, tL => match a with
              | O => None
              | S a' => if N.odd (c + 4) then Some (tH, P10, a', N.div2 (N.succ (c + 4)))
                        else Some (tZ, P10, a', N.div2 (c + 4))
              end
  | PE, tZ => match a with
              | O => None
              | S a' => if N.odd c then Some (tH, PE, a', N.div2 (N.succ c)) else Some (tZ, PE, a', N.div2 c)
              end
  | PE, tH => match a with
              | O => None
              | S a' => if N.odd c then Some (tZ, PE, a', N.div2 c) else Some (tH, PE, a', N.div2 c)
              end
  | PE, tL => Some (tL, PE, S a, N.double c)
  end.

(* n = 2 Y - c, digit arithmetic. *)
Lemma ar_even : forall Y c, N.odd c = false -> N.div2 c < Y ->
  c < 2 * Y /\ N.odd (2 * Y - c) = false /\ N.div2 (2 * Y - c) = Y - N.div2 c.
Proof.
  intros Y c E H. destruct (double_or c) as [m [-> | ->]].
  - rewrite div2_double in *.
    replace (2 * Y - N.double m) with (N.double (Y - m)) by (rewrite !N.double_spec; lia).
    split; [rewrite N.double_spec; lia|].
    split; [apply odd_double|apply div2_double].
  - rewrite odd_succ_double in E. discriminate.
Qed.

Lemma ar_oddZ : forall Y c, N.odd c = true -> N.div2 (N.succ c) < Y ->
  c < 2 * Y /\ N.odd (2 * Y - c) = true /\ N.div2 (2 * Y - c) = Y - N.div2 (N.succ c).
Proof.
  intros Y c E H. destruct (double_or c) as [m [-> | ->]].
  - rewrite odd_double in E. discriminate.
  - rewrite succ_succ_double, div2_double in *.
    replace (2 * Y - N.succ_double m) with (N.succ_double (Y - N.succ m))
      by (rewrite !N.succ_double_spec; lia).
    split; [rewrite N.succ_double_spec; lia|].
    split; [apply odd_succ_double|apply div2_succ_double].
Qed.

Lemma ar_oddH : forall Y c, N.odd c = true -> N.div2 c < Y ->
  c < 2 * Y /\ N.odd (2 * Y - c) = true /\ N.div2 (N.succ (2 * Y - c)) = Y - N.div2 c.
Proof.
  intros Y c E H. destruct (double_or c) as [m [-> | ->]].
  - rewrite odd_double in E. discriminate.
  - rewrite div2_succ_double in *.
    replace (2 * Y - N.succ_double m) with (N.succ_double (Y - N.succ m))
      by (rewrite !N.succ_double_spec; lia).
    split; [rewrite N.succ_double_spec; lia|].
    split; [apply odd_succ_double|].
    rewrite succ_succ_double, div2_double. lia.
Qed.

Lemma pw_S_mul : forall a x, pw (S a) * x = 2 * (pw a * x).
Proof. intros a x. rewrite pw_S. lia. Qed.

Lemma ar_dbl : forall Y c, N.double c < 2 * Y -> c < Y /\ N.double (Y - c) = 2 * Y - N.double c.
Proof. intros Y c H. rewrite N.double_spec in *. lia. Qed.

Lemma sstep_x : forall p t a c t' p' a' c', sstep p t a c = Some (t', p', a', c') ->
  forall x, c' < pw a' * x ->
  c < pw a * x /\ xstep p t (pw a * x - c) = Some (t', p', pw a' * x - c').
Proof.
  intros p t a c t' p' a' c' H x Hc.
  destruct p, t; cbn [sstep] in H.
  - destruct a as [|a]; [discriminate|].
    destruct (N.odd c) eqn:E; injection H as <- <- <- <-; rewrite pw_S_mul; cbn [xstep].
    + destruct (ar_oddH _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
    + destruct (ar_even _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
  - injection H as <- <- <- <-. rewrite pw_S_mul in Hc. cbn [xstep].
    destruct (ar_dbl _ _ Hc) as [H1 H2]. split; [exact H1|]. rewrite pw_S_mul, H2. reflexivity.
  - injection H as <- <- <- <-. rewrite pw_S_mul in Hc. cbn [xstep].
    destruct (ar_dbl _ _ Hc) as [H1 H2]. split; [exact H1|]. rewrite pw_S_mul, H2. reflexivity.
  - destruct a as [|a]; [discriminate|].
    destruct (N.odd c) eqn:E; injection H as <- <- <- <-; rewrite pw_S_mul; cbn [xstep].
    + destruct (ar_oddZ _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
    + destruct (ar_even _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
  - injection H as <- <- <- <-. rewrite pw_S_mul in Hc. cbn [xstep].
    destruct (ar_dbl _ _ Hc) as [H1 H2].
    split; [lia|].
    replace (N.leb 1 (pw a * x - c)) with true by (symmetry; apply N.leb_le; lia).
    replace (N.pred (pw a * x - c)) with (pw a * x - N.succ c) by lia.
    rewrite pw_S_mul, H2. reflexivity.
  - injection H as <- <- <- <-. rewrite pw_S_mul in Hc. cbn [xstep].
    destruct (ar_dbl _ _ Hc) as [H1 H2].
    split; [lia|].
    replace (N.leb 1 (pw a * x - c)) with true by (symmetry; apply N.leb_le; lia).
    replace (N.pred (pw a * x - c)) with (pw a * x - N.succ c) by lia.
    rewrite pw_S_mul, H2. reflexivity.
  - destruct a as [|a]; [discriminate|].
    destruct (N.odd c) eqn:E; injection H as <- <- <- <-; rewrite pw_S_mul; cbn [xstep].
    + destruct (ar_oddZ _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
    + destruct (ar_even _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
  - injection H as <- <- <- <-. rewrite pw_S_mul in Hc. cbn [xstep].
    destruct (ar_dbl _ _ Hc) as [H1 H2].
    split; [lia|].
    replace (N.leb 3 (pw a * x - c)) with true by (symmetry; apply N.leb_le; lia).
    replace (pw a * x - c - 3) with (pw a * x - (c + 3)) by lia.
    rewrite pw_S_mul, H2. reflexivity.
  - destruct a as [|a]; [discriminate|].
    rewrite pw_S_mul. cbn [xstep].
    destruct (N.odd (c + 4)) eqn:E; injection H as <- <- <- <-.
    + destruct (ar_oddZ _ _ E Hc) as [H1 [H2 H3]].
      split; [lia|].
      replace (N.leb 4 (2 * (pw a * x) - c)) with true by (symmetry; apply N.leb_le; lia).
      replace (2 * (pw a * x) - c - 4) with (2 * (pw a * x) - (c + 4)) by lia.
      rewrite H2, H3. reflexivity.
    + destruct (ar_even _ _ E Hc) as [H1 [H2 H3]].
      split; [lia|].
      replace (N.leb 4 (2 * (pw a * x) - c)) with true by (symmetry; apply N.leb_le; lia).
      replace (2 * (pw a * x) - c - 4) with (2 * (pw a * x) - (c + 4)) by lia.
      rewrite H2, H3. reflexivity.
  - destruct a as [|a]; [discriminate|].
    destruct (N.odd c) eqn:E; injection H as <- <- <- <-; rewrite pw_S_mul; cbn [xstep].
    + destruct (ar_oddZ _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
    + destruct (ar_even _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
  - destruct a as [|a]; [discriminate|].
    destruct (N.odd c) eqn:E; injection H as <- <- <- <-; rewrite pw_S_mul; cbn [xstep].
    + destruct (ar_oddH _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
    + destruct (ar_even _ _ E Hc) as [H1 [H2 H3]]. split; [exact H1|]. rewrite H2, H3. reflexivity.
  - injection H as <- <- <- <-. rewrite pw_S_mul in Hc. cbn [xstep].
    destruct (ar_dbl _ _ Hc) as [H1 H2]. split; [exact H1|]. rewrite pw_S_mul, H2. reflexivity.
Qed.

(* A pass over a word: for every x and every stream below. *)
Definition PassP (w w' : list Tok) (p p' : Pd) (a a' : nat) (c c' : N) : Prop :=
  forall x r r', c' < pw a' * x -> VS (pw a' * x - c') (pd p' r) r' ->
    c < pw a * x /\ VS (pw a * x - c) (pd p (tks w r)) (tks w' r').

Fixpoint spass (w : list Tok) (p : Pd) (a : nat) (c : N) (acc : list Tok) {struct w}
  : option (list Tok * Pd * nat * N) :=
  match w with
  | [] => Some (acc, p, a, c)
  | t :: w1 =>
    match p with
    | P10 =>
      match t with
      | tZ => match a with
              | O => None
              | S a' => if N.odd c then spass w1 P00 a' (N.div2 c) (tZ :: acc)
                        else spass w1 P00 a' (N.div2 c) (tH :: acc)
              end
      | tH => spass w1 P0 (S a) (N.double c) (tL :: acc)
      | tL => spass w1 P10 (S a) (N.double c) (tL :: acc)
      end
    | P00 =>
      match t with
      | tZ => match a with
              | O => None
              | S a' => if N.odd c then spass w1 P00 a' (N.div2 (N.succ c)) (tH :: acc)
                        else spass w1 P00 a' (N.div2 c) (tZ :: acc)
              end
      | tH => spass w1 P0 (S a) (N.double (N.succ c)) (tL :: acc)
      | tL => spass w1 P10 (S a) (N.double (N.succ c)) (tL :: acc)
      end
    | P0 =>
      match t with
      | tZ => match a with
              | O => None
              | S a' => if N.odd c then spass w1 P0 a' (N.div2 (N.succ c)) (tH :: acc)
                        else spass w1 P0 a' (N.div2 c) (tZ :: acc)
              end
      | tH => spass w1 PE (S a) (N.double (c + 3)) (tL :: acc)
      | tL => match a with
              | O => None
              | S a' => if N.odd (c + 4) then spass w1 P10 a' (N.div2 (N.succ (c + 4))) (tH :: acc)
                        else spass w1 P10 a' (N.div2 (c + 4)) (tZ :: acc)
              end
      end
    | PE =>
      match t with
      | tZ => match a with
              | O => None
              | S a' => if N.odd c then spass w1 PE a' (N.div2 (N.succ c)) (tH :: acc)
                        else spass w1 PE a' (N.div2 c) (tZ :: acc)
              end
      | tH => match a with
              | O => None
              | S a' => if N.odd c then spass w1 PE a' (N.div2 c) (tZ :: acc)
                        else spass w1 PE a' (N.div2 c) (tH :: acc)
              end
      | tL => spass w1 PE (S a) (N.double c) (tL :: acc)
      end
    end
  end.

Lemma spass_unfold : forall t w1 p a c acc,
  spass (t :: w1) p a c acc =
  match sstep p t a c with
  | Some (t', p', a', c') => spass w1 p' a' c' (t' :: acc)
  | None => None
  end.
Proof.
  intros t w1 p a c acc. unfold sstep. cbn [spass].
  destruct p, t; try reflexivity; destruct a as [|a]; try reflexivity;
    match goal with
    | |- context [if ?b then _ else _] => destruct b
    end; reflexivity.
Qed.

Lemma spass_ok : forall w p a c acc res p' a' c', spass w p a c acc = Some (res, p', a', c') ->
  exists w', res = rev_append w' acc /\ PassP w w' p p' a a' c c'.
Proof.
  induction w as [|t w1 IH]; intros p a c acc res p' a' c' H.
  - cbn [spass] in H. injection H as <- <- <- <-.
    exists (@nil Tok). split; [reflexivity|]. intros x r r' Hc HV. split; assumption.
  - rewrite spass_unfold in H.
    destruct (sstep p t a c) as [[[[t' p1] a1] c1]|] eqn:Hs; [|discriminate].
    destruct (IH _ _ _ _ _ _ _ _ H) as [w2 [Hr HP]].
    exists (t' :: w2). split.
    + rewrite Hr. rewrite !rev_append_rev. simpl. rewrite <- app_assoc. reflexivity.
    + intros x r r' Hc HV.
      destruct (HP x r r' Hc HV) as [H1 H2].
      destruct (sstep_x _ _ _ _ _ _ _ _ Hs x H1) as [H3 H4].
      split; [exact H3|].
      exact (xstep_ok _ _ _ _ _ _ H4 _ _ H2).
Qed.

Definition rv (l : list Tok) : list Tok := rev_append l [].

Lemma spass_nil : forall w p a c res p' a' c', spass w p a c [] = Some (res, p', a', c') ->
  PassP w (rv res) p p' a a' c c'.
Proof.
  intros w p a c res p' a' c' H.
  destruct (spass_ok _ _ _ _ _ _ _ _ _ H) as [w2 [Hr HP]].
  subst res. unfold rv.
  replace (rev_append (rev_append w2 []) []) with w2; [exact HP|].
  rewrite !rev_append_rev, !app_nil_r, rev_involutive. reflexivity.
Qed.

Definition pass (w : list Tok) (p : Pd) (a : nat) (c : N) : option (list Tok * Pd * nat * N) :=
  match spass w p a c [] with
  | Some (res, p', a', c') => Some (rv res, p', a', c')
  | None => None
  end.

Lemma pass_ok : forall w p a c w' p' a' c', pass w p a c = Some (w', p', a', c') ->
  PassP w w' p p' a a' c c'.
Proof.
  intros w p a c w' p' a' c' H. unfold pass in H.
  destruct (spass w p a c []) as [[[[res p1] a1] c1]|] eqn:Hs; [|discriminate].
  injection H as <- <- <- <-.
  exact (spass_nil _ _ _ _ _ _ _ _ Hs).
Qed.

(* The nested zone: B^t C D^t. *)
Fixpoint zone (B C D : list Tok) (t : nat) (r : side) : side :=
  match t with
  | O => tks C r
  | S t' => tks B (zone B C D t' (tks D r))
  end.

Lemma ar_layer : forall B0 Q x k e, 0 < B0 -> B0 * k + e < (B0 * Q) * x ->
  k < Q * x /\ e < B0 * (Q * x - k) /\ (B0 * Q) * x - (B0 * k + e) = B0 * (Q * x - k) - e.
Proof.
  intros B0 Q x k e HB H.
  rewrite <- N.mul_assoc in *.
  assert (Hk : k < Q * x).
  { destruct (N.le_gt_cases (Q * x) k) as [H1|H1]; [|lia].
    apply (N.mul_le_mono_l _ _ B0) in H1. lia. }
  assert (Hk2 : B0 * k < B0 * (Q * x)).
  { exact (proj1 (N.mul_lt_mono_pos_l B0 k (Q * x) HB) Hk). }
  rewrite N.mul_sub_distr_l.
  split; [exact Hk|]. lia.
Qed.

Lemma zone_ok : forall B C D B' C' D' p W Dl b cin cout k e,
  PassP B B' p p W (W + Dl) cin cout -> cout = cin + pw W * k ->
  PassP C C' p PE W b cin e ->
  PassP D D' PE PE (b + Dl) b (pw b * k + e) e ->
  forall t x r r', e < pw b * x -> VS (pw b * x - e) r r' ->
    cin < pw W * x /\ VS (pw W * x - cin) (pd p (zone B C D t r)) (zone B' C' D' t r').
Proof.
  intros B C D B' C' D' p W Dl b cin cout k e HB Ho HC HD.
  induction t as [|t IH]; intros x r r' He HV.
  - exact (HC x r r' He HV).
  - destruct (HD x r r' He HV) as [H1 H2].
    cbn [pd] in H2.
    rewrite pw_add in H1, H2.
    destruct (ar_layer _ _ _ _ _ (pw_pos b) H1) as [Hk [He1 Hq]].
    rewrite Hq in H2.
    destruct (IH (pw Dl * x - k) (tks D r) (tks D' r') He1 H2) as [H3 H4].
    (* the pass over B *)
    assert (Hc : cout < pw (W + Dl) * x).
    { rewrite Ho, pw_add, <- N.mul_assoc.
      rewrite N.mul_sub_distr_l in H3.
      assert (pw W * k <= pw W * (pw Dl * x)).
      { apply N.mul_le_mono_l. lia. }
      lia. }
    assert (Heq : pw (W + Dl) * x - cout = pw W * (pw Dl * x - k) - cin).
    { rewrite Ho, pw_add, <- N.mul_assoc.
      rewrite N.mul_sub_distr_l.
      assert (pw W * k <= pw W * (pw Dl * x)).
      { apply N.mul_le_mono_l. lia. }
      lia. }
    rewrite <- Heq in H4.
    exact (HB x _ _ Hc H4).
Qed.

(* The tail. *)
Definition TT : list Tok := [tH; tZ; tZ; tZ].

Lemma VS_TT : forall m r r', VS m r r' -> VS (16 * m) (tks TT r) (tks TT r').
Proof.
  intros m r r' H.
  replace (16 * m) with (2 * (2 * (2 * (2 * m)))) by lia.
  apply (VS_HH _ (tks [tZ;tZ;tZ] r) (tks [tZ;tZ;tZ] r')).
  apply (VS_ZZ _ (tks [tZ;tZ] r) (tks [tZ;tZ] r')).
  apply (VS_ZZ _ (tks [tZ] r) (tks [tZ] r')).
  apply (VS_ZZ _ r r').
  exact H.
Qed.

Local Open Scope nat_scope.

Lemma pw_4S : forall v, pw (4 * S v) = (16 * pw (4 * v))%N.
Proof.
  intros v. replace (4 * S v) with (S (S (S (S (4 * v))))) by lia.
  rewrite !pw_S. lia.
Qed.

Lemma VS_T_gen : forall v m R R', VS m R R' -> VS (pw (4 * v) * m)%N (rep TT v R) (rep TT v R').
Proof.
  induction v as [|v IH]; intros m R R' H.
  - replace (4 * 0) with 0 by lia. rewrite pw_0, N.mul_1_l. exact H.
  - rewrite pw_4S. rewrite <- N.mul_assoc.
    cbn [rep]. apply VS_TT. apply IH. exact H.
Qed.

Lemma VS_T : forall v, VS (pw (4 * v)) (rep TT v Zinf) (rep TT (S v) Zinf).
Proof.
  intros v.
  rewrite <- (N.mul_1_r (pw (4 * v))).
  change (rep TT (S v) Zinf) with (tks TT (rep TT v Zinf)).
  rewrite <- rep_shift.
  apply VS_T_gen.
  apply VS_1.
  replace (tks TT Zinf) with (S1 >> Zinf).
  - rewrite Zinf_unfold at 1. apply vis_0.
  - simpl. rewrite <- !Zinf_unfold. reflexivity.
Qed.

(* The configurations of the cycle. *)
Definition St : Type := (nat * list Tok * list Tok * list Tok * list Tok * list Tok * nat)%type.

Definition hh : nat := 3848.
Definition tv : nat := 962.

Definition sw (st : St) (t : nat) : side :=
  let '(k, wA, wB, wC, wD, wE, v) := st in
  rep [tL] (k + hh * t) (tks wA (zone wB wC wD t (tks wE (rep TT (v + tv * t) Zinf)))).

Fixpoint lowhi (W : nat) (c : N) : N * N :=
  match W with
  | O => (0%N, c)
  | S W' =>
    let '(l, h) := lowhi W' (N.div2 c) in
    (if N.odd c then N.succ_double l else N.double l, h)
  end.

Lemma lowhi_ok : forall W c l h, lowhi W c = (l, h) -> c = (l + pw W * h)%N.
Proof.
  induction W as [|W IH]; intros c l h H.
  - injection H as <- <-. rewrite pw_0. lia.
  - cbn [lowhi] in H.
    destruct (lowhi W (N.div2 c)) as [l1 h1] eqn:E.
    injection H as <- <-.
    pose proof (IH _ _ _ E) as H1.
    rewrite pw_S.
    destruct (double_or c) as [m [-> | ->]].
    + rewrite odd_double. rewrite div2_double in H1. rewrite H1, !N.double_spec. lia.
    + rewrite odd_succ_double. rewrite div2_succ_double in H1. rewrite H1, !N.succ_double_spec. lia.
Qed.

Fixpoint mul2k (k : nat) (c : N) : N :=
  match k with
  | O => c
  | S k' => mul2k k' (N.double c)
  end.

Lemma mul2k_ok : forall k c, mul2k k c = (pw k * c)%N.
Proof.
  induction k as [|k IH]; intros c.
  - rewrite pw_0, N.mul_1_l. reflexivity.
  - cbn [mul2k]. rewrite IH, pw_S, N.double_spec. lia.
Qed.

Definition Pd_eqb (a b : Pd) : bool :=
  match a, b with
  | P10, P10 | P00, P00 | P0, P0 | PE, PE => true
  | _, _ => false
  end.

Lemma Pd_eqb_ok : forall a b, Pd_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

(* Tokens after the last L, in a reversed word. *)
Fixpoint cntd (acc : nat) (w : list Tok) : nat :=
  match w with
  | tL :: _ => acc
  | _ :: w' => cntd (S acc) w'
  | [] => acc
  end.

Definition tok_eqb (a b : Tok) : bool :=
  match a, b with
  | tZ, tZ | tH, tH | tL, tL => true
  | _, _ => false
  end.

Lemma tok_eqb_ok : forall a b, tok_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

Fixpoint tl_eqb (a b : list Tok) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if tok_eqb x y then tl_eqb a' b' else false
  | _, _ => false
  end.

Lemma tl_eqb_ok : forall a b, tl_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros b H; destruct b as [|y b]; simpl in H; try discriminate; [reflexivity|].
  destruct (tok_eqb x y) eqn:E; [|discriminate].
  rewrite (tok_eqb_ok _ _ E), (IH _ H). reflexivity.
Qed.

(* Sizes of the counts and of the cuts. The lemmas hold for any values; the run in check_run needs these. *)
Definition W : nat := 64.
Definition K0 : nat := 64.
Definition GG : nat := 40.
Definition ylen : nat := 16.
Definition ulen : nat := 8.

Local Notation "a &&& b" := (andb a b) (at level 40, left associativity).

(* One round with x unknown. *)
Definition core (k : nat) (A B C D E : list Tok) (v : nat)
  : option (list Tok * list Tok * list Tok * list Tok * list Tok * nat) :=
  match pass A P10 K0 0%N with
  | Some (A1, p, a1, cA) =>
    let '(cin, kA) := lowhi W cA in
    match pass B p W cin with
    | Some (B1, p2, a2, cout) =>
      let '(cin2, kp) := lowhi W cout in
      let Dl := a2 - W in
      match spass C p W cin [] with
      | Some (rC, PE, b, e) =>
        match pass D PE (b + Dl) (mul2k b kp + e)%N with
        | Some (D1, PE, b2, e2) =>
          match pass E PE (b + (a1 - W) + (k - K0)) (mul2k b kA + e)%N with
          | Some (E1, PE, a3, c3) =>
            if Pd_eqb p2 p &&& N.eqb cin2 cin &&& Nat.leb W a2 &&& Nat.eqb b2 b &&& N.eqb e2 e
               &&& N.eqb c3 0 &&& Nat.eqb a3 (4 * v) &&& Nat.leb W a1 &&& Nat.leb K0 k
            then Some (A1, B1, rv rC, D1, E1, cntd 0 rC)
            else None
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | None => None
    end
  | None => None
  end.

Lemma ar_top : forall P Q0 kA cin, (0 < P)%N -> (cin < P * (Q0 - kA))%N -> (kA < Q0)%N ->
  (cin + P * kA < P * Q0)%N /\ (P * Q0 - (cin + P * kA) = P * (Q0 - kA) - cin)%N.
Proof.
  intros P Q0 kA cin HP H1 H2.
  rewrite N.mul_sub_distr_l in *.
  assert (P * kA <= P * Q0)%N by (apply N.mul_le_mono_l; lia).
  lia.
Qed.

Lemma core_ok : forall k A B C D E v A1 B1 C1 D1 E1 g,
  core k A B C D E v = Some (A1, B1, C1, D1, E1, g) ->
  forall t, VS (pw (k + hh * t))
    (pd P10 (tks A (zone B C D t (tks E (rep TT (v + tv * t) Zinf)))))
    (tks A1 (zone B1 C1 D1 t (tks E1 (rep TT (S (v + tv * t)) Zinf)))).
Proof.
  intros k A B C D E v A1' B1' C1' D1' E1' g H t.
  unfold core in H.
  destruct (pass A P10 K0 0%N) as [[[[A1 p] a1] cA]|] eqn:HA; [|discriminate].
  cbv beta iota zeta in H.
  destruct (lowhi W cA) as [cin kA] eqn:HlA.
  cbv beta iota zeta in H.
  destruct (pass B p W cin) as [[[[B1 p2] a2] cout]|] eqn:HB; [|discriminate].
  cbv beta iota zeta in H.
  destruct (lowhi W cout) as [cin2 kp] eqn:HlB.
  cbv beta iota zeta in H.
  destruct (spass C p W cin []) as [[[[rC [| | |]] b] e]|] eqn:HC; try discriminate.
  cbv beta iota zeta in H.
  destruct (pass D PE (b + (a2 - W)) (mul2k b kp + e)%N) as [[[[D1 [| | |]] b2] e2]|] eqn:HD; try discriminate.
  cbv beta iota zeta in H.
  destruct (pass E PE (b + (a1 - W) + (k - K0)) (mul2k b kA + e)%N) as [[[[E1 [| | |]] a3] c3]|] eqn:HE; try discriminate.
  cbv beta iota zeta in H.
  destruct (Pd_eqb p2 p &&& N.eqb cin2 cin &&& Nat.leb W a2 &&& Nat.eqb b2 b &&& N.eqb e2 e
            &&& N.eqb c3 0 &&& Nat.eqb a3 (4 * v) &&& Nat.leb W a1 &&& Nat.leb K0 k) eqn:Hk; [|discriminate].
  injection H as <- <- <- <- <- _.
  repeat (apply andb_prop in Hk; destruct Hk as [Hk ?]).
  rename H into Hk9, H0 into Hk8, H1 into Hk7, H2 into Hk6, H3 into Hk5, H4 into Hk4, H5 into Hk3, H6 into Hk2.
  apply Pd_eqb_ok in Hk. subst p2.
  apply N.eqb_eq in Hk2. subst cin2.
  apply Nat.leb_le in Hk3.
  apply Nat.eqb_eq in Hk4. subst b2.
  apply N.eqb_eq in Hk5. subst e2.
  apply N.eqb_eq in Hk6. subst c3.
  apply Nat.eqb_eq in Hk7. subst a3.
  apply Nat.leb_le in Hk8.
  apply Nat.leb_le in Hk9.
  pose proof (pass_ok _ _ _ _ _ _ _ _ HA) as PA.
  pose proof (pass_ok _ _ _ _ _ _ _ _ HB) as PB.
  pose proof (spass_nil _ _ _ _ _ _ _ _ HC) as PC.
  pose proof (pass_ok _ _ _ _ _ _ _ _ HD) as PD.
  pose proof (pass_ok _ _ _ _ _ _ _ _ HE) as PE'.
  pose proof (lowhi_ok _ _ _ _ HlA) as EA.
  pose proof (lowhi_ok _ _ _ _ HlB) as EB.
  rewrite !mul2k_ok in *.
  replace a2 with (W + (a2 - W)) in PB by lia.
  (* the tail *)
  set (zy := pw (hh * t)).
  set (R := tks E (rep TT (v + tv * t) Zinf)).
  set (R' := tks E1 (rep TT (S (v + tv * t)) Zinf)).
  assert (HT : VS (pw (4 * v) * zy - 0)%N (pd PE (rep TT (v + tv * t) Zinf)) (rep TT (S (v + tv * t)) Zinf)).
  { replace (pw (4 * v) * zy - 0)%N with (pw (4 * (v + tv * t))).
    - exact (VS_T (v + tv * t)).
    - unfold zy. rewrite N.sub_0_r, <- pw_add. f_equal. unfold hh, tv. lia. }
  assert (Hz : (0 < pw (4 * v) * zy)%N).
  { apply N.mul_pos_pos; apply pw_pos. }
  destruct (PE' zy _ _ Hz HT) as [H1 H2].
  cbn [pd] in H2.
  (* into the zone *)
  set (y := (pw (k - K0) * zy)%N).
  set (Q0 := (pw (a1 - W) * y)%N).
  assert (Ea : (pw (b + (a1 - W) + (k - K0)) * zy = pw b * Q0)%N).
  { unfold Q0, y. rewrite !pw_add. ring. }
  rewrite Ea in H1, H2.
  destruct (ar_layer (pw b) 1 Q0 kA e (pw_pos b)) as [H3 [H4 H5]].
  { rewrite N.mul_1_r. exact H1. }
  rewrite N.mul_1_l in H3, H4, H5. rewrite N.mul_1_r in H5.
  rewrite H5 in H2.
  destruct (zone_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ PB EB PC PD t (Q0 - kA) _ _ H4 H2) as [H6 H7].
  (* the pass over A *)
  destruct (ar_top (pw W) Q0 kA cin (pw_pos W) H6 H3) as [H8 H9].
  assert (Eb : (pw a1 * y = pw W * Q0)%N).
  { unfold Q0. rewrite N.mul_assoc, <- pw_add. f_equal. f_equal. lia. }
  assert (Hc : (cA < pw a1 * y)%N) by (rewrite Eb, EA; exact H8).
  assert (Hv : VS (pw a1 * y - cA)%N (pd p (zone B C D t R)) (zone B1 (rv rC) D1 t R')).
  { rewrite Eb, EA, H9. exact H7. }
  destruct (PA y _ _ Hc Hv) as [_ H10].
  rewrite N.sub_0_r in H10.
  replace (pw (k + hh * t)) with (pw K0 * y)%N.
  - exact H10.
  - unfold y, zy. rewrite N.mul_assoc, <- !pw_add. f_equal. lia.
Qed.

Lemma sw_eq : forall k A B C D E v t, sw (k, A, B, C, D, E, v) t =
  rep [tL] (k + hh * t) (tks A (zone B C D t (tks E (rep TT (v + tv * t) Zinf)))).
Proof. reflexivity. Qed.

(* Leading L tokens go to the left part. *)
Fixpoint dropL (k : nat) (w : list Tok) : nat * list Tok :=
  match w with
  | tL :: w' => dropL (S k) w'
  | _ => (k, w)
  end.

Lemma dropL_ok : forall w k k' w', dropL k w = (k', w') ->
  k' >= k /\ (forall r, rep [tL] k (tks w r) = rep [tL] k' (tks w' r)) /\ exists d, k' = k + d.
Proof.
  induction w as [|t w IH]; intros k k' w' H.
  - injection H as <- <-. split; [lia|]. split; [intros r; reflexivity|]. exists 0. lia.
  - destruct t; simpl in H.
    + injection H as <- <-. split; [lia|]. split; [intros r; reflexivity|]. exists 0. lia.
    + injection H as <- <-. split; [lia|]. split; [intros r; reflexivity|]. exists 0. lia.
    + destruct (IH _ _ _ H) as [H1 [H2 [d H3]]].
      split; [lia|]. split.
      * intros r. rewrite <- H2.
        change (rep [tL] (S k) (tks w r)) with (tk tL (rep [tL] k (tks w r))).
        change (tks (tL :: w) r) with (tks [tL] (tks w r)).
        rewrite rep_shift. reflexivity.
      * exists (S d). lia.
Qed.

Lemma rep_L_add : forall a b r, rep [tL] (a + b) r = rep [tL] a (rep [tL] b r).
Proof. intros. apply rep_add. Qed.

(* Move ylen tokens from the digit block to the middle word, when it runs short after the last L. *)
Definition ycut (C D E : list Tok) (g : nat) : option (list Tok * list Tok * list Tok) :=
  if Nat.ltb g GG then
    let y := firstn ylen D in
    if tl_eqb (firstn ylen E) y then
      Some (C ++ y, skipn ylen D ++ y, skipn ylen E)
    else None
  else Some (C, D, E).

Lemma zone_y : forall B C y z t R,
  zone B C (y ++ z) t (tks y R) = zone B (C ++ y) (z ++ y) t R.
Proof.
  intros B C y z. induction t as [|t IH]; intros R.
  - simpl. rewrite tks_app. reflexivity.
  - cbn [zone]. f_equal. rewrite <- IH. f_equal.
    rewrite !tks_app. reflexivity.
Qed.

Lemma ycut_ok : forall B C D E g C' D' E', ycut C D E g = Some (C', D', E') ->
  forall t R, zone B C D t (tks E R) = zone B C' D' t (tks E' R).
Proof.
  intros B C D E g C' D' E' H t R. unfold ycut in H. cbv zeta in H.
  destruct (Nat.ltb g GG).
  - destruct (tl_eqb (firstn ylen E) (firstn ylen D)) eqn:Ht; [|discriminate].
    injection H as <- <- <-.
    apply tl_eqb_ok in Ht.
    set (y := firstn ylen D) in *.
    assert (ED : D = y ++ skipn ylen D) by (symmetry; apply firstn_skipn).
    assert (EE : E = y ++ skipn ylen E) by (rewrite <- Ht; symmetry; apply firstn_skipn).
    rewrite EE at 1. rewrite tks_app.
    rewrite ED at 1. rewrite zone_y. reflexivity.
  - injection H as <- <- <-. reflexivity.
Qed.

Definition round (st : St) : option St :=
  let '(k, wA, wB, wC, wD, wE, v) := st in
  match core k wA wB wC wD wE v with
  | Some (A1, B1, C1, D1, E1, g) =>
    let '(k2, A2) := dropL k A1 in
    match ycut C1 D1 (E1 ++ TT) g with
    | Some (C2, D2, E2) => Some (k2, A2, B1, C2, D2, E2, v)
    | None => None
    end
  | None => None
  end.

Lemma round_ok : forall st st', round st = Some st' -> forall t, LE (sw st t) -->+ LE (sw st' t).
Proof.
  intros [[[[[[k A] B] C] D] E] v] st' H t. unfold round in H. cbv beta iota zeta in H.
  destruct (core k A B C D E v) as [[[[[[A1 B1] C1] D1] E1] g]|] eqn:Hc; [|discriminate].
  cbv beta iota zeta in H.
  destruct (dropL k A1) as [k2 A2] eqn:Hd.
  cbv beta iota zeta in H.
  destruct (ycut C1 D1 (E1 ++ TT) g) as [[[C2 D2] E2]|] eqn:Hy; [|discriminate].
  injection H as <-.
  pose proof (core_ok _ _ _ _ _ _ _ _ _ _ _ _ _ Hc t) as HV.
  destruct (dropL_ok _ _ _ _ Hd) as [_ [Hr [d Hk]]].
  rewrite !sw_eq.
  (* the new tape *)
  assert (Ex : rep [tL] (k2 + hh * t) (tks A2 (zone B1 C2 D2 t (tks E2 (rep TT (v + tv * t) Zinf)))) =
               rep [tL] (k + hh * t) (tks A1 (zone B1 C1 D1 t (tks E1 (rep TT (S (v + tv * t)) Zinf))))).
  { rewrite <- (ycut_ok B1 _ _ _ _ _ _ _ Hy).
    rewrite tks_app.
    change (tks TT (rep TT (v + tv * t) Zinf)) with (rep TT (S (v + tv * t)) Zinf).
    replace (k2 + hh * t) with (hh * t + k2) by lia.
    replace (k + hh * t) with (hh * t + k) by lia.
    rewrite !rep_L_add.
    rewrite <- Hr. reflexivity. }
  rewrite Ex.
  apply VS1_round. apply VS_rep_L.
  rewrite N.mul_1_r. exact HV.
Qed.

(* Move ulen tokens from the head of the block to the end of the word before it. *)
Definition ucut (st : St) : option St :=
  let '(k, wA, wB, wC, wD, wE, v) := st in
  let u := firstn ulen wB in
  if tl_eqb (firstn ulen wC) u then
    Some (k, wA ++ u, skipn ulen wB ++ u, skipn ulen wC, wD, wE, v)
  else None.

Lemma zone_u : forall u v0 C' D t R,
  zone (u ++ v0) (u ++ C') D t R = tks u (zone (v0 ++ u) C' D t R).
Proof.
  intros u v0 C' D. induction t as [|t IH]; intros R.
  - simpl. rewrite tks_app. reflexivity.
  - cbn [zone]. rewrite IH. rewrite !tks_app. reflexivity.
Qed.

Lemma ucut_ok : forall st st', ucut st = Some st' -> forall t, sw st t = sw st' t.
Proof.
  intros [[[[[[k A] B] C] D] E] v] st' H t. unfold ucut in H. cbv beta iota zeta in H.
  destruct (tl_eqb (firstn ulen C) (firstn ulen B)) eqn:Ht; [|discriminate].
  injection H as <-.
  apply tl_eqb_ok in Ht.
  rewrite !sw_eq. f_equal.
  set (u := firstn ulen B) in *.
  assert (EB : B = u ++ skipn ulen B) by (symmetry; apply firstn_skipn).
  assert (EC : C = u ++ skipn ulen C) by (rewrite <- Ht; symmetry; apply firstn_skipn).
  rewrite tks_app. f_equal.
  rewrite EB at 1. rewrite EC at 1.
  apply zone_u.
Qed.

Fixpoint rounds (n : nat) (st : St) : option St :=
  match n with
  | O => Some st
  | S n' =>
    match round st with
    | Some s => rounds n' s
    | None => None
    end
  end.

Lemma rounds_ok : forall n st st', rounds n st = Some st' ->
  forall t, LE (sw st t) -->* LE (sw st' t).
Proof.
  induction n as [|n IH]; intros st st' H t.
  - injection H as <-. apply evstep_refl.
  - cbn [rounds] in H.
    destruct (round st) as [s|] eqn:Hr; [|discriminate].
    eapply evstep_trans; [apply progress_evstep; exact (round_ok _ _ Hr t)|].
    exact (IH _ _ H t).
Qed.

Lemma rounds_ok1 : forall n st st', rounds (S n) st = Some st' ->
  forall t, LE (sw st t) -->+ LE (sw st' t).
Proof.
  intros n st st' H t. cbn [rounds] in H.
  destruct (round st) as [s|] eqn:Hr; [|discriminate].
  eapply progress_evstep_trans; [exact (round_ok _ _ Hr t)|].
  exact (rounds_ok _ _ _ H t).
Qed.

Fixpoint cyc (n : nat) (st : St) : option St :=
  match n with
  | O => Some st
  | S n' =>
    match rounds 16 st with
    | Some s =>
      match ucut s with
      | Some s2 => cyc n' s2
      | None => None
      end
    | None => None
    end
  end.

Lemma cyc_ok : forall n st st', cyc n st = Some st' -> forall t, LE (sw st t) -->* LE (sw st' t).
Proof.
  induction n as [|n IH]; intros st st' H t.
  - injection H as <-. apply evstep_refl.
  - cbn [cyc] in H.
    destruct (rounds 16 st) as [s|] eqn:Hr; [|discriminate].
    destruct (ucut s) as [s2|] eqn:Hu; [|discriminate].
    eapply evstep_trans; [exact (rounds_ok _ _ _ Hr t)|].
    rewrite (ucut_ok _ _ Hu t).
    exact (IH _ _ H t).
Qed.

Lemma cyc_ok1 : forall n st st', cyc (S n) st = Some st' -> forall t, LE (sw st t) -->+ LE (sw st' t).
Proof.
  intros n st st' H t. cbn [cyc] in H.
  destruct (rounds 16 st) as [s|] eqn:Hr; [|discriminate].
  destruct (ucut s) as [s2|] eqn:Hu; [|discriminate].
  eapply progress_evstep_trans; [exact (rounds_ok1 _ _ _ Hr t)|].
  rewrite (ucut_ok _ _ Hu t).
  exact (cyc_ok _ _ _ H t).
Qed.

(* The closure. *)
Fixpoint Tlist (n : nat) : list Tok :=
  match n with
  | O => []
  | S n' => TT ++ Tlist n'
  end.

Lemma Tlist_ok : forall n r, tks (Tlist n) r = rep TT n r.
Proof.
  induction n as [|n IH]; intros r; [reflexivity|].
  change (Tlist (S n)) with (TT ++ Tlist n). rewrite tks_app, IH. reflexivity.
Qed.

Lemma zone_shift : forall B C D t R, zone B (B ++ C) D t R = tks B (zone B C D t R).
Proof.
  intros B C D. induction t as [|t IH]; intros R.
  - simpl. rewrite tks_app. reflexivity.
  - cbn [zone]. rewrite IH. reflexivity.
Qed.

Lemma closure : forall k A B C D E v t,
  sw (k + hh, A, B, B ++ C, D, D ++ E ++ Tlist tv, v) t = sw (k, A, B, C, D, E, v) (S t).
Proof.
  intros k A B C D E v t. rewrite !sw_eq.
  replace (k + hh + hh * t) with (k + hh * S t) by (unfold hh; lia).
  f_equal. f_equal.
  rewrite zone_shift. cbn [zone]. f_equal. f_equal.
  rewrite !tks_app, Tlist_ok. f_equal. f_equal.
  rewrite <- rep_add. f_equal. unfold tv. lia.
Qed.

(* Words equal up to blanks at the end. *)
Fixpoint eqz (a b : list Tok) : bool :=
  match a, b with
  | [], _ => allz b
  | _, [] => allz a
  | x :: a', y :: b' => if tok_eqb x y then eqz a' b' else false
  end.

Lemma eqz_ok : forall a b, eqz a b = true -> tks a Zinf = tks b Zinf.
Proof.
  induction a as [|x a IH]; intros b H.
  - simpl in H. rewrite (allz_ok _ H). reflexivity.
  - destruct b as [|y b].
    + rewrite (allz_ok (x :: a) H). reflexivity.
    + simpl in H. destruct (tok_eqb x y) eqn:E; [|discriminate].
      rewrite (tok_eqb_ok _ _ E). simpl. rewrite (IH _ H). reflexivity.
Qed.

(* The whole check. rs and per are run lengths of the exact run, 481 blocks of 16 rounds make one period; the others say where to cut the words. f is fuel for one scan. *)
Definition rs : nat := 26128.
Definition per : nat := 7696.
Definition lenA : nat := 63857.
Definition lenC : nat := 108.
Definition lenE : nat := 14413.
Definition lenB : nat := 18552.
Definition lenD : nat := 4536.
Definition v0 : nat := 3264.

Definition check (f : nat) : bool :=
  match xrun f rs 0 1%N (tH :: pad8) with
  | Some (k0, n0, Ws) =>
    match xrun f per k0 n0 Ws with
    | Some (_, _, Wp) =>
      let A0 := firstn lenA Ws in
      let Ws1 := skipn lenA Ws in
      let C0 := firstn lenC Ws1 in
      let Ws2 := skipn lenC Ws1 in
      let E0 := firstn lenE Ws2 in
      let Wp1 := skipn lenA Wp in
      let B0 := firstn lenB Wp1 in
      let Wp2 := skipn (lenB + lenC) Wp1 in
      let D0 := firstn lenD Wp2 in
      if eqz Ws2 (E0 ++ Tlist v0) then
        match cyc 481 (k0, A0, B0, C0, D0, E0, v0) with
        | Some (k, wA, wB, wC, wD, wE, v) =>
          Nat.eqb k (k0 + hh) &&& tl_eqb wA A0 &&& tl_eqb wB B0 &&& tl_eqb wC (B0 ++ C0) &&& tl_eqb wD D0
            &&& tl_eqb wE (D0 ++ E0 ++ Tlist tv) &&& Nat.eqb v v0
        | None => false
        end
      else false
    | None => false
    end
  | None => false
  end.

Lemma check_ok : forall f, check f = true -> ~ halts tm c0.
Proof.
  intros f H. unfold check in H. cbv zeta in H.
  destruct (xrun f rs 0 1%N (tH :: pad8)) as [[[k0 n0] Ws]|] eqn:H1; [|discriminate].
  destruct (xrun f per k0 n0 Ws) as [[[k1 n1] Wp]|] eqn:H2; [|discriminate].
  set (A0 := firstn lenA Ws) in H.
  set (C0 := firstn lenC (skipn lenA Ws)) in H.
  set (E0 := firstn lenE (skipn lenC (skipn lenA Ws))) in H.
  set (B0 := firstn lenB (skipn lenA Wp)) in H.
  set (D0 := firstn lenD (skipn (lenB + lenC) (skipn lenA Wp))) in H.
  destruct (eqz (skipn lenC (skipn lenA Ws)) (E0 ++ Tlist v0)) eqn:H3; [|discriminate].
  destruct (cyc 481 (k0, A0, B0, C0, D0, E0, v0)) as [[[[[[[k A] B] C] D] E] v]|] eqn:H4; [|discriminate].
  repeat (apply andb_prop in H; destruct H as [H ?]).
  rename H0 into Hv, H5 into HE, H6 into HD, H7 into HC, H8 into HB, H9 into HA.
  apply Nat.eqb_eq in H. subst k.
  apply tl_eqb_ok in HA. subst A.
  apply tl_eqb_ok in HB. subst B.
  apply tl_eqb_ok in HC. subst C.
  apply tl_eqb_ok in HD. subst D.
  apply tl_eqb_ok in HE. subst E.
  apply Nat.eqb_eq in Hv. subst v.
  set (st0 := (k0, A0, B0, C0, D0, E0, v0) : St) in *.
  (* the tape at the start of the cycle *)
  assert (Hs : sw st0 0 = rep [tL] k0 (tks Ws Zinf)).
  { unfold st0. rewrite sw_eq, !Nat.mul_0_r, !Nat.add_0_r. cbn [zone].
    pose proof (eqz_ok _ _ H3) as Hz.
    rewrite tks_app, Tlist_ok in Hz. rewrite <- Hz.
    unfold A0, C0.
    rewrite <- (tks_app (firstn lenC (skipn lenA Ws))), firstn_skipn.
    rewrite <- (tks_app (firstn lenA Ws)), firstn_skipn. reflexivity. }
  destruct (xrun_ok _ _ _ _ _ _ _ _ H1 eq_refl) as [_ HB0].
  apply multistep_nonhalt with (c' := LE (sw st0 0)).
  - eapply evstep_trans; [apply progress_evstep; apply blank_start|].
    rewrite Hs.
    change (S1 >> const S0) with (S1 >> Zinf).
    replace (S1 >> Zinf) with (rep [tL] 0 (tks (tH :: pad8) Zinf)).
    + exact HB0.
    + simpl. rewrite <- !Zinf_unfold. reflexivity.
  - apply progress_nonhalt with (P := fun c => exists t, c = LE (sw st0 t)).
    + intros c [t ->].
      exists (LE (sw st0 (S t))). split; [exists (S t); reflexivity|].
      pose proof (closure k0 A0 B0 C0 D0 E0 v0 t) as Hcl.
      change (sw (k0, A0, B0, C0, D0, E0, v0) (S t)) with (sw st0 (S t)) in Hcl.
      rewrite <- Hcl.
      exact (cyc_ok1 _ _ _ H4 t).
    + exists 0. reflexivity.
Qed.

Lemma check_run : check (N.to_nat 200000) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~ halts tm c0.
Proof. exact (check_ok _ check_run). Qed.

End TM1.

Print Assumptions TM1.nonhalt.
