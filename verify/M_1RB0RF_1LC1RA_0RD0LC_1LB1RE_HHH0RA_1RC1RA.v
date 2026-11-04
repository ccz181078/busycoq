(* 1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA does not halt from the blank tape, and neither does the same table started
   in state F, which is 1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA with the states renamed (module TM2).

   Between passes the tape is 0^inf (1 0)^v, the head in state C on the last 0, then tape r (`cfg v r`). The list r
   holds digits, nearest first: U = 1 1, Z = 0 0, O = 0 1, and H = a single 1 at the far end. dcnt counts Z and O.

   The law, for all sizes (`bell_ok`). One Bell: the machine eats k leading U, then sends m = v + k + 1 waves into the
   rest, and comes back as cfg m o. The pass is a list of operations, computed from the list alone (`path`), and `it`
   runs it with m waves: a digit takes the low bit of the waves and halves them, a repair `Rp` takes one wave. `it` gives
   None only when `Rp` finds no wave, or at `Fl`. So it is enough to show this never happens along the run.

   The invariant `InvP`, with a cut below the top of the list at the level L where Y = v / 2^L is in 8..15.
   - Above the cut, a finite game. A state is (word w above the cut, Y, phase c). `closure` computes by search a set of
     states, and `okx` checks that every way a pass can arrive at the cut, with any waves and any carry the bounds allow,
     gets through w without failing and leaves a state of the set. `top_step` states this for all passes. The set is not
     written in this file: the VM computes it (`RR_some`, a cast checked at Qed, about 5 minutes).
   - Below the cut, a numeric clause (`clause`, `NCr`): at each digit boundary the number of U above it is bounded in terms
     of the waves that reach it. `low_loop` shows it carries over, level by level, and that the waves do not run out.
   `inv_step` joins the two. The clause needs L >= 13 (`K4_small`), so the invariant starts at v >= 65536.

   The start. A few plain steps (`startA`, `startF`), then a run of the law in the VM with binary numbers (`runN`,
   `runN_ok`) up to 65540 waves from state A and 65545 from state F. In both cases the word above the cut is then `bin 7`, a
   seed of the search (`invA`, `invF`). *)
From Coq Require Import NArith Pnat.
From BusyCoq Require Import Individual62.
From Coq Require Import Lia PeanoNat String Wf_nat.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

Module TM1.
Local Open Scope nat_scope.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA"%string).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* Digits of the list, nearest first: U = 1 1, Z = 0 0, O = 0 1, and H = a single 1, a half digit, only ever at the far end. *)
Inductive dg := U | Z | O | H.

Definition cw (d : dg) (s : side) : side :=
  match d with
  | U => S1 >> S1 >> s
  | Z => S0 >> S0 >> s
  | O => S0 >> S1 >> s
  | H => S1 >> s
  end.

Fixpoint tape (r : list dg) : side :=
  match r with
  | [] => const S0
  | H :: _ => S1 >> const S0
  | d :: r' => cw d (tape r')
  end.

Fixpoint inc1 (r : list dg) : list dg :=
  match r with
  | [] => [O]
  | Z :: r' => O :: r'
  | O :: r' => Z :: inc1 r'
  | U :: r' => U :: inc1 r'
  | H :: _ => [U; U]
  end.

Fixpoint incn (j : nat) (r : list dg) : list dg :=
  match j with
  | 0 => r
  | S j' => incn j' (inc1 r)
  end.

Definition bin (j : nat) : list dg := incn j [].

Definition bitd (n : nat) : dg := if Nat.even n then Z else O.

(* One wave against any digit. *)
Lemma wave_Z : forall l R, l {{A}}> S0 >> S0 >> R -->* l <{{C}} S0 >> S1 >> R.
Proof. intros. do 3 step. finish. Qed.

Lemma wave_nil : forall l, l {{A}}> const S0 -->* l <{{C}} S0 >> S1 >> const S0.
Proof. intros. do 3 step. finish. Qed.

Lemma wave_H : forall l, l {{A}}> S1 >> const S0 -->* l <{{C}} S1 >> S1 >> S1 >> S1 >> const S0.
Proof. intros. do 9 step. finish. Qed.

Lemma wave_U : forall s s1,
  (forall l, l {{A}}> s -->* l <{{C}} s1) ->
  forall l, l {{A}}> S1 >> S1 >> s -->* l <{{C}} S1 >> S1 >> s1.
Proof. intros s s1 Hw l. do 2 step. follow Hw. do 4 step. finish. Qed.

Lemma wave_O : forall s s1,
  (forall l, l {{A}}> s -->* l <{{C}} s1) ->
  forall l, l {{A}}> S0 >> S1 >> s -->* l <{{C}} S0 >> S0 >> s1.
Proof. intros s s1 Hw l. do 2 step. follow Hw. do 2 step. finish. Qed.

Lemma wave : forall r l, l {{A}}> tape r -->* l <{{C}} tape (inc1 r).
Proof.
  induction r as [|d r IH]; intros l.
  - cbn [tape inc1 cw]. apply wave_nil.
  - destruct d; cbn [tape inc1 cw].
    + apply wave_U. exact IH.
    + apply wave_Z.
    + apply wave_O. exact IH.
    + apply wave_H.
Qed.

(* A chain of n waves against a side. *)
Inductive Ws : nat -> side -> side -> Prop :=
  | Ws0 s : Ws 0 s s
  | WsS n s s1 s2 : (forall l, l {{A}}> s -->* l <{{C}} s1) -> Ws n s1 s2 -> Ws (S n) s s2.

Lemma Ws_U : forall n s s', Ws n s s' -> Ws n (cw U s) (cw U s').
Proof.
  intros n s s' H. induction H as [s|n s s1 s2 Hw Hr IH].
  - constructor.
  - apply WsS with (s1 := cw U s1); [|exact IH]. apply wave_U. exact Hw.
Qed.

Lemma bitd_SS : forall n, bitd (S (S n)) = bitd n.
Proof. intros. unfold bitd. rewrite Nat.even_succ_succ. reflexivity. Qed.

Lemma Ws_Z : forall n s s', Ws (n / 2) s s' -> Ws n (cw Z s) (cw (bitd n) s').
Proof.
  induction n as [n IH] using lt_wf_ind. intros s s' H.
  destruct n as [|[|n]].
  - inversion H. subst. simpl. constructor.
  - replace (1 / 2) with 0 in H by reflexivity. inversion H. subst.
    simpl. apply WsS with (s1 := cw O s'); [|constructor].
    intro l. apply wave_Z.
  - replace (S (S n) / 2) with (S (n / 2)) in H.
    2:{ replace (S (S n)) with (n + 1 * 2) by lia. rewrite Nat.div_add by lia. lia. }
    inversion H as [|n0 s0 s1 s2 Hw Hr]. subst.
    rewrite bitd_SS.
    apply WsS with (s1 := cw O s).
    { intro l. apply wave_Z. }
    apply WsS with (s1 := cw Z s1).
    { apply wave_O. exact Hw. }
    apply IH; [lia|exact Hr].
Qed.

Lemma Ws_O : forall n s s', Ws ((n + 1) / 2) s s' -> Ws n (cw O s) (cw (bitd (n + 1)) s').
Proof.
  intros n s s' H. destruct n as [|n].
  - replace ((0 + 1) / 2) with 0 in H by reflexivity. inversion H. subst. simpl. constructor.
  - replace ((S n + 1) / 2) with (S (n / 2)) in H.
    2:{ replace (S n + 1) with (n + 1 * 2) by lia. rewrite Nat.div_add by lia. lia. }
    inversion H as [|n0 s0 s1 s2 Hw Hr]. subst.
    replace (S n + 1) with (S (S n)) by lia. rewrite bitd_SS.
    apply WsS with (s1 := cw Z s1).
    { apply wave_O. exact Hw. }
    apply Ws_Z. exact Hr.
Qed.

Lemma Ws_tape : forall n r, Ws n (tape r) (tape (incn n r)).
Proof.
  induction n as [|n IH]; intros r.
  - constructor.
  - apply WsS with (s1 := tape (inc1 r)).
    + apply wave.
    + apply IH.
Qed.

Lemma tape_cons : forall d r, d <> H -> tape (d :: r) = cw d (tape r).
Proof. intros [] r Hd; try reflexivity. contradiction. Qed.

Lemma bitd_not_H : forall n, bitd n <> H.
Proof. intros n. unfold bitd. destruct (Nat.even n); discriminate. Qed.

Lemma incn_U : forall j r, incn j (U :: r) = U :: incn j r.
Proof.
  induction j as [|j IH]; intros r; [reflexivity|]. simpl. apply IH.
Qed.

Lemma div2_SS : forall j, (S (S j)) / 2 = S (j / 2).
Proof.
  intro j. replace (S (S j)) with (j + 1 * 2) by lia. rewrite Nat.div_add by lia. lia.
Qed.

Lemma incn_digit : forall j r,
  incn j (Z :: r) = bitd j :: incn (j / 2) r /\
  incn j (O :: r) = bitd (j + 1) :: incn ((j + 1) / 2) r.
Proof.
  induction j as [j IH] using lt_wf_ind. intros r. destruct j as [|j].
  - split; reflexivity.
  - assert (HO : incn (S j) (O :: r) = bitd (S j + 1) :: incn ((S j + 1) / 2) r).
    { simpl incn at 1.
      destruct (IH j ltac:(lia) (inc1 r)) as [Hz _]. rewrite Hz.
      replace (S j + 1) with (S (S j)) by lia. rewrite bitd_SS, div2_SS. reflexivity. }
    split; [|exact HO].
    simpl incn at 1.
    destruct (IH j ltac:(lia) r) as [_ Ho]. rewrite Ho.
    replace (j + 1) with (S j) by lia. reflexivity.
Qed.

Lemma incn_Z : forall j r, incn j (Z :: r) = bitd j :: incn (j / 2) r.
Proof. intros. apply incn_digit. Qed.

Lemma incn_O : forall j r, incn j (O :: r) = bitd (j + 1) :: incn ((j + 1) / 2) r.
Proof. intros. apply incn_digit. Qed.

Lemma incn_H : forall j x, incn (S j) (H :: x) = U :: U :: bin j.
Proof.
  intros j x. simpl. rewrite !incn_U. reflexivity.
Qed.

Lemma bin_S : forall j, bin (S j) = incn j [O].
Proof. reflexivity. Qed.

Lemma cw_bit_tape : forall n x, tape (bitd n :: x) = cw (bitd n) (tape x).
Proof. intros. apply tape_cons, bitd_not_H. Qed.

(* A pass, as a list of operations that does not depend on the wave count. *)
Inductive md := S_0 | S_1 | T_.
Inductive op := Dg | Cv | Rp | Rd | Em | E0 | E1 | E2 | EH0 | EH1 | Fl.

Definition mbit (v : nat) : md := if Nat.even v then S_0 else S_1.

Fixpoint pb (m : md) (r : list dg) : list op :=
  match r with
  | [] => match m with S_0 => [E0] | S_1 => [E1] | T_ => [E2] end
  | Z :: r' =>
    match m with
    | S_0 => Dg :: pb S_0 r'
    | S_1 => Rp :: pb T_ r'
    | T_ => Rd :: pb S_0 r'
    end
  | O :: r' =>
    match m with
    | S_0 => Dg :: pb S_1 r'
    | S_1 => Rp :: Em :: pb S_0 r'
    | T_ => Rd :: pb S_1 r'
    end
  | _ => [Fl]
  end.

Definition pdig (m : md) (v : nat) (rest : md -> list op) : list op :=
  match m with
  | S_0 => Dg :: rest (mbit v)
  | S_1 => if Nat.even v then Rp :: rest T_ else Rp :: Em :: rest S_0
  | T_ => Rd :: rest (mbit v)
  end.

Fixpoint path (m : md) (t : list dg) (cc : nat) : list op :=
  match t with
  | [] => pb m (bin cc)
  | U :: r =>
    match m with
    | S_0 => Cv :: path S_1 r cc
    | S_1 => Em :: path S_1 r cc
    | T_ => Em :: path T_ r (S cc)
    end
  | Z :: r => pdig m cc (fun m' => path m' r (cc / 2))
  | O :: r => pdig m (cc + 1) (fun m' => path m' r ((cc + 1) / 2))
  | H :: _ =>
    match cc with
    | 0 => match m with S_0 => [EH0] | S_1 => [EH1] | T_ => [Fl] end
    | S c' =>
      match m with
      | S_0 => Cv :: Em :: pb S_1 (bin c')
      | S_1 => Em :: Em :: pb S_1 (bin c')
      | T_ => Em :: Em :: pb T_ (bin (S (S c')))
      end
    end
  end.

Fixpoint it (p : list op) (n : nat) : option (list dg) :=
  match p with
  | [] => Some []
  | Dg :: p' => option_map (cons (bitd n)) (it p' (n / 2))
  | Cv :: p' => option_map (cons (bitd (n + 1))) (it p' ((n + 1) / 2))
  | Rp :: p' => match n with 0 => None | S n' => it p' n' end
  | Rd :: p' => option_map (fun o => U :: U :: o) (it p' n)
  | Em :: p' => option_map (cons U) (it p' n)
  | E0 :: _ => Some (bin n)
  | E1 :: _ => match n with 0 => Some [H] | S n' => Some (U :: U :: bin n') end
  | E2 :: _ => Some (U :: U :: bin n)
  | EH0 :: _ => Some (bin (S n))
  | EH1 :: _ => Some (U :: bin n)
  | Fl :: _ => None
  end.

(* The prefix left by a tunnel: read away from the head, 0 (1 0)^i. *)
Fixpoint pf (i : nat) (l : side) : side :=
  match i with
  | 0 => S0 >> l
  | S i' => S0 >> S1 >> pf i' l
  end.

Fixpoint ups (n : nat) (s : side) : side :=
  match n with
  | 0 => s
  | S n' => S1 >> S1 >> ups n' s
  end.

(* What a state stands for: n waves make tape o out of it. *)
Definition SM (m : md) (R : side) (n : nat) (o : list dg) : Prop :=
  match m with
  | S_0 => Ws n (S0 >> R) (tape o)
  | S_1 => Ws n (S1 >> R) (tape o)
  | T_ => exists s', (forall i l, pf (S i) l {{D}}> R -->* l <{{C}} ups i s') /\ Ws n s' (tape o)
  end.

Lemma ups_cw : forall i s, ups i (cw U s) = ups (S i) s.
Proof.
  induction i as [|i IH]; intros s; [reflexivity|].
  change (ups (S i) (cw U s)) with (S1 >> S1 >> ups i (cw U s)). rewrite IH. reflexivity.
Qed.

Lemma walk_pf : forall i l R, S1 >> pf i l <{{C}} R -->* l <{{C}} ups (S i) R.
Proof.
  induction i as [|i IH]; intros l R.
  - cbn [pf ups]. do 4 step. finish.
  - cbn [pf]. do 4 step. follow IH.
    change (S1 >> S1 >> R) with (cw U R). rewrite ups_cw. finish.
Qed.

Lemma pf_D_0 : forall i l x R, pf i l {{D}}> S0 >> x >> R -->* l <{{C}} ups (S i) (x >> R).
Proof.
  intros [|i] l x R.
  - cbn [pf ups]. do 2 step. finish.
  - cbn [pf]. do 2 step. follow walk_pf.
    change (S1 >> S1 >> x >> R) with (cw U (x >> R)). rewrite ups_cw. finish.
Qed.

Lemma tape_U : forall o, tape (U :: o) = cw U (tape o).
Proof. reflexivity. Qed.

Lemma SM_Dg_Z : forall R n o, SM S_0 R (n / 2) o -> SM S_0 (cw Z R) n (bitd n :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *. rewrite cw_bit_tape. apply (Ws_Z n (S0 >> R) (tape o)). exact H.
Qed.

Lemma SM_Dg_O : forall R n o, SM S_1 R (n / 2) o -> SM S_0 (cw O R) n (bitd n :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *. rewrite cw_bit_tape. apply (Ws_Z n (S1 >> R) (tape o)). exact H.
Qed.

Lemma SM_Cv : forall R n o, SM S_1 R ((n + 1) / 2) o -> SM S_0 (cw U R) n (bitd (n + 1) :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *. rewrite cw_bit_tape. apply (Ws_O n (S1 >> R) (tape o)). exact H.
Qed.

Lemma SM_RpO : forall R n o, SM S_0 R n o -> SM S_1 (cw O R) (S n) (U :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *.
  apply WsS with (s1 := cw U (S0 >> R)).
  - intro l. cbn [cw]. do 7 step. finish.
  - apply (Ws_U _ _ _ H).
Qed.

Lemma SM_RpZ : forall R n o, SM T_ R n o -> SM S_1 (cw Z R) (S n) o.
Proof.
  intros R n o [s' [Hd Hw]]. cbv beta iota delta [SM].
  apply WsS with (s1 := s').
  - intro l. do 3 step. apply (Hd 0 l).
  - exact Hw.
Qed.

Lemma SM_RdZ : forall R n o, SM S_0 R n o -> SM T_ (cw Z R) n (U :: U :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *. exists (cw U (cw U (S0 >> R))). split.
  - intros i l. change (cw Z R) with (S0 >> S0 >> R). follow pf_D_0.
    rewrite !ups_cw. finish.
  - apply Ws_U, Ws_U. exact H.
Qed.

Lemma SM_RdO : forall R n o, SM S_1 R n o -> SM T_ (cw O R) n (U :: U :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *. exists (cw U (cw U (S1 >> R))). split.
  - intros i l. change (cw O R) with (S0 >> S1 >> R). follow pf_D_0.
    rewrite !ups_cw. finish.
  - apply Ws_U, Ws_U. exact H.
Qed.

Lemma SM_EmS1 : forall R n o, SM S_1 R n o -> SM S_1 (cw U R) n (U :: o).
Proof.
  intros R n o H. cbv beta iota delta [SM] in *. apply (Ws_U _ _ _ H).
Qed.

Lemma SM_EmT : forall x n o, SM T_ (tape (inc1 x)) n o -> SM T_ (cw U (tape x)) n (U :: o).
Proof.
  intros x n o [s' [Hd Hw]]. exists (cw U s'). split.
  - intros i l. rewrite ups_cw. change (cw U (tape x)) with (S1 >> S1 >> tape x). do 2 step.
    change (S0 >> S1 >> pf (S i) l) with (pf (S (S i)) l).
    follow wave. change (pf (S (S i)) l) with (S0 >> S1 >> pf (S i) l). do 1 step.
    change (S0 >> S1 >> pf (S i) l) with (pf (S (S i)) l).
    apply (Hd (S i) l).
  - apply (Ws_U _ _ _ Hw).
Qed.

Lemma S0_const : S0 >> const S0 = const S0.
Proof. rewrite <- const_unfold. reflexivity. Qed.

Lemma SM_E0 : forall n, SM S_0 (const S0) n (bin n).
Proof.
  intros n. cbv beta iota delta [SM]. rewrite S0_const. apply (Ws_tape n []).
Qed.

Lemma SM_E1 : forall n, SM S_1 (const S0) n (match n with 0 => [H] | S n' => U :: U :: bin n' end).
Proof.
  intros [|n]; cbv beta iota delta [SM].
  - constructor.
  - apply WsS with (s1 := cw U (cw U (const S0))).
    + intro l. apply wave_H.
    + apply Ws_U, Ws_U. apply (Ws_tape n []).
Qed.

Lemma SM_E2 : forall n, SM T_ (const S0) n (U :: U :: bin n).
Proof.
  intros n. cbv beta iota delta [SM]. exists (cw U (cw U (const S0))). split.
  - intros i l.
    pose proof (pf_D_0 (S i) l S0 (const S0)) as P. rewrite !S0_const in P.
    rewrite !ups_cw. exact P.
  - apply Ws_U, Ws_U. apply (Ws_tape n []).
Qed.

Lemma SM_EH0 : forall n, SM S_0 (S1 >> const S0) n (bin (S n)).
Proof.
  intros n. cbv beta iota delta [SM]. apply (Ws_tape n [O]).
Qed.

Lemma SM_EH1 : forall n, SM S_1 (S1 >> const S0) n (U :: bin n).
Proof.
  intros n. cbv beta iota delta [SM]. apply (Ws_U _ _ _ (Ws_tape n [])).
Qed.

Ltac optmap H :=
  match type of H with
  | option_map _ ?e = Some _ =>
    let E := fresh "E" in destruct e as [?o|] eqn:E; simpl in H; [injection H as <-|discriminate]
  end.

Lemma pb_SM : forall x m n o, it (pb m x) n = Some o -> SM m (tape x) n o.
Proof.
  induction x as [|d x IH]; intros m n o Hit.
  - destruct m; simpl in Hit.
    + injection Hit as <-. apply SM_E0.
    + destruct n as [|n]; injection Hit as <-; apply SM_E1.
    + injection Hit as <-. apply SM_E2.
  - destruct d; cbn [tape pb] in *; try (simpl in Hit; discriminate).
    + destruct m; simpl in Hit.
      * optmap Hit. apply SM_Dg_Z. apply IH. assumption.
      * destruct n as [|n]; [discriminate|]. apply SM_RpZ. apply IH. assumption.
      * optmap Hit. apply SM_RdZ. apply IH. assumption.
    + destruct m; simpl in Hit.
      * optmap Hit. apply SM_Dg_O. apply IH. assumption.
      * destruct n as [|n]; [discriminate|]. optmap Hit. apply SM_RpO. apply IH. assumption.
      * optmap Hit. apply SM_RdO. apply IH. assumption.
Qed.

Lemma inc1_incn : forall j r, inc1 (incn j r) = incn j (inc1 r).
Proof.
  induction j as [|j IH]; intros r; [reflexivity|]. simpl. apply IH.
Qed.

Lemma cw_bit : forall v R,
  cw (bitd v) R = S0 >> (if Nat.even v then S0 else S1) >> R.
Proof. intros. unfold bitd. destruct (Nat.even v); reflexivity. Qed.

(* The digit step of a path on a list with a carry, head digit by parity of v. *)
Lemma pdig_SM : forall m v rest R n o,
  (forall m' n' o', it (rest m') n' = Some o' -> SM m' R n' o') ->
  it (pdig m v rest) n = Some o -> SM m (cw (bitd v) R) n o.
Proof.
  intros m v rest R n o Hr Hit.
  unfold bitd, pdig, mbit in *. destruct (Nat.even v), m; simpl in Hit.
  - optmap Hit. apply SM_Dg_Z. apply Hr. assumption.
  - destruct n as [|n]; [discriminate|]. apply SM_RpZ. apply Hr. assumption.
  - optmap Hit. apply SM_RdZ. apply Hr. assumption.
  - optmap Hit. apply SM_Dg_O. apply Hr. assumption.
  - destruct n as [|n]; [discriminate|]. optmap Hit. apply SM_RpO. apply Hr. assumption.
  - optmap Hit. apply SM_RdO. apply Hr. assumption.
Qed.

Lemma bin_succ : forall c, bin (S c) = inc1 (bin c).
Proof.
  intro c. unfold bin. rewrite inc1_incn. reflexivity.
Qed.

Lemma path_SM : forall t m cc n o, it (path m t cc) n = Some o -> SM m (tape (incn cc t)) n o.
Proof.
  induction t as [|d t IH]; intros m cc n o Hit.
  - cbn [path] in Hit. apply pb_SM. exact Hit.
  - destruct d; cbn [path] in Hit.
    + rewrite incn_U. cbn [tape]. destruct m; simpl in Hit.
      * optmap Hit. apply SM_Cv. apply IH. assumption.
      * optmap Hit. apply SM_EmS1. apply IH. assumption.
      * optmap Hit. apply SM_EmT. rewrite inc1_incn. apply (IH T_ (S cc)). assumption.
    + rewrite incn_Z, cw_bit_tape. eapply pdig_SM; [|exact Hit].
      intros. apply IH. assumption.
    + rewrite incn_O, cw_bit_tape. eapply pdig_SM; [|exact Hit].
      intros. apply IH. assumption.
    + destruct cc as [|c].
      * cbn [incn tape]. destruct m; simpl in Hit.
        -- injection Hit as <-. apply SM_EH0.
        -- injection Hit as <-. apply SM_EH1.
        -- discriminate.
      * rewrite incn_H. cbn [tape]. destruct m; simpl in Hit.
        -- optmap Hit. optmap E. apply SM_Cv. apply SM_EmS1. apply pb_SM. assumption.
        -- optmap Hit. optmap E. apply SM_EmS1. apply SM_EmS1. apply pb_SM. assumption.
        -- optmap Hit. optmap E.
           change (cw U (cw U (tape (bin c)))) with (cw U (tape (U :: bin c))).
           apply SM_EmT. cbn [inc1 tape]. apply SM_EmT.
           rewrite <- !bin_succ. apply pb_SM. assumption.
Qed.

(* The left part: read away from the head, (0 1)^v. *)
Fixpoint lft (v : nat) : side :=
  match v with
  | 0 => const S0
  | S v' => S0 >> S1 >> lft v'
  end.

Lemma eatU' : forall l R, S0 >> l <{{C}} S1 >> S1 >> R -->* S0 >> S1 >> S0 >> l {{A}}> R.
Proof. intros l R. do 3 step. finish. Qed.

Lemma eatU : forall v R, lft v <{{C}} S1 >> S1 >> R -->* lft (S v) {{A}}> R.
Proof.
  intros [|v] R.
  - pose proof (eatU' (const S0) R) as P. rewrite S0_const in P. exact P.
  - apply eatU'.
Qed.

Fixpoint us (k : nat) (r : list dg) : list dg :=
  match k with
  | 0 => r
  | S k' => U :: us k' r
  end.

Lemma inc1_us : forall k r, inc1 (us k r) = us k (inc1 r).
Proof.
  induction k as [|k IH]; intros r; [reflexivity|]. simpl. rewrite IH. reflexivity.
Qed.

Lemma eat : forall k v r, lft v <{{C}} tape (us k r) -->* lft (v + k) <{{C}} tape (incn k r).
Proof.
  induction k as [|k IH]; intros v r.
  - rewrite Nat.add_0_r. finish.
  - cbn [us tape incn cw]. follow eatU. follow wave. rewrite inc1_us. follow IH.
    replace (S v + k) with (v + S k) by lia. finish.
Qed.

Lemma wave_ups : forall s s1,
  (forall l, l {{A}}> s -->* l <{{C}} s1) ->
  forall n l, l {{A}}> ups n s -->* l <{{C}} ups n s1.
Proof.
  intros s s1 Hw. induction n as [|n IH]; intros l.
  - apply Hw.
  - cbn [ups]. apply wave_U. exact IH.
Qed.

Lemma drive : forall n s s', Ws n s s' -> forall v, lft v <{{C}} ups n s -->* lft (v + n) <{{C}} s'.
Proof.
  intros n s s' H. induction H as [s|n s s1 s2 Hw Hr IH]; intros v.
  - rewrite Nat.add_0_r. finish.
  - cbn [ups]. follow eatU. follow (wave_ups s s1 Hw n). follow IH.
    replace (S v + n) with (v + S n) by lia. finish.
Qed.

Lemma walk_lft : forall v R, S1 >> lft v <{{C}} R -->* lft 0 <{{C}} ups (S v) R.
Proof.
  induction v as [|v IH]; intros R.
  - cbn [lft ups]. do 4 step. finish.
  - cbn [lft]. do 4 step. follow IH.
    change (S1 >> S1 >> R) with (cw U R). rewrite ups_cw. finish.
Qed.

Lemma bell_step : forall v x R, lft (S v) <{{C}} S0 >> x >> R -->+ lft 0 <{{C}} ups (S (S v)) (x >> R).
Proof.
  intros v x R. cbn [lft].
  eapply progress_intro; [prove_step|simpl_tape].
  do 2 step. follow walk_lft.
  change (S1 >> S1 >> x >> R) with (cw U (x >> R)). rewrite ups_cw. finish.
Qed.

Definition dv (k : nat) (x : dg) : nat := match x with O => k + 1 | _ => k end.

Definition cfg (v : nat) (r : list dg) := lft v <{{C}} tape r.

(* One Bell, proved for all lists: k leading U, then a digit x, then t. The new list is what the path gives with v + k + 1 waves. *)
Theorem bell_ok : forall v k x t o,
  x = Z \/ x = O -> 1 <= v + k ->
  it (path (mbit (dv k x)) t (dv k x / 2)) (v + k + 1) = Some o ->
  cfg v (us k (x :: t)) -->+ cfg (v + k + 1) o.
Proof.
  intros v k x t o Hx Hv Hit. unfold cfg.
  eapply evstep_progress_trans; [apply eat|].
  assert (Hc : tape (incn k (x :: t)) = S0 >> (if Nat.even (dv k x) then S0 else S1) >> tape (incn (dv k x / 2) t)).
  { destruct Hx as [->| ->]; cbn [dv].
    - rewrite incn_Z, cw_bit_tape, cw_bit. reflexivity.
    - rewrite incn_O, cw_bit_tape, cw_bit. reflexivity. }
  rewrite Hc.
  destruct (v + k) as [|w] eqn:Ew; [lia|].
  eapply progress_evstep_trans; [apply bell_step|].
  replace (S w + 1) with (S (S w)) by lia.
  assert (Hs : Ws (S (S w)) ((if Nat.even (dv k x) then S0 else S1) >> tape (incn (dv k x / 2) t)) (tape o)).
  { replace (S w + 1) with (S (S w)) in Hit by lia.
    apply path_SM in Hit. unfold mbit in Hit. destruct (Nat.even (dv k x)); exact Hit. }
  pose proof (drive _ _ _ Hs 0) as Hd. simpl in Hd. exact Hd.
Qed.

(* The closure of top words. A state (w, Y, c): word w above a cut, Y = waves / 2^L in 8..15, c a phase. *)
Definition M1 (Y : nat) : nat :=
  match Y with
  | 8 => 31 | 9 => 31 | 10 => 33 | 11 => 35 | 12 => 36 | 13 => 40 | 14 => 40 | 15 => 40
  | _ => 0
  end.

Fixpoint ucnt (l : list dg) : nat :=
  match l with
  | [] => 0
  | U :: r => S (ucnt r)
  | _ :: r => ucnt r
  end.

Fixpoint trimz (l : list dg) : list dg :=
  match l with
  | [] => []
  | d :: r =>
    match d, trimz r with
    | Z, [] => []
    | _, r' => d :: r'
    end
  end.

Fixpoint strip1 (w : list dg) : list dg :=
  match w with
  | [] => []
  | U :: r => strip1 r
  | H :: r => strip1 r
  | _ :: r => r
  end.

(* The trie of keys. *)
Inductive trie := Tn | Tr (b : bool) (u z o h : trie).

Fixpoint memk (k : list dg) (t : trie) : bool :=
  match t with
  | Tn => false
  | Tr b tu tz to th =>
    match k with
    | [] => b
    | U :: k' => memk k' tu
    | Z :: k' => memk k' tz
    | O :: k' => memk k' to
    | H :: k' => memk k' th
    end
  end.

Fixpoint insk (k : list dg) (t : trie) : trie :=
  match t with
  | Tn =>
    match k with
    | [] => Tr true Tn Tn Tn Tn
    | U :: k' => Tr false (insk k' Tn) Tn Tn Tn
    | Z :: k' => Tr false Tn (insk k' Tn) Tn Tn
    | O :: k' => Tr false Tn Tn (insk k' Tn) Tn
    | H :: k' => Tr false Tn Tn Tn (insk k' Tn)
    end
  | Tr b tu tz to th =>
    match k with
    | [] => Tr true tu tz to th
    | U :: k' => Tr b (insk k' tu) tz to th
    | Z :: k' => Tr b tu (insk k' tz) to th
    | O :: k' => Tr b tu tz (insk k' to) th
    | H :: k' => Tr b tu tz to (insk k' th)
    end
  end.

Lemma memk_insk : forall k k' t, memk k (insk k' t) = true -> k = k' \/ memk k t = true.
Proof.
  induction k as [|d k IH]; intros k' t Hm.
  - destruct t, k' as [|[] k']; simpl in *; auto; try discriminate.
    all: destruct (insk k' Tn); simpl in Hm; discriminate.
  - destruct t as [|b tu tz to th]; destruct k' as [|d' k'].
    + destruct d; simpl in Hm; destruct k; discriminate.
    + destruct d, d'; simpl in Hm; try (destruct k; discriminate);
      destruct (IH _ _ Hm) as [->|Hx]; auto; destruct k; discriminate.
    + destruct d; simpl in Hm; auto.
    + destruct d, d'; simpl in Hm; simpl; auto;
      destruct (IH _ _ Hm) as [->|Hx]; auto.
Qed.

Lemma memk_insk_self : forall k t, memk k (insk k t) = true.
Proof.
  induction k as [|d k IH]; intros t.
  - destruct t; reflexivity.
  - destruct t, d; simpl; apply IH.
Qed.

Lemma memk_insk_mono : forall k k' t, memk k t = true -> memk k (insk k' t) = true.
Proof.
  induction k as [|d k IH]; intros k' t Hm.
  - destruct t; simpl in Hm; [discriminate|]. destruct k' as [|[] k']; simpl; first [reflexivity|assumption].
  - destruct t as [|b tu tz to th]; simpl in Hm; [discriminate|].
    destruct k' as [|[] k'], d; simpl; first [assumption | apply IH; assumption].
Qed.

Definition st := (list dg * nat * nat)%type.

Definition pa (n : nat) : dg := bitd (n / 4).
Definition pb2 (n : nat) : dg := bitd (n / 2).
Definition pref (Y c : nat) : list dg := [pa Y; pb2 Y; bitd Y; pb2 c; bitd c].

Definition key (x : st) : list dg :=
  match x with (w, Y, c) => pref Y c ++ w end.

Definition allowed (d c cc ck ct : nat) : list nat :=
  match d with
  | 0 => []
  | 1 => if andb (Nat.ltb 0 c) (Nat.leb cc ck) then [c - 1] else []
  | 2 => (if Nat.leb cc ck then [2] else []) ++ (if andb (Nat.ltb 0 c) (Nat.leb cc ct) then [c - 1] else [])
  | _ => [2]
  end.

(* all A in lo..hi *)
Fixpoint rng (lo n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => lo :: rng (S lo) n'
  end.

Fixpoint ofold {X : Type} (f : X -> option (list st)) (xs : list X) (acc : list st) : option (list st) :=
  match xs with
  | [] => Some acc
  | x :: xs' =>
    match f x with
    | None => None
    | Some l => ofold f xs' (l ++ acc)
    end
  end.

Definition proc (Yp c cc ck ct cap : nat) (d dg lc uem : nat) (p : list op) : option (list st) :=
  match allowed d c cc ck ct with
  | [] => Some []
  | ncs =>
    let lo := Yp - (dg + 1) / 2 in
    ofold (fun A =>
      match it p A with
      | None => None
      | Some o =>
        if andb (Nat.leb (uem + ucnt o) cap) (orb (negb (Nat.eqb Yp 15)) (Nat.leb (ucnt o) 31)) then
          let w := trimz o in Some (map (fun nc => (w, Yp, nc)) ncs)
        else None
      end) (rng lo (Yp + lc + 1 - lo)) []
  end.

Fixpoint sw (Yp c cc ck ct cap : nat) (p : list op) (d dg lc uem : nat) : option (list st) :=
  match p with
  | [] => None
  | Dg :: p' =>
    if negb (Nat.eqb lc 0) then None else
    match proc Yp c cc ck ct cap (S d) (S dg) 0 uem p' with
    | None => None
    | Some l =>
      match sw Yp c cc ck ct cap p' (S d) (S dg) 0 uem with
      | None => None
      | Some l' => Some (l ++ l')
      end
    end
  | Cv :: p' =>
    match proc Yp c cc ck ct cap (S d) dg 1 uem p' with
    | None => None
    | Some l =>
      match sw Yp c cc ck ct cap p' (S d) dg 1 uem with
      | None => None
      | Some l' => Some (l ++ l')
      end
    end
  | Rp :: p' => if Nat.leb dg 14 then sw Yp c cc ck ct cap p' d (S dg) 0 uem else None
  | Rd :: p' => sw Yp c cc ck ct cap p' d (S dg) lc (S (S uem))
  | Em :: p' => sw Yp c cc ck ct cap p' d dg lc (S uem)
  | E0 :: _ => if andb (Nat.eqb lc 0) (Nat.leb uem cap) then Some [] else None
  | E1 :: _ => if andb (Nat.leb dg 14) (Nat.leb (S (S uem)) cap) then Some [] else None
  | E2 :: _ => if andb (Nat.eqb lc 0) (Nat.leb (S (S uem)) cap) then Some [] else None
  | EH0 :: _ => if andb (Nat.eqb lc 0) (Nat.leb uem cap) then Some [(bin (S Yp), Yp, 0); (bin (S Yp), Yp, 1); (bin (S Yp), Yp, 2)] else None
  | EH1 :: _ => if Nat.leb (S uem) cap then Some [(bin (S Yp), Yp, 0); (bin (S Yp), Yp, 1); (bin (S Yp), Yp, 2)] else None
  | Fl :: _ => None
  end.

Definition drift (w : list dg) (Y dv : nat) : list dg * nat :=
  if Nat.eqb (Y + dv) 16 then (strip1 w, 8) else (w, Y + dv).

Definition ckf (c : nat) : nat := if Nat.eqb c 2 then 1 else 0.
Definition cgf (m1 U0 : nat) : nat := (68 + m1 - U0) / 2.
Definition ctf (m1 U0 : nat) : nat := Nat.max ((14 + m1 - U0) / 2) ((54 + m1 - U0) / 4).
Definition capf (m1 U0 : nat) : nat := Nat.min (U0 + 12) m1.

Fixpoint hfirst (w : list dg) : bool :=
  match w with
  | U :: r => hfirst r
  | H :: _ => true
  | _ => false
  end.

Definition succ1 (w : list dg) (Y c dv : nat) : option (list st) :=
  let '(w1, Yp) := drift w Y dv in
  let U0 := ucnt w1 in
  let m1 := M1 Yp in
  if andb (Nat.leb U0 m1) (negb (andb (Nat.eqb (Y + dv) 16) (hfirst w))) then
    ofold (fun cc =>
      ofold (fun m => sw Yp c cc (ckf c) (ctf m1 U0) (capf m1 U0) (path m w1 cc) 0 0 0 0) [S_0; S_1; T_] [])
      (rng 0 (S (cgf m1 U0))) []
  else None.

Definition succs (x : st) : option (list st) :=
  match x with
  | (w, Y, c) => ofold (succ1 w Y c) [0; 1] []
  end.

Definition vb (x : st) : bool :=
  match x with
  | (w, Y, c) => andb (andb (Nat.leb 8 Y) (Nat.leb Y 15)) (Nat.leb c 2)
  end.

(* the closure, a search with a stack of states to do *)
Fixpoint addall (l : list st) (T : trie) (todo : list st) : trie * list st :=
  match l with
  | [] => (T, todo)
  | y :: l' =>
    if memk (key y) T then addall l' T todo
    else addall l' (insk (key y) T) (y :: todo)
  end.

Fixpoint bfs (fuel : nat) (todo : list st) (T : trie) : option trie :=
  match todo with
  | [] => Some T
  | x :: todo' =>
    match fuel with
    | 0 => None
    | S f =>
      match succs x with
      | None => None
      | Some l =>
        if forallb vb l then
          let '(T', todo'') := addall l T todo' in
          bfs f todo'' T'
        else None
      end
    end
  end.

Definition seeds : list st :=
  flat_map (fun Y => flat_map (fun v => map (fun c => (bin v, Y, c)) [0; 1; 2]) (rng 0 (S Y))) (rng 8 8).

Definition closure (fuel : nat) : option trie :=
  let '(T, t) := addall seeds Tn [] in bfs fuel t T.

Fixpoint tcount (t : trie) : nat :=
  match t with
  | Tn => 0
  | Tr b u z o h => (if b then 1 else 0) + tcount u + tcount z + tcount o + tcount h
  end.

(* What the check gives. *)
Fixpoint dcnt (l : list dg) : nat :=
  match l with
  | [] => 0
  | Z :: r => S (dcnt r)
  | O :: r => S (dcnt r)
  | _ :: r => dcnt r
  end.

Fixpoint noH (l : list dg) : Prop :=
  match l with
  | [] => True
  | H :: _ => False
  | _ :: r => noH r
  end.

Fixpoint endsd (l : list dg) : Prop :=
  match l with
  | [] => False
  | [Z] => True
  | [O] => True
  | _ :: r => endsd r
  end.

Lemma ofold_spec : forall (X : Type) (f : X -> option (list st)) (xs : list X) acc l,
  ofold f xs acc = Some l ->
  (forall z, In z acc -> In z l) /\
  (forall x, In x xs -> exists lx, f x = Some lx /\ forall z, In z lx -> In z l).
Proof.
  intros X f. induction xs as [|x xs IH]; intros acc l H; simpl in H.
  - injection H as <-. split; [auto|]. intros x [].
  - destruct (f x) as [lx|] eqn:E; [|discriminate].
    destruct (IH _ _ H) as [H1 H2]. split.
    + intros z Hz. apply H1. apply in_or_app. auto.
    + intros y [<-|Hy].
      * exists lx. split; [exact E|]. intros z Hz. apply H1. apply in_or_app. auto.
      * apply H2. exact Hy.
Qed.

Lemma rng_in : forall n lo x, lo <= x -> x < lo + n -> In x (rng lo n).
Proof.
  induction n as [|n IH]; intros lo x H1 H2; [lia|].
  simpl. destruct (Nat.eq_dec lo x) as [->|Hne]; [auto|].
  right. apply IH; lia.
Qed.

Lemma tape_trimz : forall o, tape (trimz o) = tape o.
Proof.
  induction o as [|d o IH]; [reflexivity|].
  destruct d; cbn [trimz tape]; try reflexivity; try (rewrite IH; reflexivity).
  - destruct (trimz o) as [|d' o'] eqn:E.
    + cbn [tape cw]. rewrite <- IH. cbn [tape]. rewrite !S0_const. reflexivity.
    + cbn [cw]. rewrite <- IH.
      destruct d'; reflexivity.
Qed.

Lemma ucnt_trimz : forall o, ucnt (trimz o) <= ucnt o.
Proof.
  induction o as [|d o IH]; [simpl; lia|].
  destruct d; cbn [trimz ucnt]; try lia.
  destruct (trimz o) as [|d' o'] eqn:E; simpl in *; lia.
Qed.

Lemma trimz_cons_trim : forall d o, trimz o = o -> o <> [] -> trimz (d :: o) = d :: o.
Proof.
  intros d o H1 H2. cbn [trimz]. rewrite H1. destruct d; try reflexivity.
  destruct o; [contradiction|reflexivity].
Qed.

Lemma trimz_idem : forall o, trimz (trimz o) = trimz o.
Proof.
  induction o as [|d o IH]; [reflexivity|].
  cbn [trimz]. destruct (trimz o) as [|d' o'] eqn:E.
  - destruct d; reflexivity.
  - assert (Hne : d' :: o' <> []) by discriminate.
    destruct d; apply trimz_cons_trim; assumption.
Qed.

Lemma bin_rec : forall a, 0 < a -> bin a = bitd a :: bin (a / 2).
Proof.
  intros [|a] Ha; [lia|]. unfold bin. cbn [incn inc1].
  rewrite incn_O. replace (a + 1) with (S a) by lia. reflexivity.
Qed.

Lemma tape_bin : forall a, tape (bin a) = cw (bitd a) (tape (bin (a / 2))).
Proof.
  intros [|a].
  - cbn. rewrite !S0_const. reflexivity.
  - rewrite (bin_rec (S a)) at 1 by lia. apply cw_bit_tape.
Qed.

Lemma ucnt_bin : forall a, ucnt (bin a) = 0.
Proof.
  induction a as [a IH] using lt_wf_ind. destruct a as [|a]; [reflexivity|].
  rewrite bin_rec by lia. unfold bitd. destruct (Nat.even (S a)); cbn [ucnt].
  all: apply IH; apply Nat.div_lt; lia.
Qed.

Lemma noH_bin : forall a, noH (bin a).
Proof.
  induction a as [a IH] using lt_wf_ind. destruct a as [|a]; [exact I|].
  rewrite bin_rec by lia. unfold bitd. destruct (Nat.even (S a)); cbn [noH].
  all: apply IH; apply Nat.div_lt; lia.
Qed.

Lemma trimz_bin : forall a, trimz (bin a) = bin a.
Proof.
  induction a as [a IH] using lt_wf_ind. destruct a as [|a]; [reflexivity|].
  rewrite bin_rec by lia.
  assert (H1 : trimz (bin (S a / 2)) = bin (S a / 2)) by (apply IH; apply Nat.div_lt; lia).
  unfold bitd. destruct (Nat.even (S a)) eqn:E; cbn [trimz]; rewrite H1; [|reflexivity].
  destruct (bin (S a / 2)) as [|d x] eqn:E2; [|reflexivity].
  exfalso. destruct a as [|a]; [discriminate|].
  destruct (S (S a) / 2) as [|b] eqn:E3.
  - rewrite div2_SS in E3. discriminate.
  - rewrite bin_rec in E2 by lia. discriminate.
Qed.

Lemma split_bin : forall r a, 1 <= r ->
  exists oL, tape (bin a) = tape (oL ++ bin (a / 2 ^ r)) /\ dcnt oL = r /\ noH oL /\ endsd oL /\ ucnt oL = 0.
Proof.
  induction r as [|r IH]; intros a Hr; [lia|].
  destruct r as [|r].
  - exists [bitd a]. simpl. replace (2 * 1) with 2 by lia.
    split; [|unfold bitd; destruct (Nat.even a); simpl; repeat split].
    rewrite tape_bin. unfold bitd. destruct (Nat.even a); reflexivity.
  - destruct (IH (a / 2) ltac:(lia)) as [oL [H1 [H2 [H3 [H4 H5]]]]].
    exists (bitd a :: oL).
    rewrite Nat.Div0.div_div in H1 by (try lia; apply Nat.pow_nonzero; lia).
    replace (2 * 2 ^ S r) with (2 ^ S (S r)) in H1 by (simpl; lia).
    rewrite <- app_comm_cons.
    split; [|split; [|split; [|split]]].
    + rewrite tape_bin, H1. rewrite cw_bit_tape. reflexivity.
    + unfold bitd. destruct (Nat.even a); cbn [dcnt]; lia.
    + unfold bitd. destruct (Nat.even a); cbn [noH]; assumption.
    + destruct oL as [|x oL]; [contradiction|].
      unfold bitd. destruct (Nat.even a); exact H4.
    + unfold bitd. destruct (Nat.even a); cbn [ucnt]; lia.
Qed.

Lemma pow2_ge : forall r, r + 1 <= 2 ^ r.
Proof.
  induction r as [|r IH]; simpl; lia.
Qed.

Lemma d2a : forall a, a <= 2 * (a / 2) + 1.
Proof. intros a. pose proof (Nat.mod_upper_bound a 2 ltac:(lia)). pose proof (Nat.div_mod_eq a 2). lia. Qed.
Lemma d2b : forall a, 2 * (a / 2) <= a.
Proof. intros a. pose proof (Nat.mod_upper_bound a 2 ltac:(lia)). pose proof (Nat.div_mod_eq a 2). lia. Qed.
Ltac gdiv := repeat match goal with |- context[?a / 2] =>
  let q := fresh "q" in
  pose proof (d2a a); pose proof (d2b a); generalize dependent (a / 2); intros q; intros end.

Lemma pow_mul : forall r a, 2 ^ S r * a = 2 * (2 ^ r * a).
Proof. intros. simpl. lia. Qed.

Section SW.
Variables Yp c cc ck ct cap : nat.

Definition TopR (p : list op) (A uem r nc : nat) (l : list st) : Prop :=
  exists o oL w', it p A = Some o /\ tape o = tape (oL ++ w') /\ dcnt oL = r /\ noH oL /\ endsd oL /\
    trimz w' = w' /\ uem + ucnt oL + ucnt w' <= cap /\
    (In (w', Yp, nc) l \/ exists v, w' = bin v /\ v <= Yp) /\
    (Yp = 15 -> ucnt w' <= 31).

Lemma proc_spec : forall d dg lc uem p l nc A,
  proc Yp c cc ck ct cap d dg lc uem p = Some l ->
  In nc (allowed d c cc ck ct) ->
  Yp - (dg + 1) / 2 <= A -> A <= Yp + lc ->
  exists o, it p A = Some o /\ uem + ucnt o <= cap /\ (Yp = 15 -> ucnt o <= 31) /\ In (trimz o, Yp, nc) l.
Proof.
  intros d dg lc uem p l nc A Hp Hn H1 H2. unfold proc in Hp.
  destruct (allowed d c cc ck ct) as [|n0 ncs] eqn:Ea; [contradiction|].
  destruct (ofold_spec _ _ _ _ _ Hp) as [_ Hf].
  assert (Hin : In A (rng (Yp - (dg + 1) / 2) (Yp + lc + 1 - (Yp - (dg + 1) / 2)))).
  { apply rng_in; lia. }
  destruct (Hf _ Hin) as [lx [Hx Hl]].
  destruct (it p A) as [o|]; [|discriminate].
  destruct (andb _ _) eqn:Eb; [|discriminate].
  apply Bool.andb_true_iff in Eb. destruct Eb as [Eb1 Eb2].
  apply Nat.leb_le in Eb1.
  injection Hx as <-. exists o. split; [reflexivity|]. split; [exact Eb1|]. split.
  - intros ->. apply Bool.orb_true_iff in Eb2. destruct Eb2 as [E|E]; [discriminate|].
    apply Nat.leb_le. exact E.
  - apply Hl. exact (in_map (fun nc0 => (trimz o, Yp, nc0)) (n0 :: ncs) nc Hn).
Qed.

(* One emission that reaches the cut. *)
Lemma last_emit : forall d dg lc uem p l nc A0 D,
  proc Yp c cc ck ct cap d dg lc uem p = Some l ->
  In nc (allowed d c cc ck ct) ->
  D <> H ->
  Yp - (dg + 1) / 2 <= A0 -> A0 <= Yp + lc ->
  exists o oL w', it p A0 = Some o /\ tape (D :: o) = tape (oL ++ w') /\ oL = [D] /\ w' = trimz o /\
    trimz w' = w' /\ uem + ucnt w' <= cap /\ In (w', Yp, nc) l /\ (Yp = 15 -> ucnt w' <= 31).
Proof.
  intros d dg lc uem p l nc A0 D Hp Hn HD H1 H2.
  destruct (proc_spec d dg lc uem p l nc A0 Hp Hn H1 H2) as [o [Hi [Hc [H15 Hl]]]].
  exists o, [D], (trimz o). split; [exact Hi|]. split.
  { simpl app. rewrite !tape_cons by exact HD. rewrite tape_trimz. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [apply trimz_idem|].
  pose proof (ucnt_trimz o). split; [lia|]. split; [exact Hl|].
  intros Hy. specialize (H15 Hy). lia.
Qed.

Lemma bitd_cases : forall n, bitd n = Z \/ bitd n = O.
Proof. intros n. unfold bitd. destruct (Nat.even n); auto. Qed.

Lemma sw_spec : forall p d0 dg lc uem l A r nc,
  sw Yp c cc ck ct cap p d0 dg lc uem = Some l ->
  8 <= Yp -> 1 <= r -> lc <= 1 ->
  2 ^ r * Yp < A + 1 + r + dg ->
  A + 1 <= 2 ^ r * (Yp + 1) + lc ->
  In nc (allowed (d0 + r) c cc ck ct) ->
  nc <= 2 ->
  TopR p A uem r nc l.
Proof.
  induction p as [|op p IH]; intros d0 dg lc uem l A r nc Hs HY Hr Hlc HLB HUB Ha Hn2.
  { discriminate. }
  destruct r as [|r]; [lia|].
  rewrite !pow_mul in HLB, HUB.
  pose proof (pow2_ge r) as HP.
  assert (H8 : (r + 1) * 8 <= 2 ^ r * Yp) by (apply Nat.mul_le_mono; lia).
  destruct op; cbn [sw] in Hs.
  - (* Dg *)
    destruct (negb (Nat.eqb lc 0)) eqn:El; [discriminate|].
    assert (Hl0 : lc = 0) by (apply Bool.negb_false_iff in El; apply Nat.eqb_eq in El; exact El). subst lc.
    destruct (proc _ _ _ _ _ _ _ _ _ _ _) as [l1|] eqn:Ep; [|discriminate].
    destruct (sw _ _ _ _ _ _ _ _ _ _ _) as [l2|] eqn:Es; [|discriminate].
    injection Hs as <-.
    destruct r as [|r].
    + (* last emission *)
      simpl in HLB, HUB.
      destruct (last_emit (S d0) (S dg) 0 uem p l1 nc (A / 2) (bitd A) Ep) as [o [oL [w' [Hi [Ht [-> [Ew [Etw [Hc [Hl H15]]]]]]]]]].
      * replace (S d0) with (d0 + 1) by lia. exact Ha.
      * apply bitd_not_H.
      * clear -HLB HUB Hlc. gdiv. lia.
      * clear -HLB HUB Hlc. gdiv. lia.
      * exists (bitd A :: o), [bitd A], w'.
        cbn [it]. rewrite Hi. split; [reflexivity|]. split; [exact Ht|].
        destruct (bitd_cases A) as [E|E]; rewrite E.
        all: split; [reflexivity|]; split; [exact I|]; split; [exact I|]; split; [exact Etw|].
        all: split; [cbn [ucnt]; lia|]; split; [left; apply in_or_app; auto|exact H15].
    + rewrite !pow_mul in HLB, HUB.
      destruct (IH (S d0) (S dg) 0 uem l2 (A / 2) (S r) nc Es HY ltac:(lia) ltac:(lia)) as [o [oL [w' [Hi [Ht [Hd [Hh [He [Etw [Hc [Hl H15]]]]]]]]]]].
      * rewrite !pow_mul. clear -HLB HUB Hlc. gdiv. lia.
      * rewrite !pow_mul. clear -HLB HUB Hlc. gdiv. lia.
      * replace (S d0 + S r) with (d0 + S (S r)) by lia. exact Ha.
      * exact Hn2.
      * exists (bitd A :: o), (bitd A :: oL), w'.
        cbn [it]. rewrite Hi. split; [reflexivity|]. split.
        { rewrite <- app_comm_cons, !cw_bit_tape, Ht. reflexivity. }
        destruct oL as [|x oL]; [contradiction|].
        destruct (bitd_cases A) as [E|E]; rewrite E.
        all: split; [cbn [dcnt] in *; lia|]; split; [exact Hh|]; split; [exact He|]; split; [exact Etw|].
        all: split; [cbn [ucnt] in *; lia|]; split; [|exact H15].
        all: destruct Hl as [Hl|Hl]; [left; apply in_or_app; auto|right; exact Hl].
  - (* Cv *)
    destruct (proc _ _ _ _ _ _ _ _ _ _ _) as [l1|] eqn:Ep; [|discriminate].
    destruct (sw _ _ _ _ _ _ _ _ _ _ _) as [l2|] eqn:Es; [|discriminate].
    injection Hs as <-.
    destruct r as [|r].
    + simpl in HLB, HUB.
      destruct (last_emit (S d0) dg 1 uem p l1 nc ((A + 1) / 2) (bitd (A + 1)) Ep) as [o [oL [w' [Hi [Ht [-> [Ew [Etw [Hc [Hl H15]]]]]]]]]].
      * replace (S d0) with (d0 + 1) by lia. exact Ha.
      * apply bitd_not_H.
      * clear -HLB HUB Hlc. gdiv. lia.
      * clear -HLB HUB Hlc. gdiv. lia.
      * exists (bitd (A + 1) :: o), [bitd (A + 1)], w'.
        cbn [it]. rewrite Hi. split; [reflexivity|]. split; [exact Ht|].
        destruct (bitd_cases (A + 1)) as [E|E]; rewrite E.
        all: split; [reflexivity|]; split; [exact I|]; split; [exact I|]; split; [exact Etw|].
        all: split; [cbn [ucnt]; lia|]; split; [left; apply in_or_app; auto|exact H15].
    + rewrite !pow_mul in HLB, HUB.
      destruct (IH (S d0) dg 1 uem l2 ((A + 1) / 2) (S r) nc Es HY ltac:(lia) ltac:(lia)) as [o [oL [w' [Hi [Ht [Hd [Hh [He [Etw [Hc [Hl H15]]]]]]]]]]].
      * rewrite !pow_mul. clear -HLB HUB Hlc. gdiv. lia.
      * rewrite !pow_mul. clear -HLB HUB Hlc. gdiv. lia.
      * replace (S d0 + S r) with (d0 + S (S r)) by lia. exact Ha.
      * exact Hn2.
      * exists (bitd (A + 1) :: o), (bitd (A + 1) :: oL), w'.
        cbn [it]. rewrite Hi. split; [reflexivity|]. split.
        { rewrite <- app_comm_cons, !cw_bit_tape, Ht. reflexivity. }
        destruct oL as [|x oL]; [contradiction|].
        destruct (bitd_cases (A + 1)) as [E|E]; rewrite E.
        all: split; [cbn [dcnt] in *; lia|]; split; [exact Hh|]; split; [exact He|]; split; [exact Etw|].
        all: split; [cbn [ucnt] in *; lia|]; split; [|exact H15].
        all: destruct Hl as [Hl|Hl]; [left; apply in_or_app; auto|right; exact Hl].
  - (* Rp *)
    destruct (Nat.leb dg 14) eqn:Ed; [|discriminate]. apply Nat.leb_le in Ed.
    destruct A as [|A].
    + exfalso. lia.
    + cbn [it]. apply (IH d0 (S dg) 0 uem l A (S r) nc Hs HY Hr ltac:(lia)).
      * rewrite !pow_mul. lia.
      * rewrite !pow_mul. lia.
      * exact Ha.
      * exact Hn2.
  - (* Rd *)
    destruct (IH d0 (S dg) lc (S (S uem)) l A (S r) nc Hs HY Hr Hlc) as [o [oL [w' [Hi [Ht [Hd [Hh [He [Etw [Hc [Hl H15]]]]]]]]]]].
    + rewrite !pow_mul. lia.
    + rewrite !pow_mul. lia.
    + exact Ha.
    + exact Hn2.
    + exists (U :: U :: o), (U :: U :: oL), w'. cbn [it]. rewrite Hi. split; [reflexivity|]. split.
      { cbn [app tape]. rewrite Ht. reflexivity. }
      destruct oL as [|x oL]; [contradiction|].
      split; [cbn [dcnt] in *; lia|]. split; [exact Hh|]. split; [exact He|]. split; [exact Etw|].
      split; [cbn [ucnt] in *; lia|]. split; [exact Hl|exact H15].
  - (* Em *)
    destruct (IH d0 dg lc (S uem) l A (S r) nc Hs HY Hr Hlc) as [o [oL [w' [Hi [Ht [Hd [Hh [He [Etw [Hc [Hl H15]]]]]]]]]]].
    + rewrite !pow_mul. lia.
    + rewrite !pow_mul. lia.
    + exact Ha.
    + exact Hn2.
    + exists (U :: o), (U :: oL), w'. cbn [it]. rewrite Hi. split; [reflexivity|]. split.
      { cbn [app tape]. rewrite Ht. reflexivity. }
      destruct oL as [|x oL]; [contradiction|].
      split; [cbn [dcnt] in *; lia|]. split; [exact Hh|]. split; [exact He|]. split; [exact Etw|].
      split; [cbn [ucnt] in *; lia|]. split; [exact Hl|exact H15].
  - (* E0 *)
    destruct (andb _ _) eqn:Eb; [|discriminate].
    apply Bool.andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Nat.eqb_eq in E1. apply Nat.leb_le in E2. subst lc.
    assert (Hv : A / 2 ^ S r < Yp + 1).
    { apply Nat.div_lt_upper_bound; [apply Nat.pow_nonzero; lia|]. rewrite !pow_mul. lia. }
    destruct (split_bin (S r) A ltac:(lia)) as [oL [H1 [H2 [H3 [H4 H5]]]]].
    exists (bin A), oL, (bin (A / 2 ^ S r)). cbn [it].
    split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    split; [apply trimz_bin|]. split; [rewrite H5, ucnt_bin; lia|]. split.
    + right. eexists. split; [reflexivity|lia].
    + rewrite ucnt_bin. lia.
  - (* E1 *)
    destruct (andb _ _) eqn:Eb; [|discriminate].
    apply Bool.andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Nat.leb_le in E1. apply Nat.leb_le in E2.
    destruct A as [|A]; [exfalso; lia|].
    assert (Hv : A / 2 ^ S r < Yp + 1).
    { apply Nat.div_lt_upper_bound; [apply Nat.pow_nonzero; lia|]. rewrite !pow_mul. lia. }
    destruct (split_bin (S r) A ltac:(lia)) as [oL [H1 [H2 [H3 [H4 H5]]]]].
    exists (U :: U :: bin A), (U :: U :: oL), (bin (A / 2 ^ S r)). cbn [it].
    split; [reflexivity|]. split; [cbn [app tape]; rewrite H1; reflexivity|].
    destruct oL as [|x oL]; [contradiction|].
    split; [cbn [dcnt] in *; lia|]. split; [exact H3|]. split; [exact H4|].
    split; [apply trimz_bin|]. split; [rewrite ucnt_bin; cbn [ucnt] in *; lia|]. split.
    + right. eexists. split; [reflexivity|lia].
    + rewrite ucnt_bin. lia.
  - (* E2 *)
    destruct (andb _ _) eqn:Eb; [|discriminate].
    apply Bool.andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Nat.eqb_eq in E1. apply Nat.leb_le in E2. subst lc.
    assert (Hv : A / 2 ^ S r < Yp + 1).
    { apply Nat.div_lt_upper_bound; [apply Nat.pow_nonzero; lia|]. rewrite !pow_mul. lia. }
    destruct (split_bin (S r) A ltac:(lia)) as [oL [H1 [H2 [H3 [H4 H5]]]]].
    exists (U :: U :: bin A), (U :: U :: oL), (bin (A / 2 ^ S r)). cbn [it].
    split; [reflexivity|]. split; [cbn [app tape]; rewrite H1; reflexivity|].
    destruct oL as [|x oL]; [contradiction|].
    split; [cbn [dcnt] in *; lia|]. split; [exact H3|]. split; [exact H4|].
    split; [apply trimz_bin|]. split; [rewrite ucnt_bin; cbn [ucnt] in *; lia|]. split.
    + right. eexists. split; [reflexivity|lia].
    + rewrite ucnt_bin. lia.
  - (* EH0 *)
    destruct (andb _ _) eqn:Eb; [|discriminate].
    apply Bool.andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Nat.eqb_eq in E1. apply Nat.leb_le in E2. subst lc.
    injection Hs as <-.
    assert (Hv : (S A) / 2 ^ S r < Yp + 2).
    { apply Nat.div_lt_upper_bound; [apply Nat.pow_nonzero; lia|]. rewrite !pow_mul.
      replace (Yp + 2) with (Yp + 1 + 1) by lia. rewrite Nat.mul_add_distr_l, Nat.mul_1_r. lia. }
    destruct (split_bin (S r) (S A) ltac:(lia)) as [oL [H1 [H2 [H3 [H4 H5]]]]].
    exists (bin (S A)), oL, (bin (S A / 2 ^ S r)). cbn [it].
    split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    split; [apply trimz_bin|]. split; [rewrite H5, ucnt_bin; lia|]. split.
    + destruct (Nat.eq_dec (S A / 2 ^ S r) (S Yp)) as [Ee|Ee].
      * left. rewrite Ee. destruct nc as [|[|[|nc]]]; simpl; auto; lia.
      * right. eexists. split; [reflexivity|lia].
    + rewrite ucnt_bin. lia.
  - (* EH1 *)
    destruct (Nat.leb (S uem) cap) eqn:E2; [|discriminate]. apply Nat.leb_le in E2.
    injection Hs as <-.
    assert (Hv : A / 2 ^ S r < Yp + 2).
    { apply Nat.div_lt_upper_bound; [apply Nat.pow_nonzero; lia|]. rewrite !pow_mul.
      replace (Yp + 2) with (Yp + 1 + 1) by lia. rewrite Nat.mul_add_distr_l, Nat.mul_1_r. lia. }
    destruct (split_bin (S r) A ltac:(lia)) as [oL [H1 [H2 [H3 [H4 H5]]]]].
    exists (U :: bin A), (U :: oL), (bin (A / 2 ^ S r)). cbn [it].
    split; [reflexivity|]. split; [cbn [app tape]; rewrite H1; reflexivity|].
    destruct oL as [|x oL]; [contradiction|].
    split; [cbn [dcnt] in *; lia|]. split; [exact H3|]. split; [exact H4|].
    split; [apply trimz_bin|]. split; [rewrite ucnt_bin; cbn [ucnt] in *; lia|]. split.
    + destruct (Nat.eq_dec (A / 2 ^ S r) (S Yp)) as [Ee|Ee].
      * left. rewrite Ee. destruct nc as [|[|[|nc]]]; simpl; auto; lia.
      * right. eexists. split; [reflexivity|lia].
    + rewrite ucnt_bin. lia.
  - discriminate.
Qed.

End SW.

(* The closure. *)
Definition okx (T : trie) (x : st) : Prop :=
  exists l, succs x = Some l /\ forall y, In y l -> vb y = true /\ memk (key y) T = true.

Lemma okx_mono : forall T T' x,
  (forall k, memk k T = true -> memk k T' = true) -> okx T x -> okx T' x.
Proof.
  intros T T' x Hm [l [H1 H2]]. exists l. split; [exact H1|].
  intros y Hy. destruct (H2 y Hy) as [H3 H4]. split; [exact H3|]. apply Hm. exact H4.
Qed.

Lemma pref_inj : forall Y c Y' c',
  8 <= Y <= 15 -> c <= 2 -> 8 <= Y' <= 15 -> c' <= 2 -> pref Y c = pref Y' c' -> Y = Y' /\ c = c'.
Proof.
  intros Y c Y' c' H1 H2 H3 H4 H.
  assert (HY : Y = 8 \/ Y = 9 \/ Y = 10 \/ Y = 11 \/ Y = 12 \/ Y = 13 \/ Y = 14 \/ Y = 15) by lia.
  assert (HY' : Y' = 8 \/ Y' = 9 \/ Y' = 10 \/ Y' = 11 \/ Y' = 12 \/ Y' = 13 \/ Y' = 14 \/ Y' = 15) by lia.
  assert (Hc : c = 0 \/ c = 1 \/ c = 2) by lia.
  assert (Hc' : c' = 0 \/ c' = 1 \/ c' = 2) by lia.
  destruct HY as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]], Hc as [->|[->| ->]];
  destruct HY' as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]], Hc' as [->|[->| ->]];
  first [split; reflexivity | vm_compute in H; discriminate].
Qed.

Lemma key_inj : forall x y, vb x = true -> vb y = true -> key x = key y -> x = y.
Proof.
  intros [[w Y] c] [[w' Y'] c'] Hx Hy H. cbn [vb key] in *.
  apply Bool.andb_true_iff in Hx, Hy. destruct Hx as [Hx Hx3], Hy as [Hy Hy3].
  apply Bool.andb_true_iff in Hx, Hy. destruct Hx as [Hx1 Hx2], Hy as [Hy1 Hy2].
  apply Nat.leb_le in Hx1, Hx2, Hx3, Hy1, Hy2, Hy3.
  unfold pref in H. cbn [app] in H. injection H as H1 H2 H3 H4 H5 H6. subst w'.
  assert (Hp : pref Y c = pref Y' c') by (unfold pref; congruence).
  destruct (pref_inj Y c Y' c') as [-> ->]; auto.
Qed.

Lemma addall_spec : forall l T todo T' todo', addall l T todo = (T', todo') ->
  (forall k, memk k T = true -> memk k T' = true) /\
  (forall y, In y l -> memk (key y) T' = true) /\
  (forall x, In x todo -> In x todo') /\
  (forall x, In x todo' -> In x todo \/ In x l) /\
  (forall k, memk k T' = true -> memk k T = true \/ exists x, In x todo' /\ key x = k).
Proof.
  induction l as [|y l IH]; intros T todo T' todo' Ha; cbn [addall] in Ha.
  - injection Ha as <- <-. split; [auto|]. split; [intros y []|]. split; [auto|]. split; [auto|]. auto.
  - destruct (memk (key y) T) eqn:Em.
    + destruct (IH _ _ _ _ Ha) as [H1 [H2 [H3 [H4 H5]]]].
      split; [exact H1|]. split.
      { intros z [<-|Hz]; auto. }
      split; [exact H3|]. split.
      { intros x Hx. destruct (H4 x Hx); simpl; auto. }
      exact H5.
    + destruct (IH _ _ _ _ Ha) as [H1 [H2 [H3 [H4 H5]]]].
      split; [|split; [|split; [|split]]].
      * intros k Hk. apply H1. apply memk_insk_mono. exact Hk.
      * intros z [<-|Hz]; auto. apply H1. apply memk_insk_self.
      * intros x Hx. apply H3. right. exact Hx.
      * intros x Hx. destruct (H4 x Hx) as [[<-|Hz]|Hz]; simpl; auto.
      * intros k Hk. destruct (H5 k Hk) as [Hk1|Hk1].
        -- destruct (memk_insk _ _ _ Hk1) as [->|Hk2]; auto.
           right. exists y. split; [apply H3; left; reflexivity|reflexivity].
        -- auto.
Qed.

Lemma bfs_ok : forall fuel todo T R, bfs fuel todo T = Some R ->
  (forall x, vb x = true -> memk (key x) T = true -> In x todo \/ okx T x) ->
  (forall x, In x todo -> vb x = true) ->
  (forall x, vb x = true -> memk (key x) R = true -> okx R x) /\
  (forall k, memk k T = true -> memk k R = true).
Proof.
  induction fuel as [|f IH]; intros todo T R Hb I1 I2.
  - destruct todo as [|x todo]; [|discriminate].
    injection Hb as <-. split; auto.
    intros x Hx Hm. destruct (I1 x Hx Hm) as [[]|H]; exact H.
  - destruct todo as [|x todo].
    + injection Hb as <-. split; auto.
      intros x Hx Hm. destruct (I1 x Hx Hm) as [[]|H]; exact H.
    + cbn [bfs] in Hb. destruct (succs x) as [l|] eqn:Es; [|discriminate].
      destruct (forallb vb l) eqn:Efa; [|discriminate].
      destruct (addall l T todo) as [T' todo'] eqn:Ea.
      destruct (addall_spec _ _ _ _ _ Ea) as [A1 [A2 [A3 [A4 A5]]]].
      rewrite forallb_forall in Efa.
      assert (HT : forall z, In z todo' -> vb z = true).
      { intros z Hz. destruct (A4 z Hz) as [H|H].
        - apply I2. right. exact H.
        - apply Efa. exact H. }
      destruct (IH _ _ _ Hb) as [R1 R2].
      * intros z Hz Hm. destruct (A5 _ Hm) as [H|[w [Hw Hk]]].
        -- destruct (I1 z Hz H) as [[<-|H']|H'].
           ++ right. exists l. split; [exact Es|]. intros y Hy. split; [apply Efa; exact Hy|apply A2; exact Hy].
           ++ left. apply A3. exact H'.
           ++ right. apply (okx_mono T); [exact A1|exact H'].
        -- left. rewrite <- (key_inj w z (HT w Hw) Hz Hk). exact Hw.
      * exact HT.
      * split; [exact R1|]. intros k Hk. apply R2. apply A1. exact Hk.
Qed.

Definition seedsok : bool := forallb vb seeds.

Lemma closure_ok : forall fuel R, closure fuel = Some R -> seedsok = true ->
  (forall x, vb x = true -> memk (key x) R = true -> okx R x) /\
  (forall y, In y seeds -> memk (key y) R = true).
Proof.
  intros fuel R Hc Hs. unfold closure in Hc.
  destruct (addall seeds Tn []) as [T t] eqn:Ea.
  destruct (addall_spec _ _ _ _ _ Ea) as [A1 [A2 [A3 [A4 A5]]]].
  unfold seedsok in Hs. rewrite forallb_forall in Hs.
  assert (HT : forall z, In z t -> vb z = true).
  { intros z Hz. destruct (A4 z Hz) as [[]|H]. apply Hs. exact H. }
  destruct (bfs_ok _ _ _ _ Hc) as [R1 R2].
  - intros z Hz Hm. left. destruct (A5 _ Hm) as [H|[w [Hw Hk]]].
    + destruct (key z) as [|d k]; simpl in H; discriminate.
    + rewrite <- (key_inj w z (HT w Hw) Hz Hk). exact Hw.
  - exact HT.
  - split; [exact R1|]. intros y Hy. apply R2. apply A2. exact Hy.
Qed.

Lemma seeds_in : forall Y v c, 8 <= Y <= 15 -> v <= Y -> c <= 2 -> In (bin v, Y, c) seeds.
Proof.
  intros Y v c HY Hv Hc. unfold seeds.
  apply in_flat_map. exists Y. split; [apply rng_in; lia|].
  apply in_flat_map. exists v. split; [apply rng_in; lia|].
  apply (in_map (fun c0 => (bin v, Y, c0))). simpl.
  destruct c as [|[|[|c]]]; simpl; auto; lia.
Qed.

Lemma allowed_le : forall d c cc ck ct nc, c <= 2 -> In nc (allowed d c cc ck ct) -> nc <= 2.
Proof.
  intros d c cc ck ct nc Hc Hn. destruct d as [|[|[|d]]]; simpl in Hn.
  - contradiction.
  - destruct (andb _ _) in Hn; simpl in Hn; [destruct Hn as [<-|[]]; lia|contradiction].
  - apply in_app_or in Hn. destruct Hn as [Hn|Hn]; destruct (_ && _)%bool in Hn || destruct (Nat.leb cc ck) in Hn; simpl in Hn; try contradiction.
    all: destruct Hn as [<-|[]]; lia.
  - destruct Hn as [<-|[]]. lia.
Qed.

(* What the closure gives for one pass, in one statement. *)
Theorem top_step : forall R,
  (forall x, vb x = true -> memk (key x) R = true -> okx R x) ->
  (forall y, In y seeds -> memk (key y) R = true) ->
  forall w Y c dv w1 Yp m cc A d nc,
  vb (w, Y, c) = true -> memk (key (w, Y, c)) R = true -> dv <= 1 -> drift w Y dv = (w1, Yp) ->
  1 <= d ->
  In nc (allowed d c cc (ckf c) (ctf (M1 Yp) (ucnt w1))) -> cc <= cgf (M1 Yp) (ucnt w1) ->
  2 ^ d * Yp <= A + d -> A + 1 <= 2 ^ d * (Yp + 1) ->
  ucnt w1 <= M1 Yp /\ (Y + dv = 16 -> hfirst w = false) /\
  exists o oL w', it (path m w1 cc) A = Some o /\ tape o = tape (oL ++ w') /\ dcnt oL = d /\ noH oL /\ endsd oL /\
    trimz w' = w' /\ ucnt oL + ucnt w' <= capf (M1 Yp) (ucnt w1) /\
    vb (w', Yp, nc) = true /\ memk (key (w', Yp, nc)) R = true /\ (Yp = 15 -> ucnt w' <= 31).
Proof.
  intros R Hok Hseed w Y c dv w1 Yp m cc A d nc Hv Hm Hdv Hdr Hd Ha Hcc H1 H2.
  destruct (Hok _ Hv Hm) as [l [Hs Hl]].
  cbn [succs] in Hs.
  destruct (ofold_spec _ _ _ _ _ Hs) as [_ Hf].
  assert (Hin : In dv [0; 1]) by (destruct dv as [|[|dv]]; simpl; auto; lia).
  destruct (Hf _ Hin) as [l1 [Hs1 Hl1]].
  unfold succ1 in Hs1. rewrite Hdr in Hs1.
  destruct (andb _ _) eqn:Eb; [|discriminate].
  apply Bool.andb_true_iff in Eb. destruct Eb as [Eb1 Eb2].
  apply Nat.leb_le in Eb1.
  cbn [vb] in Hv. apply Bool.andb_true_iff in Hv. destruct Hv as [Hv Hv3].
  apply Bool.andb_true_iff in Hv. destruct Hv as [Hv1 Hv2].
  apply Nat.leb_le in Hv1, Hv2, Hv3.
  assert (HYp : 8 <= Yp <= 15).
  { unfold drift in Hdr. destruct (Nat.eqb (Y + dv) 16) eqn:Eq; injection Hdr as <- <-.
    - lia.
    - apply Nat.eqb_neq in Eq. lia. }
  split; [exact Eb1|]. split.
  { intros E16. apply Nat.eqb_eq in E16. rewrite E16 in Eb2. simpl in Eb2.
    destruct (hfirst w); [discriminate|reflexivity]. }
  destruct (ofold_spec _ _ _ _ _ Hs1) as [_ Hf1].
  assert (Hin2 : In cc (rng 0 (S (cgf (M1 Yp) (ucnt w1))))) by (apply rng_in; lia).
  destruct (Hf1 _ Hin2) as [l2 [Hs2 Hl2]].
  destruct (ofold_spec _ _ _ _ _ Hs2) as [_ Hf2].
  assert (Hin3 : In m [S_0; S_1; T_]) by (destruct m; simpl; auto).
  destruct (Hf2 _ Hin3) as [l3 [Hs3 Hl3]].
  pose proof (allowed_le _ _ _ _ _ _ Hv3 Ha) as Hnc.
  destruct (sw_spec Yp c cc (ckf c) (ctf (M1 Yp) (ucnt w1)) (capf (M1 Yp) (ucnt w1)) _ 0 0 0 0 l3 A d nc Hs3)
    as [o [oL [w' [Hi [Ht [Hd1 [Hh [He [Etw [Hc [Hin4 H15]]]]]]]]]]]; try lia.
  { exact Ha. }
  exists o, oL, w'. split; [exact Hi|]. split; [exact Ht|]. split; [exact Hd1|]. split; [exact Hh|].
  split; [exact He|]. split; [exact Etw|]. split; [lia|].
  assert (Hvb : vb (w', Yp, nc) = true).
  { cbn [vb]. apply Bool.andb_true_iff. split; [apply Bool.andb_true_iff; split|]; apply Nat.leb_le; lia. }
  split; [exact Hvb|]. split; [|exact H15].
  destruct Hin4 as [Hin4|[v [-> Hv]]].
  - apply (Hl (w', Yp, nc)). apply Hl1. apply Hl2. apply Hl3. exact Hin4.
  - apply Hseed. apply seeds_in; lia.
Qed.

(* The numeric clause. *)
Definition a_ (e : nat) : nat := e + 8.

Fixpoint K4 (n : nat) : nat :=
  match n with
  | 0 => 24
  | S n' => K4 n' + 3 * n' + 39
  end.

Definition top4 (x : nat) : nat := x / 2 ^ (Nat.log2 x - 3).

Definition GG (x : nat) : nat := K4 (Nat.log2 x - 4) + M1 (top4 x).

Definition clause (m c L u : nat) : Prop :=
  16 <= m / 2 ^ L -> u + c * a_ (Nat.log2 (m / 2 ^ L)) <= GG (m / 2 ^ L).

Fixpoint NCr (m c L : nat) (r : list dg) : Prop :=
  match r with
  | [] => True
  | U :: r' => NCr m c L r'
  | H :: _ => True
  | _ :: r' => clause m c (S L) (ucnt r') /\ NCr m c (S L) r'
  end.

Lemma M1_mono : forall a b, 8 <= a -> a <= b -> b <= 15 -> M1 a <= M1 b.
Proof.
  intros a b H1 H2 H3.
  assert (Ha : a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15) by lia.
  assert (Hb : b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15) by lia.
  destruct Ha as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]], Hb as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
  simpl; lia.
Qed.

Lemma M1_range : forall a, 8 <= a -> a <= 15 -> 31 <= M1 a <= 40.
Proof.
  intros a H1 H2.
  assert (Ha : a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15) by lia.
  destruct Ha as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; simpl; lia.
Qed.

Lemma K4_step : forall n, K4 (S n) = K4 n + 3 * n + 39.
Proof. reflexivity. Qed.

Lemma K4_mono : forall n d, K4 n + 39 * d <= K4 (n + d).
Proof.
  intros n d. induction d as [|d IH].
  - replace (n + 0) with n by lia. lia.
  - replace (n + S d) with (S (n + d)) by lia. rewrite K4_step. lia.
Qed.

Lemma log2_range : forall x, 0 < x -> 2 ^ Nat.log2 x <= x /\ x < 2 ^ S (Nat.log2 x).
Proof.
  intros x Hx. destruct (Nat.log2_spec x Hx) as [H1 H2]. split; assumption.
Qed.

Lemma pow_S : forall n, 2 ^ S n = 2 * 2 ^ n.
Proof. intros. reflexivity. Qed.

Lemma pow_pos : forall n, 1 <= 2 ^ n.
Proof. intros n. pose proof (Nat.pow_nonzero 2 n). lia. Qed.

Lemma log2_ge : forall x e, 2 ^ e <= x -> e <= Nat.log2 x.
Proof.
  intros x e H. apply Nat.log2_le_pow2; [pose proof (pow_pos e); lia|exact H].
Qed.

Lemma top4_range : forall x, 8 <= x -> 8 <= top4 x < 16.
Proof.
  intros x Hx. unfold top4.
  assert (He : 3 <= Nat.log2 x) by (apply log2_ge; simpl; lia).
  destruct (log2_range x ltac:(lia)) as [H1 H2].
  remember (Nat.log2 x) as e eqn:Ee.
  replace e with (3 + (e - 3)) in H1, H2 by lia.
  remember (e - 3) as f.
  split.
  - apply Nat.div_le_lower_bound; [pose proof (pow_pos f); lia|].
    rewrite Nat.pow_add_r in H1. simpl in H1. lia.
  - apply Nat.div_lt_upper_bound; [pose proof (pow_pos f); lia|].
    replace (S (3 + f)) with (4 + f) in H2 by lia. rewrite Nat.pow_add_r in H2. simpl in H2. lia.
Qed.

Lemma log2_double : forall x, 1 <= x -> Nat.log2 (2 * x) = S (Nat.log2 x).
Proof.
  intros x Hx. apply Nat.log2_double. lia.
Qed.

Lemma top4_double : forall x, 8 <= x -> top4 (2 * x) = top4 x.
Proof.
  intros x Hx. unfold top4. rewrite log2_double by lia.
  assert (He : 3 <= Nat.log2 x) by (apply log2_ge; simpl; lia).
  replace (S (Nat.log2 x) - 3) with (S (Nat.log2 x - 3)) by lia.
  rewrite pow_S. rewrite Nat.div_mul_cancel_l; [reflexivity|apply Nat.pow_nonzero; lia|lia].
Qed.

Lemma top4_mono : forall x y, 8 <= x -> x <= y -> Nat.log2 x = Nat.log2 y -> top4 x <= top4 y.
Proof.
  intros x y H1 H2 H3. unfold top4. rewrite <- H3. apply Nat.Div0.div_le_mono. exact H2.
Qed.

(* G grows faster than c * a. *)
Lemma GG_mono : forall x y c, 16 <= x -> x <= y -> c <= 2 ->
  GG x + c * a_ (Nat.log2 y) <= GG y + c * a_ (Nat.log2 x).
Proof.
  intros x y c Hx Hxy Hc. unfold GG, a_.
  assert (He4 : 4 <= Nat.log2 x) by (apply log2_ge; simpl; lia).
  assert (Hle : Nat.log2 x <= Nat.log2 y) by (apply Nat.log2_le_mono; exact Hxy).
  destruct (top4_range x ltac:(lia)) as [T1 T2].
  destruct (top4_range y ltac:(lia)) as [T3 T4].
  destruct (Nat.eq_dec (Nat.log2 x) (Nat.log2 y)) as [He|He].
  - rewrite <- He. pose proof (M1_mono (top4 x) (top4 y) T1 (top4_mono x y ltac:(lia) Hxy He) ltac:(lia)). lia.
  - pose proof (M1_range _ T1 ltac:(lia)). pose proof (M1_range _ T3 ltac:(lia)).
    pose proof (K4_mono (Nat.log2 x - 4) (Nat.log2 y - Nat.log2 x)) as HK.
    replace (Nat.log2 x - 4 + (Nat.log2 y - Nat.log2 x)) with (Nat.log2 y - 4) in HK by lia.
    destruct c as [|[|[|c]]]; try lia.
Qed.

(* N step: what a pass adds in one level. *)
Lemma GG_double : forall x, 16 <= x ->
  GG x + (Nat.log2 x + 9) + 2 * a_ (S (Nat.log2 x)) <= GG (2 * x) /\ Nat.log2 (2 * x) = S (Nat.log2 x).
Proof.
  intros x Hx.
  assert (He4 : 4 <= Nat.log2 x) by (apply log2_ge; simpl; lia).
  split; [|apply log2_double; lia].
  unfold GG, a_. rewrite top4_double by lia. rewrite log2_double by lia.
  replace (S (Nat.log2 x) - 4) with (S (Nat.log2 x - 4)) by lia.
  rewrite K4_step. lia.
Qed.

Lemma Nstep : forall x y u c, 16 <= x -> 2 * x <= y -> c <= 2 -> u <= GG x + (Nat.log2 x + 9) ->
  u + c * a_ (Nat.log2 y) <= GG y.
Proof.
  intros x y u c Hx Hxy Hc Hu.
  destruct (GG_double x Hx) as [H1 H2].
  pose proof (GG_mono (2 * x) y c ltac:(lia) Hxy Hc) as H3.
  rewrite H2 in H3.
  destruct c as [|[|[|c]]]; try lia.
Qed.

(* The cut itself: a top word enters the numeric clause. *)
Lemma Bstep : forall Y y u c, 8 <= Y -> Y <= 15 -> 2 * Y <= y -> c <= 2 -> u <= M1 Y ->
  u + c * a_ (Nat.log2 y) <= GG y.
Proof.
  intros Y y u c H1 H2 Hy Hc Hu.
  assert (H3 : GG (2 * Y) = 24 + M1 Y).
  { unfold GG. rewrite top4_double by lia.
    assert (H4 : Nat.log2 (2 * Y) = 4).
    { apply Nat.log2_unique; [lia|]. simpl. lia. }
    rewrite H4. unfold top4.
    assert (H5 : Nat.log2 Y = 3).
    { apply Nat.log2_unique; [lia|]. simpl. lia. }
    rewrite H5.
    replace (4 - 4) with 0 by reflexivity. replace (3 - 3) with 0 by reflexivity.
    rewrite Nat.pow_0_r, Nat.div_1_r. reflexivity. }
  assert (H6 : Nat.log2 (2 * Y) = 4).
  { apply Nat.log2_unique; [lia|]. simpl. lia. }
  pose proof (GG_mono (2 * Y) y c ltac:(lia) Hy Hc) as H7.
  rewrite H6 in H7. unfold a_ in *.
  destruct c as [|[|[|c]]]; try lia.
Qed.

Lemma Tstep : forall x y u u' c c', 16 <= x -> x <= y -> c' + 1 <= c -> c <= 2 ->
  u + c * a_ (Nat.log2 x) <= GG x -> u' <= u + a_ (Nat.log2 x) ->
  u' + c' * a_ (Nat.log2 y) <= GG y.
Proof.
  intros x y u u' c c' Hx Hxy Hc Hc2 H1 H2.
  pose proof (GG_mono x y c' Hx Hxy ltac:(lia)) as H3.
  destruct c as [|[|[|c]]], c' as [|[|c']]; try lia.
Qed.

(* Levels of the low part. *)
Lemma div_pow_add : forall m a b, m / 2 ^ (a + b) = (m / 2 ^ a) / 2 ^ b.
Proof.
  intros m a b. rewrite Nat.pow_add_r. rewrite Nat.Div0.div_div. reflexivity.
Qed.

Lemma x_double : forall m L, 2 * (m / 2 ^ S L) <= m / 2 ^ L.
Proof.
  intros m L. replace (S L) with (L + 1) by lia. rewrite div_pow_add.
  replace (2 ^ 1) with 2 by reflexivity.
  exact (d2b (m / 2 ^ L)).
Qed.

Lemma x_anti : forall m L L', L' <= L -> m / 2 ^ L <= m / 2 ^ L'.
Proof.
  intros m L L' H. apply Nat.div_le_compat_l. split; [pose proof (pow_pos L'); lia|].
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma x_mono : forall m m' L, m <= m' -> m / 2 ^ L <= m' / 2 ^ L.
Proof.
  intros. apply Nat.Div0.div_le_mono. assumption.
Qed.

Lemma x_step : forall m m' L L', m <= m' -> L' + 1 <= L -> 2 * (m / 2 ^ L) <= m' / 2 ^ L'.
Proof.
  intros m m' L L' Hm HL.
  destruct L as [|L]; [lia|].
  pose proof (x_double m L) as H1.
  pose proof (x_anti m L L' ltac:(lia)) as H2.
  pose proof (x_mono m m' L' Hm) as H3.
  lia.
Qed.

Lemma low_log : forall m L i, 8 <= m / 2 ^ (L + i) -> m / 2 ^ (L + i) < 16 ->
  Nat.log2 (m / 2 ^ L) = 3 + i /\ top4 (m / 2 ^ L) = m / 2 ^ (L + i).
Proof.
  intros m L i H1 H2.
  rewrite div_pow_add in H1, H2.
  remember (m / 2 ^ L) as x.
  assert (Hp : 1 <= 2 ^ i) by apply pow_pos.
  assert (H3 : 8 * 2 ^ i <= x).
  { assert (Hq : 2 ^ i * 8 <= 2 ^ i * (x / 2 ^ i)) by (apply Nat.mul_le_mono_l; exact H1).
    pose proof (Nat.div_mod_eq x (2 ^ i)). lia. }
  assert (H4 : x < 16 * 2 ^ i).
  { destruct (Nat.lt_ge_cases x (16 * 2 ^ i)) as [Hl|Hl]; [exact Hl|]. exfalso.
    assert (Hq : 16 <= x / 2 ^ i) by (apply Nat.div_le_lower_bound; lia). lia. }
  assert (He : Nat.log2 x = 3 + i).
  { apply Nat.log2_unique; [lia|]. split.
    - rewrite Nat.pow_add_r. simpl. lia.
    - replace (S (3 + i)) with (4 + i) by lia. rewrite Nat.pow_add_r. simpl. lia. }
  split; [exact He|]. unfold top4. rewrite He. replace (3 + i - 3) with i by lia.
  rewrite div_pow_add. rewrite <- Heqx. reflexivity.
Qed.

Lemma GG_low : forall m L i, 1 <= i -> 8 <= m / 2 ^ (L + i) -> m / 2 ^ (L + i) < 16 ->
  GG (m / 2 ^ L) = K4 (i - 1) + M1 (m / 2 ^ (L + i)).
Proof.
  intros m L i Hi H1 H2. destruct (low_log m L i H1 H2) as [H3 H4].
  unfold GG. rewrite H3, H4. replace (3 + i - 4) with (i - 1) by lia. reflexivity.
Qed.

Lemma d2c : forall A, A <= 2 * ((A + 1) / 2).
Proof. intros A. gdiv. lia. Qed.
Lemma d2d : forall A, 2 * ((A + 1) / 2) <= A + 1.
Proof. intros A. gdiv. lia. Qed.

Definition bv (e : dg) : nat := match e with O => 1 | _ => 0 end.

Lemma path_dig : forall m e X cc, e = Z \/ e = O ->
  path m (e :: X) cc = pdig m (cc + bv e) (fun m' => path m' X ((cc + bv e) / 2)).
Proof.
  intros m e X cc [-> | ->]; cbn [path bv]; [rewrite Nat.add_0_r|]; reflexivity.
Qed.

Lemma it_S0_dig : forall v rest A,
  it (pdig S_0 v rest) A = option_map (cons (bitd A)) (it (rest (mbit v)) (A / 2)).
Proof. reflexivity. Qed.

Lemma it_S1_even : forall v rest A, Nat.even v = true ->
  it (pdig S_1 v rest) (S A) = it (rest T_) A.
Proof. intros v rest A E. unfold pdig. rewrite E. reflexivity. Qed.

Lemma it_S1_odd : forall v rest A, Nat.even v = false ->
  it (pdig S_1 v rest) (S A) = option_map (cons U) (it (rest S_0) A).
Proof. intros v rest A E. unfold pdig. rewrite E. reflexivity. Qed.

Lemma it_T_dig : forall v rest A,
  it (pdig T_ v rest) A = option_map (fun o => U :: U :: o) (it (rest (mbit v)) A).
Proof. reflexivity. Qed.

(* Carry after reading a digit. *)
Definition nt (k cc Lin : nat) : Prop := cc * 2 ^ Lin + 1 <= k + 2 ^ Lin.

Lemma nt_step : forall k cc Lin v, nt k cc Lin -> v <= cc + 1 -> nt k (v / 2) (S Lin).
Proof.
  intros k cc Lin v H Hv. unfold nt in *. rewrite pow_S.
  pose proof (d2b v) as H1.
  assert (H2 : v / 2 * (2 * 2 ^ Lin) <= (cc + 1) * 2 ^ Lin).
  { replace (v / 2 * (2 * 2 ^ Lin)) with ((2 * (v / 2)) * 2 ^ Lin) by lia.
    apply Nat.mul_le_mono_r. lia. }
  rewrite Nat.mul_add_distr_r in H2. lia.
Qed.

Definition tbq (k L M cc u Lin : nat) : Prop :=
  exists i Lb ib cz, Lin = Lb + i /\ L = Lb + ib /\ 1 <= ib /\
    2 ^ i * cc + u + ib + 11 <= 2 ^ i + cz + K4 (ib - 1) + M /\ cz * 2 ^ Lb <= k.

Lemma tbq_step : forall k L M cc u Lin v, tbq k L M cc u Lin -> v <= cc + 1 ->
  tbq k L M (v / 2) u (S Lin).
Proof.
  intros k L M cc u Lin v [i [Lb [ib [cz [E1 [E2 [E3 [E4 E5]]]]]]]] Hv.
  exists (S i), Lb, ib, cz. split; [lia|]. split; [exact E2|]. split; [exact E3|]. split; [|exact E5].
  rewrite pow_S. pose proof (d2b v) as H1.
  assert (H2 : 2 * 2 ^ i * (v / 2) <= 2 ^ i * (cc + 1)).
  { replace (2 * 2 ^ i * (v / 2)) with (2 ^ i * (2 * (v / 2))) by lia.
    apply Nat.mul_le_mono_l. lia. }
  rewrite Nat.mul_add_distr_l in H2. lia.
Qed.

Lemma tbq_u : forall k L M cc u u' Lin, tbq k L M cc u Lin -> u' <= u -> tbq k L M cc u' Lin.
Proof.
  intros k L M cc u u' Lin [i [Lb [ib [cz [E1 [E2 [E3 [E4 E5]]]]]]]] H.
  exists i, Lb, ib, cz. repeat split; try assumption. lia.
Qed.

(* The end of a T tunnel at the cut. *)
Lemma K4_high : forall t, K4 (2 + t) + 2 ^ t <= 14 + t + 100 * 2 ^ t.
Proof.
  induction t as [|t IH]; [simpl; lia|].
  replace (2 + S t) with (S (2 + t)) by lia. rewrite K4_step, pow_S. pose proof (pow_pos t) as P.
  pose proof (pow2_ge t). lia.
Qed.

Lemma T_final : forall k L M cc U0,
  tbq k L M cc U0 L -> k * 8 < 2 ^ L -> U0 <= M ->
  cc <= ctf M U0.
Proof.
  intros k L M cc U0 [i [Lb [ib [cz [E1 [E2 [E3 [E4 E5]]]]]]]] Hk HU.
  assert (Hi : i = ib) by lia. subst i.
  unfold ctf. apply Nat.max_le_iff.
  destruct (Nat.le_gt_cases ib 3) as [Hsmall|Hbig].
  - assert (Hcz : cz = 0).
    { destruct cz as [|cz]; [reflexivity|]. exfalso.
      assert (H2 : 2 ^ L <= 2 ^ Lb * 8).
      { rewrite E2. rewrite Nat.pow_add_r. apply Nat.mul_le_mono_l.
        replace 8 with (2 ^ 3) by reflexivity. apply Nat.pow_le_mono_r; lia. }
      simpl in E5. lia. }
    subst cz.
    assert (Hib : ib = 1 \/ ib = 2 \/ ib = 3) by lia.
    destruct Hib as [->|[->| ->]]; simpl in E4.
    + left. apply Nat.div_le_lower_bound; lia.
    + right. apply Nat.div_le_lower_bound; lia.
    + right. apply Nat.div_le_lower_bound; lia.
  - right. apply Nat.div_le_lower_bound; [lia|].
    destruct ib as [|[|[|ib]]]; try lia.
    set (t := ib) in *.
    replace (S (S (S t))) with (3 + t) in * by lia.
    replace (3 + t - 1) with (2 + t) in E4 by lia.
    rewrite Nat.pow_add_r in E4. simpl (2 ^ 3) in E4.
    pose proof (K4_high t) as KH.
    pose proof (pow_pos t) as Pp.
    assert (Hcz : cz <= 2 ^ t).
    { assert (H2 : cz * 2 ^ Lb * 8 < 2 ^ Lb * (8 * 2 ^ t)).
      { rewrite E2 in Hk. rewrite Nat.pow_add_r, Nat.pow_add_r in Hk. simpl (2 ^ 3) in Hk.
        pose proof (Nat.mul_le_mono_r _ _ 8 E5). lia. }
      assert (H3 : 2 ^ Lb * (cz * 8) < 2 ^ Lb * (8 * 2 ^ t)).
      { replace (2 ^ Lb * (cz * 8)) with (cz * 2 ^ Lb * 8) by lia. exact H2. }
      apply Nat.mul_lt_mono_pos_l in H3; [lia|pose proof (pow_pos Lb); lia]. }
    set (P := 2 ^ t) in *.
    assert (H4 : P * (4 * (4 * cc)) <= P * (4 * (54 + M - U0)) ).
    { assert (H5 : P * (8 * cc) + U0 <= 108 * P + M) by nia.
      assert (H6 : M - U0 <= P * (M - U0)) by nia.
      nia. }
    apply Nat.mul_le_mono_pos_l in H4; lia.
Qed.

Lemma A_pos : forall m L Y Lout D, Y * 2 ^ L <= m -> 8 <= Y -> Lout + D + 1 <= L ->
  m < (0 + 1 + D) * 2 ^ Lout -> False.
Proof.
  intros m L Y Lout D H1 H2 H3 H4.
  assert (H5 : 2 ^ (Lout + D + 1) <= 2 ^ L) by (apply Nat.pow_le_mono_r; lia).
  rewrite !Nat.pow_add_r in H5. simpl (2 ^ 1) in H5.
  pose proof (pow2_ge D) as H6. pose proof (pow_pos Lout) as H7.
  set (P := 2 ^ Lout) in *. set (Q := 2 ^ D) in *.
  assert (H8 : 8 * (P * (Q * 2)) <= m).
  { assert (H9 : 8 * 2 ^ L <= Y * 2 ^ L) by (apply Nat.mul_le_mono_r; exact H2). lia. }
  assert (H10 : (D + 1) * P <= Q * P) by (apply Nat.mul_le_mono_r; lia).
  lia.
Qed.

(* The numeric clause for what comes out of the top. *)
Lemma dg_cases : forall d : dg, d = U \/ (d = Z \/ d = O) \/ d = H.
Proof. intros []; auto. Qed.

Lemma NCr_dig : forall d m c L r, d = Z \/ d = O ->
  NCr m c L (d :: r) = (clause m c (S L) (ucnt r) /\ NCr m c (S L) r).
Proof. intros d m c L r [-> | ->]; reflexivity. Qed.

Lemma ucnt_dig : forall d r, d = Z \/ d = O -> ucnt (d :: r) = ucnt r.
Proof. intros d r [-> | ->]; reflexivity. Qed.

Lemma dcnt_dig : forall d r, d = Z \/ d = O -> dcnt (d :: r) = S (dcnt r).
Proof. intros d r [-> | ->]; reflexivity. Qed.

Lemma noH_dig : forall d r, d = Z \/ d = O -> noH (d :: r) = noH r.
Proof. intros d r [-> | ->]; reflexivity. Qed.

Lemma ucnt_app : forall a b, ucnt (a ++ b) = ucnt a + ucnt b.
Proof.
  induction a as [|d a IH]; intros b; [reflexivity|].
  destruct d; cbn [app ucnt]; rewrite IH; lia.
Qed.

Lemma dcnt_ends : forall l, endsd l -> 1 <= dcnt l.
Proof.
  induction l as [|d l IH]; intros H; [contradiction|].
  destruct d; destruct l as [|d' l']; cbn [endsd dcnt] in *; try contradiction; try lia.
  all: specialize (IH H); lia.
Qed.

Lemma endsd_cons : forall d l, endsd l -> endsd (d :: l).
Proof.
  intros d l H. destruct l as [|d' l']; [contradiction|].
  destruct d; exact H.
Qed.

Lemma endsd_tail : forall d l, l <> [] -> endsd (d :: l) -> endsd l.
Proof.
  intros d [|d' l'] Hn H; [contradiction|]. destruct d; exact H.
Qed.

Lemma NCr_high : forall s m' c' L0 Y, m' / 2 ^ L0 <= Y + 1 -> Y <= 15 -> NCr m' c' L0 s.
Proof.
  induction s as [|d s IH]; intros m' c' L0 Y H1 H2; [exact I|].
  destruct (dg_cases d) as [->|[Hd| ->]].
  - cbn [NCr]. apply (IH _ _ _ Y); assumption.
  - rewrite NCr_dig by exact Hd. pose proof (x_double m' L0). split.
    + unfold clause. intros H16. lia.
    + apply (IH _ _ _ 15); lia.
  - exact I.
Qed.

Lemma NCr_top : forall oL Lo L Y m' c' w',
  dcnt oL + Lo = L -> endsd oL -> noH oL ->
  8 <= Y -> Y <= 15 -> Y <= m' / 2 ^ L -> m' / 2 ^ L <= Y + 1 -> c' <= 2 ->
  ucnt oL + ucnt w' <= M1 Y -> (Y = 15 -> ucnt w' <= 31) ->
  NCr m' c' Lo (oL ++ w').
Proof.
  induction oL as [|d oL IH]; intros Lo L Y m' c' w' Hd He Hh H8 H15 H1 H2 Hc Hu H31; [contradiction|].
  destruct (dg_cases d) as [->|[Hdd| ->]].
  - cbn [app NCr dcnt ucnt noH] in *.
    destruct oL as [|d' oL']; [contradiction|].
    apply (IH _ L Y); try lia; try assumption.
  - rewrite <- app_comm_cons, NCr_dig by exact Hdd.
    rewrite dcnt_dig in Hd by exact Hdd. rewrite ucnt_dig in Hu by exact Hdd.
    rewrite noH_dig in Hh by exact Hdd.
    destruct oL as [|d' oL'].
    + cbn [app dcnt ucnt] in *. split.
      * unfold clause. intros H16.
        replace (S Lo) with L by lia.
        replace (S Lo) with L in H16 by lia.
        assert (HY : Y = 15) by lia. subst Y.
        assert (Hx : m' / 2 ^ L = 16) by lia. rewrite Hx.
        specialize (H31 eq_refl).
        assert (E1 : GG 16 = 55) by (vm_compute; reflexivity).
        assert (E2 : Nat.log2 16 = 4) by reflexivity.
        rewrite E1, E2. unfold a_. destruct c' as [|[|[|c']]]; lia.
      * replace (S Lo) with L by lia. apply (NCr_high _ _ _ _ Y); assumption.
    + assert (He' : endsd (d' :: oL')) by (apply (endsd_tail d); [discriminate|exact He]).
      pose proof (dcnt_ends _ He') as Hd1. split.
      * unfold clause. intros H16.
        rewrite ucnt_app.
        apply (Bstep Y); try assumption.
        assert (HLo : S Lo + 1 <= L) by lia.
        pose proof (x_step m' m' L (S Lo) (le_n m') HLo). lia.
      * apply (IH _ L Y); try lia; try assumption.
  - cbn [noH] in Hh. contradiction.
Qed.

Definition HDm (mode : md) (low F : list dg) : Prop :=
  match mode with
  | S_0 => 1 <= dcnt low -> exists d F', F = d :: F' /\ (d = Z \/ d = O)
  | S_1 => 2 <= dcnt low -> exists F', F = U :: F'
  | T_ => 1 <= dcnt low -> exists F', F = U :: F'
  end.

Definition tbq0 (k L M cc u Lin : nat) : Prop :=
  exists ib cz, L = Lin + ib /\ 1 <= ib /\ cc + u + ib + 11 <= 1 + cz + K4 (ib - 1) + M /\ cz * 2 ^ Lin <= k.

Lemma tbq0_tbq : forall k L M cc u Lin, tbq0 k L M cc u Lin -> tbq k L M cc u Lin.
Proof.
  intros k L M cc u Lin [ib [cz [E1 [E2 [E3 E4]]]]].
  exists 0, Lin, ib, cz. split; [lia|]. split; [exact E1|]. split; [exact E2|]. split; [simpl; lia|exact E4].
Qed.

Section Loop.
Variables (m L Y M U0 k c cS : nat) (w1 : list dg) (pf : bool) (Good : list dg -> nat -> Prop).
Hypotheses (HY : m / 2 ^ L = Y) (HY8 : 8 <= Y) (HY15 : Y <= 15) (HM : M = M1 Y) (HU : U0 = ucnt w1) (HU0 : U0 <= M)
  (HL : 3 <= L) (Hk : k * 8 < 2 ^ L) (Hc2 : c <= cS) (HcS : cS <= 2) (Hpf : pf = true -> 1 <= c)
  (Hck : k = 0 \/ cS = 2).
Hypothesis Htop : forall mode cc A d nc, 1 <= d ->
  In nc (allowed d cS cc (ckf cS) (ctf M U0)) -> cc <= cgf M U0 ->
  2 ^ d * Y <= A + d -> A + 1 <= 2 ^ d * (Y + 1) ->
  exists o oL w', it (path mode w1 cc) A = Some o /\ tape o = tape (oL ++ w') /\ dcnt oL = d /\
    noH oL /\ endsd oL /\ trimz w' = w' /\ ucnt oL + ucnt w' <= capf M U0 /\ Good w' nc /\ (Y = 15 -> ucnt w' <= 31).

Definition LR (mode : md) (low : list dg) (cc A Lout : nat) : Prop :=
  exists o F oL w' nc, it (path mode (low ++ w1) cc) A = Some o /\ tape o = tape F /\ F = oL ++ w' /\
    dcnt oL + Lout = L /\ noH oL /\ endsd oL /\ trimz w' = w' /\ Good w' nc /\ (Y = 15 -> ucnt w' <= 31) /\
    (nc = 2 \/ (pf = true /\ nc + 1 = cS)) /\
    ucnt F <= ucnt (low ++ w1) + dcnt low + 12 + (match mode with T_ => 1 | _ => 0 end) /\
    (low = [] -> ucnt F <= M) /\
    (forall m' c', m <= m' -> m' / 2 ^ L <= Y + 1 -> c' <= 2 -> (pf = true -> c' + 1 <= c) -> NCr m' c' Lout F) /\
    HDm mode low F.

Definition pe : nat := if pf then 0 else 1.

Lemma m_bounds : Y * 2 ^ L <= m /\ m < (Y + 1) * 2 ^ L.
Proof.
  pose proof (pow_pos L) as P. split.
  - rewrite <- HY. pose proof (Nat.div_mod_eq m (2 ^ L)).
    rewrite (Nat.mul_comm (m / 2 ^ L)). lia.
  - rewrite <- HY. pose proof (Nat.div_mod_eq m (2 ^ L)).
    pose proof (Nat.mod_upper_bound m (2 ^ L) ltac:(lia)).
    rewrite Nat.mul_add_distr_r, (Nat.mul_comm (m / 2 ^ L)). lia.
Qed.

(* At a level of the low part: size of x, its G. *)
Lemma low_fact : forall Lin i, Lin + i = L -> 1 <= i ->
  16 <= m / 2 ^ Lin /\ Nat.log2 (m / 2 ^ Lin) = 3 + i /\ GG (m / 2 ^ Lin) = K4 (i - 1) + M.
Proof.
  intros Lin i E Hi. subst L.
  destruct (low_log m Lin i ltac:(lia) ltac:(lia)) as [H1 H2].
  pose proof (GG_low m Lin i Hi ltac:(lia) ltac:(lia)) as H3.
  rewrite HY in H3. rewrite <- HM in H3.
  split; [|split; assumption].
  assert (H4 : 2 ^ (3 + i) <= m / 2 ^ Lin).
  { rewrite <- H1. apply Nat.log2_spec.
    destruct (m / 2 ^ Lin) eqn:E0; [|lia]. rewrite Nat.log2_nonpos in H1 by lia. lia. }
  rewrite Nat.pow_add_r in H4. pose proof (pow2_ge i). simpl (2 ^ 3) in H4. lia.
Qed.

(* Emission clauses. *)
Lemma emit_N : forall Lin Lo i uin u' m' c', Lin + i = L -> 1 <= i -> Lo + 1 <= Lin ->
  m <= m' -> c' <= 2 ->
  uin + c * a_ (3 + i) <= K4 (i - 1) + M -> u' <= uin + i + 12 ->
  clause m' c' Lo u'.
Proof.
  intros Lin Lo i uin u' m' c' E Hi HLo Hm Hc H1 H2.
  destruct (low_fact Lin i E Hi) as [F1 [F2 F3]].
  unfold clause. intros _.
  pose proof (x_step m m' Lin Lo Hm HLo) as H3.
  apply (Nstep (m / 2 ^ Lin)); try assumption.
  rewrite F3, F2. lia.
Qed.

Lemma emit_T : forall Lin i uin u' m' c', Lin + i = L -> 1 <= i ->
  m <= m' -> c' + 1 <= c -> c <= 2 ->
  uin + c * a_ (3 + i) <= K4 (i - 1) + M -> u' <= uin + a_ (3 + i) ->
  clause m' c' Lin u'.
Proof.
  intros Lin i uin u' m' c' E Hi Hm Hc Hc3 H1 H2.
  destruct (low_fact Lin i E Hi) as [F1 [F2 F3]].
  unfold clause. intros _.
  pose proof (x_mono m m' Lin Hm) as H3.
  apply (Tstep (m / 2 ^ Lin) _ uin u' c c'); try assumption.
  - rewrite F2, F3. exact H1.
  - rewrite F2. exact H2.
Qed.

Lemma emit_B : forall Lo u' m' c', Lo + 1 <= L -> m <= m' -> c' <= 2 -> u' <= M ->
  clause m' c' Lo u'.
Proof.
  intros Lo u' m' c' HLo Hm Hc Hu.
  unfold clause. intros _.
  pose proof (x_step m m' L Lo Hm HLo) as H3.
  rewrite HY in H3. subst M.
  apply (Bstep Y); assumption.
Qed.

(* Reading a clause at a level, to bound the next U count. *)
Lemma clause_u : forall Lin i u, Lin + i = L -> 1 <= i -> clause m c Lin u -> u + c * a_ (3 + i) <= K4 (i - 1) + M.
Proof.
  intros Lin i u E Hi H.
  destruct (low_fact Lin i E Hi) as [F1 [F2 F3]].
  specialize (H F1). rewrite F2, F3 in H. exact H.
Qed.

(* Carry bound of all tunnels. *)
Lemma gamma_step : forall cc u i v, 1 <= i -> v <= cc + 1 ->
  cc + u <= K4 i + 3 * (i + 1) + 40 + M -> u <= K4 (i - 1) + M ->
  v / 2 + u <= K4 (i - 1) + 3 * i + 40 + M.
Proof.
  intros cc u i v Hi Hv H1 H2.
  destruct i as [|i]; [lia|]. replace (S i - 1) with i in * by lia.
  rewrite K4_step in H1.
  pose proof (d2b v). lia.
Qed.

Lemma gamma_end : forall cc v, v <= cc + 1 ->
  cc + U0 <= K4 0 + 3 * (0 + 1) + 40 + M -> v / 2 <= cgf M U0.
Proof.
  intros cc v Hv H. unfold cgf. simpl K4 in H.
  apply Nat.Div0.div_le_mono. lia.
Qed.

Definition Bcls (mode : md) (lc : nat) (low : list dg) (cc Lin D : nat) : Prop :=
  match mode with
  | S_0 => (D <= 1 -> nt k cc Lin) /\ (D = 2 -> nt k cc Lin \/ (pf = true /\ tbq k L M cc (ucnt (low ++ w1)) Lin))
  | S_1 =>
    if Nat.eqb lc 0 then
      (D <= 1 -> nt k cc Lin) /\ (D = 2 -> nt k cc Lin \/ (pf = true /\ tbq k L M cc (ucnt (low ++ w1)) Lin))
    else
      (D = 0 -> nt k cc Lin) /\ (D = 1 -> nt k cc Lin \/ (pf = true /\ tbq k L M cc (ucnt (low ++ w1)) Lin))
  | T_ =>
    (D <= 1 -> (nt k cc Lin /\ clause m c Lin (ucnt (low ++ w1))) \/ (low <> [] /\ tbq0 k L M cc (ucnt (low ++ w1)) Lin)) /\
    (D = 2 -> low = [] -> nt k cc Lin \/ (pf = true /\ tbq k L M cc (ucnt (low ++ w1)) Lin))
  end.

Definition Dcns (mode : md) (lc : nat) (Lin D : nat) : Prop :=
  match mode with
  | S_0 => 1 + pe <= D
  | S_1 => if Nat.eqb lc 0 then 1 <= D /\ (1 + pe <= D \/ Lin <= 2) else pe <= D
  | T_ => 1 + pe <= D
  end.

Definition Ggm (low : list dg) (cc : nat) : Prop :=
  match low with
  | [] => cc <= cgf M U0
  | _ => cc + ucnt (low ++ w1) <= K4 (dcnt low - 1) + 3 * dcnt low + 40 + M
  end.

Lemma low_base : forall mode cc A Lin Lout D,
  Lin = Lout + D -> Lin = L -> Dcns mode 0 Lin D ->
  m < (A + 1 + D) * 2 ^ Lout -> A * 2 ^ Lout <= m ->
  cc <= cgf M U0 -> Bcls mode 0 [] cc Lin D ->
  LR mode [] cc A Lout.
Proof.
  intros mode cc A Lin Lout D E1 E2 HD HLB HUB Hg Hb.
  assert (E3 : L = Lout + D) by lia.
  rewrite E2 in HD, Hb.
  destruct m_bounds as [Mb1 Mb2].
  assert (Hpw : 2 ^ L = 2 ^ D * 2 ^ Lout) by (rewrite E3, Nat.pow_add_r; lia).
  pose proof (pow_pos Lout) as HP.
  assert (HD1 : 1 <= D).
  { destruct mode; cbn [Dcns] in HD; unfold pe in HD; simpl in HD; lia. }
  assert (Hpf1 : D = 1 -> pf = true).
  { intros ->. destruct pf eqn:Ep; [reflexivity|]. exfalso.
    destruct mode; cbn [Dcns] in HD; unfold pe in HD; rewrite Ep in HD; simpl in HD; lia. }
  assert (HA1 : 2 ^ D * Y <= A + D).
  { assert (Hq : (2 ^ D * Y) * 2 ^ Lout < (A + 1 + D) * 2 ^ Lout).
    { replace (2 ^ D * Y * 2 ^ Lout) with (Y * (2 ^ D * 2 ^ Lout)) by lia. rewrite <- Hpw. lia. }
    apply Nat.mul_lt_mono_pos_r in Hq; lia. }
  assert (HA2 : A + 1 <= 2 ^ D * (Y + 1)).
  { assert (Hq : A * 2 ^ Lout < (2 ^ D * (Y + 1)) * 2 ^ Lout).
    { replace (2 ^ D * (Y + 1) * 2 ^ Lout) with ((Y + 1) * (2 ^ D * 2 ^ Lout)) by lia. rewrite <- Hpw. lia. }
    apply Nat.mul_lt_mono_pos_r in Hq; lia. }
  assert (Hntck : nt k cc L -> cc <= ckf cS).
  { unfold nt. intros Hn. unfold ckf.
    destruct Hck as [-> | ->].
    - destruct cc as [|cc]; [lia|]. exfalso. pose proof (pow_pos L). simpl in Hn. nia.
    - simpl. destruct cc as [|[|cc]]; try lia. }
  assert (Hbc : (D <= 1 -> nt k cc L) /\ (D = 2 -> nt k cc L \/ (pf = true /\ tbq k L M cc U0 L))).
  { rewrite HU. destruct mode; cbn [Bcls] in Hb; simpl (Nat.eqb 0 0) in Hb; simpl app in Hb.
    - exact Hb.
    - exact Hb.
    - destruct Hb as [B1 B2]. split.
      + intros Hd. destruct (B1 Hd) as [[B3 _]|[B3 _]]; [exact B3|contradiction].
      + intros Hd. apply B2; [exact Hd|reflexivity]. }
  destruct Hbc as [Hb1 Hb2].
  assert (Hin : exists nc, In nc (allowed D cS cc (ckf cS) (ctf M U0)) /\ (nc = 2 \/ (pf = true /\ nc + 1 = cS))).
  { destruct D as [|[|[|D]]]; [lia| | |].
    - exists (cS - 1). specialize (Hb1 ltac:(lia)). specialize (Hpf1 eq_refl).
      pose proof (Hpf Hpf1) as Hp.
      split; [|right; split; [exact Hpf1|lia]].
      cbn [allowed]. assert (Hl1 : (0 <? cS) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hl1. simpl. rewrite (proj2 (Nat.leb_le _ _) (Hntck Hb1)). simpl. left. reflexivity.
    - destruct (Hb2 eq_refl) as [Hn|[Hp1 Hq]].
      + exists 2. split; [|left; reflexivity].
        cbn [allowed]. rewrite (proj2 (Nat.leb_le _ _) (Hntck Hn)). simpl. left. reflexivity.
      + exists (cS - 1). pose proof (Hpf Hp1) as Hp.
        split; [|right; split; [exact Hp1|lia]].
        cbn [allowed]. assert (Hl1 : (0 <? cS) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hl1. pose proof (T_final k L M cc U0 Hq Hk HU0) as Hct.
        rewrite (proj2 (Nat.leb_le _ _) Hct). simpl. apply in_or_app. right. simpl. left. reflexivity.
    - exists 2. split; [|left; reflexivity]. simpl. left. reflexivity. }
  destruct Hin as [nc [Hn Hnc]].
  destruct (Htop mode cc A D nc HD1 Hn Hg HA1 HA2) as [o [oL [w' [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]]]].
  unfold capf in H7.
  exists o, (oL ++ w'), oL, w', nc. simpl (nil ++ w1).
  split; [exact H1|]. split; [exact H2|]. split; [reflexivity|]. split; [lia|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H8|]. split; [exact H9|]. split; [exact Hnc|].
  rewrite ucnt_app. split.
  { rewrite <- HU. destruct mode; simpl; lia. }
  split; [intros _; lia|].
  split.
  - intros m' c' Hm' Hx' Hc' _.
    assert (Hy1 : Y <= m' / 2 ^ L) by (rewrite <- HY; apply x_mono; exact Hm').
    assert (Hu1 : ucnt oL + ucnt w' <= M1 Y) by (rewrite <- HM; lia).
    apply (NCr_top oL Lout L Y); try assumption. lia.
  - destruct mode; cbn [HDm dcnt]; lia.
Qed.


Lemma lb_dg : forall A q D P m0, A <= 2 * q + 1 -> m0 < (A + 1 + D) * P -> m0 < (q + 1 + D) * (2 * P).
Proof.
  intros A q D P m0 H1 H2.
  assert (H3 : (A + 1 + D) * P <= (2 * (q + 1 + D)) * P) by (apply Nat.mul_le_mono_r; lia).
  replace ((q + 1 + D) * (2 * P)) with (2 * (q + 1 + D) * P) by lia. lia.
Qed.

Lemma lb_cv : forall A q D P m0, A <= 2 * q -> 1 <= D -> m0 < (A + 1 + D) * P -> m0 < (q + 1 + (D - 1)) * (2 * P).
Proof.
  intros A q D P m0 H1 HD H2.
  assert (H3 : (A + 1 + D) * P <= (2 * (q + 1 + (D - 1))) * P) by (apply Nat.mul_le_mono_r; lia).
  replace ((q + 1 + (D - 1)) * (2 * P)) with (2 * (q + 1 + (D - 1)) * P) by lia. lia.
Qed.

Lemma ub_dg : forall A q P m0, 2 * q <= A -> 2 * (A * P) <= 2 * m0 -> 2 * (q * (2 * P)) <= 2 * m0.
Proof.
  intros A q P m0 H1 H2.
  assert (H3 : (2 * q) * P <= A * P) by (apply Nat.mul_le_mono_r; lia).
  replace (q * (2 * P)) with (2 * q * P) by lia. lia.
Qed.

Lemma ub_cv : forall A q P m0, 2 * q <= A + 1 -> 2 * (A * P) <= 2 * m0 -> 2 * (q * (2 * P)) <= 2 * m0 + 1 * (2 * P).
Proof.
  intros A q P m0 H1 H2.
  assert (H3 : (2 * q) * P <= (A + 1) * P) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_add_distr_r in H3.
  replace (q * (2 * P)) with (2 * q * P) by lia. lia.
Qed.

Lemma ub_rp : forall A' P m0 lc, lc <= 1 -> 2 * (S A' * P) <= 2 * m0 + lc * P -> 2 * (A' * P) <= 2 * m0 + 0 * P.
Proof.
  intros A' P m0 lc H1 H2.
  destruct lc as [|[|lc]]; try lia; cbn [Nat.mul] in *; lia.
Qed.

Lemma mbit_cases : forall v, mbit v = S_0 \/ mbit v = S_1.
Proof. intros v. unfold mbit. destruct (Nat.even v); auto. Qed.

Lemma ne_ends_dcnt : forall l, l <> [] -> (l = [] \/ endsd l) -> 1 <= dcnt l.
Proof. intros l H1 [H2|H2]; [contradiction|apply dcnt_ends; exact H2]. Qed.

Lemma Ggm_ne : forall l cc, l <> [] -> Ggm l cc -> cc + ucnt (l ++ w1) <= K4 (dcnt l - 1) + 3 * dcnt l + 40 + M.
Proof. intros [|d l] cc H1 H2; [contradiction|exact H2]. Qed.

Lemma Ggm_ne' : forall l cc, l <> [] -> cc + ucnt (l ++ w1) <= K4 (dcnt l - 1) + 3 * dcnt l + 40 + M -> Ggm l cc.
Proof. intros [|d l] cc H1 H2; [contradiction|exact H2]. Qed.

Lemma bcls_S : forall mode low cc Lin D, mode = S_0 \/ mode = S_1 ->
  (D <= 1 -> nt k cc Lin) -> (D = 2 -> nt k cc Lin \/ (pf = true /\ tbq k L M cc (ucnt (low ++ w1)) Lin)) ->
  Bcls mode 0 low cc Lin D.
Proof.
  intros mode low cc Lin D [-> | ->] H1 H2; split; assumption.
Qed.

Lemma low_loop : forall low mode cc A Lin Lout D lc,
  Lin = Lout + D -> Lin + dcnt low = L -> noH low -> (low = [] \/ endsd low) ->
  lc <= 1 -> (lc = 1 -> mode = S_1 /\ low <> []) -> (lc = 0 \/ mode = S_1) ->
  NCr m c Lin (low ++ w1) ->
  (mode = S_0 -> clause m c Lin (ucnt (low ++ w1))) ->
  m < (A + 1 + D) * 2 ^ Lout ->
  2 * (A * 2 ^ Lout) <= 2 * m + lc * 2 ^ Lout ->
  Dcns mode lc Lin D -> Ggm low cc -> Bcls mode lc low cc Lin D ->
  LR mode low cc A Lout.
Proof.
  induction low as [|e lr IH]; intros mode cc A Lin Lout D lc E1 E2 Hh Hend Hlc Hlc1 Hlc0 Hnum Hcl HLB HUB HD Hg Hb.
  - (* at the cut *)
    assert (Hl0 : lc = 0).
    { destruct lc as [|[|lc]]; [reflexivity| |lia]. destruct (Hlc1 eq_refl) as [_ Hx]. contradiction. }
    subst lc.
    apply low_base with (Lin := Lin) (D := D); try assumption.
    + cbn [dcnt] in E2. lia.
    + rewrite Nat.mul_0_l, Nat.add_0_r in HUB. lia.
  - destruct m_bounds as [Mb1 Mb2].
    assert (HP : 1 <= 2 ^ Lout) by apply pow_pos.
    destruct (dg_cases e) as [->|[He| ->]]; [| |cbn [noH] in Hh; contradiction].
    + (* a U *)
      cbn [noH dcnt app ucnt NCr] in *.
      assert (Hne : lr <> []).
      { intros ->. destruct Hend as [Hx|Hx]; [discriminate|contradiction]. }
      assert (Hend' : lr = [] \/ endsd lr).
      { right. destruct Hend as [Hx|Hx]; [discriminate|]. apply (endsd_tail U); assumption. }
      pose proof (ne_ends_dcnt lr Hne Hend') as Hi.
      assert (Hg' : cc + S (ucnt (lr ++ w1)) <= K4 (dcnt lr - 1) + 3 * dcnt lr + 40 + M).
      { exact Hg. }
      destruct mode.
      * (* conv *)
        assert (Hlc00 : lc = 0).
        { destruct Hlc0 as [Hx|Hx]; [exact Hx|discriminate]. }
        subst lc. cbn [Dcns Bcls] in HD, Hb. destruct Hb as [Hb1 Hb2].
        assert (HD1 : 1 <= D) by lia.
        specialize (Hcl eq_refl).
        assert (HIH : LR S_1 lr cc ((A + 1) / 2) (S Lout)).
        { apply (IH S_1 cc _ Lin (S Lout) (D - 1) 1); try assumption.
          - lia.
          - lia.
          - intros _. split; [reflexivity|exact Hne].
          - right. reflexivity.
          - intros Hx. discriminate.
          - rewrite pow_S. apply lb_cv with (A := A); try assumption. apply d2c.
          - rewrite pow_S. apply ub_cv with (A := A).
            + apply d2d.
            + rewrite Nat.mul_0_l, Nat.add_0_r in HUB. exact HUB.
          - cbn [Dcns]. simpl (Nat.eqb 1 0). lia.
          - apply Ggm_ne'; [exact Hne|lia].
          - cbn [Bcls]. simpl (Nat.eqb 1 0). split.
            + intros Hx. apply Hb1. lia.
            + intros Hx. destruct (Hb2 ltac:(lia)) as [Hy|[Hy1 Hy2]]; [left; exact Hy|right].
              split; [exact Hy1|]. apply (tbq_u _ _ _ _ _ _ _ Hy2). cbn [app ucnt]. lia. }
        destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
        exists (bitd (A + 1) :: o), (bitd (A + 1) :: F), (bitd (A + 1) :: oL), w', nc.
        cbn [app path it]. rewrite H1. simpl option_map.
        assert (Hbd : bitd (A + 1) = Z \/ bitd (A + 1) = O) by apply bitd_cases.
        split; [reflexivity|]. split; [rewrite !cw_bit_tape, H2; reflexivity|].
        split; [subst F; reflexivity|]. split; [rewrite dcnt_dig by exact Hbd; lia|].
        split; [rewrite noH_dig by exact Hbd; exact H5|]. split; [apply endsd_cons; exact H6|].
        split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
        rewrite ucnt_dig by exact Hbd. split; [cbn [dcnt ucnt] in *; lia|].
        split; [intros Hx0; discriminate Hx0|]. split.
        -- intros m' c' Hm' Hx Hc' Hpf'. rewrite NCr_dig by exact Hbd. split.
           ++ pose proof (clause_u Lin (dcnt lr) (S (ucnt (lr ++ w1))) ltac:(lia) Hi Hcl) as Hin.
              destruct (Nat.eq_dec D 1) as [Hd1|Hd1].
              ** assert (Hpt : pf = true).
                 { unfold pe in HD. destruct pf; [reflexivity|]. lia. }
                 replace (S Lout) with Lin by lia.
                 assert (Hcc : c' + 1 <= c) by (apply Hpf'; exact Hpt).
                 assert (Hau : ucnt F <= S (ucnt (lr ++ w1)) + a_ (3 + dcnt lr)) by (unfold a_; lia).
                 apply (emit_T Lin (dcnt lr) (S (ucnt (lr ++ w1)))); try assumption; lia.
              ** apply (emit_N Lin (S Lout) (dcnt lr) (S (ucnt (lr ++ w1)))); try lia; try assumption.
           ++ apply H13; assumption.
        -- intros _. exists (bitd (A + 1)), F. split; [reflexivity|exact Hbd].
      * (* U in S1 *)
        assert (HIH : LR S_1 lr cc A Lout).
        { apply (IH S_1 cc A Lin Lout D lc); try assumption.
          - intros Hx. split; [reflexivity|exact Hne].
          - intros Hx. discriminate.
          - apply Ggm_ne'; [exact Hne|lia].
          - cbn [Bcls] in Hb |- *. destruct (Nat.eqb lc 0).
            + destruct Hb as [Hb1 Hb2]. split; [exact Hb1|].
              intros Hx. destruct (Hb2 Hx) as [Hy|[Hy1 Hy2]]; [left; exact Hy|right].
              split; [exact Hy1|]. apply (tbq_u _ _ _ _ _ _ _ Hy2). cbn [app ucnt]. lia.
            + destruct Hb as [Hb1 Hb2]. split; [exact Hb1|].
              intros Hx. destruct (Hb2 Hx) as [Hy|[Hy1 Hy2]]; [left; exact Hy|right].
              split; [exact Hy1|]. apply (tbq_u _ _ _ _ _ _ _ Hy2). cbn [app ucnt]. lia. }
        destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
        exists (U :: o), (U :: F), (U :: oL), w', nc.
        cbn [app path it]. rewrite H1. simpl option_map.
        split; [reflexivity|]. split; [cbn [tape]; rewrite H2; reflexivity|].
        split; [subst F; reflexivity|]. split; [cbn [dcnt]; lia|]. split; [exact H5|]. split; [apply endsd_cons; exact H6|].
        split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
        split; [cbn [ucnt dcnt] in *; lia|]. split; [intros Hx0; discriminate Hx0|]. split.
        -- intros m' c' Hm' Hx Hc' Hpf'. cbn [NCr]. apply H13; assumption.
        -- intros _. exists F. reflexivity.
      * (* U in T *)
        assert (Hlc00 : lc = 0).
        { destruct Hlc0 as [Hx|Hx]; [exact Hx|discriminate]. }
        subst lc. cbn [Dcns Bcls] in HD, Hb. destruct Hb as [Hb1 Hb2].
        assert (HIH : LR T_ lr (S cc) A Lout).
        { apply (IH T_ (S cc) A Lin Lout D 0); try assumption.
          - intros Hx. discriminate.
          - intros Hx. discriminate.
          - apply Ggm_ne'; [exact Hne|lia].
          - cbn [Bcls]. split.
            + intros Hx. right. split; [exact Hne|].
              destruct (Hb1 Hx) as [[Hn Hc0]|[_ Hq]].
              * assert (Hpt : pf = true).
                { unfold pe in HD. destruct pf; [reflexivity|]. lia. }
                pose proof (Hpf Hpt) as Hc1.
                pose proof (clause_u Lin (dcnt lr) (S (ucnt (lr ++ w1))) ltac:(lia) Hi Hc0) as Hin.
                exists (dcnt lr), (cc - 1).
                split; [lia|]. split; [exact Hi|]. unfold a_ in Hin.
                assert (Hmul : 3 + dcnt lr + 8 <= c * (3 + dcnt lr + 8)) by nia.
                split; [lia|].
                unfold nt in Hn. destruct cc as [|cc0]; [simpl; lia|].
                replace (S cc0 - 1) with cc0 by lia. simpl in Hn. lia.
              * destruct Hq as [ib [cz [Q1 [Q2 [Q3 Q4]]]]].
                cbn [app ucnt] in Q3.
                exists ib, cz. repeat split; try assumption. lia.
            + intros _ Hx. contradiction. }
        destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
        exists (U :: o), (U :: F), (U :: oL), w', nc.
        cbn [app path it]. rewrite H1. simpl option_map.
        split; [reflexivity|]. split; [cbn [tape]; rewrite H2; reflexivity|].
        split; [subst F; reflexivity|]. split; [cbn [dcnt]; lia|]. split; [exact H5|]. split; [apply endsd_cons; exact H6|].
        split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
        split; [cbn [ucnt dcnt] in *; lia|]. split; [intros Hx0; discriminate Hx0|]. split.
        -- intros m' c' Hm' Hx Hc' Hpf'. cbn [NCr]. apply H13; assumption.
        -- intros _. exists F. reflexivity.
    + (* a digit *)
      rewrite noH_dig in Hh by exact He.
      rewrite dcnt_dig in E2 by exact He.
      cbn [app] in Hnum |- *. rewrite NCr_dig in Hnum by exact He. destruct Hnum as [Hcln Hnum].
      assert (Hend' : lr = [] \/ endsd lr).
      { destruct lr as [|d' l']; [left; reflexivity|right].
        destruct Hend as [Hx|Hx]; [discriminate|]. apply (endsd_tail e); [discriminate|exact Hx]. }
      set (v := cc + bv e) in *.
      assert (Hv : v <= cc + 1) by (subst v; destruct He as [-> | ->]; simpl; lia).
      assert (Hpd : forall mm, path mm ((e :: lr) ++ w1) cc = pdig mm v (fun m' => path m' (lr ++ w1) (v / 2))).
      { intros mm. apply path_dig. exact He. }
      assert (Hucnt : ucnt ((e :: lr) ++ w1) = ucnt (lr ++ w1)) by (apply ucnt_dig; exact He).
      assert (Hg2 : Ggm lr (v / 2)).
      { destruct lr as [|d' l'] eqn:Elr.
        - cbn [Ggm]. apply (gamma_end cc v Hv).
          assert (Hg3 : Ggm (e :: []) cc) by exact Hg.
          pose proof (Ggm_ne (e :: []) cc ltac:(discriminate) Hg3) as Hg4.
          rewrite dcnt_dig in Hg4 by exact He. cbn [app] in Hg4. rewrite ucnt_dig in Hg4 by exact He.
          rewrite <- HU in Hg4. simpl in Hg4. simpl. lia.
        - apply Ggm_ne'; [discriminate|].
          rewrite <- Elr in *.
          assert (Hne : lr <> []) by (rewrite Elr; discriminate).
          pose proof (ne_ends_dcnt lr Hne Hend') as Hi.
          pose proof (Ggm_ne (e :: lr) cc ltac:(discriminate) Hg) as Hg4.
          rewrite dcnt_dig in Hg4 by exact He. rewrite Hucnt in Hg4.
          pose proof (clause_u (S Lin) (dcnt lr) (ucnt (lr ++ w1)) ltac:(lia) Hi Hcln) as Hin.
          apply (gamma_step cc); try lia.
          + replace (S (dcnt lr) - 1) with (dcnt lr) in Hg4 by lia. lia.
      }
      destruct mode.
      * (* digit read by S0 *)
        assert (Hlc00 : lc = 0).
        { destruct Hlc0 as [Hx|Hx]; [exact Hx|discriminate]. }
        subst lc. cbn [Dcns Bcls] in HD, Hb. destruct Hb as [Hb1 Hb2].
        assert (HIH : LR (mbit v) lr (v / 2) (A / 2) (S Lout)).
        { apply (IH (mbit v) (v / 2) (A / 2) (S Lin) (S Lout) D 0); try assumption.
          - lia.
          - lia.
          - intros Hx. discriminate.
          - left. reflexivity.
          - intros _. exact Hcln.
          - rewrite pow_S. apply lb_dg with (A := A); [apply d2a|exact HLB].
          - rewrite pow_S. rewrite Nat.mul_0_l, Nat.add_0_r.
            apply ub_dg with (A := A); [apply d2b|]. rewrite Nat.mul_0_l, Nat.add_0_r in HUB. exact HUB.
          - destruct (mbit_cases v) as [-> | ->]; cbn [Dcns]; [lia|].
            simpl (Nat.eqb 0 0). split; [lia|left; lia].
          - apply bcls_S; [apply mbit_cases| |].
            + intros Hx. apply (nt_step k cc Lin v); [apply Hb1; exact Hx|exact Hv].
            + intros Hx. destruct (Hb2 Hx) as [Hy|[Hy1 Hy2]].
              * left. apply (nt_step k cc Lin v); [exact Hy|exact Hv].
              * right. split; [exact Hy1|]. rewrite Hucnt in Hy2. apply (tbq_step _ _ _ cc); assumption. }
        destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
        exists (bitd A :: o), (bitd A :: F), (bitd A :: oL), w', nc.
        rewrite Hpd, it_S0_dig. rewrite H1. simpl option_map.
        assert (Hbd : bitd A = Z \/ bitd A = O) by apply bitd_cases.
        split; [reflexivity|]. split; [rewrite !cw_bit_tape, H2; reflexivity|].
        split; [subst F; reflexivity|]. split; [rewrite dcnt_dig by exact Hbd; lia|].
        split; [rewrite noH_dig by exact Hbd; exact H5|]. split; [apply endsd_cons; exact H6|].
        split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
        assert (Hmb : match mbit v with T_ => 1 | _ => 0 end = 0) by (destruct (mbit_cases v) as [-> | ->]; reflexivity).
        rewrite Hmb in H11.
        rewrite ucnt_dig by exact Hbd. split.
        { rewrite Hucnt, dcnt_dig by exact He. cbn. lia. }
        split; [intros Hx0; discriminate Hx0|]. split.
        -- intros m' c' Hm' Hx Hc' Hpf'. rewrite NCr_dig by exact Hbd. split.
           ++ destruct lr as [|d' l'] eqn:Elr.
              ** apply (emit_B (S Lout)); try assumption.
                 --- cbn [dcnt] in E2. lia.
                 --- apply H12 . reflexivity.
              ** rewrite <- Elr in *.
                 assert (Hne : lr <> []) by (rewrite Elr; discriminate).
                 pose proof (ne_ends_dcnt lr Hne Hend') as Hi.
                 pose proof (clause_u (S Lin) (dcnt lr) (ucnt (lr ++ w1)) ltac:(lia) Hi Hcln) as Hin.
                 apply (emit_N (S Lin) (S Lout) (dcnt lr) (ucnt (lr ++ w1))); try lia; try assumption.
           ++ apply H13; assumption.
        -- intros _. exists (bitd A), F. split; [reflexivity|exact Hbd].
      * (* digit read by S1: a repair *)
        destruct A as [|A'].
        { exfalso. apply (A_pos m L Y Lout D Mb1 HY8); [lia|exact HLB]. }
        pose proof (ub_rp A' _ _ lc Hlc HUB) as HUB'.
        assert (HD' : pe <= D /\ (D = 0 -> lc = 1)).
        { cbn [Dcns] in HD. destruct lc as [|[|lc]]; simpl (Nat.eqb _ _) in HD; try lia.
          unfold pe in *. destruct pf; lia. }
        destruct HD' as [HD1 HD2].
        assert (Hbn : D = 0 -> nt k cc Lin).
        { intros Hx. pose proof (HD2 Hx) as Hl1. subst lc. cbn [Bcls] in Hb. simpl (Nat.eqb 1 0) in Hb.
          apply Hb. exact Hx. }
        assert (Hbt : D = 1 -> nt k cc Lin \/ (pf = true /\ tbq k L M cc (ucnt (lr ++ w1)) Lin)).
        { intros Hx. cbn [Bcls] in Hb. rewrite <- Hucnt.
          destruct lc as [|[|lc]]; simpl (Nat.eqb _ _) in Hb; try lia.
          - left. apply Hb. lia.
          - apply Hb. exact Hx. }
        destruct (Nat.even v) eqn:Ev.
        -- (* head Z: the tunnel state *)
           assert (HIH : LR T_ lr (v / 2) A' Lout).
           { apply (IH T_ (v / 2) A' (S Lin) Lout (S D) 0); try assumption.
             - lia.
             - lia.
             - lia.
             - intros Hx. discriminate.
             - left. reflexivity.
             - intros Hx. discriminate.
             - replace (A' + 1 + S D) with (S A' + 1 + D) by lia. exact HLB.
             - cbn [Dcns]. lia.
             - cbn [Bcls]. split.
               + intros Hx. left. split; [|exact Hcln].
                 apply (nt_step k cc Lin v); [apply Hbn; lia|exact Hv].
               + intros Hx _. destruct (Hbt ltac:(lia)) as [Hy|[Hy1 Hy2]].
                 * left. apply (nt_step k cc Lin v); [exact Hy|exact Hv].
                 * right. split; [exact Hy1|]. apply (tbq_step _ _ _ cc); assumption. }
           destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
           exists o, F, oL, w', nc.
           rewrite Hpd, it_S1_even by exact Ev.
           split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
           split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
           split.
           { rewrite Hucnt, dcnt_dig by exact He. lia. }
           split; [intros Hx0; discriminate Hx0|]. split; [exact H13|].
           cbn [HDm] in H14 |- *. intros Hx. apply H14. rewrite dcnt_dig in Hx by exact He. lia.
        -- (* head O *)
           assert (HIH : LR S_0 lr (v / 2) A' Lout).
           { apply (IH S_0 (v / 2) A' (S Lin) Lout (S D) 0); try assumption.
             - lia.
             - lia.
             - lia.
             - intros Hx. discriminate.
             - left. reflexivity.
             - intros _. exact Hcln.
             - replace (A' + 1 + S D) with (S A' + 1 + D) by lia. exact HLB.
             - cbn [Dcns]. lia.
             - apply bcls_S; [left; reflexivity| |].
               + intros Hx. apply (nt_step k cc Lin v); [apply Hbn; lia|exact Hv].
               + intros Hx. destruct (Hbt ltac:(lia)) as [Hy|[Hy1 Hy2]].
                 * left. apply (nt_step k cc Lin v); [exact Hy|exact Hv].
                 * right. split; [exact Hy1|]. apply (tbq_step _ _ _ cc); assumption. }
           destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
           exists (U :: o), (U :: F), (U :: oL), w', nc.
           rewrite Hpd, it_S1_odd by exact Ev. rewrite H1. simpl option_map.
           split; [reflexivity|]. split; [cbn [tape]; rewrite H2; reflexivity|].
           split; [subst F; reflexivity|]. split; [cbn [dcnt]; lia|]. split; [exact H5|]. split; [apply endsd_cons; exact H6|].
           split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
           split.
           { cbn [ucnt]. rewrite Hucnt, dcnt_dig by exact He. lia. }
           split; [intros Hx0; discriminate Hx0|]. split.
           ** intros m' c' Hm' Hx Hc' Hpf'. cbn [NCr]. apply H13; assumption.
           ** intros _. exists F. reflexivity.
      * (* digit read in the tunnel state *)
        assert (Hlc00 : lc = 0).
        { destruct Hlc0 as [Hx|Hx]; [exact Hx|discriminate]. }
        subst lc. cbn [Dcns Bcls] in HD, Hb. destruct Hb as [Hb1 Hb2].
        rewrite Hucnt in Hb1.
        assert (HIH : LR (mbit v) lr (v / 2) A Lout).
        { apply (IH (mbit v) (v / 2) A (S Lin) Lout (S D) 0); try assumption.
          - lia.
          - lia.
          - intros Hx. discriminate.
          - left. reflexivity.
          - intros _. exact Hcln.
          - apply (Nat.lt_le_trans _ _ _ HLB). apply Nat.mul_le_mono_r. lia.
          - destruct (mbit_cases v) as [-> | ->]; cbn [Dcns]; [lia|].
            simpl (Nat.eqb 0 0). split; [lia|left; lia].
          - apply bcls_S; [apply mbit_cases| |].
            + intros Hx. exfalso. unfold pe in HD. destruct pf; lia.
            + intros Hx. destruct (Hb1 ltac:(lia)) as [[Hn _]|[_ Hq]].
              * left. apply (nt_step k cc Lin v); [exact Hn|exact Hv].
              * right. split.
                -- unfold pe in HD. destruct pf; [reflexivity|lia].
                -- apply (tbq_step _ _ _ cc); [apply tbq0_tbq; exact Hq|exact Hv]. }
        destruct HIH as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
        exists (U :: U :: o), (U :: U :: F), (U :: U :: oL), w', nc.
        rewrite Hpd, it_T_dig. rewrite H1. simpl option_map.
        assert (Hmb : match mbit v with T_ => 1 | _ => 0 end = 0) by (destruct (mbit_cases v) as [-> | ->]; reflexivity).
        rewrite Hmb in H11.
        split; [reflexivity|]. split; [cbn [tape]; rewrite H2; reflexivity|].
        split; [subst F; reflexivity|]. split; [cbn [dcnt]; lia|]. split; [exact H5|].
        split; [apply endsd_cons, endsd_cons; exact H6|].
        split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
        split.
        { cbn [ucnt]. rewrite Hucnt, dcnt_dig by exact He. lia. }
        split; [intros Hx0; discriminate Hx0|]. split.
        -- intros m' c' Hm' Hx Hc' Hpf'. cbn [NCr]. apply H13; assumption.
        -- intros _. exists (U :: F). reflexivity.
Qed.

Definition FR (p : list op) (P2 : list dg -> Prop) : Prop :=
  exists o F oL w' nc, it p m = Some o /\ tape o = tape F /\ F = oL ++ w' /\
    dcnt oL = L /\ noH oL /\ endsd oL /\ trimz w' = w' /\ Good w' nc /\ (Y = 15 -> ucnt w' <= 31) /\
    (nc = 2 \/ (pf = true /\ nc + 1 = cS)) /\
    (forall m' c', m <= m' -> m' / 2 ^ L <= Y + 1 -> c' <= 2 -> (pf = true -> c' + 1 <= c) ->
      clause m' c' 0 (ucnt F) /\ NCr m' c' 0 F) /\
    P2 F.

(* Start in S1: the first digit was a 1. *)
Lemma start_S1 : forall low cc,
  1 + dcnt low = L -> noH low -> endsd low -> pf = false ->
  NCr m c 1 (low ++ w1) -> clause m c 1 (ucnt (low ++ w1)) ->
  cc + ucnt (low ++ w1) <= K4 (dcnt low - 1) + 3 * dcnt low + 40 + M -> nt k cc 1 ->
  FR (path S_1 (low ++ w1) cc) (fun _ => True).
Proof.
  intros low cc E1 Hh He Hpf0 Hn Hcl Hg Hnt.
  assert (Hi : 1 <= dcnt low) by (apply dcnt_ends; exact He).
  assert (Hne : low <> []) by (intros ->; contradiction).
  assert (HLR : LR S_1 low cc m 0).
  { apply (low_loop low S_1 cc m 1 0 1 0); try assumption.
    - reflexivity.
    - right. exact He.
    - lia.
    - intros Hx. discriminate.
    - left. reflexivity.
    - intros Hx. discriminate.
    - simpl. lia.
    - cbn [Nat.mul]. simpl. lia.
    - cbn [Dcns]. simpl (Nat.eqb 0 0). split; [lia|right; lia].
    - apply Ggm_ne'; [exact Hne|exact Hg].
    - apply bcls_S; [right; reflexivity| |].
      + intros _. exact Hnt.
      + intros Hx. discriminate. }
  destruct HLR as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
  exists o, F, oL, w', nc.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [lia|]. split; [exact H5|]. split; [exact H6|].
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [|exact I].
  intros m' c' Hm' Hx Hc' Hp'. split.
  - pose proof (clause_u 1 (dcnt low) (ucnt (low ++ w1)) ltac:(lia) Hi Hcl) as Hin.
    apply (emit_N 1 0 (dcnt low) (ucnt (low ++ w1))); try assumption; try lia.
  - apply H13; assumption.
Qed.

(* Start in S0, then a conversion: the second element is U. *)
Lemma start_conv : forall lr cc,
  1 + dcnt lr = L -> noH lr -> endsd lr -> pf = true ->
  NCr m c 1 (lr ++ w1) -> clause m c 1 (S (ucnt (lr ++ w1))) ->
  cc + S (ucnt (lr ++ w1)) <= K4 (dcnt lr - 1) + 3 * dcnt lr + 40 + M -> nt k cc 1 ->
  FR (Cv :: path S_1 (lr ++ w1) cc)
     (fun F => exists F2, F = bitd (m + 1) :: F2 /\ (2 <= dcnt lr -> exists F3, F2 = U :: F3)).
Proof.
  intros lr cc E1 Hh He Hp Hn Hcl Hg Hnt.
  assert (Hi : 1 <= dcnt lr) by (apply dcnt_ends; exact He).
  assert (Hne : lr <> []) by (intros ->; contradiction).
  assert (HLR : LR S_1 lr cc ((m + 1) / 2) 1).
  { apply (low_loop lr S_1 cc _ 1 1 0 1); try assumption.
    - reflexivity.
    - right. exact He.
    - lia.
    - intros _. split; [reflexivity|exact Hne].
    - right. reflexivity.
    - intros Hx. discriminate.
    - simpl (2 ^ 1). pose proof (lb_cv m ((m + 1) / 2) 1 1 m (d2c m) ltac:(lia) ltac:(lia)) as Hq.
      replace (1 - 1) with 0 in Hq by lia. rewrite Nat.mul_1_r in Hq. exact Hq.
    - simpl (2 ^ 1). pose proof (d2d m) as Hq. lia.
    - cbn [Dcns]. simpl (Nat.eqb 1 0). unfold pe. rewrite Hp. lia.
    - apply Ggm_ne'; [exact Hne|lia].
    - cbn [Bcls]. simpl (Nat.eqb 1 0). split; [intros _; exact Hnt|intros Hx; discriminate]. }
  destruct HLR as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
  assert (Hbd : bitd (m + 1) = Z \/ bitd (m + 1) = O) by apply bitd_cases.
  exists (bitd (m + 1) :: o), (bitd (m + 1) :: F), (bitd (m + 1) :: oL), w', nc.
  cbn [it]. rewrite H1. simpl option_map.
  split; [reflexivity|]. split; [rewrite !cw_bit_tape, H2; reflexivity|].
  split; [subst F; reflexivity|]. split; [rewrite dcnt_dig by exact Hbd; lia|].
  split; [rewrite noH_dig by exact Hbd; exact H5|]. split; [apply endsd_cons; exact H6|].
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split.
  - intros m' c' Hm' Hx Hc' Hp'.
    pose proof (clause_u 1 (dcnt lr) (S (ucnt (lr ++ w1))) ltac:(lia) Hi Hcl) as Hin.
    rewrite ucnt_dig, NCr_dig by exact Hbd. split; [|split].
    + apply (emit_N 1 0 (dcnt lr) (S (ucnt (lr ++ w1)))); try assumption; try lia.
    + assert (Hcc : c' + 1 <= c) by (apply Hp'; exact Hp).
      assert (Hau : ucnt F <= S (ucnt (lr ++ w1)) + a_ (3 + dcnt lr)) by (unfold a_; lia).
      apply (emit_T 1 (dcnt lr) (S (ucnt (lr ++ w1)))); try assumption; lia.
    + apply H13; assumption.
  - exists F. split; [reflexivity|]. exact H14.
Qed.

(* Start in S0, then a digit. *)
Lemma start_dig : forall e lr cc v,
  e = Z \/ e = O -> 2 + dcnt lr = L -> noH lr -> endsd lr ->
  v <= cc + 1 ->
  (forall mm, path mm (e :: lr ++ w1) cc = pdig mm v (fun m' => path m' (lr ++ w1) (v / 2))) ->
  (Nat.even v = true -> pf = true) -> (Nat.even v = false -> pf = false) ->
  NCr m c 2 (lr ++ w1) -> clause m c 2 (ucnt (lr ++ w1)) ->
  cc + ucnt (lr ++ w1) <= K4 (S (dcnt lr) - 1) + 3 * S (dcnt lr) + 40 + M -> nt k cc 1 ->
  FR (path S_0 (e :: lr ++ w1) cc)
     (fun F => exists F2, F = bitd m :: F2 /\ (Nat.even v = true -> exists d F3, F2 = d :: F3 /\ (d = Z \/ d = O))).
Proof.
  intros e lr cc v He E1 Hh Hend Hv Hpd Hpt Hpf0 Hn Hcl Hg Hnt.
  assert (Hi : 1 <= dcnt lr) by (apply dcnt_ends; exact Hend).
  assert (Hne : lr <> []) by (intros ->; contradiction).
  pose proof (clause_u 2 (dcnt lr) (ucnt (lr ++ w1)) ltac:(lia) Hi Hcl) as Hin.
  assert (Hg2 : v / 2 + ucnt (lr ++ w1) <= K4 (dcnt lr - 1) + 3 * dcnt lr + 40 + M).
  { apply (gamma_step cc); try lia.
    replace (S (dcnt lr) - 1) with (dcnt lr) in Hg by lia. lia. }
  assert (HLR : LR (mbit v) lr (v / 2) (m / 2) 1).
  { apply (low_loop lr (mbit v) (v / 2) _ 2 1 1 0); try assumption.
    - reflexivity.
    - right. exact Hend.
    - lia.
    - intros Hx. discriminate.
    - left. reflexivity.
    - intros _. exact Hcl.
    - simpl (2 ^ 1). pose proof (lb_dg m (m / 2) 1 1 m (d2a m) ltac:(lia)) as Hq. rewrite Nat.mul_1_r in Hq. exact Hq.
    - simpl (2 ^ 1). pose proof (d2b m) as Hq. lia.
    - unfold mbit. destruct (Nat.even v) eqn:Ev.
      + cbn [Dcns]. unfold pe. rewrite (Hpt eq_refl). lia.
      + cbn [Dcns]. simpl (Nat.eqb 0 0). split; [lia|right; lia].
    - apply Ggm_ne'; [exact Hne|exact Hg2].
    - apply bcls_S; [apply mbit_cases| |].
      + intros _. apply (nt_step k cc 1 v); [exact Hnt|exact Hv].
      + intros Hx. discriminate. }
  destruct HLR as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]]]]].
  assert (Hbd : bitd m = Z \/ bitd m = O) by apply bitd_cases.
  assert (Hmb : match mbit v with T_ => 1 | _ => 0 end = 0) by (destruct (mbit_cases v) as [-> | ->]; reflexivity).
  rewrite Hmb in H11.
  exists (bitd m :: o), (bitd m :: F), (bitd m :: oL), w', nc.
  rewrite Hpd. rewrite it_S0_dig. rewrite H1. simpl option_map.
  split; [reflexivity|]. split; [rewrite !cw_bit_tape, H2; reflexivity|].
  split; [subst F; reflexivity|]. split; [rewrite dcnt_dig by exact Hbd; lia|].
  split; [rewrite noH_dig by exact Hbd; exact H5|]. split; [apply endsd_cons; exact H6|].
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split.
  - intros m' c' Hm' Hx Hc' Hp'.
    rewrite ucnt_dig, NCr_dig by exact Hbd. split; [|split].
    + apply (emit_N 2 0 (dcnt lr) (ucnt (lr ++ w1))); try assumption; try lia.
    + apply (emit_N 2 1 (dcnt lr) (ucnt (lr ++ w1))); try assumption; try lia.
    + apply H13; assumption.
  - exists F. split; [reflexivity|]. intros Ev.
    unfold mbit in H14. rewrite Ev in H14. cbn [HDm] in H14. apply H14. exact Hi.
Qed.

End Loop.

Definition phase (k : nat) (X : list dg) (m : nat) : nat :=
  if Nat.ltb 0 k then 2 else
  match X with
  | Z :: Z :: _ => if Nat.even m then 2 else 1
  | Z :: U :: _ => if Nat.even m then 1 else 2
  | Z :: [] => if Nat.even m then 2 else 1
  | _ => 0
  end.

Lemma phase_le : forall k X m, phase k X m <= 2.
Proof.
  intros k X m. unfold phase. destruct (Nat.ltb 0 k); [lia|].
  destruct X as [|[] [|[] X']]; try lia; destruct (Nat.even m); lia.
Qed.

Definition InvP (T : trie) (v k : nat) (x0 : dg) (low1 w : list dg) (L c : nat) : Prop :=
  (x0 = Z \/ x0 = O) /\ noH low1 /\ endsd low1 /\ 1 + dcnt low1 = L /\ 13 <= L /\
  8 <= v / 2 ^ L /\ v / 2 ^ L <= 15 /\ trimz w = w /\ c <= 2 /\
  vb (w, v / 2 ^ L, c) = true /\ memk (key (w, v / 2 ^ L, c)) T = true /\
  (k = 0 \/ c = 2) /\ k * 8 < 2 ^ L /\
  phase k (x0 :: low1 ++ w) (v + k + 1) <= c /\
  clause (v + k + 1) (phase k (x0 :: low1 ++ w) (v + k + 1)) 0 (ucnt (us k (x0 :: low1 ++ w))) /\
  NCr (v + k + 1) (phase k (x0 :: low1 ++ w) (v + k + 1)) 0 (us k (x0 :: low1 ++ w)).

Lemma us_ucnt : forall k X, ucnt (us k X) = k + ucnt X.
Proof. induction k as [|k IH]; intros X; [reflexivity|]. simpl. rewrite IH. lia. Qed.

Lemma us_NCr : forall k m c L X, NCr m c L (us k X) = NCr m c L X.
Proof. induction k as [|k IH]; intros m c L X; [reflexivity|]. simpl. apply IH. Qed.

Lemma K4_small : forall n, (K4 (12 + n) + 40) * 8 < 2 ^ (13 + n) /\ 24 * (12 + n) + 312 <= 2 ^ (13 + n).
Proof.
  induction n as [|n IH]; [vm_compute; split; lia|].
  destruct IH as [H1 H2].
  replace (12 + S n) with (S (12 + n)) by lia. replace (13 + S n) with (S (13 + n)) by lia.
  rewrite K4_step, pow_S. lia.
Qed.

Lemma tape_app_congr : forall l s s', noH l -> tape s = tape s' -> tape (l ++ s) = tape (l ++ s').
Proof.
  induction l as [|d l IH]; intros s s' Hh He; [exact He|].
  destruct (dg_cases d) as [->|[Hd| ->]].
  - cbn [app tape]. rewrite (IH s s' Hh He). reflexivity.
  - rewrite noH_dig in Hh by exact Hd. rewrite <- !app_comm_cons.
    rewrite !tape_cons by (destruct Hd as [-> | ->]; discriminate).
    rewrite (IH s s' Hh He). reflexivity.
  - contradiction.
Qed.

Lemma tape_Z_end : forall l, noH l -> tape (l ++ [Z]) = tape l.
Proof.
  induction l as [|d l IH]; intros Hh.
  - cbn. rewrite !S0_const. reflexivity.
  - destruct (dg_cases d) as [->|[Hd| ->]].
    + cbn [app tape]. rewrite (IH Hh). reflexivity.
    + rewrite noH_dig in Hh by exact Hd. rewrite <- app_comm_cons.
      rewrite !tape_cons by (destruct Hd as [-> | ->]; discriminate).
      rewrite (IH Hh). reflexivity.
    + contradiction.
Qed.

Lemma split_w : forall w, hfirst w = false ->
  exists a, noH a /\ endsd a /\ dcnt a = 1 /\ ucnt a + ucnt (strip1 w) = ucnt w /\
    tape (a ++ strip1 w) = tape w /\
    (a ++ strip1 w = w \/ (a ++ strip1 w = w ++ [Z] /\ noH w /\ dcnt w = 0)).
Proof.
  induction w as [|d w IH]; intros Hf.
  - exists [Z]. cbn. rewrite !S0_const. repeat split; try reflexivity. right. repeat split.
  - destruct (dg_cases d) as [->|[Hd| ->]].
    + cbn in Hf. destruct (IH Hf) as [a [H1 [H2 [H3 [H4 [H5 H6]]]]]].
      exists (U :: a). cbn [noH strip1 dcnt ucnt app tape]. split; [exact H1|]. split; [apply endsd_cons; exact H2|].
      split; [exact H3|]. split; [lia|]. split; [rewrite H5; reflexivity|].
      destruct H6 as [H6|[H6 [H7 H8]]].
      * left. rewrite H6. reflexivity.
      * right. split; [rewrite H6; reflexivity|]. split; [exact H7|exact H8].
    + exists [d]. destruct Hd as [-> | ->]; cbn [strip1 app noH endsd dcnt ucnt].
      all: split; [exact I|]; split; [exact I|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; left; reflexivity.
    + cbn in Hf. discriminate.
Qed.

Lemma NCr_snocZ : forall l m c L, noH l -> m / 2 ^ (S L + dcnt l) < 16 -> NCr m c L l -> NCr m c L (l ++ [Z]).
Proof.
  induction l as [|d l IH]; intros m c L Hh Hx Hn.
  - cbn [app NCr]. split; [|exact I]. unfold clause. intros H16. cbn [dcnt] in Hx. replace (S L + 0) with (S L) in Hx by lia. lia.
  - destruct (dg_cases d) as [->|[Hd| ->]].
    + cbn [app NCr noH dcnt] in *. apply IH; assumption.
    + rewrite noH_dig in Hh by exact Hd. rewrite dcnt_dig in Hx by exact Hd.
      rewrite <- app_comm_cons, NCr_dig by exact Hd. rewrite NCr_dig in Hn by exact Hd.
      destruct Hn as [H1 H2]. rewrite ucnt_app. simpl (ucnt [Z]). rewrite Nat.add_0_r. split; [exact H1|].
      apply IH; [exact Hh| |exact H2]. replace (S (S L) + dcnt l) with (S L + S (dcnt l)) by lia. exact Hx.
    + contradiction.
Qed.

Lemma split_lead : forall l, noH l -> endsd l ->
  exists k x l', l = us k (x :: l') /\ (x = Z \/ x = O) /\ noH l' /\ dcnt l = 1 + dcnt l' /\ (l' = [] \/ endsd l').
Proof.
  induction l as [|d l IH]; intros Hh He; [contradiction|].
  destruct (dg_cases d) as [->|[Hd| ->]].
  - assert (He' : endsd l).
    { destruct l as [|d' l']; [contradiction|exact He]. }
    destruct (IH Hh He') as [k [x [l' [E1 [E2 [E3 [E4 E5]]]]]]].
    exists (S k), x, l'. cbn [us dcnt]. rewrite E1. split; [reflexivity|]. rewrite <- E1. auto.
  - exists 0, d, l. rewrite noH_dig in Hh by exact Hd. rewrite dcnt_dig by exact Hd.
    split; [reflexivity|]. split; [exact Hd|]. split; [exact Hh|]. split; [reflexivity|].
    destruct l as [|d' l']; [left; reflexivity|right].
    apply (endsd_tail d); [discriminate|exact He].
  - contradiction.
Qed.

Lemma us_app : forall k X s, us k X ++ s = us k (X ++ s).
Proof. induction k as [|k IH]; intros X s; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma x_add : forall v k p, 1 <= p -> k <= p -> (v + k) / p <= v / p + 1.
Proof.
  intros v k p Hp Hk.
  assert (H1 : (v + k) / p <= (v + 1 * p) / p).
  { apply Nat.Div0.div_le_mono. lia. }
  rewrite Nat.div_add in H1 by lia. exact H1.
Qed.

Lemma dcnt_app : forall a b, dcnt (a ++ b) = dcnt a + dcnt b.
Proof.
  induction a as [|d a IH]; intros b; [reflexivity|].
  destruct d; cbn [app dcnt]; rewrite IH; lia.
Qed.

Lemma noH_app : forall a b, noH a -> noH b -> noH (a ++ b).
Proof.
  induction a as [|d a IH]; intros b H1 H2; [exact H2|].
  destruct d; cbn [app noH] in *; try (apply IH; assumption). contradiction.
Qed.

Lemma endsd_app : forall a b, endsd b -> endsd (a ++ b).
Proof.
  induction a as [|d a IH]; intros b H; [exact H|].
  rewrite <- app_comm_cons. apply endsd_cons. apply IH. exact H.
Qed.

Lemma low_fact' : forall m L1 i Lin, Lin + i = L1 -> 1 <= i -> 8 <= m / 2 ^ L1 -> m / 2 ^ L1 <= 15 ->
  16 <= m / 2 ^ Lin /\ Nat.log2 (m / 2 ^ Lin) = 3 + i /\ GG (m / 2 ^ Lin) = K4 (i - 1) + M1 (m / 2 ^ L1).
Proof.
  intros m L1 i Lin E Hi H1 H2. subst L1.
  destruct (low_log m Lin i H1 ltac:(lia)) as [H3 H4].
  pose proof (GG_low m Lin i Hi H1 ltac:(lia)) as H5.
  split; [|split; assumption].
  assert (H6 : 2 ^ (3 + i) <= m / 2 ^ Lin).
  { rewrite <- H3. apply Nat.log2_spec.
    destruct (m / 2 ^ Lin) eqn:E0; [|lia]. rewrite Nat.log2_nonpos in H3 by lia. lia. }
  rewrite Nat.pow_add_r in H6. pose proof (pow2_ge i). simpl (2 ^ 3) in H6. lia.
Qed.

Lemma dv_le : forall k x, x = Z \/ x = O -> dv k x <= k + 1.
Proof. intros k x [-> | ->]; cbn [dv]; lia. Qed.

Lemma nt_start : forall k x, x = Z \/ x = O -> nt k (dv k x / 2) 1.
Proof.
  intros k x Hx. unfold nt. pose proof (dv_le k x Hx). pose proof (d2b (dv k x)).
  simpl (2 ^ 1). lia.
Qed.

Lemma bitd_dig : forall n, bitd n = Z \/ bitd n = O.
Proof. intros n. unfold bitd. destruct (Nat.even n); auto. Qed.

Lemma phase_pos : forall k X m, k <> 0 -> phase k X m = 2.
Proof. intros [|k] X m H; [contradiction|reflexivity]. Qed.

Lemma phase_ZU : forall X m, phase 0 (Z :: U :: X) m = if Nat.even m then 1 else 2.
Proof. reflexivity. Qed.

Lemma phase_ZZ : forall X m, phase 0 (Z :: Z :: X) m = if Nat.even m then 2 else 1.
Proof. reflexivity. Qed.

Lemma even_S1 : forall m, Nat.even (m + 1) = negb (Nat.even m).
Proof. intros m. rewrite Nat.add_1_r, Nat.even_succ, <- Nat.negb_even. reflexivity. Qed.

Lemma phase_conv : forall m F3, phase 0 (bitd (m + 1) :: U :: F3) (m + 1) + 1 <= (if Nat.even m then 1 else 2).
Proof.
  intros m F3. unfold bitd. rewrite even_S1. destruct (Nat.even m) eqn:E; cbn [negb].
  - cbn. lia.
  - rewrite phase_ZU, even_S1, E. cbn [negb]. lia.
Qed.

Lemma phase_dig : forall m d F3, d = Z \/ d = O -> phase 0 (bitd m :: d :: F3) (m + 1) + 1 <= (if Nat.even m then 2 else 1).
Proof.
  intros m d F3 Hd. unfold bitd. destruct (Nat.even m) eqn:E.
  - destruct Hd as [-> | ->].
    + rewrite phase_ZZ, even_S1, E. cbn [negb]. lia.
    + cbn. lia.
  - cbn. lia.
Qed.

Lemma noH_us : forall k X, noH X -> noH (us k X).
Proof. induction k as [|k IH]; intros X H; [exact H|]. cbn [us noH]. apply IH. exact H. Qed.

Section Step.
Variable T : trie.
Hypothesis Hok : forall x, vb x = true -> memk (key x) T = true -> okx T x.
Hypothesis Hseed : forall y, In y seeds -> memk (key y) T = true.

Theorem inv_step : forall v k x0 low1 w L c, InvP T v k x0 low1 w L c ->
  exists v' k' x0' low1' w' L' c',
    cfg v (us k (x0 :: low1 ++ w)) -->+ cfg v' (us k' (x0' :: low1' ++ w')) /\
    InvP T v' k' x0' low1' w' L' c'.
Proof.
  intros v k x0 low1 w L c Hinv.
  destruct Hinv as [Hx0 [Hh1 [He1 [Hd1 [HL13 [HY8 [HY15 [Htr [Hc2 [Hvb [Hmem [Hkc [Hk8 [Hph [Hcl0 Hnc0]]]]]]]]]]]]]]].
  remember (v + k + 1) as m eqn:Em.
  remember (phase k (x0 :: low1 ++ w) m) as ph eqn:Eph.
  remember (v / 2 ^ L) as Y0 eqn:EY0.
  pose proof (pow_pos L) as Hp2.
  assert (Hk1 : k + 1 <= 2 ^ L) by lia.
  assert (Hm1 : Y0 <= m / 2 ^ L).
  { rewrite EY0. apply x_mono. lia. }
  assert (Hm2 : m / 2 ^ L <= Y0 + 1).
  { rewrite EY0, Em. replace (v + k + 1) with (v + (k + 1)) by lia. apply x_add; lia. }
  remember (m / 2 ^ L - Y0) as dd eqn:Edd.
  assert (Hdd : dd <= 1) by lia.
  assert (HmY : m / 2 ^ L = Y0 + dd) by lia.
  assert (Hv1 : 1 <= v + k).
  { pose proof (Nat.div_mod_eq v (2 ^ L)) as Hdm. rewrite <- EY0 in Hdm.
    assert (Hz : 2 ^ L * 8 <= 2 ^ L * Y0) by (apply Nat.mul_le_mono_l; lia). lia. }
  destruct (drift w Y0 dd) as [w1 Yp] eqn:Edr.
  assert (HYp : 8 <= Yp <= 15 /\ (Y0 + dd = 16 -> Yp = 8 /\ w1 = strip1 w) /\ (Y0 + dd <> 16 -> Yp = Y0 + dd /\ w1 = w)).
  { unfold drift in Edr. destruct (Nat.eqb (Y0 + dd) 16) eqn:Eq; injection Edr as <- <-.
    - apply Nat.eqb_eq in Eq. split; [lia|]. split; [auto|]. intros Hne. contradiction.
    - apply Nat.eqb_neq in Eq. split; [lia|]. split; [intros Hx; contradiction|auto]. }
  destruct HYp as [HYp [HYs HYn]].
  (* a dummy move gives the side facts *)
  assert (Hdummy : ucnt w1 <= M1 Yp /\ (Y0 + dd = 16 -> hfirst w = false)).
  { assert (Hallow : In 2 (allowed 3 c 0 (ckf c) (ctf (M1 Yp) (ucnt w1)))) by (simpl; left; reflexivity).
    destruct (top_step T Hok Hseed w Y0 c dd w1 Yp S_0 0 (2 ^ 3 * Yp) 3 2 Hvb Hmem Hdd Edr ltac:(lia) Hallow ltac:(lia))
      as [H1 [H2 _]].
    - lia.
    - simpl (2 ^ 3). lia.
    - split; assumption. }
  destruct Hdummy as [Hu1 Hhf].
  (* the low part and the word after a possible shift of the cut *)
  assert (Hshape : exists L1 lowh,
    1 + dcnt lowh = L1 /\ endsd lowh /\ noH lowh /\ 13 <= L1 /\ m / 2 ^ L1 = Yp /\ 2 ^ L <= 2 ^ L1 /\
    tape (lowh ++ w1) = tape (low1 ++ w) /\ ucnt (lowh ++ w1) = ucnt (low1 ++ w) /\
    (NCr m ph 1 (low1 ++ w) -> NCr m ph 1 (lowh ++ w1)) /\
    (forall e1 l1, low1 = e1 :: l1 -> exists lr, lowh = e1 :: lr)).
  { destruct (Nat.eq_dec (Y0 + dd) 16) as [E16|Ene].
    - destruct (HYs E16) as [-> ->].
      destruct (split_w w (Hhf E16)) as [a [A1 [A2 [A3 [A4 [A5 A6]]]]]].
      exists (S L), (low1 ++ a).
      assert (Hm8 : m / 2 ^ S L = 8).
      { replace (S L) with (L + 1) by lia. rewrite div_pow_add. rewrite HmY, E16. reflexivity. }
      split; [rewrite dcnt_app; lia|]. split; [apply endsd_app; exact A2|]. split; [apply noH_app; assumption|].
      split; [lia|]. split; [exact Hm8|]. split; [apply Nat.pow_le_mono_r; lia|].
      split.
      { rewrite <- app_assoc. apply tape_app_congr; [exact Hh1|exact A5]. }
      split.
      { rewrite !ucnt_app, <- A4. lia. }
      split.
      { intros Hn. rewrite <- app_assoc. destruct A6 as [A6|[A6 [A7 A8]]].
        - rewrite A6. exact Hn.
        - rewrite A6. rewrite app_assoc. apply NCr_snocZ; [apply noH_app; assumption| |exact Hn].
          rewrite dcnt_app, A8.
          replace (S 1 + (dcnt low1 + 0)) with (S L) by lia. lia. }
      intros e1 l1 ->. exists (l1 ++ a). reflexivity.
    - destruct (HYn Ene) as [-> ->].
      exists L, low1. repeat split; try assumption; try lia.
      + intros Hn. exact Hn.
      + intros e1 l1 ->. exists l1. reflexivity. }
  destruct Hshape as [L1 [lowh [S1 [S2 [S3 [S4 [S5 [S6 [S7 [S8 [S9 S10]]]]]]]]]]].
  assert (Hk81 : k * 8 < 2 ^ L1) by lia.
  rewrite us_NCr in Hnc0. rewrite NCr_dig in Hnc0 by exact Hx0. destruct Hnc0 as [Hcl1 Hnc1].
  rewrite us_ucnt, ucnt_dig in Hcl0 by exact Hx0.
  rewrite <- S8 in Hcl1, Hcl0.
  apply S9 in Hnc1.
  assert (Hdh : 1 <= dcnt lowh) by (apply dcnt_ends; exact S2).
  destruct (low_fact' m L1 (dcnt lowh) 1 ltac:(lia) Hdh ltac:(lia) ltac:(lia)) as [F1 [F2 F3]].
  rewrite S5 in F3.
  destruct (low_fact' m L1 L1 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [F4 [F5 F6]].
  rewrite S5 in F6.
  assert (Hub0 : k + ucnt (lowh ++ w1) <= K4 (dcnt lowh) + M1 Yp).
  { specialize (Hcl0 F4). rewrite F5, F6 in Hcl0.
    replace (L1 - 1) with (dcnt lowh) in Hcl0 by lia. lia. }
  assert (Hub1 : ucnt (lowh ++ w1) + ph * a_ (3 + dcnt lowh) <= K4 (dcnt lowh - 1) + M1 Yp).
  { specialize (Hcl1 F1). rewrite F2, F3 in Hcl1. exact Hcl1. }
  (* the section facts *)
  set (Good := fun w' nc => vb (w', Yp, nc) = true /\ memk (key (w', Yp, nc)) T = true).
  assert (Htop : forall mode cc A d nc, 1 <= d ->
    In nc (allowed d c cc (ckf c) (ctf (M1 Yp) (ucnt w1))) -> cc <= cgf (M1 Yp) (ucnt w1) ->
    2 ^ d * Yp <= A + d -> A + 1 <= 2 ^ d * (Yp + 1) ->
    exists o oL w', it (path mode w1 cc) A = Some o /\ tape o = tape (oL ++ w') /\ dcnt oL = d /\
      noH oL /\ endsd oL /\ trimz w' = w' /\ ucnt oL + ucnt w' <= capf (M1 Yp) (ucnt w1) /\ Good w' nc /\ (Yp = 15 -> ucnt w' <= 31)).
  { intros mode cc A d nc H1 H2 H3 H4 H5.
    destruct (top_step T Hok Hseed w Y0 c dd w1 Yp mode cc A d nc Hvb Hmem Hdd Edr H1 H2 H3 H4 H5)
      as [_ [_ [o [oL [w' [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 G10]]]]]]]]]]]]]].
    exists o, oL, w'. repeat split; try assumption. }
  (* the start of the pass *)
  remember (dv k x0) as v0 eqn:Ev0.
  remember (v0 / 2) as cc0 eqn:Ecc.
  assert (Hnt : nt k cc0 1) by (rewrite Ecc, Ev0; apply nt_start; exact Hx0).
  assert (Hv0 : v0 <= k + 1) by (rewrite Ev0; apply dv_le; exact Hx0).
  assert (Hcc : cc0 <= k) by (rewrite Ecc; pose proof (d2b v0); lia).
  assert (Hg0 : cc0 + ucnt (lowh ++ w1) <= K4 (dcnt lowh - 1) + 3 * dcnt lowh + 40 + M1 Yp).
  { destruct (dcnt lowh) as [|j] eqn:Ej; [lia|].
    rewrite ?Ej in Hub0. rewrite K4_step in Hub0. replace (S j - 1) with j by lia. lia. }
  assert (HY8' : 8 <= Yp) by lia.
  assert (HY15' : Yp <= 15) by lia.
  assert (HL1' : 3 <= L1) by lia.
  (* what is common to all three starts *)
  assert (Hfin : forall (pf : bool) (P2 : list dg -> Prop) (p : list op),
    FR m L1 Yp ph c pf Good p P2 -> p = path (mbit v0) (lowh ++ w1) cc0 ->
    (forall F, pf = true -> P2 F -> exists x' F', F = x' :: F' /\ (x' = Z \/ x' = O) /\ phase 0 F (m + 1) + 1 <= ph) ->
    exists v' k' x0' low1' w' L' c',
      cfg v (us k (x0 :: low1 ++ w)) -->+ cfg v' (us k' (x0' :: low1' ++ w')) /\
      InvP T v' k' x0' low1' w' L' c').
  { intros pf P2 p HFR Ep Hnext.
    unfold FR in HFR.
    destruct HFR as [o [F [oL [w' [nc [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]]]]]]]]]].
    destruct (split_lead oL H5 H6) as [k' [x' [l' [E1 [E2 [E3 [E4 E5]]]]]]].
    assert (EF : F = us k' (x' :: l' ++ w')) by (rewrite H3, E1, us_app; reflexivity).
    assert (Hd : pf = true -> k' = 0 /\ phase 0 F (m + 1) + 1 <= ph).
    { intros Epf. destruct (Hnext F Epf H12) as [x2 [F' [G1 [G2 G3]]]].
      split; [|exact G3].
      destruct k' as [|k2]; [reflexivity|]. exfalso. rewrite EF in G1. cbn [us] in G1. injection G1 as G4 _.
      destruct G2 as [-> | ->]; discriminate. }
    assert (Hcl : clause m 0 0 (ucnt F) /\ NCr m 0 0 F).
    { apply H11.
      - lia.
      - rewrite S5. lia.
      - lia.
      - intros Epf. destruct (Hd Epf) as [_ G]. lia. }
    destruct Hcl as [Hcl _].
    assert (Hu : ucnt F <= K4 (L1 - 1) + M1 Yp).
    { unfold clause in Hcl. specialize (Hcl F4). rewrite F5, F6 in Hcl. lia. }
    assert (Hk8' : (K4 (L1 - 1) + 40) * 8 < 2 ^ L1).
    { destruct (K4_small (L1 - 13)) as [K1 _].
      replace (12 + (L1 - 13)) with (L1 - 1) in K1 by lia.
      replace (13 + (L1 - 13)) with L1 in K1 by lia. exact K1. }
    assert (HM : M1 Yp <= 40) by (pose proof (M1_range Yp HY8' HY15'); lia).
    assert (Hkk : k' <= ucnt F) by (rewrite EF, us_ucnt; lia).
    assert (Hk88 : k' * 8 < 2 ^ L1) by lia.
    assert (Hk1' : k' + 1 <= 2 ^ L1) by lia.
    assert (Hm' : (m + k' + 1) / 2 ^ L1 <= Yp + 1).
    { replace (m + k' + 1) with (m + (k' + 1)) by lia. rewrite <- S5. apply x_add; lia. }
    assert (Hnum : clause (m + k' + 1) (phase k' (x' :: l' ++ w') (m + k' + 1)) 0 (ucnt F) /\
                   NCr (m + k' + 1) (phase k' (x' :: l' ++ w') (m + k' + 1)) 0 F).
    { apply H11.
      - lia.
      - exact Hm'.
      - apply phase_le.
      - intros Epf. destruct (Hd Epf) as [G1 G2]. subst k'.
        replace (m + 0 + 1) with (m + 1) by lia.
        rewrite EF in G2. exact G2. }
    exists m, k', x'. exists l', w'. exists L1. exists nc.
    split.
    - assert (Ht1 : tape (us k (x0 :: low1 ++ w)) = tape (us k (x0 :: lowh ++ w1))).
      { change (x0 :: low1 ++ w) with ([x0] ++ (low1 ++ w)). change (x0 :: lowh ++ w1) with ([x0] ++ (lowh ++ w1)).
        rewrite <- !us_app. apply tape_app_congr; [|symmetry; exact S7].
        apply noH_us. destruct Hx0 as [-> | ->]; exact I. }
      assert (Hb : cfg v (us k (x0 :: lowh ++ w1)) -->+ cfg (v + k + 1) o).
      { apply bell_ok; [exact Hx0|exact Hv1|]. rewrite <- Ev0, <- Ecc, <- Em, <- Ep. exact H1. }
      rewrite <- Em in Hb. unfold cfg in *. rewrite Ht1, <- EF, <- H2. exact Hb.
    - unfold InvP. rewrite S5, <- EF.
      unfold Good in H8. destruct H8 as [H8a H8b].
      split; [exact E2|]. split; [exact E3|].
      split; [destruct E5 as [E5|E5]; [subst l'; cbn [dcnt] in E4; lia|exact E5]|].
      split; [lia|]. split; [exact S4|]. split; [lia|]. split; [lia|]. split; [exact H7|].
      split; [lia|]. split; [exact H8a|]. split; [exact H8b|].
      split; [destruct H10 as [H10|[H10a H10b]]; [right; exact H10|left; destruct (Hd H10a) as [G _]; exact G]|].
      split; [exact Hk88|].
      split.
      { destruct H10 as [->|[H10a H10b]]; [apply phase_le|].
        destruct (Hd H10a) as [G1 G2]. subst k'. rewrite EF in G2.
        replace (m + 0 + 1) with (m + 1) by lia. cbn [us] in G2. lia. }
      exact Hnum. }
  destruct (Nat.even v0) eqn:Ev.
  - (* even head: the pass starts in S_0 and reads the next element *)
    assert (Hmb : mbit v0 = S_0) by (unfold mbit; rewrite Ev; reflexivity).
    destruct low1 as [|e1 l1]; [cbn [dcnt] in Hd1; lia|].
    destruct (S10 e1 l1 eq_refl) as [lr ->].
    assert (Hk0 : k = 0 -> x0 = Z /\ cc0 = 0).
    { intros Hk. rewrite Hk in Ev0. destruct Hx0 as [Ex | Ex]; rewrite Ex in Ev0.
      - split; [exact Ex|]. rewrite Ecc, Ev0. reflexivity.
      - exfalso. rewrite Ev0 in Ev. cbn in Ev. discriminate. }
    destruct (dg_cases e1) as [->|[He| ->]].
    + (* a U: conversion *)
      assert (S1' : 1 + dcnt lr = L1) by exact S1.
      assert (S3' : noH lr) by exact S3.
      assert (S2' : endsd lr).
      { destruct lr as [|d' l']; [contradiction|exact S2]. }
      assert (Hphc : (if Nat.even m then 1 else 2) <= ph).
      { destruct (Nat.eq_dec k 0) as [Hk|Hk].
        - destruct (Hk0 Hk) as [Ex _]. rewrite Eph, Hk, Ex. cbn [app]. rewrite phase_ZU. destruct (Nat.even m); lia.
        - rewrite (phase_pos k _ m Hk) in Eph. rewrite Eph. destruct (Nat.even m); lia. }
      assert (Hpf1 : true = true -> 1 <= ph).
      { intros _. destruct (Nat.even m); lia. }
      assert (HF : FR m L1 Yp ph c true Good (Cv :: path S_1 (lr ++ w1) cc0)
        (fun F => exists F2, F = bitd (m + 1) :: F2 /\ (2 <= dcnt lr -> exists F3, F2 = U :: F3))).
      { apply (start_conv m L1 Yp (M1 Yp) (ucnt w1) k ph c w1 true Good S5 HY8' HY15' eq_refl eq_refl Hu1 HL1' Hk81 Hph Hc2 Hpf1 Hkc Htop lr cc0
          S1' S3' S2' eq_refl Hnc1 Hcl1 Hg0 Hnt). }
      apply (Hfin true _ _ HF).
      * rewrite Hmb. reflexivity.
      * intros F _ [Fb [G1 G2]].
        assert (Hd2 : 2 <= dcnt lr) by lia.
        destruct (G2 Hd2) as [Fc ->].
        exists (bitd (m + 1)), (U :: Fc). split; [exact G1|]. split; [apply bitd_dig|].
        rewrite G1. eapply Nat.le_trans; [apply phase_conv|exact Hphc].
    + (* a digit *)
      rewrite dcnt_dig in S1 by exact He.
      rewrite noH_dig in S3 by exact He.
      assert (S2' : endsd lr).
      { destruct lr as [|d' l']; [cbn [dcnt] in S1; lia|].
        apply (endsd_tail e1); [destruct He as [-> | ->]; discriminate|exact S2]. }
      assert (Hbv : bv e1 <= 1) by (destruct He as [-> | ->]; cbn; lia).
      assert (Hph_d : Nat.even (cc0 + bv e1) = true -> (if Nat.even m then 2 else 1) <= ph).
      { intros Ee. destruct (Nat.eq_dec k 0) as [Hk|Hk].
        - destruct (Hk0 Hk) as [Ex Ec]. rewrite Ec in Ee.
          assert (Eez : e1 = Z).
          { destruct He as [-> | ->]; [reflexivity|]. cbn in Ee. discriminate. }
          rewrite Eph, Hk, Ex, Eez. cbn [app]. rewrite phase_ZZ. destruct (Nat.even m); lia.
        - rewrite (phase_pos k _ m Hk) in Eph. rewrite Eph. destruct (Nat.even m); lia. }
      assert (Hpf_d : Nat.even (cc0 + bv e1) = true -> 1 <= ph).
      { intros Ee. specialize (Hph_d Ee). destruct (Nat.even m); lia. }
      rewrite <- app_comm_cons, NCr_dig in Hnc1 by exact He.
      destruct Hnc1 as [Hc2' Hnc2].
      rewrite <- app_comm_cons, ucnt_dig, dcnt_dig in Hg0 by exact He.
      assert (HF : FR m L1 Yp ph c (Nat.even (cc0 + bv e1)) Good (path S_0 (e1 :: lr ++ w1) cc0)
        (fun F => exists F2, F = bitd m :: F2 /\ (Nat.even (cc0 + bv e1) = true -> exists d F3, F2 = d :: F3 /\ (d = Z \/ d = O)))).
      { apply (start_dig m L1 Yp (M1 Yp) (ucnt w1) k ph c w1 (Nat.even (cc0 + bv e1)) Good S5 HY8' HY15' eq_refl eq_refl Hu1 HL1' Hk81 Hph Hc2 Hpf_d Hkc Htop e1 lr cc0 (cc0 + bv e1)
          He ltac:(lia) S3 S2' ltac:(lia) (fun mm => path_dig mm e1 (lr ++ w1) cc0 He) (fun H => H) (fun H => H) Hnc2 Hc2' Hg0 Hnt). }
      apply (Hfin _ _ _ HF).
      * rewrite Hmb. reflexivity.
      * intros F Ee [Fb [G1 G2]].
        destruct (G2 Ee) as [d [Fc [-> Gd]]].
        exists (bitd m), (d :: Fc). split; [exact G1|]. split; [apply bitd_dig|].
        rewrite G1. eapply Nat.le_trans; [apply phase_dig; exact Gd|]. apply Hph_d. exact Ee.
    + cbn [noH] in S3. contradiction.
  - (* odd head: the pass starts in S_1 *)
    assert (Hmb : mbit v0 = S_1) by (unfold mbit; rewrite Ev; reflexivity).
    assert (Hpf0 : false = true -> 1 <= ph) by discriminate.
    assert (HF := start_S1 m L1 Yp (M1 Yp) (ucnt w1) k ph c w1 false Good S5 HY8' HY15' eq_refl eq_refl Hu1 HL1' Hk81 Hph Hc2 Hpf0 Hkc Htop lowh cc0
      S1 S3 S2 eq_refl Hnc1 Hcl1 Hg0 Hnt).
    apply (Hfin _ _ _ HF).
    + rewrite Hmb. reflexivity.
    + intros F Ef. discriminate.
Qed.

End Step.

(* The law run in the VM, with binary numbers. *)
Definition bitN (n : N) : dg := if N.even n then Z else O.

Fixpoint itN (p : list op) (n : N) : option (list dg) :=
  match p with
  | [] => Some []
  | Dg :: p' => option_map (cons (bitN n)) (itN p' (N.div2 n))
  | Cv :: p' => option_map (cons (bitN (n + 1)%N)) (itN p' (N.div2 (n + 1)%N))
  | Rp :: p' => match n with N0 => None | _ => itN p' (N.pred n) end
  | Rd :: p' => option_map (fun o => U :: U :: o) (itN p' n)
  | Em :: p' => option_map (cons U) (itN p' n)
  | E0 :: _ => Some (bin (N.to_nat n))
  | E1 :: _ => match n with N0 => Some [H] | _ => Some (U :: U :: bin (N.to_nat (N.pred n))) end
  | E2 :: _ => Some (U :: U :: bin (N.to_nat n))
  | EH0 :: _ => Some (bin (S (N.to_nat n)))
  | EH1 :: _ => Some (U :: bin (N.to_nat n))
  | Fl :: _ => None
  end.

Lemma even_N : forall n, N.even (N.of_nat n) = Nat.even n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite Nat2N.inj_succ, N.even_succ, <- N.negb_even, IH, Nat.even_succ, <- Nat.negb_even. reflexivity.
Qed.

Lemma bitN_ok : forall n, bitN (N.of_nat n) = bitd n.
Proof. intros n. unfold bitN, bitd. rewrite even_N. reflexivity. Qed.

Lemma div2_N : forall n, N.div2 (N.of_nat n) = N.of_nat (n / 2).
Proof. intros n. rewrite <- Nat2N.inj_div2, Nat.div2_div. reflexivity. Qed.

Lemma pred_N : forall n, N.pred (N.of_nat (S n)) = N.of_nat n.
Proof. intros n. rewrite Nat2N.inj_succ, N.pred_succ. reflexivity. Qed.

Lemma itN_ok : forall p n, itN p (N.of_nat n) = it p n.
Proof.
  induction p as [|o p IH]; intros n; [reflexivity|].
  destruct o; cbn [itN it].
  - rewrite bitN_ok, div2_N, IH. reflexivity.
  - assert (E : (N.of_nat n + 1)%N = N.of_nat (n + 1)) by (rewrite Nat2N.inj_add; reflexivity).
    rewrite E, bitN_ok, div2_N, IH. reflexivity.
  - destruct n as [|n']; [reflexivity|].
    change (itN p (N.pred (N.of_nat (S n'))) = it p n'). rewrite pred_N. apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite Nat2N.id. reflexivity.
  - destruct n as [|n']; [reflexivity|].
    change (Some (U :: U :: bin (N.to_nat (N.pred (N.of_nat (S n'))))) = Some (U :: U :: bin n')).
    rewrite pred_N, Nat2N.id. reflexivity.
  - rewrite Nat2N.id. reflexivity.
  - rewrite Nat2N.id. reflexivity.
  - rewrite Nat2N.id. reflexivity.
  - reflexivity.
Qed.

Fixpoint lead (r : list dg) : option (nat * dg * list dg) :=
  match r with
  | [] => Some (0, Z, [])
  | U :: r' => match lead r' with Some (k, x, t) => Some (S k, x, t) | None => None end
  | H :: _ => None
  | d :: t => Some (0, d, t)
  end.

Lemma lead_ok : forall r k x t, lead r = Some (k, x, t) -> (x = Z \/ x = O) /\ tape r = tape (us k (x :: t)).
Proof.
  induction r as [|d r IH]; intros k x t Hl.
  - cbn in Hl. injection Hl as <- <- <-. split; [left; reflexivity|]. cbn. rewrite !S0_const. reflexivity.
  - destruct d; cbn [lead] in Hl.
    + destruct (lead r) as [[[k1 x1] t1]|] eqn:E; [|discriminate].
      injection Hl as <- <- <-. destruct (IH _ _ _ eq_refl) as [H1 H2]. split; [exact H1|].
      cbn [us tape]. rewrite H2. reflexivity.
    + injection Hl as <- <- <-. split; [left; reflexivity|reflexivity].
    + injection Hl as <- <- <-. split; [right; reflexivity|reflexivity].
    + discriminate.
Qed.

Definition bell1N (v : N) (r : list dg) : option (N * list dg) :=
  match lead r with
  | None => None
  | Some (k, x, t) =>
    match v with
    | N0 => None
    | _ =>
      match itN (path (mbit (dv k x)) t (dv k x / 2)) (v + N.of_nat k + 1)%N with
      | None => None
      | Some o => Some ((v + N.of_nat k + 1)%N, o)
      end
    end
  end.

Lemma bell1N_ok : forall v r v' r', bell1N v r = Some (v', r') -> cfg (N.to_nat v) r -->+ cfg (N.to_nat v') r'.
Proof.
  intros v r v' r' Hb. unfold bell1N in Hb.
  destruct (lead r) as [[[k x] t]|] eqn:El; [|discriminate].
  destruct v as [|pv]; [discriminate|].
  assert (Em : (N.pos pv + N.of_nat k + 1)%N = N.of_nat (N.to_nat (N.pos pv) + k + 1)).
  { rewrite !Nat2N.inj_add, N2Nat.id. reflexivity. }
  rewrite Em, itN_ok in Hb.
  destruct (it (path (mbit (dv k x)) t (dv k x / 2)) (N.to_nat (N.pos pv) + k + 1)) as [o|] eqn:Eo; [|discriminate].
  injection Hb as <- <-.
  rewrite Nat2N.id.
  destruct (lead_ok _ _ _ _ El) as [Hx Ht].
  unfold cfg. rewrite Ht.
  assert (H1 : 1 <= N.to_nat (N.pos pv) + k).
  { pose proof (Pos2Nat.is_pos pv). cbn [N.to_nat]. lia. }
  exact (bell_ok _ k x t o Hx H1 Eo).
Qed.

Fixpoint runN (f : nat) (v : N) (r : list dg) : option (N * list dg) :=
  match f with
  | 0 => Some (v, r)
  | S f' =>
    match bell1N v r with
    | None => None
    | Some (v1, r1) => runN f' v1 r1
    end
  end.

Lemma runN_ok : forall f v r v' r', runN f v r = Some (v', r') -> cfg (N.to_nat v) r -->* cfg (N.to_nat v') r'.
Proof.
  induction f as [|f IH]; intros v r v' r' Hr.
  - cbn in Hr. injection Hr as <- <-. apply evstep_refl.
  - cbn [runN] in Hr. destruct (bell1N v r) as [[v1 r1]|] eqn:E; [|discriminate].
    eapply evstep_trans; [apply progress_evstep; exact (bell1N_ok _ _ _ _ E)|exact (IH _ _ _ _ Hr)].
Qed.

Definition clauseb (m c L u : nat) : bool :=
  implb (Nat.leb 16 (m / 2 ^ L)) (Nat.leb (u + c * a_ (Nat.log2 (m / 2 ^ L))) (GG (m / 2 ^ L))).

Lemma clauseb_ok : forall m c L u, clauseb m c L u = true -> clause m c L u.
Proof.
  intros m c L u Hb H16. unfold clauseb in Hb. apply Nat.leb_le in H16. rewrite H16 in Hb.
  cbn [implb] in Hb. apply Nat.leb_le. exact Hb.
Qed.

Fixpoint NCrb (m c L : nat) (r : list dg) : bool :=
  match r with
  | [] => true
  | U :: r' => NCrb m c L r'
  | H :: _ => true
  | _ :: r' => andb (clauseb m c (S L) (ucnt r')) (NCrb m c (S L) r')
  end.

Lemma NCrb_ok : forall r m c L, NCrb m c L r = true -> NCr m c L r.
Proof.
  induction r as [|d r IH]; intros m c L Hb; [exact I|].
  destruct d; cbn [NCrb] in Hb; cbn [NCr].
  - apply IH. exact Hb.
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. split; [apply clauseb_ok; exact H1|apply IH; exact H2].
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. split; [apply clauseb_ok; exact H1|apply IH; exact H2].
  - exact I.
Qed.

(* The run from the blank tape in state A, up to the size where the invariant holds. *)
Definition v0A : N := 1%N.
Definition r0A : list dg := [U; U].
Definition vA : N := 65540%N.
Definition lA : list dg := [U; U; U; U; U; U; U; U; U; O; U; O; U; O; Z; O; O; O; O; O; O; O; O].
Definition wA : list dg := [O; O; O].
Definition rA : list dg := us 11 (O :: lA ++ wA).

Lemma runA : runN 7089 v0A r0A = Some (vA, rA).
Proof. vm_compute. reflexivity. Qed.

Lemma numA : let m := N.to_nat vA + 11 + 1 in
  let ph := phase 11 (O :: lA ++ wA) m in
  andb (clauseb m ph 0 (ucnt rA)) (NCrb m ph 0 rA) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma invA : forall T : trie, (forall y, In y seeds -> memk (key y) T = true) ->
  InvP T (N.to_nat vA) 11 O lA wA 13 2.
Proof.
  intros T Hseed.
  assert (EY : N.to_nat vA / 2 ^ 13 = 8) by (vm_compute; reflexivity).
  pose proof numA as Hn. cbv zeta in Hn. apply andb_prop in Hn. destruct Hn as [Hn1 Hn2].
  unfold InvP. rewrite EY.
  split; [right; reflexivity|]. split; [exact I|]. split; [exact I|]. split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
  split; [reflexivity|]. split; [exact (Hseed _ (seeds_in 8 7 2 ltac:(lia) ltac:(lia) ltac:(lia)))|].
  split; [right; reflexivity|]. split; [vm_compute; lia|]. split; [apply phase_le|].
  split; [apply clauseb_ok; exact Hn1|apply NCrb_ok; exact Hn2].
Qed.

Lemma startA : c0 -->* cfg (N.to_nat v0A) r0A.
Proof.
  unfold c0. change (N.to_nat v0A) with 1. unfold cfg. cbn [lft tape cw r0A].
  do 18 step. finish.
Qed.

(* The run from the blank tape in state F, up to the size where the invariant holds. *)
Definition v0F : N := 1%N.
Definition r0F : list dg := [].
Definition vF : N := 65545%N.
Definition lF : list dg := [U; U; U; U; U; U; U; U; U; U; Z; U; Z; U; U; U; O; U; U; U; U; U; U; U; Z; U; Z; U; Z; U; Z; O; O; O; O; O].
Definition wF : list dg := [O; O; O].
Definition rF : list dg := us 0 (Z :: lF ++ wF).

Lemma runF : runN 7121 v0F r0F = Some (vF, rF).
Proof. vm_compute. reflexivity. Qed.

Lemma numF : let m := N.to_nat vF + 0 + 1 in
  let ph := phase 0 (Z :: lF ++ wF) m in
  andb (clauseb m ph 0 (ucnt rF)) (NCrb m ph 0 rF) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma invF : forall T : trie, (forall y, In y seeds -> memk (key y) T = true) ->
  InvP T (N.to_nat vF) 0 Z lF wF 13 2.
Proof.
  intros T Hseed.
  assert (EY : N.to_nat vF / 2 ^ 13 = 8) by (vm_compute; reflexivity).
  pose proof numF as Hn. cbv zeta in Hn. apply andb_prop in Hn. destruct Hn as [Hn1 Hn2].
  unfold InvP. rewrite EY.
  split; [left; reflexivity|]. split; [exact I|]. split; [exact I|]. split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
  split; [reflexivity|]. split; [exact (Hseed _ (seeds_in 8 7 2 ltac:(lia) ltac:(lia) ltac:(lia)))|].
  split; [right; reflexivity|]. split; [vm_compute; lia|]. split; [apply phase_le|].
  split; [apply clauseb_ok; exact Hn1|apply NCrb_ok; exact Hn2].
Qed.

Lemma startF : (F;; tape0) -->* cfg (N.to_nat v0F) r0F.
Proof.
  change (N.to_nat v0F) with 1. unfold cfg. cbn [lft tape cw r0F].
  do 1 step. finish.
Qed.

Definition isS (x : option trie) : bool := match x with Some _ => true | None => false end.

Lemma RR_some : isS (closure 40000) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma seedsok_t : seedsok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma isS_ex : forall x, isS x = true -> exists t, x = Some t.
Proof. intros [t|] H; [exists t; reflexivity|discriminate]. Qed.

Theorem closed_ex : exists R : trie,
  (forall x, vb x = true -> memk (key x) R = true -> okx R x) /\
  (forall y, In y seeds -> memk (key y) R = true).
Proof.
  destruct (isS_ex _ RR_some) as [R HR].
  exists R. exact (closure_ok _ _ HR seedsok_t).
Qed.

Definition stE : Type := nat * nat * dg * list dg * list dg * nat * nat.

Definition CE (i : stE) :=
  match i with (v, k, x, l, w, Lc, c) => cfg v (us k (x :: l ++ w)) end.

Definition PE (T : trie) (i : stE) : Prop :=
  match i with (v, k, x, l, w, Lc, c) => InvP T v k x l w Lc c end.

Theorem nonhalt_entry : forall c v k x l w Lc cp,
  (forall T : trie, (forall y, In y seeds -> memk (key y) T = true) -> InvP T v k x l w Lc cp) ->
  c -->* cfg v (us k (x :: l ++ w)) -> ~ halts tm c.
Proof.
  intros c v k x l w Lc cp Hi Hr.
  destruct closed_ex as [T [Hok Hseed]].
  apply multistep_nonhalt with (c' := CE (v, k, x, l, w, Lc, cp)); [exact Hr|].
  apply (progress_nonhalt_cond tm _ _ CE (PE T)).
  - intros [[[[[[v1 k1] x1] l1] w1] Lc1] c1] HP.
    destruct (inv_step T Hok Hseed v1 k1 x1 l1 w1 Lc1 c1 HP) as [v' [k' [x' [l' [w' [L' [c' [H1 H2]]]]]]]].
    exists (v', k', x', l', w', L', c'). split; [exact H1|exact H2].
  - apply Hi. exact Hseed.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (nonhalt_entry c0 (N.to_nat vA) 11 O lA wA 13 2 invA).
  eapply evstep_trans; [exact startA|]. exact (runN_ok _ _ _ _ _ runA).
Qed.

Theorem nonhalt_F : ~ halts tm (F;; tape0).
Proof.
  apply (nonhalt_entry (F;; tape0) (N.to_nat vF) 0 Z lF wF 13 2 invF).
  eapply evstep_trans; [exact startF|]. exact (runN_ok _ _ _ _ _ runF).
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA"%string).
Definition rename q := match q with A => F | B => C | C => D | D => B | E => E | F => A end.

Lemma renamed : Perm tm TM1.tm rename.
Proof.
  split.
  - intros [] []; cbn; congruence.
  - intros [] [] w d q H; inversion H; reflexivity.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (perm_nonhalt tm TM1.tm rename A tape0); [apply renamed|apply TM1.nonhalt_F].
Qed.
End TM2.

Print Assumptions TM1.nonhalt.
Print Assumptions TM2.nonhalt.
