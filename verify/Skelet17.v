(** * Skelet #17 *)

From BusyCoq Require Import Individual52.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import PeanoNat. Import Nat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => None
  | B, 0 => Some (0, L, C)  | B, 1 => Some (1, R, E)
  | C, 0 => Some (0, L, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, B)
  | E, 0 => Some (0, R, B)  | E, 1 => Some (0, R, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).


Lemma shift10 : forall n l (i o : Sym),
  l << i << o <* <[i; o]^^n = l <* <[i; o]^^n << i << o.
Proof.
  introv.
  change (l << i << o) with (l <* <[i; o]).
  rewrite lpow_shift'.
  reflexivity.
Qed.

Local Hint Rewrite shift10 : tape_post.

(** ** List-of-exponents representation *)

(* the list starts with the element closest to the tape head *)

(* Note: [lowerL'] and [lowerR'] assume a (10)^n term will get prepended, and
   thus emit the separator for it. This could be written without an auxiliary
   definition, but this form is much easier to state lemmas about. *)
Fixpoint lowerL' (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => lowerL' xs <* <[1; 0]^^x << 1
  end.

Definition lowerL (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => lowerL' xs <* <[1; 0]^^x
  end.

Fixpoint lowerR' (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => 1 >> [1; 0]^^x *> lowerR' xs
  end.

Definition lowerR (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => [1; 0]^^x *> lowerR' xs
  end.

Definition lower (xs : list nat) : Q * tape :=
  lowerL xs <| lowerR' [].

Definition lower' (xs : list nat) : Q * tape :=
  lowerL xs |> lowerR' [].

Lemma lowerL_merge : forall x y ys,
  lowerL (y :: ys) <* <[1; 0]^^x = lowerL (x + y :: ys).
Proof.
  introv.
  destruct ys as [| y0 ys]; simpl_tape; reflexivity.
Qed.

Lemma lowerL_nonempty : forall xs,
  xs <> [] ->
  lowerL' xs = lowerL xs << 1.
Proof.
  introv H.
  destruct xs; try congruence.
  reflexivity.
Qed.

Lemma fold_lowerL' : forall x xs,
  lowerL' xs <* <[1; 0]^^x << 1 = lowerL' (x :: xs).
Proof. reflexivity. Qed.


Lemma fold_lowerR' : forall x xs,
  1 >> [1; 0]^^x *> lowerR' xs = lowerR' (x :: xs).
Proof. reflexivity. Qed.

Arguments lowerL : simpl never.
Arguments lowerL' : simpl never.
Arguments lowerR : simpl never.
Arguments lowerR' : simpl never.

(** Basic machine behavior *)

Lemma goright_10 : forall n l r,
  l |> [1; 0]^^n *> r -->* l <* <[1; 0]^^n |> r.
Proof.
  induction n.
  - triv.
  - execute. follow IHn. simpl_tape. finish.
Qed.

Lemma goleft_even10 : forall n l r,
  Even n ->
  l <* <[1; 0]^^n <| r -->* l <| [1; 0]^^n *> r.
Proof.
  introv H. destruct H as [n' H]. rewrite H.
  simpl. rewrite <- plus_n_O. clear n H. rename n' into n.
  simpl_tape.
  generalize dependent l. generalize dependent r.
  induction n; introv.
  - finish.
  - execute. follow IHn. simpl_tape. finish.
Qed.

Lemma goleft_odd10 : forall n l r,
  Even n ->
  l << 1 <* <[1; 0]^^(S n) <| r -->*
  l <* <[1; 0; 1] <* <[1; 0]^^n |> r.
Proof.
  introv H.
  cbn[lpow]. rewrite <- lpow_shift, Str_app_assoc.
  follow goleft_even10. execute.
  follow goright_10. finish.
Qed.

(** ** Higher-level behavior *)

Notation Nonzero := (fun n => n <> O).

Ltac evstep1 := (econstructor; [ econstructor; reflexivity | cbn ]).

Lemma goright_nonzero_step : forall xs x y ys,
  lowerL (y :: ys) |> lowerR' ((S x) :: xs) -->*
  lowerL (x :: (S y) :: ys) |> lowerR' xs.
Proof.
  introv.
  unfold lowerR'. fold lowerR'.
  execute.
  follow goright_10.
  finish.
Qed.


Lemma goright_nonzero_steps : forall xs x y ys zs,
  Forall Nonzero xs ->
  lowerL (y :: ys) |> lowerR' (xs ++ (S x) :: zs) -->*
  lowerL (x :: rev xs ++ (S y) :: ys) |> lowerR' zs.
Proof.
  induction xs; introv Hxs.
  1: apply goright_nonzero_step.
  inverts Hxs as Ha Hxs.
  destruct a as [|a].
  1: congruence.
  eapply evstep_trans.
  2: {
    cbn.
    rewrite <-app_assoc.
    cbn.
    apply IHxs,Hxs.
  }
  cbn.
  apply goright_nonzero_step.
Qed.

Lemma goright_nonzero : forall xs x x' y ys,
  Forall Nonzero xs ->
  lowerL (y :: ys) |> lowerR (x :: xs ++ [S x']) -->*
  lowerL (x' :: rev xs ++ (S x + y) :: ys) |> const 0.
Proof.
  introv Hxs.
  unfold lowerR.
  follow goright_10.
  rewrite lowerL_merge.
  applys_eq goright_nonzero_steps; auto 1.
Qed.


Lemma goright_nonzero' : forall xs x y ys,
  Forall Nonzero xs ->
  lowerL (y :: ys) |> lowerR' (xs ++ [S x]) -->*
  lowerL (x :: rev xs ++ (S y) :: ys) |> const 0.
Proof.
  introv Hxs.
  apply goright_nonzero with (x := O). assumption.
Qed.

Lemma app_nonempty_r : forall A (xs ys : list A),
  ys <> [] -> xs ++ ys <> [].
Proof.
  introv H. destruct xs.
  - apply H.
  - discriminate.
Qed.

Lemma cons_nonempty : forall A (x : A) xs,
  x :: xs <> [].
Proof. discriminate. Qed.

#[export] Hint Resolve app_nonempty_r : core.
#[export] Hint Immediate cons_nonempty : core.

Lemma goleft_even : forall xs l r,
  Forall Even xs ->
  l <> [] ->
  lowerL (xs ++ l) <| lowerR' r -->*
  lowerL l <| lowerR' (rev xs ++ r).
Proof.
  induction xs as [| x xs]; introv Heven Hl.
  - finish.
  - inverts Heven as Hx Hxs.
    simpl lowerL. follow goleft_even10.
    rewrite lowerL_nonempty by auto. execute.
    rewrite fold_lowerR'. follow IHxs.
    rewrite <- app_assoc. finish.
Qed.

#[export] Hint Resolve -> Odd_succ : core.
#[export] Hint Resolve Forall_rev : core.

Lemma increment_S_even : forall x xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ y :: z :: zs) -->*
  lower (x :: xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)).
  destruct y. { destruct Hy. lia. }
  unfold lowerL. rewrite <- fold_lowerL'.
  follow goleft_odd10. (* could get -->+ here *)
  change ([1; 0; 1] *> [0; 1] ^^ z *> lowerL' zs) with
  (1 >> [0; 1]^^(S z) *> lowerL' zs).
  rewrite fold_lowerL'.
  rewrite app_nil_r.
  follow goright_nonzero'.
  rewrite rev_involutive. execute.
Qed.


Lemma increment_O_even : forall x xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (O :: S x :: xs ++ y :: z :: zs) -->*
  lower (S x :: xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hx Hy.
  remember (lower (S x :: xs ++ y :: S z :: zs)) as tg.
  unfold lower,lowerL.
  cbn.
  unfold lowerL'. fold lowerL'.
  evstep1.
  change (C, ((1 >> [0; 1] ^^ x *> lowerL' (xs ++ y :: z :: zs), 0, 1 >> lowerR' []))) with
  ([0; 1] ^^ (S x) *> lowerL' (xs ++ y :: z :: zs) <| lowerR' [O]).
  follow (goleft_even (S x :: xs)).
  destruct y. { destruct Hy. lia. }
  unfold lowerL. rewrite <- fold_lowerL'.
  follow goleft_odd10. (* could get -->+ here *)
  change ([1; 0; 1] *> [0; 1] ^^ z *> lowerL' zs) with
  (1 >> [0; 1]^^(S z) *> lowerL' zs).
  rewrite fold_lowerL'.
  cbn.
  rewrite <-app_assoc. cbn.
  change [S x; O] with ([S x] ++ [O]).
  change ([0; 1] ^^ y *> lowerL' (S z :: zs)) with (lowerL (y::S z::zs)).
  follow goright_nonzero_steps.
  cbn.
  rewrite rev_involutive.
  subst.
  unfold lowerR'.
  do 3 evstep1.
  rewrite <-const_unfold.
  finish.
Qed.

#[local] Hint Extern 1 (Even _) => rewrite <- even_spec; reflexivity : core.


Lemma increment_S_odd : forall x y xs,
  Odd (S x) ->
  lower (S x :: y :: xs) -->*
  lower (x :: S y :: xs).
Proof.
  introv Hx. follow goleft_odd10. execute.
Qed.

Lemma increment_O_odd : forall x y xs,
  Odd (S x) ->
  lower (O :: S x :: y :: xs) -->*
  lower (S x :: S y :: xs).
Proof.
  introv Hx.
  remember (lower (S x :: S y :: xs)) as tg.
  unfold lower,lowerL.
  cbn.
  unfold lowerL'. fold lowerL'.
  evstep1.
  follow goleft_odd10.
  cbn.
  unfold lowerR'.
  unfold lower in Heqtg.
  do 3 evstep1.
  subst.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma increment_O : forall xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  lower (O :: xs ++ y :: z :: zs) -->*
  lower (xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hy.
  destruct y as [|y].
  1: inverts Hy; lia.
  destruct xs as [|x xs].
  - cbn.
    apply increment_O_odd,Hy.
  - cbn.
    inverts Hnonzero as Hx Hxs.
    inverts Heven as Hx' Hxs'.
    destruct x as [|x].
    1: lia.
    apply increment_O_even; auto 1.
Qed.

(* This corresponds to overflow followed by empty in Chris Xu's writeup.
   The config [lower (xs ++ [S y; O])] he lists isn't visited. *)
Lemma overflow_S : forall x xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 1; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)). rewrite app_nil_r.
  destruct y. { destruct Hy. lia. }
  unfold lowerL, lowerL'.
  replace (S y) with (y+1) by lia.
  rewrite lpow_add.
  cbn. rewrite Str_app_assoc. cbn.
  follow goleft_even10. execute.
  change (const 0 << 1 << 1 << 1 << 0 << 1 << 1 << 0)
    with (lowerL [1; 1; 0; 0])%nat.
  follow goright_nonzero. rewrite rev_involutive.
  execute.
Qed.

Lemma overflow_O : forall xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  lower (O :: xs ++ [y]) -->*
  lower (xs ++ [S y; 1; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hy.
  follow (goleft_even (O :: xs)). rewrite app_nil_r.
  destruct y. { destruct Hy. lia. }
  unfold lowerL, lowerL'.
  replace (S y) with (y+1) by lia.
  rewrite lpow_add.
  cbn. rewrite Str_app_assoc. cbn.
  follow goleft_even10. execute.
  change (const 0 << 1 << 1 << 1 << 0 << 1 << 1 << 0)
    with (lowerL [1; 1; 0; 0])%nat.
  destruct xs as [|x xs].
  - cbn.
    unfold lowerR'. cbn.
    follow goright_10.
    do 3 evstep1.
    rewrite <-const_unfold.
    unfold lower,lowerR',lowerL.
    simpl_tape.
    finish.
  - cbn. rewrite <-app_assoc. cbn.
    inverts Hnonzero as Hx Hxs.
    inverts Heven as Hx' Hxs'.
    destruct x as [|x]. 1: lia.
    follow goright_10.
    rewrite lowerL_merge.
    follow goright_nonzero_steps. rewrite rev_involutive.
    do 3 evstep1.
    rewrite <-const_unfold.
    unfold lower,lowerR',lowerL.
    simpl_tape.
    finish.
Qed.

Lemma zero_S : forall x xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Even y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)). rewrite app_nil_r.
  unfold lowerL, lowerL'.
  follow goleft_even10. execute.
  follow goright_10.
  change ([0; 1] ^^ y *> 1>>1>>const 0) with (lowerL [y; 0; 0]%nat).
  follow goright_nonzero_steps. rewrite rev_involutive.
  unfold lower,lowerR'.
  do 1 evstep1.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma zero_O : forall xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even y ->
  lower (O :: xs ++ [y]) -->*
  lower (xs ++ [S y; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hy.
  follow (goleft_even (O :: xs)). rewrite app_nil_r.
  unfold lowerL, lowerL'.
  follow goleft_even10. execute.
  follow goright_10.
  change ([0; 1] ^^ y *> 1>>1>>const 0) with (lowerL [y; 0; 0]%nat).
  destruct xs as [|x xs].
  - cbn.
    unfold lowerR'. cbn.
    do 3 evstep1.
    rewrite <-const_unfold.
    finish.
  - cbn. rewrite <-app_assoc. cbn.
    inverts Hnonzero as Hx Hxs.
    inverts Heven as Hx' Hxs'.
    destruct x as [|x]. 1: lia.
    follow goright_nonzero_steps. rewrite rev_involutive.
    do 3 evstep1.
    rewrite <-const_unfold.
    finish.
Qed.

(* from here we talk about the operations defined in Chris Xu's paper *)

Inductive Increment: (nat*(list nat))->(nat*(list nat))->Prop :=
| Increment_even x xs y z zs:
  Even x ->
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  Increment
  (S x, xs ++ y :: z :: zs)
  (x, xs ++ y :: S z :: zs)
| Increment_odd x y xs:
  Odd x ->
  Increment
  (S x, y :: xs)
  (x, S y :: xs)
.

Inductive Halve: (nat*(list nat))->(nat*(list nat))->Prop :=
| Halve_intro x xs:
  Halve
  (O, x :: xs)
  (S x, xs)
.

Inductive Zero: (nat*(list nat))->(nat*(list nat))->Prop :=
| Zero_intro x xs y:
  Forall Nonzero xs ->
  Forall Even xs ->
  Even x ->
  Even y ->
  Zero
  (S x, xs ++ [y])
  (x, xs ++ [S y; O; O])
.

Inductive Overflow: (nat*(list nat))->(nat*(list nat))->Prop :=
| Overflow_intro x xs y:
  Forall Nonzero xs ->
  Forall Even xs ->
  Even x ->
  Odd y ->
  Overflow
  (S x, xs ++ [y])
  (S x, xs ++ [S y; O])
.

Inductive TryHalve: (nat*(list nat))->(nat*(list nat))->Prop :=
| TryHalve_1 x xs:
  TryHalve
  (O, x :: xs)
  (S x, xs)
| TryHalve_0 x xs:
  TryHalve
  (S x, xs)
  (S x, xs)
.



(* translation between savask's operations and Chris Xu's operations *)

Inductive toConfig: (nat*(list nat))->(Q*tape)->Prop :=
| toConfig_intro x xs:
  toConfig (S x,xs) (lower (x::xs))
.

Lemma Increment_toConfig s1 s2 s3 c1 c3:
  Increment s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.
Proof.
  intros I12 I23 T1 T3.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct s3 as [x3 xs3].
  inverts I12.
  - inverts I23.
    + inverts T1.
      inverts T3.
      rewrite H1.
      follow increment_O. finish.
    + inverts T1.
      inverts T3.
      follow increment_S_even.
      finish.
  - inverts I23.
    1: inverts H0; lia.
    inverts T1.
    inverts T3.
    follow increment_S_odd.
    finish.
Qed.

Lemma Zero_toConfig s1 s2 s3 c1 c3:
  Zero s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.
Proof.
  intros I12 I23 T1 T3.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct s3 as [x3 xs3].
  inverts I12.
  inverts I23.
  + inverts T1.
    inverts T3.
    rewrite H1.
    follow zero_O. finish.
  + inverts T1.
    inverts T3.
    follow zero_S. finish.
Qed.

Lemma Overflow_toConfig s1 s2 s3 s4 c1 c4:
  Overflow s1 s2 ->
  Zero s2 s3 ->
  TryHalve s3 s4 ->
  toConfig s1 c1 ->
  toConfig s4 c4 ->
  c1 -->* c4.
Proof.
  intros I12 I23 I34 T1 T4.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct s3 as [x3 xs3].
  destruct s4 as [x4 xs4].
  inverts T1.
  inverts T4.
  inverts I12.
  inverts I23.
  inverts I34.
  - follow overflow_O.
    rewrite H2.
    rewrite (app_cons_r xs) in H0.
    rewrite app_inj_tail_iff in H0.
    destruct H0.
    subst.
    rewrite <-app_assoc.
    finish.
  - follow overflow_S.
    rewrite (app_cons_r xs) in H0.
    rewrite app_inj_tail_iff in H0.
    destruct H0.
    subst.
    rewrite <-app_assoc.
    finish.
Qed.


(* decode of Grey Code *)
Fixpoint grey_to_binary(xs:list bool):(list bool) :=
match xs with
| nil => nil
| xh::xt => (xorb xh (hd false (grey_to_binary xt)))::(grey_to_binary xt)
end.

Definition list_to_binary(xs:list nat):(list bool) :=
  grey_to_binary (map odd xs).

Fixpoint binary_to_nat(xs:list bool):nat :=
match xs with
| nil => O
| xh::xt =>
  (if xh then (S O) else O)+(binary_to_nat xt)*2
end.

(* n (binary) *)
Definition to_n_binary(s:nat*(list nat)) :=
  list_to_binary (snd s).

(* n *)
Definition to_n(s:nat*(list nat)) :=
  binary_to_nat (to_n_binary s).

(* s *)
Definition to_s(s:nat*(list nat)) :=
  let (x,xs):=s in
  xorb (even x) (hd false (list_to_binary xs)).

(* l *)
Definition to_l(s:nat*(list nat)) :=
  length (to_n_binary s).


Ltac simpl_xor_neg :=
  repeat (
    rewrite <-Bool.negb_xorb_l ||
    rewrite <-Bool.negb_xorb_r ||
    rewrite Bool.negb_involutive ||
    rewrite Bool.xorb_true_l ||
    rewrite Bool.negb_true_iff ||
    rewrite Bool.negb_false_iff);
  try reflexivity.

Ltac simpl_oe_S :=
  repeat (rewrite odd_succ || rewrite even_succ).

Ltac OE_oe :=
  repeat (match goal with
  | H: Even _ |- _ => rewrite <-even_spec in H
  | H: Odd _ |- _ => rewrite <-odd_spec in H
  end).


(* some trivial lemmas *)

Lemma map_odd_Even xs:
  Forall Even xs ->
  map odd xs = repeat false (length xs).
Proof.
  induction xs.
  1: reflexivity.
  intros Hev.
  inverts Hev as Ha Hxs.
  specialize (IHxs Hxs).
  cbn.
  f_equal; auto 1.
  unfold odd.
  OE_oe.
  rewrite Ha.
  reflexivity.
Qed.

Lemma grey_to_binary_0s_hd n xs:
  hd false (grey_to_binary (repeat false n ++ xs)) = hd false (grey_to_binary xs).
Proof.
  induction n; auto 1.
Qed.

Lemma grey_to_binary_0s n xs:
  grey_to_binary ((repeat false n) ++ xs) =
  (repeat (hd false (grey_to_binary xs)) n) ++ grey_to_binary xs.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite <-IHn.
  f_equal.
  apply grey_to_binary_0s_hd.
Qed.

Lemma hd_repeat(x:bool) n xs:
  hd false ((repeat x n)++x::xs) = x.
Proof.
  destruct n; reflexivity.
Qed.

Lemma repeat_app_S{A} (x:A) n xs:
  repeat x n ++ x :: xs =
  (repeat x (S n)) ++ xs.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  reflexivity.
Qed.

Lemma binary_to_nat_S n xs:
  S (binary_to_nat (repeat true n ++ false :: xs)) =
  binary_to_nat (repeat false n ++ true :: xs).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite <-IHn.
  lia.
Qed.

Lemma list_to_binary_app_O_hd xs:
  (hd false (list_to_binary (xs ++ [O]))) =
  (hd false (list_to_binary (xs))).
Proof.
  induction xs.
  1: reflexivity.
  cbn.
  unfold list_to_binary in IHxs.
  rewrite IHxs.
  reflexivity.
Qed.

Lemma list_to_binary_S_hd xs z zs:
  (hd false (list_to_binary (xs ++ S z :: zs))) =
  negb (hd false (list_to_binary (xs ++ z :: zs))).
Proof.
  induction xs.
  - cbn.
    simpl_oe_S.
    unfold odd.
    simpl_xor_neg.
  - cbn.
    unfold list_to_binary in IHxs.
    rewrite IHxs.
    simpl_xor_neg.
Qed.

Lemma list_to_binary_app_S_hd xs y:
  (hd false (list_to_binary (xs ++ [S y]))) =
  negb (hd false (list_to_binary (xs ++ [y]))).
Proof.
  induction xs.
  - cbn.
    simpl_oe_S.
    unfold odd.
    simpl_xor_neg.
  - cbn.
    unfold list_to_binary in IHxs.
    rewrite IHxs.
    simpl_xor_neg.
Qed.

Lemma binary_to_nat_app_O xs:
  binary_to_nat (xs ++ [false]) =
  binary_to_nat (xs).
Proof.
  induction xs.
  1: reflexivity.
  cbn.
  rewrite IHxs.
  reflexivity.
Qed.

Lemma pow2_nez i:
  2 ^ i <> O.
Proof.
  apply pow_nonzero; lia.
Qed.

Lemma binary_to_nat_1s_app n xs:
  binary_to_nat (repeat true n ++ xs) =
  (binary_to_nat xs)*(2^n) + (2^n) - 1.
Proof.
  induction n.
  1: cbn; lia.
  cbn.
  rewrite IHn.
  pose proof (pow2_nez n).
  lia.
Qed.

Lemma binary_to_nat_0s_app n xs:
  binary_to_nat (repeat false n ++ xs) =
  (binary_to_nat xs)*(2^n).
Proof.
  induction n.
  1: cbn; lia.
  cbn.
  rewrite IHn.
  pose proof (pow2_nez n).
  lia.
Qed.

Lemma binary_to_nat_1s n:
  binary_to_nat (repeat true n) =
  (2^n)-1.
Proof.
  pose proof (binary_to_nat_1s_app n nil) as H.
  cbn in H.
  rewrite app_nil_r in H.
  apply H.
Qed.

Lemma binary_to_nat_0s n:
  binary_to_nat (repeat false n) =
  O.
Proof.
  pose proof (binary_to_nat_0s_app n nil) as H.
  cbn in H.
  rewrite app_nil_r in H.
  apply H.
Qed.

Lemma grey_to_binary_length xs:
  length (grey_to_binary xs) = length xs.
Proof.
  induction xs.
  1: reflexivity.
  cbn.
  f_equal.
  apply IHxs.
Qed.

Ltac simpl_list_to_binary_0s:=
  unfold list_to_binary;
  rewrite map_app;
  rewrite map_odd_Even; [idtac | auto 1; fail];
  rewrite grey_to_binary_0s;
  cbn;
  try rewrite hd_repeat.




(* s after Inc/Halve/Zero/Overflow *)

Lemma Increment_sgn s1 s2:
  Increment s1 s2 ->
  to_s s1 = to_s s2.
Proof.
  intro I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts I.
  - unfold to_s.
    simpl_oe_S.
    unfold odd.
    symmetry.
    rewrite app_cons_r.
    rewrite list_to_binary_S_hd.
    rewrite <-app_cons_r.
    simpl_xor_neg.
  - unfold to_s.
    simpl_oe_S.
    unfold odd.
    change (S y :: xs) with (nil ++ ((S y :: xs))).
    rewrite (list_to_binary_S_hd). cbn.
    simpl_xor_neg.
Qed.


Lemma Halve_sgn s1 s2:
  Halve s1 s2 ->
  negb (to_s s1) = (to_s s2).
Proof.
  intro H.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts H.
  unfold to_s.
  simpl_oe_S.
  cbn.
  unfold list_to_binary.
  destruct (xorb (odd x) (hd false (grey_to_binary (map odd xs2)))); reflexivity.
Qed.


Lemma Zero_sgn s1 s2:
  Zero s1 s2 ->
  (to_s s2) = false.
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  unfold to_s.
  simpl_oe_S.
  OE_oe.
  rewrite H5.
  simpl_xor_neg.
  simpl_list_to_binary_0s.
  simpl_oe_S.
  rewrite H6.
  reflexivity.
Qed.

Lemma Overflow_sgn s1 s2:
  Overflow s1 s2 ->
  (to_s s2) = false.
Proof.
  intro Ov.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Ov.
  unfold to_s.
  simpl_oe_S.
  unfold odd.
  OE_oe.
  rewrite H5.
  simpl_xor_neg.
  simpl_list_to_binary_0s.
  simpl_oe_S.
  unfold odd in H6.
  rewrite Bool.negb_true_iff in H6.
  rewrite H6.
  reflexivity.
Qed.

(* trivial properties of the config before Increment *)

Lemma Increment_inc x2 xs y z zs:
  to_s (S x2, xs ++ y :: z :: zs) = true ->
  Even x2 ->
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  (grey_to_binary (map odd (xs ++ y :: z :: zs))) =
  repeat true (S (length xs)) ++ false :: (grey_to_binary (map odd zs)).
Proof.
  intros.
  unfold to_s in H.
  generalize H; clear H.
  simpl_oe_S.
  change (odd x2) with (negb (even x2)).
  OE_oe.
  rewrite H0.
  cbn.
  simpl_list_to_binary_0s.
  rewrite H3.
  simpl_xor_neg.
  destruct (xorb (odd z) (hd false (grey_to_binary (map odd zs)))).
  1: intro X; cbn in X; congruence.
  intro X.
  cbn.
  rewrite repeat_app_S.
  reflexivity.
Qed.

Lemma Increment_dec x2 xs y z zs:
  to_s (S x2, xs ++ y :: z :: zs) = false ->
  Even x2 ->
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  (grey_to_binary (map odd (xs ++ y :: z :: zs))) =
  repeat false (S (length xs)) ++ true :: (grey_to_binary (map odd zs)).
Proof.
  intros.
  unfold to_s in H.
  generalize H; clear H.
  simpl_oe_S.
  change (odd x2) with (negb (even x2)).
  OE_oe.
  rewrite H0.
  cbn.
  simpl_list_to_binary_0s.
  rewrite H3.
  simpl_xor_neg.
  destruct (xorb (odd z) (hd false (grey_to_binary (map odd zs)))).
  2: intro X; cbn in X; congruence.
  intro X.
  cbn.
  rewrite repeat_app_S.
  reflexivity.
Qed.

Lemma Increment_inc_odd x2 y xs:
  to_s (S x2, y :: xs) = true ->
  Odd x2 ->
  (grey_to_binary (map odd (y :: xs))) =
  false :: (grey_to_binary (map odd xs)).
Proof.
  unfold to_s.
  simpl_oe_S.
  intros.
  OE_oe.
  rewrite H0 in H.
  generalize H; clear H.
  simpl_xor_neg.
  cbn.
  congruence.
Qed.

Lemma Increment_dec_odd x2 y xs:
  to_s (S x2, y :: xs) = false ->
  Odd x2 ->
  (grey_to_binary (map odd (y :: xs))) =
  true :: (grey_to_binary (map odd xs)).
Proof.
  unfold to_s.
  simpl_oe_S.
  intros.
  OE_oe.
  rewrite H0 in H.
  generalize H; clear H.
  simpl_xor_neg.
  cbn.
  congruence.
Qed.


Lemma to_s_S x2 xs z zs:
  to_s (x2, xs ++ S z :: zs) =
  negb (to_s (x2, xs ++ z :: zs)).
Proof.
  unfold to_s.
  rewrite list_to_binary_S_hd.
  simpl_xor_neg.
Qed.

Lemma to_s_S' x2 xs y z zs:
  to_s (x2, xs ++ y :: S z :: zs) =
  negb (to_s (x2, xs ++ y :: z :: zs)).
Proof.
  rewrite app_cons_r.
  rewrite to_s_S.
  rewrite <-app_cons_r.
  reflexivity.
Qed.

Lemma to_s_S_odd x2 y zs:
  to_s (x2, S y :: zs) =
  negb (to_s (x2, y :: zs)).
Proof.
  pose proof (to_s_S x2 nil y zs).
  cbn in H. cbn.
  apply H.
Qed.



(* n after Inc/Halve/Zero/Overflow *)

Lemma Increment_n s1 s2:
  Increment s1 s2 ->
  if to_s s1 then
  S (to_n s1) = to_n s2
  else
  to_n s1 = S (to_n s2).
Proof.
  destruct (to_s s1) eqn:E.
  {
    intro I.
    destruct s1 as [x1 xs1].
    destruct s2 as [x2 xs2].
    inverts I.
    - cbn.
      rewrite Increment_inc with (x2:=x2); auto 1.
      rewrite Increment_dec with (x2:=x2); auto 1.
      2: rewrite to_s_S',E; reflexivity.
      rewrite binary_to_nat_S.
      reflexivity.
    - unfold to_n,to_n_binary,snd,list_to_binary.
      rewrite Increment_inc_odd with (x2:=x2); auto 1.
      rewrite Increment_dec_odd with (x2:=x2); auto 1.
      rewrite to_s_S_odd,E. reflexivity.
  }
  {
    intro I.
    destruct s1 as [x1 xs1].
    destruct s2 as [x2 xs2].
    inverts I.
    - cbn.
      rewrite Increment_dec with (x2:=x2); auto 1.
      rewrite Increment_inc with (x2:=x2); auto 1.
      2: rewrite to_s_S',E; reflexivity.
      rewrite binary_to_nat_S.
      reflexivity.
    - unfold to_n,to_n_binary,snd,list_to_binary.
      rewrite Increment_dec_odd with (x2:=x2); auto 1.
      rewrite Increment_inc_odd with (x2:=x2); auto 1.
      rewrite to_s_S_odd,E. reflexivity.
  }
Qed.

Lemma Halve_n s1 s2:
  Halve s1 s2 ->
  div2 (to_n s1) = to_n s2.
Proof.
  intro H.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts H.
  cbn.
  remember (xorb (odd x) (hd false (grey_to_binary (map odd xs2)))) as v1.
  destruct v1; lia.
Qed.

Lemma Zero_n s1 s2:
  Zero s1 s2 ->
  to_n s2 = (2 ^ (to_l s1)) - 1.
Proof.
  unfold to_l.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  unfold to_n_binary,snd,list_to_binary.
  rewrite grey_to_binary_length,map_length,app_length.
  cbn.
  rewrite map_app,map_odd_Even.
  2: auto 1.
  rewrite grey_to_binary_0s.
  OE_oe.
  cbn.
  simpl_oe_S.
  rewrite H6.
  cbn.
  rewrite repeat_app_S.
  rewrite app_cons_r.
  do 2 rewrite binary_to_nat_app_O.
  rewrite binary_to_nat_1s.
  rewrite Nat.add_comm.
  cbn; lia.
Qed.

Lemma Overflow_n s1 s2:
  Overflow s1 s2 ->
  to_n s2 = O.
Proof.
  unfold to_l.
  intro Ov.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Ov.
  cbn.
  simpl_list_to_binary_0s.
  simpl_oe_S.
  OE_oe.
  unfold odd in H6.
  rewrite Bool.negb_true_iff in H6.
  rewrite H6.
  cbn.
  rewrite binary_to_nat_0s_app.
  reflexivity.
Qed.



(* l after Inc/Halve/Zero/Overflow *)

Lemma Increment_len s1 s2:
  Increment s1 s2 ->
  to_l s1 = to_l s2.
Proof.
  intro I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts I.
  - cbn.
    repeat rewrite grey_to_binary_length,map_length,app_length.
    reflexivity.
  - reflexivity.
Qed.

Lemma Halve_len s1 s2:
  Halve s1 s2 ->
  to_l s1 = S (to_l s2).
Proof.
  intro H.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts H.
  cbn.
  reflexivity.
Qed.

Lemma Zero_len s1 s2:
  Zero s1 s2 ->
  to_l s2 = to_l s1 + 2.
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  cbn.
  repeat rewrite grey_to_binary_length,map_length,app_length.
  cbn.
  lia.
Qed.

Lemma Overflow_len s1 s2:
  Overflow s1 s2 ->
  to_l s2 = to_l s1 + 1.
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  cbn.
  repeat rewrite grey_to_binary_length,map_length,app_length.
  cbn.
  lia.
Qed.




(* <n/2^i> *)

Definition divpow2r(n i:nat) :=
  (n+(2^i))/(2^(i+1)).

Lemma divpow2r_inc n i:
  n mod 2^(i+1) = (2^i)-1 ->
  (divpow2r n i)+1 =
  divpow2r (n+1) i.
Proof.
  unfold divpow2r.
  intro H.
  rewrite (Div0.div_mod n (2 ^ (i + 1))).
  rewrite H.
  pose proof (pow2_nez i) as E.
  remember (n / 2 ^ (i + 1)) as v1.
  rewrite (Nat.add_comm i 1).
  change (2^(1+i)) with (2*2^i).
  replace (2 * 2 ^ i * v1 + (2 ^ i - 1) + 1 + 2 ^ i) with
  ((v1 + 1) * (2 * 2 ^ i)) by lia.
  rewrite Nat.div_mul. 2: lia.
  rewrite <-Nat.add_assoc.
  rewrite (Nat.mul_comm (2*2^i) v1).
  rewrite div_add_l. 2: lia.
  rewrite div_small; lia.
Qed.

Lemma divpow2r_eq n i:
  n mod 2^(i+1) <> (2^i)-1 ->
  (divpow2r n i) =
  divpow2r (n+1) i.
Proof.
  unfold divpow2r.
  rewrite (Nat.add_comm i 1).
  intro H.
  rewrite (Div0.div_mod n (2 ^ (1+i))).
  remember (n / 2 ^ (1+i)) as v1.
  remember (n mod 2 ^ (1+i)) as v2.
  rewrite (Nat.mul_comm (2^(1+i)) v1).
  repeat rewrite <-Nat.add_assoc.
  rewrite div_add_l. 2: apply pow2_nez.
  rewrite div_add_l. 2: apply pow2_nez.
  assert (E:v2<2^i-1\/2^i<=v2) by lia.
  destruct E as [E|E].
  - rewrite div_small. 2: cbn; lia.
    rewrite div_small. 2: cbn; lia.
    lia.
  - assert (E0:v2=v2-2^i+2^i) by lia.
    rewrite E0.
    remember (v2-2^i) as v3.
    replace (v3 + 2 ^ i + 2 ^ i) with (1 * (2 * 2 ^ i) + v3) by lia.
    change (2*2^i) with (2^(1+i)).
    rewrite div_add_l. 2: apply pow2_nez.
    eassert (E1:_) by apply (mod_upper_bound n (2^(1+i))),pow2_nez.
    rewrite <-Heqv2 in E1. cbn in E1.
    rewrite div_small. 2: cbn; lia.
    replace (v3 + 2 ^ i + (1 + 2 ^ i)) with (1 * (2 * 2 ^ i) + (v3 + 1)) by lia.
    rewrite div_add_l. 2: apply pow2_nez.
    rewrite div_small. 2: cbn; lia.
    reflexivity.
Qed.



Lemma divpow2r_d_lt i n xs:
  i<n ->
  divpow2r (binary_to_nat ((repeat true n) ++ false :: xs)) i =
  divpow2r (binary_to_nat ((repeat false n) ++ true :: xs)) i.
Proof.
  rewrite <-binary_to_nat_S.
  rewrite binary_to_nat_1s_app.
  cbn.
  remember (binary_to_nat xs) as v1.
  intro H.
  rewrite <- (Nat.add_1_r (v1 * 2 * 2 ^ n + 2 ^ n - 1)).
  apply divpow2r_eq.
  replace (v1 * 2 * 2 ^ n + 2 ^ n - 1) with (2^n*(v1*2)+(2^n-1)) by lia.
  replace (2^n) with (2^(i+1) * 2^(n-(i+1))).
  2: {
    rewrite <-pow_add_r.
    f_equal. lia.
  }
  rewrite <-Div0.add_mod_idemp_l.
  rewrite <-Nat.mul_assoc.
  rewrite mul_comm,Div0.mod_mul.
  cbn.
  assert (E:(n - (i + 1) = 0 \/ (n - (i + 1))>0)%nat) by lia.
  destruct E as [E|E].
  - rewrite E.
    cbn.
    pose proof (pow2_nez (i+1)) as E0.
    pose proof (pow2_nez (i)) as E1.
    rewrite mul_1_r,mod_small. 2: lia.
    rewrite add_comm. cbn. lia.
  - pose proof (pow2_nez (i+1)) as E0.
    pose proof (pow2_nez (i)) as E1.
    pose proof (pow2_nez (n-(i+1))) as E2.
    remember (n-(i+1)) as v2.
    replace (2^v2) with (2^v2-1+1) by lia.
    rewrite mul_add_distr_l.
    rewrite <-add_sub_assoc. 2: lia.
    rewrite <-Div0.add_mod_idemp_l.
    rewrite mul_comm,Div0.mod_mul.
    cbn.
    rewrite mul_1_r,mod_small. 2: lia.
    rewrite add_comm.
    cbn. lia.
Qed.


Lemma divpow2r_d_eq n xs:
  S (divpow2r (binary_to_nat ((repeat true n) ++ false :: xs)) n) =
  divpow2r (binary_to_nat ((repeat false n) ++ true :: xs)) n.
Proof.
  rewrite <-binary_to_nat_S.
  rewrite binary_to_nat_1s_app.
  cbn.
  remember (binary_to_nat xs) as v1.
  rewrite <- (Nat.add_1_r (divpow2r (v1 * 2 * 2 ^ n + 2 ^ n - 1) n)).
  rewrite <- (Nat.add_1_r (v1 * 2 * 2 ^ n + 2 ^ n - 1)).
  apply divpow2r_inc.
  rewrite <-mul_assoc.
  change (2*2^n) with (2^(1+n)).
  rewrite (add_comm n 1).
  pose proof (pow2_nez (n)) as E.
  rewrite <-add_sub_assoc. 2: lia.
  rewrite <-Div0.add_mod_idemp_l.
  rewrite Div0.mod_mul.
  rewrite mod_small. 2: cbn; lia.
  reflexivity.
Qed.

Lemma divpow2r_d_gt i n xs:
  n<i ->
  divpow2r (binary_to_nat ((repeat true n) ++ false :: xs)) i =
  divpow2r (binary_to_nat ((repeat false n) ++ true :: xs)) i.
Proof.
  rewrite <-binary_to_nat_S.
  rewrite binary_to_nat_1s_app.
  cbn.
  remember (binary_to_nat xs) as v1.
  intro H.
  rewrite <- (Nat.add_1_r (v1 * 2 * 2 ^ n + 2 ^ n - 1)).
  apply divpow2r_eq.
  rewrite <-mul_assoc.
  change (2*2^n) with (2^(1+n)).
  pose proof (pow2_nez (n)) as E.
  rewrite <-add_sub_assoc. 2: lia.
  rewrite (add_comm 1 n).
  replace (2^(i+1)) with (2^(n+1)*2^(i-n)).
  2: {
    rewrite <-pow_add_r.
    f_equal. lia.
  }
  rewrite <-Div0.add_mod_idemp_l.
  rewrite mul_comm,Div0.mul_mod_distr_l.
  remember (v1 mod 2 ^ (i - n)) as v2.
  replace (2^(i)) with (2^(n)*2^(i-n)).
  2: {
    rewrite <-pow_add_r.
    f_equal. lia.
  }
  rewrite (add_comm n 1).
  change (2^(1+n)) with (2*2^n).
  remember (2^n) as v3.
  assert (E0:(i-n=0\/i-n>0)%nat) by lia.
  destruct E0 as [E0|E0].
  - rewrite E0.
    change (2^0)%nat with 1%nat.
    rewrite mul_1_r.
    rewrite <-Div0.add_mod_idemp_l.
    rewrite mul_comm,Div0.mod_mul.
    rewrite mod_small; lia.
  - rewrite Div0.add_mul_mod_distr_l. 2: lia.
    intro H0.
    pose proof (pow2_nez (i-n)) as E1.
    assert (E2:2 * v3 * (v2 mod 2 ^ (i - n)) + (v3) = v3 * 2 ^ (i - n)) by lia.
    remember (v2 mod 2 ^ (i - n)) as v4.
    replace (i-n) with (1+(i-n-1)) in E2 by lia.
    change (2^(1+(i-n-1))) with (2*(2^(i-n-1))) in E2.
    replace (2 * v3 * v4 + v3) with (v3*(v4*2+1)) in E2 by lia.
    rewrite mul_cancel_l in E2. 2: auto 1.
    lia.
Qed.

(* one induction step of Proposition 2.2 *)
Lemma Increment_d s1 s2:
  Increment s1 s2 ->
  if to_s s1 then
  forall i,
    nth i (snd s2) O + divpow2r (to_n s1) i =
    nth i (snd s1) O + divpow2r (to_n s2) i
  else
  forall i,
    nth i (snd s1) O + divpow2r (to_n s1) i =
    nth i (snd s2) O + divpow2r (to_n s2) i.
Proof.
  intro I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct (to_s (x1,xs1)) eqn:E.
{
  inverts I.
  - intro i.
    cbn.
    rewrite Increment_inc with (x2:=x2); auto 1.
    rewrite Increment_dec with (x2:=x2); auto 1.
    2: rewrite to_s_S',E; reflexivity.
    remember (S (length xs)) as sl.
    cbn.
    remember (grey_to_binary (map odd zs)) as v1.
    assert (E0:i<sl\/i=sl\/i>sl) by lia.
    assert (E1:length (xs++[y]) = sl). {
      rewrite app_length.
      cbn. lia.
    }
    rewrite app_cons_r.
    symmetry. 
    rewrite app_cons_r.
    destruct E0 as [E0|[E0|E0]].
    + rewrite app_nth1. 2: lia.
      symmetry.
      rewrite app_nth1. 2: lia.
      f_equal.
      apply divpow2r_d_lt,E0.
    + rewrite E0,<-E1.
      do 2 rewrite nth_middle.
      rewrite E1.
      rewrite <-divpow2r_d_eq.
      lia.
    + rewrite app_cons_r.
      symmetry. 
      rewrite app_cons_r.
      assert (E2:length ((xs ++ [y]) ++ [S z])=S sl) by (rewrite app_length; cbn; lia).
      assert (E3:length ((xs ++ [y]) ++ [z])=S sl) by (rewrite app_length; cbn; lia).
      rewrite app_nth2. 2: lia.
      rewrite app_nth2. 2: lia.
      rewrite E2,E3.
      f_equal.
      apply divpow2r_d_gt. lia.
  - intro i.
    unfold to_n,to_n_binary,snd,list_to_binary.
    rewrite Increment_inc_odd with (x2:=x2); auto 1.
    rewrite Increment_dec_odd with (x2:=x2); auto 1.
    2: rewrite to_s_S_odd,E; reflexivity.
    destruct i as [|i].
    + cbn[nth].
      pose proof (divpow2r_d_eq O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H.
      lia.
    + cbn[nth].
      f_equal.
      pose proof (divpow2r_d_gt (S i) O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H. 2: lia.
      reflexivity.
}
{
  inverts I.
  - intro i.
    cbn.
    rewrite Increment_dec with (x2:=x2); auto 1.
    rewrite Increment_inc with (x2:=x2); auto 1.
    2: rewrite to_s_S',E; reflexivity.
    remember (S (length xs)) as sl.
    cbn.
    remember (grey_to_binary (map odd zs)) as v1.
    assert (E0:i<sl\/i=sl\/i>sl) by lia.
    assert (E1:length (xs++[y]) = sl). {
      rewrite app_length.
      cbn. lia.
    }
    rewrite app_cons_r.
    symmetry. 
    rewrite app_cons_r.
    destruct E0 as [E0|[E0|E0]].
    + rewrite app_nth1. 2: lia.
      symmetry.
      rewrite app_nth1. 2: lia.
      f_equal. symmetry.
      apply divpow2r_d_lt,E0.
    + rewrite E0,<-E1.
      do 2 rewrite nth_middle.
      rewrite E1.
      rewrite <-divpow2r_d_eq.
      lia.
    + rewrite app_cons_r.
      symmetry. 
      rewrite app_cons_r.
      assert (E2:length ((xs ++ [y]) ++ [S z])=S sl) by (rewrite app_length; cbn; lia).
      assert (E3:length ((xs ++ [y]) ++ [z])=S sl) by (rewrite app_length; cbn; lia).
      rewrite app_nth2. 2: lia.
      rewrite app_nth2. 2: lia.
      rewrite E2,E3.
      f_equal. symmetry.
      apply divpow2r_d_gt. lia.
  - intro i.
    unfold to_n,to_n_binary,snd,list_to_binary.
    rewrite Increment_dec_odd with (x2:=x2); auto 1.
    rewrite Increment_inc_odd with (x2:=x2); auto 1.
    2: rewrite to_s_S_odd,E; reflexivity.
    destruct i as [|i].
    + cbn[nth].
      pose proof (divpow2r_d_eq O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H.
      lia.
    + cbn[nth].
      f_equal.
      pose proof (divpow2r_d_gt (S i) O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H. 2: lia.
      reflexivity.
}
Qed.



Inductive Increments: nat->(nat*(list nat))->(nat*(list nat))->Prop :=
| Increments_O s: Increments O s s
| Increments_S n s1 s2 s3:
  Increment s1 s2 ->
  Increments n s2 s3 ->
  Increments (S n) s1 s3
.

(* Proposition 2.2 (i>=1) *)
Lemma Increments_d n s1 s2:
  Increments n s1 s2 ->
  if to_s s1 then
  forall i,
    nth i (snd s2) O + divpow2r (to_n s1) i =
    nth i (snd s1) O + divpow2r (to_n s2) i
  else
  forall i,
    nth i (snd s1) O + divpow2r (to_n s1) i =
    nth i (snd s2) O + divpow2r (to_n s2) i.
Proof.
  intro I.
  induction I.
  1: destruct (to_s s); reflexivity.
  pose proof (Increment_d _ _ H) as Hd.
  rewrite <-(Increment_sgn _ _ H) in IHI.
  pose proof (Increment_n _ _ H) as Hn.
  destruct (to_s s2) eqn:E;
    intro i;
    specialize (IHI i);
    specialize (Hd i);
    lia.
Qed.

(* Proposition 2.2 (i=0) *)
Lemma Increments_d0 n s1 s2:
  Increments n s1 s2 ->
  if to_s s1 then
    (fst s1) + (to_n s1) =
    (fst s2) + (to_n s2)
  else
    (fst s2) + (to_n s1) =
    (fst s1) + (to_n s2).
Proof.
  intro I.
  induction I.
  1: destruct (to_s s); reflexivity.
  rewrite <-(Increment_sgn _ _ H) in IHI.
  pose proof (Increment_n _ _ H) as Hn.
  destruct (to_s s2) eqn:E;
    inverts H;
      destruct s4 as [x4 xs4];
      unfold fst;
      unfold fst in IHI;
      lia.
Qed.

Lemma Increment_d0 s1 s2:
  Increment s1 s2 ->
  if to_s s1 then
    (fst s1) + (to_n s1) =
    (fst s2) + (to_n s2)
  else
    (fst s2) + (to_n s1) =
    (fst s1) + (to_n s2).
Proof.
  intros.
  eapply (Increments_d0 1 s1 s2).
  econstructor; eauto 1; constructor.
Qed.




(* some trivial lemmas *)
Lemma Forall_Even_dec xs:
  Forall Even xs \/
  exists xs0 y zs,
    Forall Even xs0 /\
    Odd y /\
    xs = xs0 ++ y :: zs.
Proof.
  induction xs.
  - left. auto 1.
  - destruct IHxs as [IHxs|[xs0 [y [zs [H0 [H1 H2]]]]]].
    + destruct (Even_or_Odd a) as [H|H].
      * left. auto 2.
      * right.
        exists (@nil nat) a xs.
        repeat split; auto 1.
    + right.
      destruct (Even_or_Odd a) as [H|H].
      * exists (a::xs0) y zs.
        repeat split; auto 1.
        -- constructor; auto 1.
        -- cbn. congruence.
      * exists (@nil nat) a xs.
        repeat split; auto 1.
Qed.

Lemma to_n_Even x xs:
  Forall Even xs ->
  to_n (x,xs) = O.
Proof.
  intro H.
  cbn.
  replace ((grey_to_binary (map odd xs))) with (repeat false (length xs)). 2:{
    induction xs.
    1: reflexivity.
    inverts H.
    cbn.
    rewrite <-IHxs; auto 1.
    f_equal.
    unfold odd.
    OE_oe. rewrite H2.
    cbn.
    destruct xs; reflexivity.
  }
  apply binary_to_nat_0s.
Qed.

Lemma to_n_0_binary_0_Even x xs:
  to_n (x, xs) = O ->
  (grey_to_binary (map odd xs)) = repeat false (length xs) /\
  Forall Even xs.
Proof.
  unfold to_n. cbn.
  induction xs.
  1: intro; split; [reflexivity | constructor ].
  intro H.
  cbn in H.
  rewrite eq_add_0 in H.
  destruct H as [X1 X2].
  rewrite eq_mul_0 in X2.
  destruct X2 as [X2|X2]. 2: congruence.
  specialize (IHxs X2).
  destruct IHxs as [I1 I2].
  cbn.
  rewrite I1.
  rewrite I1 in X1.
  assert (E1:hd false (repeat false (length xs)) = false)
    by (destruct xs; reflexivity).
  rewrite E1 in X1.
  destruct (odd a) eqn:E; cbn in X1.
  1: congruence.
  cbn.
  simpl_xor_neg.
  rewrite E1.
  split; auto 1.
  constructor; auto 1.
  unfold odd in E.
  rewrite <-even_spec.
  destruct (even a); cbn in E; congruence.
Qed.

Lemma to_n_0_Even x xs:
  to_n (x, xs) = O ->
  Forall Even xs.
Proof.
  intro H.
  apply (to_n_0_binary_0_Even _ _ H).
Qed.




(* weak pre-cond for Inc/Halve/Zero/Overflow *)
Inductive WF: (nat*(list nat))->Prop :=
| WF_1 x xs y:
  Forall Nonzero xs ->
  WF (x,xs ++ [y])
| WF_2 x xs y zs:
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  Forall Nonzero zs ->
  WF (x,xs ++ y :: zs ++ [O; O])
.

Inductive Step: (nat*(list nat))->(nat*(list nat))->Prop :=
| IncrementStep s1 s2: Increment s1 s2 -> Step s1 s2
| HalveStep s1 s2: Halve s1 s2 -> Step s1 s2
| ZeroStep s1 s2: Zero s1 s2 -> Step s1 s2
| OverflowStep s1 s2: Overflow s1 s2 -> Step s1 s2
.

Definition is_WF_1 (s1:nat*(list nat)):Prop :=
  exists x xs y, Forall Nonzero xs /\ s1 = (x,xs++[y]).

Lemma is_WF_1_00 x xs:
  ~is_WF_1 (x, xs ++ [0; 0]%nat).
Proof.
  intro H.
  destruct H as [x0 [xs0 [y0 [H H0]]]].
  inverts H0.
  rewrite app_cons_r in H3.
  rewrite app_inj_tail_iff in H3.
  destruct H3 as [H3 H4].
  rewrite <-H3 in H.
  rewrite Forall_app in H.
  destruct H as [_ H].
  inverts H.
  lia.
Qed.


Lemma WF_Step s1:
  WF s1 ->
  exists s2, Step s1 s2.
Proof.
  intro Hwf.
  inverts Hwf.
  - destruct x as [|x].
    { destruct xs;
        eexists; apply HalveStep; econstructor. }
    destruct (Even_or_Odd x) as [Ex|Ox].
    {
      destruct (Forall_Even_dec xs) as [H0|[xs0 [y0 [zs [H0 [H1 H2]]]]]].
      - destruct (Even_or_Odd y) as [H1|H1].
        + eexists. apply ZeroStep. econstructor; eauto 1.
        + eexists. apply OverflowStep. econstructor; eauto 1.
      - rewrite H2.
        rewrite <-app_assoc. cbn.
        destruct zs;
          cbn;
          eexists; apply IncrementStep;
          eapply Increment_even; eauto 1;
          rewrite H2 in H;
          rewrite Forall_app in H;
          apply H.
    }
    {
      destruct xs;
        cbn;
        eexists; apply IncrementStep;
        eapply Increment_odd; eauto 1.
    }
  - destruct x as [|x].
    { destruct xs;
        eexists; apply HalveStep; econstructor. }
    destruct (Even_or_Odd x) as [Ex|Ox].
    {
      destruct zs;
        eexists; apply IncrementStep; eapply Increment_even; eauto 1.
    }
    {
      destruct xs; cbn;
        eexists; apply IncrementStep; eapply Increment_odd; eauto 1.
    }
Qed.

Lemma WF_nonempty {x xs}:
  WF (x,xs) ->
  xs<>nil.
Proof.
  intro H.
  inverts H;
    eapply app_nonempty_r; eauto 1.
Qed.


(* more pre-cond to keep post-cond also WF *)
Lemma Increment_inc_precond s1:
  WF s1 ->
  to_s s1 = true ->
  to_n s1 < 2^(to_l s1) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF s2.
Proof.
  intros.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  destruct (Even_or_Odd x1) as [Ex1|Ox1].
  - inverts H.
    + destruct (Forall_Even_dec xs) as [H0'|[xs0 [y0 [zs [H0' [H1' H2']]]]]].
      {
        generalize H0; clear H0.
        unfold to_s.
        simpl_oe_S.
        OE_oe.
        unfold odd. rewrite Ex1.
        cbn.
        simpl_list_to_binary_0s.
        destruct (odd y) eqn:E.
        2: cbn; intro X; congruence.
        intro X. clear X.
        generalize H1; clear H1.
        unfold to_n,to_n_binary,snd.
        simpl_list_to_binary_0s.
        rewrite E. cbn.
        rewrite (grey_to_binary_length),map_length,app_length.
        rewrite repeat_app_S,app_nil_r.
        rewrite binary_to_nat_1s,Nat.add_comm. cbn.
        intro. lia.
      }
      {
        rewrite H2',<-app_assoc. cbn.
        destruct zs; cbn.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + rewrite app_cons_r.
            apply WF_1.
            rewrite <-H2'. apply H4.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + applys_eq WF_1.
            * f_equal.
              do 2 rewrite app_cons_r.
              rewrite app_assoc.
              f_equal.
            * do 2 rewrite <-app_assoc.
              repeat rewrite Forall_app.
              rewrite H2' in H4.
              do 2 rewrite app_cons_r in H4.
              repeat rewrite Forall_app in H4.
              destruct H4 as [[[H4a H4b] H4c] H4d].
              repeat split; auto 1. 
              repeat constructor. lia.
      }
    + destruct zs.
      * eexists.
        split.
        1: eapply Increment_even; eauto 1.
        do 2 rewrite app_cons_r.
        destruct y as [|y]. 1: inverts H7; lia.
        apply WF_1.
        repeat rewrite Forall_app.
        repeat split; auto 1; repeat constructor; lia.
      * eexists.
        split.
        1: cbn; eapply Increment_even; eauto 1.
        applys_eq WF_2.
        1: do 3 f_equal; rewrite app_comm_cons; f_equal.
        all: auto 1.
        inverts H8.
        constructor; auto 1; lia.
  - destruct xs1 as [|x2 xs1].
    1: pose proof (WF_nonempty H); congruence.
    assert (I12:Increment (S x1, x2 :: xs1) (x1, S x2 :: xs1)).
    { eapply Increment_odd; eauto 1. }
    pose proof (Increment_n _ _ I12) as I12n.
    rewrite H0 in I12n.
    eexists.
    split. 1: apply I12.
    destruct x1.
    1: inverts Ox1; lia.
    rewrite Odd_succ in Ox1.
    inverts H.
    {
      destruct xs.
      - cbn in H5.
        inverts H5.
        apply (WF_1 (S x1) []),H4.
      - cbn in H5.
        inverts H5.
        rewrite app_comm_cons.
        apply WF_1.
        inverts H4.
        constructor; auto 1; lia.
    }
    {
      destruct xs.
      - cbn in H4.
        inverts H4.
        rewrite <-Even_succ in H7.
        destruct (Forall_Even_dec zs) as [E|E].
        + assert (Ev:Forall Even (S x2 :: zs ++ [0; 0]%nat)).
          {
            rewrite app_comm_cons.
            rewrite Forall_app.
            split.
            1: constructor; auto 1.
            repeat constructor;
            rewrite <-even_spec; reflexivity.
          }
          rewrite (to_n_Even (S x1) _ Ev) in I12n.
          inverts I12n.
        + destruct E as [xs0 [y [zs0 [E0 [E1 E2]]]]].
          subst zs.
          rewrite app_cons_r in H8.
          repeat rewrite Forall_app in H8.
          destruct H8 as [[H8a H8b] H8c].
          applys_eq (WF_2 (S x1) (S x2::xs0) y zs0).
          1: f_equal; cbn; rewrite <-app_assoc; reflexivity.
          all: try constructor; auto 1; lia.
      - cbn in H4. inverts H4.
        inverts H6. inverts H5.
        rewrite <-Odd_succ in H4.
        applys_eq (WF_2 (S x1) nil (S x2) (xs++y::zs)).
        1: rewrite <-app_assoc; reflexivity.
        all: auto 1.
        rewrite Forall_app. split; auto 1.
        constructor; auto 1.
        intro X. subst. OE_oe. cbn in H7. congruence.
    }
Qed.

Lemma Increment_dec_precond s1:
  WF s1 ->
  to_s s1 = false ->
  to_n s1 > O ->
  fst s1 > O ->
  (to_n s1 = S O -> is_WF_1 s1) ->
  exists s2, Increment s1 s2 /\ WF s2.
Proof.
  intros.
  rename H3 into H3'.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  destruct (Even_or_Odd x1) as [Ex1|Ox1].
  - inverts H.
    + destruct (Forall_Even_dec xs) as [H0'|[xs0 [y0 [zs [H0' [H1' H2']]]]]].
      {
        generalize H0; clear H0.
        unfold to_s.
        simpl_oe_S.
        OE_oe.
        unfold odd. rewrite Ex1.
        cbn.
        simpl_list_to_binary_0s.
        destruct (odd y) eqn:E.
        1: cbn; intro X; congruence.
        intro X. clear X.
        generalize H1; clear H1.
        unfold to_n,to_n_binary,snd.
        simpl_list_to_binary_0s.
        rewrite E. cbn.
        rewrite repeat_app_S,app_nil_r.
        rewrite binary_to_nat_0s.
        intro. lia.
      }
      {
        rewrite H2',<-app_assoc. cbn.
        destruct zs; cbn.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + rewrite app_cons_r.
            apply WF_1.
            rewrite <-H2'. apply H4.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + applys_eq WF_1.
            * f_equal.
              do 2 rewrite app_cons_r.
              rewrite app_assoc.
              f_equal.
            * do 2 rewrite <-app_assoc.
              repeat rewrite Forall_app.
              rewrite H2' in H4.
              do 2 rewrite app_cons_r in H4.
              repeat rewrite Forall_app in H4.
              destruct H4 as [[[H4a H4b] H4c] H4d].
              repeat split; auto 1. 
              repeat constructor. lia.
      }
    + destruct zs.
      * eexists.
        split.
        1: eapply Increment_even; eauto 1.
        do 2 rewrite app_cons_r.
        destruct y as [|y]. 1: inverts H7; lia.
        apply WF_1.
        repeat rewrite Forall_app.
        repeat split; auto 1; repeat constructor; lia.
      * eexists.
        split.
        1: cbn; eapply Increment_even; eauto 1.
        applys_eq WF_2.
        1: do 3 f_equal; rewrite app_comm_cons; f_equal.
        all: auto 1.
        inverts H8.
        constructor; auto 1; lia.
  - destruct xs1 as [|x2 xs1].
    1: pose proof (WF_nonempty H); congruence.
    assert (I12:Increment (S x1, x2 :: xs1) (x1, S x2 :: xs1)).
    { eapply Increment_odd; eauto 1. }
    pose proof (Increment_n _ _ I12) as I12n.
    rewrite H0 in I12n.
    eexists.
    split. 1: apply I12.
    destruct x1.
    1: inverts Ox1; lia.
    rewrite Odd_succ in Ox1.
    inverts H.
    {
      destruct xs.
      - cbn in H5.
        inverts H5.
        apply (WF_1 (S x1) []),H4.
      - cbn in H5.
        inverts H5.
        rewrite app_comm_cons.
        apply WF_1.
        inverts H4.
        constructor; auto 1; lia.
    }
    {
      destruct xs.
      - cbn in H4.
        inverts H4.
        rewrite <-Even_succ in H7.
        destruct (Forall_Even_dec zs) as [E|E].
        + assert (Ev:Forall Even (S x2 :: zs ++ [0; 0]%nat)).
          {
            rewrite app_comm_cons.
            rewrite Forall_app.
            split.
            1: constructor; auto 1.
            repeat constructor;
            rewrite <-even_spec; reflexivity.
          }
          rewrite (to_n_Even (S x1) _ Ev) in I12n.
          specialize (H3' I12n).
          rewrite app_comm_cons in H3'.
          destruct (is_WF_1_00 _ _ H3').
        + destruct E as [xs0 [y [zs0 [E0 [E1 E2]]]]].
          subst zs.
          rewrite app_cons_r in H8.
          repeat rewrite Forall_app in H8.
          destruct H8 as [[H8a H8b] H8c].
          applys_eq (WF_2 (S x1) (S x2::xs0) y zs0).
          1: f_equal; cbn; rewrite <-app_assoc; reflexivity.
          all: try constructor; auto 1; lia.
      - cbn in H4. inverts H4.
        inverts H6. inverts H5.
        rewrite <-Odd_succ in H4.
        applys_eq (WF_2 (S x1) nil (S x2) (xs++y::zs)).
        1: rewrite <-app_assoc; reflexivity.
        all: auto 1.
        rewrite Forall_app. split; auto 1.
        constructor; auto 1.
        intro X. subst. OE_oe. cbn in H7. congruence.
    }
Qed.

Lemma Halve_precond s1:
  WF s1 ->
  fst s1 = O ->
  to_l s1 >= 2 ->
  (to_n s1 = S O -> is_WF_1 s1) ->
  exists s2, Halve s1 s2 /\ WF s2.
Proof.
  destruct s1 as [x xs].
  cbn.
  intros.
  rename H1 into H1'.
  rename H2 into H2'.
  subst.
  inverts H.
  - destruct xs0.
    + cbn.
      eexists.
      split.
      1: econstructor.
      rewrite grey_to_binary_length,map_length in H1'.
      cbn in H1'. lia.
    + cbn.
      eexists.
      split.
      1: econstructor.
      inverts H1.
      apply WF_1; auto 1.
  - destruct xs0.
    + cbn.
      eexists.
      split.
      1: econstructor.
      destruct (Forall_Even_dec zs) as [E|E].
      * generalize H2'; clear H2'.
        cbn.
        simpl_list_to_binary_0s.
        OE_oe.
        rewrite H4.
        cbn.
        rewrite binary_to_nat_0s_app.
        cbn.
        intro X.
        specialize (X (eq_refl _)).
        rewrite app_comm_cons in X.
        destruct (is_WF_1_00 _ _ X).
      * destruct E as [xs0 [y0 [zs0 [E0 [E1 E2]]]]].
        subst zs.
        rewrite Forall_app in H5.
        destruct H5 as [H5a H5b].
        inverts H5b.
        applys_eq WF_2.
        1: rewrite <-app_assoc; cbn; reflexivity.
        all: auto 1.
    + cbn.
      eexists.
      split.
      1: econstructor.
      inverts H2. inverts H3.
      apply WF_2; auto 1.
Qed.


Lemma Zero_precond s1:
  WF s1 ->
  to_s s1 = false ->
  to_n s1 = O ->
  Odd (fst s1) ->
  exists s2, Zero s1 s2 /\ WF s2.
Proof.
  intros.
  inverts H.
  2: {
    pose proof (to_n_0_Even _ _ H1) as Ev.
    rewrite Forall_app in Ev.
    destruct Ev as [_ Ev].
    inverts Ev.
    OE_oe.
    unfold odd in H5.
    rewrite H8 in H5.
    cbn in H5.
    congruence.
  }
  pose proof (to_n_0_Even _ _ H1) as Ev.
  rewrite Forall_app in Ev.
  destruct Ev as [Ev1 Ev2].
  cbn in H2.
  destruct x as [|x]. 1: inverts H2; lia.
  rewrite Odd_succ in H2.
  inverts Ev2.
  eexists.
  split.
  1: constructor; auto 1.
  apply (WF_2 x xs (S y) nil); auto 1.
  rewrite Odd_succ.
  apply H5.
Qed.

Lemma Increments_inc_precond s1 n:
  WF s1 ->
  to_s s1 = true ->
  to_n s1 + n < 2^(to_l s1) ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF s2.
Proof.
  gen s1.
  induction n.
  - intros. eexists.
    split. 1: constructor.
    auto 1.
  - intros.
    eassert (I:_) by
      (eapply Increment_inc_precond; eauto 1; lia).
    destruct I as [s4 [I1 I2]].
    pose proof (Increment_n _ _ I1) as Hn.
    pose proof (Increment_sgn _ _ I1) as Hs.
    pose proof (Increment_len _ _ I1) as Hl.
    pose proof (Increment_d0 _ _ I1) as Hd.
    rewrite H0 in Hn,Hd.
    eassert (X:_). {
      apply IHn.
      - apply I2.
      - rewrite <-Hs. apply H0.
      - pose proof (pow2_nez (to_l s4)).
        rewrite Hl in H1.
        lia.
      - lia.
    }
    destruct X as [s3 [X1 X2]].
    eexists s3.
    split.
    + econstructor; eauto 1.  
    + auto 1.
Qed.

Lemma Increments_dec_precond s1 n:
  WF s1 ->
  to_s s1 = false ->
  to_n s1 >= n ->
  fst s1 >= n ->
  (to_n s1 = n -> is_WF_1 s1) ->
  exists s2, Increments n s1 s2 /\ WF s2.
Proof.
  gen s1.
  induction n.
  - intros. eexists.
    split. 1: constructor.
    auto 1.
  - intros.
    eassert (I:_) by
      (eapply Increment_inc_precond; eauto 1; lia).
    destruct I as [s4 [I1 I2]].
    pose proof (Increment_n _ _ I1) as Hn.
    pose proof (Increment_sgn _ _ I1) as Hs.
    pose proof (Increment_len _ _ I1) as Hl.
    pose proof (Increment_d0 _ _ I1) as Hd.
    rewrite H0 in Hn,Hd.
    eassert (X:_). {
      apply IHn.
      - apply I2.
      - rewrite <-Hs. apply H0.
      - pose proof (pow2_nez (to_l s4)).
        rewrite Hl in H1.
        lia.
      - lia.
    }
    destruct X as [s3 [X1 X2]].
    eexists s3.
    split.
    + econstructor; eauto 1.  
    + auto 1.
Qed.



Inductive embanked: (nat*(list nat))->Prop :=
| embanked_intro n1 n2 n3 s1 s2 s3 s4 s5 s6 s7 s8:
  Zero s1 s2 ->
  Increments n1 s2 s3 ->
  Halve s3 s4 ->
  Increments n2 s4 s5 ->
  Halve s5 s6 ->
  Increments n3 s6 s7 ->
  Zero s7 s8 ->
  embanked s1.

Inductive weakly_embanked: (nat*(list nat))->Prop :=
| weakly_embanked_intro n1 n2 s1 s2 s3 s4 s5 s6:
  Zero s1 s2 ->
  Increments n1 s2 s3 ->
  Halve s3 s4 ->
  Increments n2 s4 s5 ->
  Halve s5 s6 ->
  weakly_embanked s1.














Lemma halt_case : forall x xs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even x ->
  exists c1,
  lower (x :: xs ++ [O; O]) -->*
  c1 /\ halted tm c1.
Proof.
  introv Hxsnz Hxsev Hx.
  destruct (rev xs) eqn:E.
  - destruct x as [|x].
    + eexists. split.
      * follow (goleft_even (O::xs)).
        repeat evstep1.
        unfold lowerL,lowerL'.
        rewrite E.
        cbn. unfold lowerR'. cbn.
        repeat evstep1.
        finish.
      * constructor.
    + eexists. split.
      * follow (goleft_even (S x::xs)).
        repeat evstep1.
        unfold lowerL,lowerL'.
        rewrite E.
        cbn. unfold lowerR'. cbn.
        repeat evstep1.
        finish.
      * constructor.
  - destruct n as [|n].
    + pose proof (Forall_rev Hxsnz) as H.
      rewrite E in H.
      inverts H as H1 H2. congruence.
    + eexists. split.
      * follow (goleft_even (x::xs)).
        repeat evstep1.
        unfold lowerL,lowerL'.
        cbn.
        rewrite <-app_assoc.
        cbn.
        rewrite E.
        cbn.
        repeat evstep1.
        finish.
      * constructor.
Qed.


Lemma base :
  c0 -->*
  lower ([0; 4; 2; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 205 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base' :
  c0 -->*
  lower ([4; 2; 1; 0; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 240 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'1 :
  c0 -->*
  lower ([3; 2; 1; 1; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 274 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'2 :
  c0 -->*
  lower ([2; 3; 1; 1; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 288 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'3 :
  c0 -->*
  lower ([1; 3; 2; 1; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 312 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'5 :
  c0 -->*
  lower ([4; 2; 1; 1]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 355 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'6 :
  c0 -->*
  lower ([3; 2; 1; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 389 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'7 :
  c0 -->*
  lower ([2; 3; 1; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 403 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'8 :
  c0 -->*
  lower ([1; 3; 2; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 427 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'9 :
  c0 -->*
  lower ([0; 4; 2; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 433 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'10 :
  c0 -->*
  lower ([4; 2; 3; 0; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 476 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma halt_case_1 :
  halts tm (lower ([4; 4; 0; 0]%nat)).
Proof.
  unfold halts.
  eexists.
  unfold halts_in.
  eexists.
  split.
  - repeat evstep1.
    constructor.
  - constructor.
Qed.


