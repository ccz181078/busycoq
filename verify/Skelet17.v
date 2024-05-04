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

Definition to_n_binary(s:nat*(list nat)) :=
  list_to_binary (snd s).

Definition to_n(s:nat*(list nat)) :=
  binary_to_nat (to_n_binary s).

Definition to_s(s:nat*(list nat)) :=
  let (x,xs):=s in
  xorb (even x) (hd false (list_to_binary xs)).

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
  rewrite <-even_spec in Ha.
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

Ltac simpl_xor_neg :=
  repeat (rewrite <-Bool.negb_xorb_l || rewrite <-Bool.negb_xorb_r || rewrite Bool.negb_involutive);
  try reflexivity.

Ltac simpl_oe_S :=
  repeat (rewrite odd_succ || rewrite even_succ).

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

Lemma binary_to_nat_1s n:
  binary_to_nat (repeat true n) =
  Nat.pred (pow 2 n).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  assert (2^n <> O) by (apply pow_nonzero; auto 1).
  lia.
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
  (to_s s1) = (to_s s2).
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  unfold to_s.
  simpl_oe_S.
  unfold odd.
  simpl_xor_neg.
  symmetry.
  do 2 rewrite app_cons_r.
  do 2 rewrite list_to_binary_app_O_hd.
  rewrite list_to_binary_app_S_hd.
  simpl_xor_neg.
Qed.

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
  cbn in E.
  unfold list_to_binary in E.
  inverts I.
  - cbn.
    generalize E; clear E.
    repeat rewrite map_app.
    rewrite map_odd_Even; auto 1.
    rewrite <-even_spec in H3.
    rewrite <-odd_spec in H6.
    simpl_oe_S.
    change (odd x2) with (negb (even x2)).
    rewrite H3.
    cbn.
    rewrite H6.
    repeat rewrite grey_to_binary_0s. cbn.
    remember ((grey_to_binary (map odd zs))) as v1.
    remember (hd false v1) as v2.
    simpl_oe_S.
    remember (odd z) as oz.
    unfold odd in Heqoz.
    subst oz.
    simpl_xor_neg.
    rewrite hd_repeat.
    remember (xorb (even z) v2) as v4.
    intro E.
    destruct v4; cbn in E; try congruence.
    cbn.
    repeat rewrite repeat_app_S.
    apply binary_to_nat_S.
  - cbn.
    generalize E; clear E.
    simpl_oe_S.
    rewrite <-odd_spec in H0.
    rewrite H0.
    cbn.
    remember ((grey_to_binary (map odd xs))) as v1.
    remember (odd y) as oy.
    unfold odd in Heqoy.
    subst oy.
    simpl_xor_neg.
    destruct ((xorb (even y) (hd false v1))); cbn; congruence.
}
{
  intros I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  cbn in E.
  unfold list_to_binary in E.
  inverts I.
  - cbn.
    generalize E; clear E.
    repeat rewrite map_app.
    rewrite map_odd_Even; auto 1.
    rewrite <-even_spec in H3.
    rewrite <-odd_spec in H6.
    simpl_oe_S.
    change (odd x2) with (negb (even x2)).
    rewrite H3.
    cbn.
    rewrite H6.
    repeat rewrite grey_to_binary_0s. cbn.
    remember ((grey_to_binary (map odd zs))) as v1.
    remember (hd false v1) as v2.
    simpl_oe_S.
    remember (odd z) as oz.
    unfold odd in Heqoz.
    subst oz.
    simpl_xor_neg.
    rewrite hd_repeat.
    remember (xorb (even z) v2) as v4.
    intro E.
    destruct v4; cbn in E; try congruence.
    cbn.
    repeat rewrite repeat_app_S.
    symmetry.
    apply binary_to_nat_S.
  - cbn.
    generalize E; clear E.
    simpl_oe_S.
    rewrite <-odd_spec in H0.
    rewrite H0.
    cbn.
    remember ((grey_to_binary (map odd xs))) as v1.
    remember (odd y) as oy.
    unfold odd in Heqoy.
    subst oy.
    simpl_xor_neg.
    destruct ((xorb (even y) (hd false v1))); cbn; congruence.
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
  to_n s2 = pred (2 ^ (length (to_n_binary s1))).
Proof.
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
  rewrite <-even_spec in H6.
  cbn.
  simpl_oe_S.
  rewrite H6.
  cbn.
  rewrite repeat_app_S.
  rewrite app_cons_r.
  do 2 rewrite binary_to_nat_app_O.
  rewrite binary_to_nat_1s.
  rewrite Nat.add_comm.
  reflexivity.
Qed.


Lemma Increment_len s1 s2:
  Increment s1 s2 ->
  length (to_n_binary s1) = length (to_n_binary s2).
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
  length (to_n_binary s1) = S (length (to_n_binary s2)).
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
  length (to_n_binary s2) = length (to_n_binary s1) + 2.
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


