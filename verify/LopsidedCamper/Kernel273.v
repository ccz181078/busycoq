(** Kernel check of the c273 orbit: the map on PrimInt63, and the bridge to Rules273's step273 on nat. *)
From Coq Require Import Uint63 PArith ZArith Lia.
From BusyCoq.LopsidedCamper Require Import Rules273.
Local Open Scope Z_scope.

Inductive res := Halt | Go (a b c : int).

(** No per-step bound test: X=a+2b+c grows by at most 6 per step, so one check of X0+6p < 2^61 per job covers a job of p steps. *)
Definition step63 (a b c : int) : res :=
  if (c <? 3*a+3)%uint63 then let k := (c / 3)%uint63 in Go (4*k+2*b+2*(c - 3*k)+1)%uint63 1%uint63 (a-k+1)%uint63
  else if (c <? 3*a+5)%uint63 then Halt else Go (4*a+2*b+4)%uint63 2%uint63 (c-3*a-5)%uint63.

Fixpoint itp (p:positive) (a b c:int) : res :=
  match p with
  | xH => step63 a b c
  | xO q => match itp q a b c with Go a b c => itp q a b c | x => x end
  | xI q => match step63 a b c with Go a b c => match itp q a b c with Go a b c => itp q a b c | x => x end | x => x end
  end.

Notation "[| x |]" := (to_Z x).
Definition D (a b c : int) : nat*nat*nat := (Z.to_nat [|a|], Z.to_nat [|b|], Z.to_nat [|c|]).
Definition X (a b c : int) : Z := [|a|] + 2*[|b|] + [|c|].
Definition L := 2^61.

Lemma bnd x : 0 <= [|x|] < 2^63.
Proof. apply to_Z_bounded. Qed.

Ltac small := rewrite Z.mod_small by (pose proof (bnd _); lia).
Lemma add_s x y: [|x|]+[|y|] < 2^63 -> [|(x+y)%uint63|] = [|x|]+[|y|].
Proof. intros H. rewrite add_spec. change wB with (2^63). apply Z.mod_small. pose proof (bnd x); pose proof (bnd y); lia. Qed.
Lemma mul_s x y: [|x|]*[|y|] < 2^63 -> [|(x*y)%uint63|] = [|x|]*[|y|].
Proof. intros H. rewrite mul_spec. change wB with (2^63). apply Z.mod_small. pose proof (bnd x); pose proof (bnd y); nia. Qed.
Lemma sub_s x y: [|y|] <= [|x|] -> [|(x-y)%uint63|] = [|x|]-[|y|].
Proof. intros H. rewrite sub_spec. change wB with (2^63). apply Z.mod_small. pose proof (bnd x); pose proof (bnd y); lia. Qed.

Lemma nltb (x y : Z) (k : nat): 0 <= x -> 0 <= y -> (Z.to_nat x <? 3 * Z.to_nat y + k)%nat = (x <? 3*y + Z.of_nat k).
Proof.
  intros Hx Hy. destruct (x <? 3*y + Z.of_nat k) eqn:E.
  - apply Z.ltb_lt in E. apply Nat.ltb_lt. lia.
  - apply Z.ltb_ge in E. apply Nat.ltb_ge. lia.
Qed.
Lemma c3: [|3%uint63|] = 3. Proof. reflexivity. Qed.
Lemma c2: [|2%uint63|] = 2. Proof. reflexivity. Qed.
Lemma c4: [|4%uint63|] = 4. Proof. reflexivity. Qed.
Lemma c1: [|1%uint63|] = 1. Proof. reflexivity. Qed.
Lemma c5: [|5%uint63|] = 5. Proof. reflexivity. Qed.

(** lia slows to a crawl when hypotheses mention to_Z of Uint63 expressions; clear those first. *)
(** It assumes the abbreviations A B C for [|a|] [|b|] [|c|] in step63_spec and folds them first. *)
Ltac lz_ A B C := repeat match goal with
           | H : context [to_Z ?x] |- _ =>
               first [ change (to_Z x) with A in H | change (to_Z x) with B in H | change (to_Z x) with C in H | clear H ]
           end; lia.

Lemma step63_spec a b c : X a b c < L ->
  match step63 a b c with
  | Halt => step273 (D a b c) = None
  | Go a' b' c' => step273 (D a b c) = Some (D a' b' c') /\ X a' b' c' <= X a b c + 6
  end.
Proof.
  unfold X, L, D, step63. intros HX.
  pose proof (bnd a) as Ba; pose proof (bnd b) as Bb; pose proof (bnd c) as Bc.
  set (A:=[|a|]) in *; set (B:=[|b|]) in *; set (C:=[|c|]) in *.
  assert (M3a: [|(3*a)%uint63|] = 3*A) by (rewrite mul_s; rewrite c3; [reflexivity|(lz_ A B C)]).
  assert (E3: [|(3*a+3)%uint63|] = 3*A+3) by (rewrite add_s; rewrite ?M3a, ?c3; (lz_ A B C)).
  assert (E5: [|(3*a+5)%uint63|] = 3*A+5) by (rewrite add_s; rewrite ?M3a, ?c5; (lz_ A B C)).
  cbn [step273]. rewrite (nltb C A 3 (proj1 Bc) (proj1 Ba)), (nltb C A 5 (proj1 Bc) (proj1 Ba)). cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct (c <? 3*a+3)%uint63 eqn:L1.
  - apply ltb_spec in L1. rewrite E3 in L1. replace (C <? 3*A+3) with true by (symmetry; apply Z.ltb_lt; (lz_ A B C)).
    set (k:=(c/3)%uint63).
    assert (Ek: [|k|] = C / 3) by (unfold k; rewrite div_spec; rewrite c3; reflexivity).
    pose proof (Z.mod_pos_bound C 3 ltac:((lz_ A B C))) as Mb. pose proof (Z.div_mod C 3 ltac:((lz_ A B C))) as Dm.
    assert (Hk: 0 <= C/3 <= A) by (lz_ A B C).
    assert (M3k: [|(3*k)%uint63|] = 3*(C/3)) by (rewrite mul_s; rewrite ?c3, ?Ek; (lz_ A B C)).
    assert (Er: [|(c - 3*k)%uint63|] = C mod 3) by (rewrite sub_s; rewrite ?M3k; (lz_ A B C)).
    assert (M4k: [|(4*k)%uint63|] = 4*(C/3)) by (rewrite mul_s; rewrite ?c4, ?Ek; (lz_ A B C)).
    assert (M2b: [|(2*b)%uint63|] = 2*B) by (rewrite mul_s; rewrite ?c2; (lz_ A B C)).
    assert (M2r: [|(2*(c-3*k))%uint63|] = 2*(C mod 3)) by (rewrite mul_s; rewrite ?c2, ?Er; (lz_ A B C)).
    assert (S1: [|(4*k+2*b)%uint63|] = 4*(C/3)+2*B) by (rewrite add_s; rewrite ?M4k, ?M2b; (lz_ A B C)).
    assert (S2: [|(4*k+2*b+2*(c-3*k))%uint63|] = 4*(C/3)+2*B+2*(C mod 3)) by (rewrite add_s; rewrite ?S1, ?M2r; (lz_ A B C)).
    assert (Ea: [|(4*k+2*b+2*(c-3*k)+1)%uint63|] = 4*(C/3)+2*B+2*(C mod 3)+1) by (rewrite add_s; rewrite ?S2, ?c1; (lz_ A B C)).
    assert (Sk: [|(a-k)%uint63|] = A - C/3) by (rewrite sub_s; rewrite ?Ek; (lz_ A B C)).
    assert (Ec: [|(a-k+1)%uint63|] = A - C/3 + 1) by (rewrite add_s; rewrite ?Sk, ?c1; (lz_ A B C)).
    destruct (dm3 (Z.to_nat C)) as [Hd Hm].
    assert (Zd: Z.of_nat (d3 (Z.to_nat C)) = C/3 /\ Z.of_nat (m3 (Z.to_nat C)) = C mod 3) by (lz_ A B C).
    split.
    + unfold D. rewrite Ea, Ec, c1. f_equal. f_equal; [f_equal | ]; (lz_ A B C).
    + rewrite Ea, Ec, c1. (lz_ A B C).
  - assert (L1': ~ (C < 3*A+3)) by (intro H; rewrite <- E3 in H; apply ltb_spec in H; rewrite H in L1; discriminate).
    replace (C <? 3*A+3) with false by (symmetry; apply Z.ltb_ge; (lz_ A B C)).
    destruct (c <? 3*a+5)%uint63 eqn:L2.
    + apply ltb_spec in L2. rewrite E5 in L2. replace (C <? 3*A+5) with true by (symmetry; apply Z.ltb_lt; (lz_ A B C)). reflexivity.
    + assert (L2': ~ (C < 3*A+5)) by (intro H; rewrite <- E5 in H; apply ltb_spec in H; rewrite H in L2; discriminate).
      replace (C <? 3*A+5) with false by (symmetry; apply Z.ltb_ge; (lz_ A B C)).
      assert (M4a: [|(4*a)%uint63|] = 4*A) by (rewrite mul_s; rewrite ?c4; (lz_ A B C)).
      assert (M2b: [|(2*b)%uint63|] = 2*B) by (rewrite mul_s; rewrite ?c2; (lz_ A B C)).
      assert (S1: [|(4*a+2*b)%uint63|] = 4*A+2*B) by (rewrite add_s; rewrite ?M4a, ?M2b; (lz_ A B C)).
      assert (Ea: [|(4*a+2*b+4)%uint63|] = 4*A+2*B+4) by (rewrite add_s; rewrite ?S1, ?c4; (lz_ A B C)).
      assert (Sc: [|(c-3*a)%uint63|] = C-3*A) by (rewrite sub_s; rewrite ?M3a; (lz_ A B C)).
      assert (Ec: [|(c-3*a-5)%uint63|] = C-3*A-5) by (rewrite sub_s; rewrite ?Sc, ?c5; (lz_ A B C)).
      split.
      * unfold D. rewrite Ea, Ec, c2. f_equal. f_equal; [f_equal | ]; (lz_ A B C).
      * rewrite Ea, Ec, c2. (lz_ A B C).
Qed.

(** Iterating: p map steps of itp agree with iter (Pos.to_nat p) of step273, while X0 + 6p < 2^61. *)
Lemma iter_add n m s: iter (n + m) s = match iter n s with Some s' => iter m s' | None => None end.
Proof.
  revert s. induction n; intros s; [reflexivity| ].
  cbn [Nat.add iter]. destruct (step273 s) as [s'| ]; [apply IHn|reflexivity].
Qed.

Lemma itp_spec p : forall a b c, X a b c + 6 * Zpos p < L ->
  match itp p a b c with
  | Halt => iter (Pos.to_nat p) (D a b c) = None
  | Go a' b' c' => iter (Pos.to_nat p) (D a b c) = Some (D a' b' c') /\ X a' b' c' <= X a b c + 6 * Zpos p
  end.
Proof.
  induction p as [q IH|q IH| ]; intros a b c HB.
  - (* xI: one step, then twice q *)
    cbn [itp]. pose proof (step63_spec a b c ltac:(lia)) as H1.
    replace (Pos.to_nat q~1) with (1 + (Pos.to_nat q + Pos.to_nat q))%nat by lia.
    rewrite iter_add. cbn [iter]. destruct (step63 a b c) as [ | a1 b1 c1].
    + rewrite H1. reflexivity.
    + destruct H1 as [H1 X1]. rewrite H1. cbn [iter].
      pose proof (IH a1 b1 c1 ltac:(lia)) as H2. rewrite iter_add.
      destruct (itp q a1 b1 c1) as [ | a2 b2 c2].
      * rewrite H2. reflexivity.
      * destruct H2 as [H2 X2]. rewrite H2.
        pose proof (IH a2 b2 c2 ltac:(lia)) as H3.
        destruct (itp q a2 b2 c2) as [ | a3 b3 c3]; [exact H3| ]. destruct H3 as [H3 X3]. split; [exact H3|lia].
  - cbn [itp]. replace (Pos.to_nat q~0) with (Pos.to_nat q + Pos.to_nat q)%nat by lia.
    rewrite iter_add.
    pose proof (IH a b c ltac:(lia)) as H2.
    destruct (itp q a b c) as [ | a2 b2 c2].
    + rewrite H2. reflexivity.
    + destruct H2 as [H2 X2]. rewrite H2.
      pose proof (IH a2 b2 c2 ltac:(lia)) as H3.
      destruct (itp q a2 b2 c2) as [ | a3 b3 c3]; [exact H3| ]. destruct H3 as [H3 X3]. split; [exact H3|lia].
  - cbn [itp]. pose proof (step63_spec a b c ltac:(lia)) as H1.
    replace (Pos.to_nat 1) with 1%nat by reflexivity. cbn [iter].
    destruct (step63 a b c) as [ | a1 b1 c1].
    + rewrite H1. reflexivity.
    + destruct H1 as [H1 X1]. rewrite H1. split; [reflexivity|lia].
Qed.

(** One job: from checkpoint (a,b,c), p map steps reach (a',b',c'). The bound is checked by computation. *)
Definition job_ok (p:positive) (a b c a' b' c' : int) : Prop :=
  (X a b c + 6 * Zpos p <? L)%Z = true /\ itp p a b c = Go a' b' c'.
Definition job_halt (p:positive) (a b c : int) : Prop :=
  (X a b c + 6 * Zpos p <? L)%Z = true /\ itp p a b c = Halt.

Lemma job_ok_iter p a b c a' b' c': job_ok p a b c a' b' c' -> iter (Pos.to_nat p) (D a b c) = Some (D a' b' c').
Proof.
  intros [HB HI]. apply Z.ltb_lt in HB. pose proof (itp_spec p a b c HB) as H. rewrite HI in H. apply H.
Qed.
Lemma job_halt_iter p a b c: job_halt p a b c -> iter (Pos.to_nat p) (D a b c) = None.
Proof.
  intros [HB HI]. apply Z.ltb_lt in HB. pose proof (itp_spec p a b c HB) as H. rewrite HI in H. exact H.
Qed.

(** A chain of jobs from A(0,1,0) ending in a halt gives the machine's halt. *)
Inductive chain : int -> int -> int -> Prop :=
  | ch_halt p a b c : job_halt p a b c -> chain a b c
  | ch_step p a b c a' b' c' : job_ok p a b c a' b' c' -> chain a' b' c' -> chain a b c.

Lemma chain_iter a b c: chain a b c -> exists N, iter N (D a b c) = None.
Proof.
  induction 1 as [p a b c H|p a b c a' b' c' H _ [N IH]].
  - exists (Pos.to_nat p). apply job_halt_iter. exact H.
  - exists (Pos.to_nat p + N)%nat. rewrite iter_add. rewrite (job_ok_iter _ _ _ _ _ _ _ H). exact IH.
Qed.

(** The start A(0,1,0) as ints, so files that cannot import Uint63 can name it. *)
Definition i0 : int := 0%uint63.
Definition i1 : int := 1%uint63.
