(* SOC23.TM51: nonhalting by a generated-block queue invariant.
   Standalone; only BusyCoq and standard-library dependencies.
   The finite entry is checked using binary integers, not expanded tapes.
   See SOC51_BLOCK_PROOF.md for the mathematical argument. *)
From BusyCoq Require Import Individual62 Helper SimplTape ES_v3 BinaryCounter_v2.
From Coq Require Import String List Arith NArith ZifyNat Lia.
Import ListNotations.

Module TM51.
Open Scope sym_scope.
(* SOC51_TwoRuns *)
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC1LB_1LE1RD_1RB0RC_1RA0LE_1RD---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].

(* These exits do not inspect the left context. *)
Lemma D_generic_even4 b l:
  l {{D}}> [1]^^(1+b*2) *> [0;0;0] *> [1]^^4 *> 0inf -->*
  l <* <[0;1]^^b <* [1]^^5 <{{B}} [1;1;1;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma D_generic_even6 b c l:
  l {{D}}> [1]^^(3+b*2) *> [0;0;0] *> [1]^^(6+c*2) *> 0inf -->*
  l <* <[0;1]^^b <* <[1] <* ld0^^(4+c)
    <* <[1;0;1;1;1] {{C}}> 0inf.
Proof. es' b c & l. Qed.

Lemma D_generic_odd3 b c l:
  l {{D}}> [1]^^(3+b*2) *> [0;0;0] *> [1]^^(3+c*2) *> 0inf -->*
  l <* <[0;1]^^b <* <[1] <* ld0^^(2+c)
    <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b c & l. Qed.

(* A local all-one counter with a 101 separator, not a blank boundary. *)
Lemma local_counter_overflow n l r:
  l <* <[1;0;1] <* ld1^^n <{{B}} [1;1;1;0;0] *> r -->*
  l <* ld1 <* ld0^^(1+n) <* ld1^^2 {{D}}> r.
Proof. es' n & l r. Qed.

Lemma D_return h l r:
  l <* ld0^^2 <* ld1^^2 {{D}}> [1;0;0]^^h *> [0;0;0] *> r -->*
  l <* ld0 <{{B}} [1;1;1;0;0] *> [0;0;0]^^(1+h) *> [1] *> r.
Proof. es' h & l r. Qed.

Lemma D_even_even4 b c l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0] *> [1]^^(4+c*2) *> 0inf -->*
  l <* <[0;1]^^b <* <[1;1;0;1] <* ld1 <* ld0^^(1+c)
    <* <[1;0;1;1;1] {{C}}> 0inf.
Proof. es' b c & l. Qed.

Lemma D_even_odd5 b c l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0] *> [1]^^(5+c*2) *> 0inf -->*
  l <* <[0;1]^^b <* <[1;1;0;1] <* ld1 <* ld0^^(1+c)
    <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b c & l. Qed.

Lemma D_odd_two b l:
  l {{D}}> [1]^^(1+b*2) *> [0;0;0;1;1] *> 0inf -->*
  l <* <[0;1]^^b <* [1]^^3 <{{B}} [1;1;1;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma D_even_two b l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0;1;1] *> 0inf -->*
  l <* <[0;1]^^b <* <[1;1;0;1] <* ld0 <{{B}} [1;1;1;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma D_one_ee a c l:
  l <* ld0 <* [1]^^(4+a*2) {{D}}> [1;0;0;0] *> [1]^^(2+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(3+a+c) <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof.
  destruct c as [|[|c]].
  - es' a & l.
  - es' a & l.
  - change (S (S c)) with (2+c).
    replace (2+(2+c)*2) with (6+c*2) by lia.
    replace (3+a+(2+c)) with (5+c+a) by lia. es' a c & l.
Qed.

Lemma D_one_eo a c l:
  l <* ld0 <* [1]^^(4+a*2) {{D}}> [1;0;0;0] *> [1]^^(1+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(3+a+c) <* <[1;0;1;1;1] {{C}}> 0inf.
Proof.
  destruct c as [|[|c]].
  - es' a & l.
  - es' a & l.
  - change (S (S c)) with (2+c).
    replace (1+(2+c)*2) with (5+c*2) by lia.
    replace (3+a+(2+c)) with (5+c+a) by lia. es' a c & l.
Qed.

Lemma D_one_oe a c l:
  l <* ld0 <* [1]^^(5+a*2) {{D}}> [1;0;0;0] *> [1]^^(2+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(4+a+c) <* <[1;0;1;1;1] {{C}}> 0inf.
Proof.
  destruct c as [|[|c]].
  - es' a & l.
  - es' a & l.
  - change (S (S c)) with (2+c).
    replace (2+(2+c)*2) with (6+c*2) by lia.
    replace (4+a+(2+c)) with (6+c+a) by lia. es' a c & l.
Qed.

Lemma D_one_oo a c l:
  l <* ld0 <* [1]^^(5+a*2) {{D}}> [1;0;0;0] *> [1]^^(1+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(3+a+c) <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof.
  destruct c as [|[|c]].
  - es' a & l.
  - es' a & l.
  - change (S (S c)) with (2+c).
    replace (1+(2+c)*2) with (5+c*2) by lia.
    replace (3+a+(2+c)) with (5+c+a) by lia. es' a c & l.
Qed.

Lemma D_two_ee a c l:
  l <* ld0 <* [1]^^(4+a*2) {{D}}> [1;1;0;0;0] *> [1]^^(4+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(1+a) <* <[1;0;1] <* ld1 <* ld0^^(1+c)
    <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' a c & l. Qed.

Lemma D_two_eo a c l:
  l <* ld0 <* [1]^^(4+a*2) {{D}}> [1;1;0;0;0] *> [1]^^(5+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(1+a) <* <[1;0;1] <* ld1 <* ld0^^(2+c)
    <* <[1;0;1;1;1] {{C}}> 0inf.
Proof. es' a c & l. Qed.

Lemma D_two_oe a c l:
  l <* ld0 <* [1]^^(5+a*2) {{D}}> [1;1;0;0;0] *> [1]^^(4+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(2+a) <* <[1;0;1] <* ld1 <* ld0^^(1+c)
    <* <[1;0;1;1;1] {{C}}> 0inf.
Proof. es' a c & l. Qed.

Lemma D_two_oo a c l:
  l <* ld0 <* [1]^^(5+a*2) {{D}}> [1;1;0;0;0] *> [1]^^(5+c*2) *> 0inf -->*
  l <* ld1 <* ld0^^(2+a) <* <[1;0;1] <* ld1 <* ld0^^(1+c)
    <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' a c & l. Qed.

Lemma D_empty_two l:
  l <* <[1] {{D}}> [1;1] *> 0inf -->*
  l <* <[1;0;1;1;1] {{C}}> 0inf.
Proof. es' & l. Qed.

Lemma D_empty_three l:
  l <* <[1] {{D}}> [1;1;1] *> 0inf -->*
  l <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' & l. Qed.

Lemma D_empty_even4 b l:
  l {{D}}> [1]^^(4+b*2) *> 0inf -->*
  l <* <[0;1]^^b <* <[0] <* <[1;0;1;1;1] {{C}}> 0inf.
Proof. es' b & l. Qed.

Lemma D_empty_odd5 b l:
  l {{D}}> [1]^^(5+b*2) *> 0inf -->*
  l <* <[0;1]^^b <* <[0] <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma D_empty_one n l:
  l <* ld0 <* [1]^^(4+n*3) {{D}}> [1] *> 0inf -->*
  l <{{B}} [1;1;1;0;0] *> [0;0;0]^^(2+n) *> [1;0;0] *> 0inf.
Proof. es' n & l. Qed.

(* Extra high digit remaining after an over-capacity excursion. *)
Lemma D_tail_oo b c l:
  l {{D}}> [1]^^(3+b*2) *> [0;0;0] *> [1]^^(1+c*2) *> [0;0;0;1;0;0] *> 0inf -->*
  l <* <[0;1]^^b <* <[1] <* ld0^^(1+c) <* ld1 <* ld0
    <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b c & l. Qed.

Lemma D_tail_oe b c l:
  l {{D}}> [1]^^(3+b*2) *> [0;0;0] *> [1]^^(2+c*2) *> [0;0;0;1;0;0] *> 0inf -->*
  l <* <[0;1]^^b <* <[1] <* ld0^^(1+c) <* ld1
    <{{B}} [1;1;1;0;0] *> [0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. es' b c & l. Qed.

Lemma D_tail_eo b c l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0] *> [1]^^(3+c*2) *> [0;0;0;1;0;0] *> 0inf -->*
  l <* <[0;1]^^b <* <[1;1;0;1] <* ld1 <* ld0^^c <* ld1 <* ld0
    <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b c & l. Qed.

Lemma D_tail_ee b c l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0] *> [1]^^(4+c*2) *> [0;0;0;1;0;0] *> 0inf -->*
  l <* <[0;1]^^b <* <[1;1;0;1] <* ld1 <* ld0^^c <* ld1
    <{{B}} [1;1;1;0;0] *> [0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. es' b c & l. Qed.


Lemma D_odd_one b l:
  l {{D}}> [1]^^(3+b*2) *> [0;0;0;1] *> 0inf -->*
  l <* <[0;1]^^b <* <[1] <* ld0 <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma D_even_one b l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0;1] *> 0inf -->*
  l <* <[0;1]^^b <* <[1] <{{B}} [1;1;1;0;0] *> [0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. es' b & l. Qed.

Lemma D_even_three b l:
  l {{D}}> [1]^^(4+b*2) *> [0;0;0;1;1;1] *> 0inf -->*
  l <* <[0;1]^^b <* <[1;1;0;1] <* ld1 <{{B}} [1;1;1;0;0] *> [0;0;0;1;0;0] *> 0inf.
Proof. es' b & l. Qed.












(* Arithmetic obligations for the generated-block argument. These do not
   yet connect the block predicate to c0 or constitute a nonhalt theorem. *)
Definition separated t u := t*8+9 <= u \/ u*8 <= t+5.




Lemma generated_main_bound old current r tail gap:
  16 <= old -> old*125 <= current*8 -> r <= old -> tail <= old+8 ->
  current*3 <= gap*2+4 -> (r+tail)*8+9 <= gap.
Proof. lia. Qed.

(* SOC51_Counter *)
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation ldh := (0inf <* <[1]).
Notation z := [0;0;0].
Notation d := [1;0;0].
Notation "l <| r" := (l <{{B}} [1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;0;1;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es' n & l r. Qed.
Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+ l <| z^^n *> [1] *> r.
Proof. es' n & l r. Qed.
Lemma LOv r n m:
  ldh <* ld1^^n <| d^^m *> z *> r -->+
  ldh <* ld0^^n <| z^^(m+1) *> [1] *> r.
Proof. es' n m & r. Qed.

(* Finite, low-bit-first digits.  The semantic lists need never be evaluated
   for the very large widths reached by the accelerated execution. *)
Inductive Digits : nat -> nat -> list Sym -> Prop :=
| digits_nil: Digits 0 0 []
| digits_zero n v w: Digits n v w -> Digits (1+n) (v*2) (z++w)
| digits_one n v w: Digits n v w -> Digits (1+n) (v*2+1) (d++w).

Lemma digits_bound n v w: Digits n v w -> v<2^n.
Proof. intros H; induction H; cbn [Nat.add Nat.pow]; lia. Qed.
Lemma digits_zeros n: Digits n 0 (z^^n).
Proof. induction n; cbn [lpow]; [constructor|apply (digits_zero _ 0); assumption]. Qed.
Lemma digits_ones n: Digits n (2^n-1) (d^^n).
Proof.
  induction n; [constructor|].
  replace (2^S n-1) with ((2^n-1)*2+1) by
    (pose proof (Nat.pow_nonzero 2 n); cbn [Nat.pow]; lia).
  apply digits_one; assumption.
Qed.
Lemma digits_full n v w: Digits n v w -> v=2^n-1 -> w=d^^n.
Proof.
  intros H; induction H; intros Hv; [reflexivity| |].
  - pose proof (Nat.pow_nonzero 2 n); cbn [Nat.add Nat.pow] in Hv; lia.
  - cbn [Nat.add lpow]. f_equal. apply IHDigits.
    pose proof (Nat.pow_nonzero 2 n); cbn [Nat.add Nat.pow] in Hv; lia.
Qed.

Lemma digits_low_zero n v w: Digits n v w -> 1+v<2^n ->
  exists i j m s, n=i+1+j /\ v=(m*2+1)*2^i-1 /\
    w=d^^i++z++s /\ Digits j m s.
Proof.
  intros H; induction H; intros Hv; [cbn in Hv; lia| |].
  - exists 0%nat, n, v, w; cbn; repeat split; auto; lia.
  - destruct IHDigits as [i [j [m [s [Hn [Hx [Hw Hs]]]]]]];
      [cbn [Nat.add Nat.pow] in Hv; lia|].
    exists (1+i), j, m, s. repeat split; auto; try lia.
    + pose proof (Nat.pow_nonzero 2 i); cbn [Nat.add Nat.pow]; nia.
    + cbn [Nat.add lpow]; rewrite Hw; reflexivity.
Qed.

Lemma digits_low_zeros i j m s: Digits j m s ->
  Digits (i+j) (m*2^i) (z^^i++s).
Proof.
  intros H; induction i.
  - cbn; replace (m*1) with m by lia; assumption.
  - replace (m*2^S i) with ((m*2^i)*2) by (cbn [Nat.pow]; nia).
    apply digits_zero; assumption.
Qed.

Lemma digits_increment n v w: Digits n v w -> 1+v<2^n ->
  exists w', Digits n (1+v) w' /\ forall l r,
    l |> w *> r -->+ l <| w' *> r.
Proof.
  intros H Hv. destruct (digits_low_zero _ _ _ H Hv)
    as [i [j [m [s [Hn [Hx [Hw Hs]]]]]]].
  exists (z^^i++d++s). split.
  - subst n v. replace (1+((m*2+1)*2^i-1)) with ((m*2+1)*2^i) by
      (pose proof (Nat.pow_nonzero 2 i); nia).
    replace (i+1+j) with (i+(1+j)) by lia.
    apply digits_low_zeros, digits_one; assumption.
  - intros l r; rewrite Hw. simpl_tape. apply RInc.
Qed.

Lemma marked_carry l r p i:
  l |> d^^p *> [1] *> d^^i *> z *> r -->+
  l <| z^^(1+p+i) *> [1] *> r.
Proof. es' p i & l r. Qed.

(* The marker replaces a single virtual one-bit.  When j>0, the high
   finite word retains its top zero; when j=0 the marker is at the top. *)
Inductive Marked : nat -> nat -> list Sym -> Prop :=
| marked p j u m a b: Digits p u a -> Digits j m b ->
    (j=0%nat \/ m<2^(j-1)) ->
    Marked (p+j) ((m*2+1)*2^p+u) (a++[1]++b).

Lemma high_zero_tail i j m v: v=(m*2+1)*2^i-1 -> v<2^(i+j) ->
  j=0%nat \/ m<2^(j-1).
Proof.
  intros Hv Htop. destruct j; [auto|right].
  replace (S j-1) with j by lia. rewrite Nat.pow_add_r in Htop.
  pose proof (Nat.pow_nonzero 2 i). cbn [Nat.pow] in Htop. nia.
Qed.

Lemma marked_high p j u m: u<2^p -> m<2^(j-1) -> 0<j ->
  (m*2+1)*2^p+u < 2^(p+j).
Proof.
  intros Hu Hm Hj. destruct j; [lia|].
  replace (S j-1) with j in Hm by lia. rewrite Nat.pow_add_r.
  pose proof (Nat.pow_nonzero 2 p). cbn [Nat.pow]. nia.
Qed.

Lemma marked_finished J V w: Marked J V w -> 2^J<=V ->
  exists u a, V=2^J+u /\ Digits J u a /\ w=a++[1].
Proof.
  intros H HV. destruct H as [p j u m a b Ha Hb Htop].
  destruct j as [|j].
  - inversion Hb; subst. exists u, a. rewrite Nat.add_0_r, app_nil_r.
    repeat split; auto; lia.
  - pose proof (digits_bound _ _ _ Ha).
    assert (m<2^(S j-1)) by lia.
    pose proof (marked_high _ _ _ _ H H0 ltac:(lia)); lia.
Qed.

Lemma marked_increment J V w: Marked J V w -> 1+V<2^(J+1) ->
  exists w', Marked J (1+V) w' /\ forall l r,
    l |> w *> r -->+ l <| w' *> r.
Proof.
  intros H Hv. destruct H as [p j u m a b Ha Hb Htop].
  pose proof (digits_bound _ _ _ Ha) as Hu.
  destruct (lt_dec (1+u) (2^p)) as [Hlow|Hfull].
  - destruct (digits_increment _ _ _ Ha Hlow) as [a' [Ha' Hr]].
    exists (a'++[1]++b). split.
    + replace (1+((m*2+1)*2^p+u)) with ((m*2+1)*2^p+(1+u)) by lia.
      constructor; assumption.
    + intros l r; simpl_tape; apply Hr.
  - assert (Huf:u=2^p-1) by lia.
    assert (Hj:0<j).
    { destruct j; [|lia].
      pose proof (digits_bound _ _ _ Hb) as Hm.
      assert (m=0%nat) by (cbn [Nat.pow] in Hm; lia). subst m.
      rewrite Nat.add_0_r, pow2_S in Hv. cbn [Nat.mul Nat.add] in Hv. lia. }
    assert (Hm_inc:1+m<2^j).
    { destruct j; [lia|].
      replace (S j-1) with j in Htop by lia.
      pose proof (Nat.pow_nonzero 2 j); cbn [Nat.pow]; lia. }
    destruct (digits_low_zero _ _ _ Hb Hm_inc)
      as [i [k [v [s [Hjk [Hm [Hword Hs]]]]]]].
    assert (Hnewtop:k=0%nat \/ v<2^(k-1)).
    { eapply high_zero_tail; [exact Hm|].
      replace (i+k) with (j-1) by lia. lia. }
    assert (Hm1:m+1=(v*2+1)*2^i) by
      (pose proof (Nat.pow_nonzero 2 i); nia).
    exists (z^^(p+i+1)++[1]++s). split.
    + replace (p+j) with ((p+i+1)+k) by lia.
      replace (1+((m*2+1)*2^p+u)) with ((v*2+1)*2^(p+i+1)+0) by
        (repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
      constructor; auto using digits_zeros.
    + intros l r. rewrite (digits_full _ _ _ Ha Huf), Hword.
      repeat rewrite Str_app_assoc.
      replace (p+i+1) with (1+p+i) by lia.
      apply marked_carry.
Qed.

Definition LC len k l := BinDec ld0 ld1 len k l.
Lemma LC_Inc len k l r: 1+k<2^len ->
  LC len (1+k) l <| r -->+ LC len k l |> r.
Proof. unfold LC; intros; apply LBinDec_spec; auto using LInc. Qed.

Lemma marked_calls len k c J V w l r:
  k+c<2^len -> V+c<2^(J+1) -> Marked J V w ->
  exists w', Marked J (V+c) w' /\
    LC len (k+c) l <| w *> r -->* LC len k l <| w' *> r.
Proof.
  revert V w. induction c; intros V w Hk HV Hm.
  - exists w. rewrite !Nat.add_0_r. split; [assumption|apply evstep_refl].
  - destruct (marked_increment _ _ _ Hm ltac:(lia)) as [w1 [Hm1 Hr]].
    destruct (IHc (1+V) w1 ltac:(lia) ltac:(lia) Hm1) as [w' [Hm' Hrun]].
    exists w'; split; [applys_eq Hm'; flia|].
    replace (k+S c) with (1+(k+c)) by lia.
    eapply evstep_trans; [apply progress_evstep, LC_Inc; lia|].
    eapply evstep_trans; [apply progress_evstep, Hr|exact Hrun].
Qed.

Lemma marked_to_digits len k J V w l r:
  k<2^len -> 2^J<=V+k<2^(J+1) -> Marked J V w ->
  exists a, Digits J (V+k-2^J) a /\
    LC len k l <| w *> r -->* LC len 0 l <| a *> [1] *> r.
Proof.
  intros Hk [Hlo Hhi] Hm.
  destruct (marked_calls len 0 k J V w l r Hk Hhi Hm) as [w' [Hm' Hrun]].
  destruct (marked_finished _ _ _ Hm' Hlo) as [u [a [HV [Ha Hw]]]].
  exists a; split.
  - replace (V+k-2^J) with u by lia; assumption.
  - rewrite Hw in Hrun; repeat rewrite Str_app_assoc in Hrun; exact Hrun.
Qed.

Lemma below_half J n: n*2+1<2^J -> n<2^(J-1).
Proof.
  destruct J; cbn [Nat.pow]; intros; [lia|].
  replace (S J-1) with J by lia. lia.
Qed.

Lemma left_overflow_marked len J n w r:
  Digits J n w -> n*2+1<2^J ->
  exists w', Marked J (n*2+2) w' /\
    LC len 0 ldh <| w *> r -->+ LC len (2^len-1) ldh <| w' *> r.
Proof.
  intros Hd Hn. destruct (digits_low_zero _ _ _ Hd ltac:(lia))
    as [i [j [m [s [HJ [Hn0 [Hw Hs]]]]]]].
  assert (Htop:j=0%nat \/ m<2^(j-1)).
  { eapply high_zero_tail; [exact Hn0|].
    replace (i+j) with (J-1) by lia. apply below_half; assumption. }
  exists (z^^(i+1)++[1]++s). split.
  - replace J with ((i+1)+j) by lia.
    replace (n*2+2) with ((m*2+1)*2^(i+1)+0) by
      (rewrite pow2_S; pose proof (Nat.pow_nonzero 2 i); nia).
    constructor; auto using digits_zeros.
  - unfold LC; rewrite BinDec_O, BinDec_full, Hw.
    repeat rewrite Str_app_assoc. apply LOv.
Qed.

Lemma frame_zero L n w r: Digits L n w -> n*2+1<2^L ->
  exists a, Digits L (n*2+1) a /\
    LC L 0 ldh <| w *> r -->+ LC L 0 ldh <| a *> [1] *> r.
Proof.
  intros Hd Hn. destruct (left_overflow_marked L _ _ _ r Hd Hn) as [w' [Hm Hstart]].
  assert (Hcap:2^L-1<2^L) by (pose proof (Nat.pow_nonzero 2 L); lia).
  assert (HV:2^L<=n*2+2+(2^L-1)<2^(L+1)) by (rewrite pow2_S; lia).
  destruct (marked_to_digits L (2^L-1) L (n*2+2) w' ldh r Hcap HV Hm)
    as [a [Ha Hrun]].
  exists a; split.
  - replace (n*2+2+(2^L-1)-2^L) with (n*2+1) in Ha by lia; assumption.
  - eapply progress_evstep_trans; eauto.
Qed.

Lemma digits_append_zero n v w: Digits n v w -> Digits (n+1) v (w++z).
Proof.
  intros H; induction H.
  - apply (digits_zero 0 0 []), digits_nil.
  - apply digits_zero; assumption.
  - apply digits_one; assumption.
Qed.

Lemma digits_top_zero n v w: Digits n v w -> forall j, n=1+j -> v<2^j ->
  exists a, Digits j v a /\ w=a++z.
Proof.
  intros H; induction H; intros j Hn Hv; [lia| |].
  - destruct j as [|j].
    + assert (n=0%nat) by lia; subst n. inversion H; subst.
      exists ([]:list Sym); split; constructor.
    + destruct (IHDigits j ltac:(lia) ltac:(cbn [Nat.pow] in Hv; lia)) as [a [Ha Hw]].
      exists (z++a); split; [apply digits_zero; assumption|rewrite Hw; reflexivity].
  - destruct j as [|j]; [cbn [Nat.pow] in Hv; lia|].
    destruct (IHDigits j ltac:(lia) ltac:(cbn [Nat.pow] in Hv; lia)) as [a [Ha Hw]].
    exists (d++a); split; [apply digits_one; assumption|rewrite Hw; reflexivity].
Qed.

Lemma frame_one L n w r: Digits L n w -> 2^L<=n*2+1 ->
  exists a, Digits L (n*2+1-2^L) a /\
    LC L 0 ldh <| w *> z *> r -->+ LC L 0 ldh <| a *> z *> [1] *> r.
Proof.
  intros Hd Hn. pose proof (digits_bound _ _ _ Hd) as Hbound.
  assert (Hupper:n*2+1<2^(L+1)) by (rewrite pow2_S; lia).
  destruct (left_overflow_marked L (L+1) n (w++z) r (digits_append_zero _ _ _ Hd) Hupper)
    as [w' [Hm Hstart]].
  assert (Hcap:2^L-1<2^L) by (pose proof (Nat.pow_nonzero 2 L); lia).
  assert (HV:2^(L+1)<=n*2+2+(2^L-1)<2^(L+1+1)) by (rewrite !pow2_S; lia).
  destruct (marked_to_digits L (2^L-1) (L+1) (n*2+2) w' ldh r Hcap HV Hm)
    as [a [Ha Hrun]].
  replace (n*2+2+(2^L-1)-2^(L+1)) with (n*2+1-2^L) in Ha by (rewrite pow2_S; lia).
  destruct (digits_top_zero _ _ _ Ha L ltac:(lia) ltac:(lia)) as [b [Hb Hab]].
  exists b; split; [assumption|].
  rewrite Str_app_assoc in Hstart. rewrite Hab, Str_app_assoc in Hrun.
  eapply progress_evstep_trans; eauto.
Qed.

Lemma R_finish_even l r a b:
  l |> d^^(a*2) *> [1] *> d^^b *> r -->+
  l <* ld0 <* [1]^^(4+b*3+a*6) {{D}}> r.
Proof. es' a b & l r. Qed.
Lemma R_finish_odd l r a b:
  l |> d^^(1+a*2) *> [1] *> d^^b *> r -->+
  l <* ld0 <* [1]^^(7+b*3+a*6) {{D}}> r.
Proof. es' a b & l r. Qed.

Lemma R_finish l r J b:
  l |> d^^J *> [1] *> d^^b *> r -->+
  l <* ld0 <* [1]^^(4+(J+b)*3) {{D}}> r.
Proof.
  destruct (divmod2 J) as [n a Hn|n a Hn]; subst n.
  - applys_eq (R_finish_even l r a b); flia.
  - replace (a*2+1) with (1+a*2) by lia.
    applys_eq (R_finish_odd l r a b); flia.
Qed.

Lemma full_to_D n r:
  LC n 0 ldh <| d^^n *> r -->+
  LC n (2^n-1) ldh <* ld0 <* [1]^^(4+n*3) {{D}}> r.
Proof. unfold LC; rewrite BinDec_O, BinDec_full; es' n & r. Qed.

Lemma high_prefix_to_D J k n w r: Digits J n w -> n*2+1<2^J -> 0<k ->
  LC (J+k) 0 ldh <| w *> d^^k *> r -->+
  LC (J+k) (2^(J+k)-2^(J+1)+n*2+1) ldh <* ld0 <* [1]^^(4+(J+k)*3) {{D}}> r.
Proof.
  intros Hd Hn Hk.
  assert (HP:2^(J+1)<=2^(J+k)) by (apply Nat.pow_le_mono_r; lia).
  pose proof (Nat.pow_nonzero 2 J) as Hpow.
  set (V:=n*2+2).
  set (c:=2^(J+1)-1-V).
  set (K:=2^(J+k)-2^(J+1)+n*2+1).
  assert (Hvalue:V+c=2^(J+1)-1) by (unfold V,c; rewrite pow2_S; lia).
  assert (Hbudget:K+1+c=2^(J+k)-1) by (unfold K,c,V; rewrite pow2_S in *; lia).
  destruct (left_overflow_marked (J+k) J n w (d^^k *> r) Hd Hn) as [s [Hm Hstart]].
  destruct (marked_calls (J+k) (K+1) c J V s ldh (d^^k *> r)
    ltac:(lia) ltac:(rewrite Hvalue; pose proof (Nat.pow_nonzero 2 (J+1)); lia) Hm)
    as [s' [Hm' Hrun]].
  destruct (marked_finished _ _ _ Hm' ltac:(rewrite Hvalue, pow2_S; lia))
    as [u [a [Hu [Ha Hs]]]].
  assert (Huf:u=2^J-1) by (rewrite Hvalue, pow2_S in Hu; lia).
  rewrite (digits_full _ _ _ Ha Huf) in Hs.
  rewrite Hbudget in Hrun.
  eapply progress_evstep_trans; [exact Hstart|].
  eapply evstep_trans; [exact Hrun|].
  rewrite Hs; repeat rewrite Str_app_assoc.
  replace (K+1) with (1+K) by lia.
  eapply evstep_trans; [apply progress_evstep, LC_Inc; lia|].
  apply progress_evstep, R_finish.
Qed.

Lemma digits_high_zero n v w: Digits n v w -> v<2^n-1 ->
  exists j u a k, n=j+k /\ 1<=j /\ u*2+1<2^j /\ w=a++d^^k /\
    Digits j u a /\ v=2^n-2^j+u.
Proof.
  intros H; induction H; intros Hv; [cbn in Hv; lia| |].
  - destruct (lt_dec v (2^n-1)) as [Hsmall|Hfull].
    + destruct (IHDigits Hsmall) as [j [u [a [k [Hn [Hj [Hu [Hw [Ha Heq]]]]]]]]].
      assert (HP:2^j<=2^n) by (apply Nat.pow_le_mono_r; lia).
      exists (1+j), (u*2), (z++a), k.
      repeat split; auto using digits_zero; cbn [Nat.add Nat.pow]; try lia.
      rewrite Hw; reflexivity.
    + pose proof (digits_bound _ _ _ H) as Hbound.
      assert (Heq:v=2^n-1) by lia.
      exists 1%nat, 0%nat, z, n.
      repeat split; cbn [Nat.add Nat.pow]; try lia.
      * rewrite (digits_full _ _ _ H Heq); reflexivity.
      * apply (digits_zero 0 0 []), digits_nil.
  - destruct IHDigits as [j [u [a [k [Hn [Hj [Hu [Hw [Ha Heq]]]]]]]]];
      [cbn [Nat.add Nat.pow] in Hv; lia|].
    assert (HP:2^j<=2^n) by (apply Nat.pow_le_mono_r; lia).
    exists (1+j), (u*2+1), (d++a), k.
    repeat split; auto using digits_one; cbn [Nat.add Nat.pow]; try lia.
    rewrite Hw; reflexivity.
Qed.

Lemma frame_to_D L n w r: Digits L n w -> 2^L<=n*2+1 ->
  LC L 0 ldh <| w *> r -->+
  LC L (n*2+1-2^L) ldh <* ld0 <* [1]^^(4+L*3) {{D}}> r.
Proof.
  intros Hd Hn. pose proof (digits_bound _ _ _ Hd) as Hbound.
  destruct (lt_dec n (2^L-1)) as [Hsmall|Hfull].
  - destruct (digits_high_zero _ _ _ Hd Hsmall)
      as [J [u [a [k [HL [HJ [Hu [Hw [Ha Heq]]]]]]]]].
    assert (Hk:0<k).
    { destruct k; [|lia]. rewrite Nat.add_0_r in HL; subst L; lia. }
    assert (HP:2^(J+1)<=2^L) by (apply Nat.pow_le_mono_r; lia).
    replace (n*2+1-2^L) with (2^L-2^(J+1)+u*2+1) by (rewrite pow2_S in *; lia).
    rewrite Hw, Str_app_assoc, HL. apply high_prefix_to_D; assumption.
  - assert (Heq:n=2^L-1) by lia.
    rewrite (digits_full _ _ _ Hd Heq).
    replace (n*2+1-2^L) with (2^L-1) by lia. apply full_to_D.
Qed.

Definition seed_word := d++z++d++z++d^^3.
Lemma init: c0 -->* LC 7 0 ldh <| seed_word *> 0inf.
Proof. unfold LC; rewrite BinDec_O; unfold seed_word; esx. Qed.

(* SOC51_Return *)
Definition RC n := BinInc d n.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H|].

Lemma digits_RC n v w: Digits n v w -> forall m,
  w *> RC m = RC (v+2^n*m).
Proof.
  intros H; induction H; intros m; unfold RC in *.
  - cbn; f_equal; lia.
  - rewrite Str_app_assoc, IHDigits.
    change z with (BinaryCounter.d0 d). rewrite <-BinInc_mul2.
    f_equal; cbn [Nat.add Nat.pow]; nia.
  - rewrite Str_app_assoc, IHDigits, <-BinInc_mul2add1.
    f_equal; cbn [Nat.add Nat.pow]; nia.
Qed.

Lemma digits_exist n v: v<2^n -> exists w, Digits n v w.
Proof.
  revert v; induction n; intros v Hv.
  - exists ([]:list Sym). replace v with 0%nat by (cbn in Hv; lia); constructor.
  - divmod2_cases v;
      destruct (IHn n' ltac:(cbn [Nat.pow] in Hv; lia)) as [w Hw].
    + exists (z++w); apply digits_zero; assumption.
    + exists (d++w); apply digits_one; assumption.
Qed.

Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec. intros; simpl_tape; apply RInc. Qed.

Lemma RC_calls len k c v l: k+c<2^len ->
  LC len (k+c) l <| RC v -->* LC len k l <| RC (v+c).
Proof.
  revert v; induction c; intros v Hk.
  - rewrite !Nat.add_0_r; finish.
  - replace (k+S c) with (1+(k+c)) by lia.
    follow_inc LC_Inc; [lia|]. follow_inc RC_Inc.
    follow IHc; [lia|]. applys_eq evstep_refl; flia.
Qed.

Lemma RC_finish len k v l: k<2^len ->
  LC len k l |> RC v -->* LC len 0 l <| RC (k+v+1).
Proof.
  intros Hk. follow_inc RC_Inc. follow (RC_calls len 0 k).
  applys_eq evstep_refl; flia.
Qed.

(* Overflow at a local 101 boundary, not at the infinite blank boundary. *)
Lemma local_marked m i l r:
  l <* <[1;0;1] <* ld1^^(1+m) <| d^^i *> z *> r -->*
  l <* ld1 <* ld0^^(1+m) <| z^^(1+i) *> [1] *> r.
Proof.
  follow local_counter_overflow.
  replace (1+(1+m)) with (2+m) by lia.
  rewrite <-lpow_add'. simpl_tape.
  follow D_return. finish.
Qed.

Lemma local_overflow_marked m J v w l r:
  0<m -> Digits J v w -> v*2+1<2^J ->
  exists w', Marked J (v*2+2) w' /\
    LC m 0 (l <* <[1;0;1]) <| w *> r -->*
    LC m (2^m-1) (l <* ld1) <| w' *> r.
Proof.
  intros Hm Hd Hv. destruct (digits_low_zero _ _ _ Hd ltac:(lia))
    as [i [j [u [s [HJ [Hval [Hw Hs]]]]]]].
  assert (Htop:j=0%nat \/ u<2^(j-1)).
  { eapply high_zero_tail; [exact Hval|].
    replace (i+j) with (J-1) by lia. apply below_half; assumption. }
  exists (z^^(i+1)++[1]++s). split.
  - replace J with ((i+1)+j) by lia.
    replace (v*2+2) with ((u*2+1)*2^(i+1)+0) by
      (rewrite pow2_S; pose proof (Nat.pow_nonzero 2 i); nia).
    constructor; auto using digits_zeros.
  - unfold LC; rewrite BinDec_O, BinDec_full, Hw.
    repeat rewrite Str_app_assoc. destruct m; [lia|].
    replace (i+1) with (1+i) by lia. apply local_marked.
Qed.


(* Stop at the first point where the marker is ordinary, then use RC_calls.
   There is no upper bound on the final right value V+k. *)
Lemma marked_drain len k J V w l:
  k<2^len -> V<2^(J+1) -> 2^J<=V+k -> Marked J V w ->
  LC len k l <| w *> 0inf -->* LC len 0 l <| RC (V+k).
Proof.
  intros Hk HV Hlo Hm. set (c:=2^J-V).
  assert (Hc:c<=k) by (unfold c; lia).
  assert (Hvc:2^J<=V+c<2^(J+1)) by
    (unfold c; rewrite pow2_S in *; lia).
  destruct (marked_calls len (k-c) c J V w l 0inf ltac:(lia) ltac:(lia) Hm)
    as [a [Ha Hrun]].
  destruct (marked_finished _ _ _ Ha ltac:(lia)) as [u [b [Hu [Hb Hab]]]].
  rewrite Hab in Hrun; repeat rewrite Str_app_assoc in Hrun.
  change (LC len (k-c+c) l <| w *> 0inf -->*
    LC len (k-c) l <| b *> [1] *> 0inf) in Hrun.
  replace ([1] *> 0inf) with (RC 1) in Hrun by
    (change ([1;0;0] *> 0inf=[1] *> 0inf); cbn;
      repeat rewrite <-(const_unfold _ 0); reflexivity).
  rewrite (digits_RC _ _ _ Hb) in Hrun.
  replace (k-c+c) with k in Hrun by lia.
  follow Hrun. follow (RC_calls len 0 (k-c)); [lia|].
  applys_eq evstep_refl; flia.
Qed.

Lemma local_overflow_RC m J v l:
  0<m -> v*2+1<2^J ->
  exists w, Marked J (v*2+2) w /\
    LC m 0 (l <* <[1;0;1]) <| RC v -->*
    LC m (2^m-1) (l <* ld1) <| w *> 0inf.
Proof.
  intros Hm Hv. destruct (digits_exist J v ltac:(lia)) as [a Ha].
  destruct (local_overflow_marked m J v a l 0inf Hm Ha Hv) as [w [Hw Hrun]].
  exists w; split; [assumption|].
  change (a *> 0inf) with (a *> RC 0) in Hrun.
  rewrite (digits_RC _ _ _ Ha) in Hrun.
  applys_eq Hrun; flia.
Qed.

Lemma LC_YX len k n l: k<2^len ->
  LC len k l <* ld1 <* ld0^^n =
  LC (len+1+n) ((k*2+1)*2^n-1) l.
Proof.
  intros Hk. unfold LC. rewrite BinDec_mulpow2sub1; [reflexivity|].
  rewrite Nat.pow_add_r, pow2_S. pose proof (Nat.pow_nonzero 2 n); nia.
Qed.

Lemma YX_left len k n v l: k<2^len ->
  LC len k l <* ld1 <* ld0^^n <| RC v -->*
  LC (len+1+n) 0 l <| RC ((k*2+1)*2^n-1+v).
Proof.
  intros Hk. rewrite LC_YX by assumption.
  follow (RC_calls (len+1+n) 0 ((k*2+1)*2^n-1)).
  - rewrite Nat.pow_add_r, pow2_S. pose proof (Nat.pow_nonzero 2 n); nia.
  - applys_eq evstep_refl; flia.
Qed.

Lemma YX_right len k n v l: k<2^len ->
  LC len k l <* ld1 <* ld0^^n |> RC v -->*
  LC (len+1+n) 0 l <| RC ((k*2+1)*2^n+v).
Proof.
  intros Hk. rewrite LC_YX by assumption.
  eapply evstep_trans; [apply RC_finish|].
  - rewrite Nat.pow_add_r, pow2_S. pose proof (Nat.pow_nonzero 2 n); nia.
  - replace ((k*2+1)*2^n-1+v+1) with ((k*2+1)*2^n+v) by
      (pose proof (Nat.pow_nonzero 2 n); nia). finish.
Qed.

Lemma local_finish m v l: 0<m -> v*2+1<2^m ->
  LC m 0 (l <* <[1;0;1]) <| RC v -->*
  LC m 0 (l <* ld1) <| RC (2^m+v*2+1).
Proof.
  intros Hm Hv. destruct (local_overflow_RC m m v l Hm Hv) as [w [Hw Hrun]].
  follow Hrun. eapply evstep_trans;
    [eapply marked_drain with (J:=m) (V:=v*2+2)|].
  - lia.
  - rewrite pow2_S; lia.
  - lia.
  - assumption.
  - applys_eq evstep_refl; flia.
Qed.

Lemma yx_bound len k n: k<2^len -> (k*2+1)*2^n-1<2^(len+1+n).
Proof.
  intros Hk. rewrite Nat.pow_add_r, pow2_S.
  pose proof (Nat.pow_nonzero 2 n); nia.
Qed.

Lemma LC_compose len k n v l: k<2^len -> v<2^n ->
  LC n v (LC len k l) = LC (len+n) (k*2^n+v) l.
Proof.
  intros Hk; revert v; induction n; intros v Hv.
  - replace v with 0%nat by (cbn in Hv; lia).
    unfold LC; rewrite BinDec_O; cbn [lpow Nat.pow].
    rewrite Nat.add_0_r, Nat.mul_1_r, Nat.add_0_r; reflexivity.
  - divmod2_cases v; unfold LC in *;
      replace (S n) with (n+1) in * by lia;
      replace (len+(n+1)) with ((len+n)+1) by lia.
    + replace (k*2^(n+1)+n'*2) with ((k*2^n+n')*2) by (rewrite pow2_S; nia).
      rewrite !BinDec_mul2; try (rewrite !pow2_S, ?Nat.pow_add_r in *; nia).
      rewrite IHn; [reflexivity|rewrite pow2_S in Hv; lia].
    + replace (k*2^(n+1)+(n'*2+1)) with ((k*2^n+n')*2+1) by (rewrite pow2_S; nia).
      rewrite !BinDec_mul2add1; try (rewrite !pow2_S, ?Nat.pow_add_r in *; nia).
      rewrite IHn; [reflexivity|rewrite pow2_S in Hv; lia].
Qed.

Lemma local_outer_finish len k m v l:
  k<2^len -> 0<m -> v*2+1<2^m ->
  LC m 0 (LC len k l <* <[1;0;1]) <| RC v -->*
  LC (len+1+m) 0 l <| RC (k*2^(m+1)+2^m+v*2+1).
Proof.
  intros Hk Hm Hv. follow local_finish.
  replace (LC len k l <* ld1) with (LC (len+1) (k*2) l) by
    (unfold LC; rewrite BinDec_mul2; [reflexivity|rewrite pow2_S; lia]).
  rewrite LC_compose; [|rewrite pow2_S; lia|lia].
  follow (RC_calls (len+1+m) 0 (k*2*2^m+0)).
  - rewrite Nat.pow_add_r, pow2_S. pose proof (Nat.pow_nonzero 2 m); nia.
  - rewrite pow2_S. applys_eq evstep_refl; flia.
Qed.

(* A local counter can be drained even when its own budget cannot erase
   the marker: the preceding Y X^a contributes enough global budget. *)
Lemma local_after_YX len k a m v l:
  k<2^len -> 1<=a -> 0<m -> v*2+1<2^(m+1) ->
  LC m 0 (LC len k l <* ld1 <* ld0^^a <* <[1;0;1]) <| RC v -->*
  LC (len+1+a+1+m) 0 l <|
    RC ((((k*2+1)*2^a-1)*2+1)*2^m-1+v*2+2).
Proof.
  intros Hk Ha Hm Hv.
  destruct (local_overflow_RC m (m+1) v (LC len k l <* ld1 <* ld0^^a) Hm Hv)
    as [w [Hw Hrun]].
  follow Hrun. unfold LC; rewrite BinDec_full; fold LC.
  change (LC len k l <* ld1 <* ld0^^a <* ld1 <* ld0^^m <| w *> 0inf -->*
    LC (len+1+a+1+m) 0 l <|
      RC ((((k*2+1)*2^a-1)*2+1)*2^m-1+v*2+2)).
  rewrite LC_YX by assumption.
  rewrite LC_YX by (apply yx_bound; assumption).
  eapply evstep_trans;
    [eapply marked_drain with (J:=m+1) (V:=v*2+2)|].
  - apply yx_bound, yx_bound; assumption.
  - rewrite pow2_S; lia.
  - assert (2<=2^a) by
      (change (2^1<=2^a); apply Nat.pow_le_mono_r; lia).
    rewrite pow2_S. pose proof (Nat.pow_nonzero 2 m); nia.
  - assumption.
  - applys_eq evstep_refl; flia.
Qed.

Lemma local_YX n l:
  l <* ld1 <* ld0^^n = LC (1+n) (2^n-1) l.
Proof.
  pose proof (LC_YX 0 0 n l ltac:(cbn; lia)) as H.
  unfold LC at 1 in H; rewrite BinDec_O in H.
  cbn [lpow Nat.add Nat.mul] in H. rewrite Nat.add_0_r in H; exact H.
Qed.

Lemma two_local_finish len k a c e l:
  k<2^len -> 1<=a -> 1<=c -> e<=1 ->
  LC (1+c) 0 (LC len k l <* ld1 <* ld0^^a <* <[1;0;1]) <| RC (2^c+e) -->*
  LC (len+a+c+3) 0 l <| RC ((k*2+1)*2^(a+c+2)+(e*2+1)).
Proof.
  intros Hk Ha Hc He.
  assert (Hpow:2<=2^c) by
    (change (2^1<=2^c); apply Nat.pow_le_mono_r; lia).
  eapply evstep_trans; [apply local_after_YX; try assumption; try lia|].
  - replace (1+c+1) with ((c+1)+1) by lia. rewrite !pow2_S; lia.
  - replace ((((k*2+1)*2^a-1)*2+1)*2^(1+c)-1+(2^c+e)*2+2)
      with ((k*2+1)*2^(a+c+2)+e*2+1) by
      (replace (1+c) with (c+1) by lia;
        rewrite !Nat.pow_add_r; cbn [Nat.pow];
        pose proof (Nat.pow_nonzero 2 a); nia).
    applys_eq evstep_refl; flia.
Qed.

Lemma two_YX_right len k a c l: k<2^len -> 1<=a -> 1<=c ->
  LC len k l <* ld1 <* ld0^^a <* <[1;0;1] <* ld1 <* ld0^^c |> RC 0 -->*
  LC (len+a+c+3) 0 l <| RC ((k*2+1)*2^(a+c+2)+1).
Proof.
  intros Hk Ha Hc. rewrite local_YX.
  eapply evstep_trans; [apply RC_finish|].
  - pose proof (Nat.pow_nonzero 2 c); cbn [Nat.add Nat.pow]; lia.
  - replace (2^c-1+0+1) with (2^c+0) by
      (pose proof (Nat.pow_nonzero 2 c); lia).
    apply (two_local_finish len k a c 0); auto.
Qed.

Lemma two_YX_left len k a c l: k<2^len -> 1<=a -> 1<=c ->
  LC len k l <* ld1 <* ld0^^a <* <[1;0;1] <* ld1 <* ld0^^c <| RC 2 -->*
  LC (len+a+c+3) 0 l <| RC ((k*2+1)*2^(a+c+2)+3).
Proof.
  intros Hk Ha Hc. rewrite local_YX.
  follow (RC_calls (1+c) 0 (2^c-1)).
  - pose proof (Nat.pow_nonzero 2 c); cbn [Nat.add Nat.pow]; lia.
  - replace (2+(2^c-1)) with (2^c+1) by
      (pose proof (Nat.pow_nonzero 2 c); lia).
    apply (two_local_finish len k a c 1); auto.
Qed.

Lemma D_one_ee_finish len k a c l: k<2^len ->
  LC len k l <* ld0 <* [1]^^(4+a*2) {{D}}>
    [1;0;0;0] *> [1]^^(2+c*2) *> 0inf -->*
  LC (len+1+(3+a+c)) 0 l <| RC ((k*2+1)*2^(3+a+c)+1).
Proof.
  intros Hk. follow D_one_ee.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  follow YX_left. applys_eq evstep_refl;
    pose proof (Nat.pow_nonzero 2 (3+a+c)); flia.
Qed.

Lemma D_one_eo_finish len k a c l: k<2^len ->
  LC len k l <* ld0 <* [1]^^(4+a*2) {{D}}>
    [1;0;0;0] *> [1]^^(1+c*2) *> 0inf -->*
  LC (len+1+(3+a+c)) 0 l <| RC ((k*2+1)*2^(3+a+c)).
Proof.
  intros Hk. follow D_one_eo. change 0inf with (RC 0).
  follow YX_right. applys_eq evstep_refl; flia.
Qed.

Lemma D_one_oe_finish len k a c l: k<2^len ->
  LC len k l <* ld0 <* [1]^^(5+a*2) {{D}}>
    [1;0;0;0] *> [1]^^(2+c*2) *> 0inf -->*
  LC (len+1+(4+a+c)) 0 l <| RC ((k*2+1)*2^(4+a+c)).
Proof.
  intros Hk. follow D_one_oe. change 0inf with (RC 0).
  follow YX_right. applys_eq evstep_refl; flia.
Qed.

Lemma D_one_oo_finish len k a c l: k<2^len ->
  LC len k l <* ld0 <* [1]^^(5+a*2) {{D}}>
    [1;0;0;0] *> [1]^^(1+c*2) *> 0inf -->*
  LC (len+1+(3+a+c)) 0 l <| RC ((k*2+1)*2^(3+a+c)+1).
Proof.
  intros Hk. follow D_one_oo.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  follow YX_left. applys_eq evstep_refl;
    pose proof (Nat.pow_nonzero 2 (3+a+c)); flia.
Qed.

(* All positive lengths of the final one-run, both parities of len. *)
Lemma D_one_finish len k t s e l:
  k<2^len -> 0<t -> e<=1 -> len*3+t+7=s*2+e ->
  LC len k l <* ld0 <* [1]^^(4+len*3) {{D}}>
    [1;0;0;0] *> [1]^^t *> 0inf -->*
  LC (len+s) 0 l <| RC (k*2^s+2^(s-1)+e).
Proof.
  intros Hk Ht He Hs. divmod2_cases len; rename n' into a.
  - divmod2_cases t; rename n' into c.
    + destruct c; [lia|].
      replace (4+a*2*3) with (4+(a*3)*2) by lia.
      replace (S c*2) with (2+c*2) by lia.
      follow D_one_ee_finish.
      assert (e=1%nat /\ s=4+a*3+c) as [-> ->] by lia.
      replace (4+a*3+c-1) with (3+a*3+c) by lia.
      replace (4+a*3+c) with ((3+a*3+c)+1) by lia.
      rewrite pow2_S. applys_eq evstep_refl; flia.
    + replace (4+a*2*3) with (4+(a*3)*2) by lia.
      replace (c*2+1) with (1+c*2) by lia.
      follow D_one_eo_finish.
      assert (e=0%nat /\ s=4+a*3+c) as [-> ->] by lia.
      replace (4+a*3+c-1) with (3+a*3+c) by lia.
      replace (4+a*3+c) with ((3+a*3+c)+1) by lia.
      rewrite pow2_S. applys_eq evstep_refl; flia.
  - divmod2_cases t; rename n' into c.
    + destruct c; [lia|].
      replace (4+(a*2+1)*3) with (5+(1+a*3)*2) by lia.
      replace (S c*2) with (2+c*2) by lia.
      follow D_one_oe_finish.
      assert (e=0%nat /\ s=6+a*3+c) as [-> ->] by lia.
      replace (6+a*3+c-1) with (4+(1+a*3)+c) by lia.
      replace (6+a*3+c) with ((4+(1+a*3)+c)+1) by lia.
      rewrite pow2_S. applys_eq evstep_refl; flia.
    + replace (4+(a*2+1)*3) with (5+(1+a*3)*2) by lia.
      replace (c*2+1) with (1+c*2) by lia.
      follow D_one_oo_finish.
      assert (e=1%nat /\ s=5+a*3+c) as [-> ->] by lia.
      replace (5+a*3+c-1) with (3+(1+a*3)+c) by lia.
      replace (5+a*3+c) with ((3+(1+a*3)+c)+1) by lia.
      rewrite pow2_S. applys_eq evstep_refl; flia.
Qed.

Lemma D_two_finish len k t s e l:
  k<2^len -> 4<=t -> e<=1 -> len*3+t+7=s*2+e ->
  LC len k l <* ld0 <* [1]^^(4+len*3) {{D}}>
    [1;1;0;0;0] *> [1]^^t *> 0inf -->*
  LC (len+s) 0 l <| RC (k*2^s+2^(s-1)+e*2+1).
Proof.
  intros Hk Ht He Hs.
  assert (exists c, t=4+c) as [c ->] by (exists (t-4); lia).
  divmod2_cases len; rename n' into a;
    divmod2_cases c; rename n' into c.
  - replace (4+a*2*3) with (4+(a*3)*2) by lia.
    follow D_two_ee.
    change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
    eapply evstep_trans; [apply two_YX_left; try assumption; lia|].
    assert (e=1%nat /\ s=5+a*3+c) as [-> ->] by lia.
    replace (5+a*3+c-1) with ((1+a*3)+(1+c)+2) by lia.
    replace (5+a*3+c) with (((1+a*3)+(1+c)+2)+1) by lia.
    rewrite pow2_S. applys_eq evstep_refl; flia.
  - replace (4+a*2*3) with (4+(a*3)*2) by lia.
    replace (4+(c*2+1)) with (5+c*2) by lia.
    follow D_two_eo. change 0inf with (RC 0).
    eapply evstep_trans; [apply two_YX_right; try assumption; lia|].
    assert (e=0%nat /\ s=6+a*3+c) as [-> ->] by lia.
    replace (6+a*3+c-1) with ((1+a*3)+(2+c)+2) by lia.
    replace (6+a*3+c) with (((1+a*3)+(2+c)+2)+1) by lia.
    rewrite pow2_S. applys_eq evstep_refl; flia.
  - replace (4+(a*2+1)*3) with (5+(1+a*3)*2) by lia.
    follow D_two_oe. change 0inf with (RC 0).
    eapply evstep_trans; [apply two_YX_right; try assumption; lia|].
    assert (e=0%nat /\ s=7+a*3+c) as [-> ->] by lia.
    replace (7+a*3+c-1) with ((2+(1+a*3))+(1+c)+2) by lia.
    replace (7+a*3+c) with (((2+(1+a*3))+(1+c)+2)+1) by lia.
    rewrite pow2_S. applys_eq evstep_refl; flia.
  - replace (4+(a*2+1)*3) with (5+(1+a*3)*2) by lia.
    replace (4+(c*2+1)) with (5+c*2) by lia.
    follow D_two_oo.
    change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
    eapply evstep_trans; [apply two_YX_left; try assumption; lia|].
    assert (e=1%nat /\ s=7+a*3+c) as [-> ->] by lia.
    replace (7+a*3+c-1) with ((2+(1+a*3))+(1+c)+2) by lia.
    replace (7+a*3+c) with (((2+(1+a*3))+(1+c)+2)+1) by lia.
    rewrite pow2_S. applys_eq evstep_refl; flia.
Qed.

(* The fixed prefix left after D's short-word scan has only two alignments.
   The tail below it is a counter; its construction is independent of len. *)
Definition Dbase len k l := LC len k l <* ld0 <* [1]^^(len*3+3).

Lemma LC_XY len k n l: k<2^len ->
  LC len k l <* ld0 <* ld1^^n = LC (len+1+n) ((k*2+1)*2^n) l.
Proof.
  intros Hk. unfold LC.
  rewrite BinDec_mulpow2; [rewrite BinDec_mul2add1|];
    try reflexivity; repeat rewrite Nat.pow_add_r; cbn [Nat.pow];
    pose proof (Nat.pow_nonzero 2 n); nia.
Qed.

Lemma Dbase_odd a k l: k<2^(a*2+1) ->
  Dbase (a*2+1) k l =
  LC (a*2+1+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) l.
Proof.
  intros Hk. unfold Dbase.
  replace ((a*2+1)*3+3) with ((a*3+3)*2) by lia.
  rewrite lpow_mul. apply LC_XY; assumption.
Qed.

Lemma Dbase_even a k l:
  Dbase (a*2) k l = LC (a*3+1) 0 (LC (a*2) k l <* <[1;0;1]).
Proof.
  unfold Dbase, LC; rewrite BinDec_O.
  replace (a*2*3+3) with ((a*3+1)*2+1) by lia.
  rewrite lpow_add, lpow_mul, Str_app_assoc. reflexivity.
Qed.

Lemma Dbase_left_odd a k n v r l:
  k<2^(a*2+1) -> v<2^n ->
  LC n v (Dbase (a*2+1) k l) <| RC r -->*
  LC (a*2+1+(a*3+4+n)) 0 l <|
    RC ((k*2+1)*2^(a*3+3+n)+v+r).
Proof.
  intros Hk Hv. rewrite Dbase_odd by assumption.
  rewrite LC_compose; [| |assumption].
  2: repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *;
    pose proof (Nat.pow_nonzero 2 (a*3)); nia.
  follow (RC_calls (a*2+1+1+(a*3+3)+n) 0 (((k*2+1)*2^(a*3+3))*2^n+v)).
  - repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *.
    pose proof (Nat.pow_nonzero 2 n); pose proof (Nat.pow_nonzero 2 (a*3)); nia.
  - replace (r+((k*2+1)*2^(a*3+3)*2^n+v))
      with ((k*2+1)*2^(a*3+3+n)+v+r) by (rewrite Nat.pow_add_r; nia).
    applys_eq evstep_refl; flia.
Qed.

Lemma Dbase_left_even a k n v r l:
  0<a -> k<2^(a*2) -> v<2^n -> v+r<2^(n+2) ->
  LC n v (Dbase (a*2) k l) <| RC r -->*
  LC (a*2+(a*3+2+n)) 0 l <|
    RC ((k*2+1)*2^(a*3+1+n)+(v+r)*2+1).
Proof.
  intros Ha Hk Hv Hvr. rewrite Dbase_even, LC_compose; [|lia|assumption].
  replace (0*2^n+v) with v by lia.
  assert (Hn:2^n<=2^(a*3+1+n)) by (apply Nat.pow_le_mono_r; lia).
  follow (RC_calls (a*3+1+n) 0 v); [lia|].
  eapply evstep_trans; [apply local_outer_finish; try assumption; try lia|].
  - assert (Hp:2^(n+2+1)<=2^(a*3+1+n)) by (apply Nat.pow_le_mono_r; lia).
    rewrite pow2_S in Hp; lia.
  - rewrite pow2_S. applys_eq evstep_refl; flia.
Qed.

Lemma rotate_Dprefix a b l:
  l <* [1]^^(1+a) <* <[0;1]^^b <* <[1] =
  l <* [1]^^a <* ld0^^b <* ld1.
Proof.
  change (1 >> [1;0]^^b *> 1 >> ([1]^^a *> l) =
    1 >> 1 >> ld0^^b *> ([1]^^a *> l)).
  rewrite lpow_rotate; reflexivity.
Qed.

Lemma tail_XYX b c l:
  l <* ld0^^b <* ld1 <* ld0^^c =
  LC (b+1+c) ((2^(b+1)-1)*2^c-1) l.
Proof.
  replace ((2^(b+1)-1)*2^c-1) with (((2^b-1)*2+1)*2^c-1) by
    (rewrite pow2_S; pose proof (Nat.pow_nonzero 2 b); nia).
  rewrite <-(LC_YX b (2^b-1) c l) by (pose proof (Nat.pow_nonzero 2 b); lia).
  unfold LC; rewrite BinDec_full; reflexivity.
Qed.

Lemma xyx_bound b c: (2^(b+1)-1)*2^c-1<2^(b+1+c).
Proof.
  rewrite (Nat.pow_add_r 2 (b+1) c).
  pose proof (Nat.pow_nonzero 2 c); pose proof (Nat.pow_nonzero 2 (b+1)); nia.
Qed.

Lemma D_odd_odd_exit len k b c l:
  LC len k l <* ld0 <* [1]^^(4+len*3) {{D}}>
    [1]^^(3+b*2) *> z *> [1]^^(3+c*2) *> 0inf -->*
  LC (b+1+(2+c)) ((2^(b+1)-1)*2^(2+c)-1) (Dbase len k l) <| RC 2.
Proof.
  follow D_generic_odd3.
  replace (4+len*3) with (1+(len*3+3)) by lia.
  rewrite rotate_Dprefix, tail_XYX. finish.
Qed.

Lemma Dbase_left a q h k n v r l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) -> v<2^n -> v+r<2^(n+2) ->
  let s:=a*3+2+q*2+n in
  LC n v (Dbase (a*2+q) k l) <| RC r -->*
  LC (a*2+q+s) 0 l <| RC (k*2^s+2^(s-1)+(v+r)*(1+h)+h).
Proof.
  intros Hqh HL Hk Hv Hr; cbn zeta.
  destruct q as [|[|q]]; try lia.
  - replace h with 1%nat by lia. rewrite !Nat.add_0_r in *.
    eapply evstep_trans; [apply Dbase_left_even; try assumption; lia|].
    replace (a*3+2+n-1) with (a*3+1+n) by lia.
    replace (a*3+2+n) with ((a*3+1+n)+1) by lia.
    rewrite pow2_S. applys_eq evstep_refl; flia.
  - replace h with 0%nat by lia.
    eapply evstep_trans; [apply Dbase_left_odd; assumption|].
    replace (a*3+2+1*2+n-1) with (a*3+3+n) by lia.
    replace (a*3+2+1*2+n) with ((a*3+3+n)+1) by lia.
    rewrite pow2_S. applys_eq evstep_refl; flia.
Qed.

Lemma D_odd_odd_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+1+(2+c)) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(3+b*2) *> z *> [1]^^(3+c*2) *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(2+c)+1)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_odd_odd_exit.
  pose proof (xyx_bound b (2+c)) as Hv.
  eapply evstep_trans; [apply (Dbase_left a q h); try assumption|].
  - rewrite (Nat.pow_add_r 2 (b+1+(2+c)) 2); cbn [Nat.pow].
    pose proof (Nat.pow_nonzero 2 (b+1+(2+c))); lia.
  - replace ((2^(b+1)-1)*2^(2+c)-1+2)
      with ((2^(b+1)-1)*2^(2+c)+1) by
      (rewrite pow2_S; pose proof (Nat.pow_nonzero 2 b);
        pose proof (Nat.pow_nonzero 2 (2+c)); nia).
    finish.
Qed.

Lemma D_XYX_finish a q h k b c r l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) -> 1<=r<=2 ->
  let s:=a*3+2+q*2+(b+1+c) in
  LC (b+1+c) ((2^(b+1)-1)*2^c-1) (Dbase (a*2+q) k l) <| RC r -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^c+(r-1))*(1+h)+h).
Proof.
  intros Hqh HL Hk Hr; cbn zeta.
  pose proof (xyx_bound b c) as Hv.
  eapply evstep_trans; [apply (Dbase_left a q h); try assumption|].
  - rewrite (Nat.pow_add_r 2 (b+1+c) 2); cbn [Nat.pow].
    pose proof (Nat.pow_nonzero 2 (b+1+c)); lia.
  - replace ((2^(b+1)-1)*2^c-1+r) with ((2^(b+1)-1)*2^c+(r-1)) by
      (rewrite pow2_S; pose proof (Nat.pow_nonzero 2 b);
        pose proof (Nat.pow_nonzero 2 c); nia).
    finish.
Qed.

Lemma D_odd_even6_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+1+(4+c)) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(3+b*2) *> z *> [1]^^(6+c*2) *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(4+c))*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_generic_even6.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix, tail_XYX. fold Dbase.
  change 0inf with (RC 0). follow_inc RC_Inc.
  eapply evstep_trans; [apply (D_XYX_finish a q h); try assumption; lia|].
  applys_eq evstep_refl; flia.
Qed.

Lemma D_odd_one_finish a q h k b l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+1+1) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(3+b*2) *> z *> [1] *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2+1)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_odd_one.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix.
  change ld0 with (ld0^^1). rewrite tail_XYX. fold Dbase.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  apply (D_XYX_finish a q h); try assumption; lia.
Qed.

Lemma tail_XY b c l:
  l <* ld0^^b <* ld1^^c = LC (b+c) ((2^b-1)*2^c) l.
Proof.
  unfold LC. rewrite BinDec_mulpow2, BinDec_full; [reflexivity|].
  rewrite Nat.pow_add_r; pose proof (Nat.pow_nonzero 2 b);
    pose proof (Nat.pow_nonzero 2 c); nia.
Qed.

Lemma D_XY_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+c) in
  Dbase (a*2+q) k l <* ld0^^b <* ld1^^c <| RC 0 -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^b-1)*2^c)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. rewrite tail_XY.
  assert (Hv:(2^b-1)*2^c<2^(b+c)) by
    (rewrite Nat.pow_add_r; pose proof (Nat.pow_nonzero 2 b);
      pose proof (Nat.pow_nonzero 2 c); nia).
  eapply evstep_trans; [apply (Dbase_left a q h); try assumption|].
  - rewrite (Nat.pow_add_r 2 (b+c) 2); cbn [Nat.pow].
    pose proof (Nat.pow_nonzero 2 (b+c)); lia.
  - applys_eq evstep_refl; flia.
Qed.

Lemma rotate_Dprefix_tail a b c l:
  l <* [1]^^(1+a) <* <[0;1]^^b <* [1]^^(1+c*2) =
  l <* [1]^^a <* ld0^^b <* ld1^^(1+c).
Proof.
  replace (1+c*2) with (c*2+1) by lia.
  rewrite lpow_add, lpow_mul, Str_app_assoc.
  change (l <* [1]^^(1+a) <* <[0;1]^^b <* <[1] <* ld1^^c =
    l <* [1]^^a <* ld0^^b <* ld1^^(1+c)).
  rewrite rotate_Dprefix. replace (1+c) with (c+1) by lia.
  rewrite lpow_add, Str_app_assoc; reflexivity.
Qed.

Lemma D_odd_two_finish a q h k b l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+2) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(1+b*2) *> z *> [1;1] *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^b-1)*4)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_odd_two.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite (rotate_Dprefix_tail ((a*2+q)*3+3) b 1). fold Dbase.
  change 0inf with (RC 0). apply (D_XY_finish a q h); assumption.
Qed.

Lemma D_odd_four_finish a q h k b l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+3) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(1+b*2) *> z *> [1]^^4 *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^b-1)*8)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_generic_even4.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite (rotate_Dprefix_tail ((a*2+q)*3+3) b 2). fold Dbase.
  change 0inf with (RC 0). apply (D_XY_finish a q h); assumption.
Qed.

Lemma rotate_Dprefix_zero a b l:
  l <* [1]^^(1+a) <* <[0;1]^^b <* <[0] = l <* [1]^^a <* ld0^^(1+b).
Proof.
  change (0 >> [1;0]^^b *> 1 >> ([1]^^a *> l) =
    0 >> 1 >> ld0^^b *> ([1]^^a *> l)).
  rewrite lpow_rotate; reflexivity.
Qed.

Lemma D_zero_even a j l:
  l <* [1]^^(1+a) {{D}}> [1]^^(2+j*2) *> 0inf -->*
  l <* [1]^^a <* ld0^^j |> RC 0.
Proof.
  destruct j as [|j].
  - change (l <* [1]^^a <* <[1] {{D}}> [1;1] *> 0inf -->*
      l <* [1]^^a |> RC 0).
    follow D_empty_two; finish.
  - replace (2+S j*2) with (4+j*2) by lia.
    follow D_empty_even4. rewrite rotate_Dprefix_zero; finish.
Qed.

Lemma D_zero_odd a j l:
  l <* [1]^^(1+a) {{D}}> [1]^^(3+j*2) *> 0inf -->*
  l <* [1]^^a <* ld0^^j <| RC 2.
Proof.
  destruct j as [|j].
  - change (l <* [1]^^a <* <[1] {{D}}> [1;1;1] *> 0inf -->*
      l <* [1]^^a <| RC 2).
    follow D_empty_three; finish.
  - replace (3+S j*2) with (5+j*2) by lia.
    follow D_empty_odd5. rewrite rotate_Dprefix_zero; finish.
Qed.

Lemma D_zero_exit len k j p l: p<=1 ->
  LC len k l <* ld0 <* [1]^^(4+len*3) {{D}}>
    [1]^^(2+j*2+p) *> 0inf -->*
  LC j (2^j-1) (Dbase len k l) <| RC (1+p).
Proof.
  intros Hp. unfold Dbase, LC; rewrite BinDec_full; fold LC.
  replace (4+len*3) with (1+(len*3+3)) by lia.
  destruct p as [|[|p]]; try lia.
  - rewrite Nat.add_0_r. follow D_zero_even. follow_inc RC_Inc; finish.
  - replace (2+j*2+1) with (3+j*2) by lia. apply D_zero_odd.
Qed.

Lemma D_zero_finish a q h k j p l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) -> p<=1 ->
  let s:=a*3+2+q*2+j in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(2+j*2+p) *> 0inf -->*
  LC (a*2+q+s) 0 l <| RC (k*2^s+2^(s-1)+(2^j+p)*(1+h)+h).
Proof.
  intros Hqh HL Hk Hp; cbn zeta. follow D_zero_exit.
  pose proof (Nat.pow_nonzero 2 j) as Hpow.
  eapply evstep_trans; [apply (Dbase_left a q h); try assumption; try lia|].
  - rewrite (Nat.pow_add_r 2 j 2); cbn [Nat.pow]; lia.
  - replace (2^j-1+(1+p)) with (2^j+p) by lia; finish.
Qed.

(* This is deliberately not a capacity-preserving frame return. *)
Lemma D_overcapacity len k l: k<2^len ->
  LC len k l <* ld0 <* [1]^^(4+len*3) {{D}}> [1] *> 0inf -->*
  LC len 0 l <| RC (k+2^(len+2)).
Proof.
  intros Hk. follow D_empty_one.
  replace (2+len) with (len+2) by lia.
  change (z^^(len+2) *> d *> 0inf) with
    ((BinaryCounter.d0 d)^^(len+2) *> d *> 0inf).
  rewrite <-BinInc_pow2; fold RC.
  follow (RC_calls len 0 k). applys_eq evstep_refl; flia.
Qed.

Lemma D_overcapacity_tail len k w l: Digits len k w ->
  LC len k l <* ld0 <* [1]^^(4+len*3) {{D}}> [1] *> 0inf -->*
  LC len 0 l <| w *> RC 4.
Proof.
  intros Hw. pose proof (digits_bound _ _ _ Hw) as Hk.
  follow D_overcapacity. rewrite (digits_RC _ _ _ Hw), Nat.pow_add_r.
  finish.
Qed.

Lemma D_even_one_finish a q h k b l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+1) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1] *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+(2^(b+1)+2)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_even_one.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix. change ld1 with (ld1^^1).
  rewrite tail_XY. fold Dbase.
  change ([0;0;0;0;0;0;1;0;0] *> 0inf) with (RC 4).
  pose proof (Nat.pow_nonzero 2 b) as Hp.
  eapply evstep_trans; [apply (Dbase_left a q h); try assumption|].
  - rewrite pow2_S; cbn [Nat.pow]; lia.
  - rewrite (Nat.pow_add_r 2 (b+1) 2), pow2_S; cbn [Nat.pow]; nia.
  - replace ((2^b-1)*2^1+4) with (2^(b+1)+2) by (rewrite pow2_S; cbn; lia).
    finish.
Qed.

Lemma local_tail_finish n k m J v l:
  k<2^n -> 0<m -> v*2+1<2^J ->
  2^J<=((k*2+1)*2^m-1)+(v*2+2) ->
  LC m 0 (LC n k l <* <[1;0;1]) <| RC v -->*
  LC (n+1+m) 0 l <| RC ((k*2+1)*2^m-1+v*2+2).
Proof.
  intros Hk Hm Hv Hsum.
  destruct (local_overflow_RC m J v (LC n k l) Hm Hv) as [w [Hw Hrun]].
  follow Hrun. unfold LC; rewrite BinDec_full; fold LC.
  rewrite LC_YX by assumption.
  eapply evstep_trans; [eapply marked_drain with (J:=J) (V:=v*2+2)|].
  - apply yx_bound; assumption.
  - rewrite pow2_S; lia.
  - lia.
  - assumption.
  - applys_eq evstep_refl; flia.
Qed.

Lemma even_core b c e l: e<=1 -> (1<=c \/ e=0%nat) ->
  LC (1+c) 0 (l <* ld0^^b <* ld1 <* <[1;0;1]) <| RC (2^c+e) -->*
  LC (b+c+3) 0 l <| RC ((2^(b+1)-1)*2^(c+2)+(e*2+1)).
Proof.
  intros He Hc. change ld1 with (ld1^^1). rewrite tail_XY.
  pose proof (Nat.pow_nonzero 2 b) as Hb.
  pose proof (Nat.pow_nonzero 2 c) as Hp.
  assert (Hsmall:(2^c+e)*2+1<2^(c+2)).
  { rewrite (Nat.pow_add_r 2 c 2); cbn [Nat.pow].
    destruct Hc as [Hc| ->]; [|lia].
    assert (2<=2^c) by (change (2^1<=2^c); apply Nat.pow_le_mono_r; lia). lia. }
  eapply evstep_trans; [eapply local_tail_finish with (J:=c+2)|].
  - rewrite pow2_S; cbn [Nat.pow]; lia.
  - lia.
  - assumption.
  - replace (1+c) with (c+1) by lia.
    rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia.
  - replace (((2^b-1)*2^1*2+1)*2^(1+c)-1+(2^c+e)*2+2)
      with ((2^(b+1)-1)*2^(c+2)+e*2+1) by
      (replace (1+c) with (c+1) by lia;
        rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia).
    applys_eq evstep_refl; flia.
Qed.

Lemma even_core_right b c l:
  l <* ld0^^b <* ld1 <* <[1;0;1] <* ld1 <* ld0^^c |> RC 0 -->*
  LC (b+c+3) 0 l <| RC ((2^(b+1)-1)*2^(c+2)+1).
Proof.
  rewrite local_YX.
  eapply evstep_trans; [apply RC_finish|].
  - pose proof (Nat.pow_nonzero 2 c); cbn [Nat.add Nat.pow]; lia.
  - replace (2^c-1+0+1) with (2^c+0) by (pose proof (Nat.pow_nonzero 2 c); lia).
    eapply evstep_trans; [apply (even_core b c 0); auto|].
    applys_eq evstep_refl; flia.
Qed.

Lemma even_core_left b c l: 1<=c ->
  l <* ld0^^b <* ld1 <* <[1;0;1] <* ld1 <* ld0^^c <| RC 2 -->*
  LC (b+c+3) 0 l <| RC ((2^(b+1)-1)*2^(c+2)+3).
Proof.
  intros Hc. rewrite local_YX. follow (RC_calls (1+c) 0 (2^c-1)).
  - pose proof (Nat.pow_nonzero 2 c); cbn [Nat.add Nat.pow]; lia.
  - replace (2+(2^c-1)) with (2^c+1) by (pose proof (Nat.pow_nonzero 2 c); lia).
    apply (even_core b c 1); auto.
Qed.

Lemma rotate_Dprefix_local a b l:
  l <* [1]^^(1+a) <* <[0;1]^^b <* <[1;1;0;1] =
  l <* [1]^^a <* ld0^^b <* ld1 <* <[1;0;1].
Proof.
  change (l <* [1]^^(1+a) <* <[0;1]^^b <* <[1] <* <[1;0;1] =
    l <* [1]^^a <* ld0^^b <* ld1 <* <[1;0;1]).
  rewrite rotate_Dprefix; reflexivity.
Qed.

Lemma even_value_bound b c e: e<=1 ->
  (2^(b+1)-1)*2^(c+2)+e*2+1<2^(b+c+3+2).
Proof.
  intros He. repeat rewrite Nat.pow_add_r; cbn [Nat.pow].
  pose proof (Nat.pow_nonzero 2 b); pose proof (Nat.pow_nonzero 2 c); nia.
Qed.

Lemma D_even_tail_finish a q h k b c e l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) -> e<=1 ->
  let s:=a*3+2+q*2+(b+c+3) in
  LC (b+c+3) 0 (Dbase (a*2+q) k l) <| RC ((2^(b+1)-1)*2^(c+2)+(e*2+1)) -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(c+2)+(e*2+1))*(1+h)+h).
Proof.
  intros Hqh HL Hk He; cbn zeta.
  apply (Dbase_left a q h k (b+c+3) 0 ((2^(b+1)-1)*2^(c+2)+(e*2+1)) l);
    try assumption.
  - pose proof (Nat.pow_nonzero 2 (b+c+3)); lia.
  - pose proof (even_value_bound b c e He); lia.
Qed.

Lemma D_even_even4_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+(1+c)+3) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1]^^(4+c*2) *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(1+c+2)+1)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_even_even4.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix_local; fold Dbase. change 0inf with (RC 0).
  follow even_core_right. apply (D_even_tail_finish a q h k b (1+c) 0); auto.
Qed.

Lemma D_even_odd5_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+(1+c)+3) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1]^^(5+c*2) *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(1+c+2)+3)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_even_odd5.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix_local; fold Dbase.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  follow even_core_left; [lia|]. apply (D_even_tail_finish a q h k b (1+c) 1); auto.
Qed.

Lemma local_X l: l <* ld0 = LC 1 1 l.
Proof. unfold LC; rewrite BinDec_full; reflexivity. Qed.
Lemma local_Y l: l <* ld1 = LC 1 0 l.
Proof. unfold LC; rewrite BinDec_O; reflexivity. Qed.

Lemma D_even_two_finish a q h k b l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+0+3) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1;1] *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*4+1)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_even_two.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix_local; fold Dbase.
  rewrite local_X. change 0inf with (RC 0).
  follow (RC_calls 1 0 1).
  follow (even_core b 0 0).
  apply (D_even_tail_finish a q h k b 0 0); auto.
Qed.

Lemma even_core_short b l: 1<=b ->
  LC 1 0 (l <* ld0^^b <* ld1 <* <[1;0;1]) <| RC 2 -->*
  LC (b+3) 0 l <| RC ((2^(b+1)-1)*4+3).
Proof.
  intros Hb. change ld1 with (ld1^^1). rewrite tail_XY.
  assert (Hp:2<=2^b) by (change (2^1<=2^b); apply Nat.pow_le_mono_r; lia).
  eapply evstep_trans; [eapply local_tail_finish with (J:=3)|].
  - rewrite pow2_S; cbn [Nat.pow]; lia.
  - lia.
  - cbn; lia.
  - cbn [Nat.pow]; nia.
  - replace (((2^b-1)*2^1*2+1)*2^1-1+2*2+2) with ((2^(b+1)-1)*4+3) by
      (rewrite pow2_S; cbn [Nat.pow]; nia).
    applys_eq evstep_refl; flia.
Qed.

Lemma D_even_three_finish a q h k b l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) -> 1<=b ->
  let s:=a*3+2+q*2+(b+0+3) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1;1;1] *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*4+3)*(1+h)+h).
Proof.
  intros Hqh HL Hk Hb; cbn zeta. follow D_even_three.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix_local; fold Dbase. rewrite local_Y.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  follow even_core_short.
  applys_eq (D_even_tail_finish a q h k b 0 1 l Hqh HL Hk ltac:(lia)); flia.
Qed.

Lemma LC_Y n k l: k<2^n -> LC n k l <* ld1 = LC (n+1) (k*2) l.
Proof. intros Hk; unfold LC; rewrite BinDec_mul2; [reflexivity|rewrite pow2_S; lia]. Qed.

Lemma budget_small n k r: 1<=n -> k<2^n -> r<=4 -> k+r<2^(n+2).
Proof.
  intros Hn Hk Hr. assert (2<=2^n) by
    (change (2^1<=2^n); apply Nat.pow_le_mono_r; lia).
  rewrite (Nat.pow_add_r 2 n 2); cbn [Nat.pow]; lia.
Qed.

Lemma D_extra_oo_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let n:=b+1+(1+c) in let s:=a*3+2+q*2+(n+1+1) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(3+b*2) *> z *> [1]^^(1+c*2) *> z *> d *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(1+c+2)-1)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_tail_oo.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix, tail_XYX; fold Dbase.
  change ld0 with (ld0^^1). rewrite LC_YX by apply xyx_bound.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  set (v:=(2^(b+1)-1)*2^(1+c)-1).
  assert (Hv:v<2^(b+1+(1+c))) by apply xyx_bound.
  eapply evstep_trans; [apply (Dbase_left a q h k (b+1+(1+c)+1+1)
    ((v*2+1)*2^1-1) 2 l); try assumption|].
  - apply yx_bound; assumption.
  - apply budget_small; try lia. apply yx_bound; assumption.
  - replace ((v*2+1)*2^1-1+2) with ((2^(b+1)-1)*2^(1+c+2)-1) by
      (unfold v; rewrite (Nat.pow_add_r 2 (1+c) 2), pow2_S;
        cbn [Nat.pow]; pose proof (Nat.pow_nonzero 2 b);
        pose proof (Nat.pow_nonzero 2 (1+c)); nia).
    finish.
Qed.

Lemma D_extra_oe_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let n:=b+1+(1+c) in let s:=a*3+2+q*2+(n+1) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(3+b*2) *> z *> [1]^^(2+c*2) *> z *> d *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(1+c+1)+2)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_tail_oe.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix, tail_XYX; fold Dbase.
  rewrite LC_Y by apply xyx_bound.
  change ([0;0;0;0;0;0;1;0;0] *> 0inf) with (RC 4).
  set (v:=(2^(b+1)-1)*2^(1+c)-1).
  assert (Hv:v<2^(b+1+(1+c))) by apply xyx_bound.
  assert (Hvv:v*2<2^(b+1+(1+c)+1)) by (rewrite pow2_S; lia).
  eapply evstep_trans; [apply (Dbase_left a q h k (b+1+(1+c)+1) (v*2) 4 l);
    try assumption|].
  - apply budget_small; auto; lia.
  - replace (v*2+4) with ((2^(b+1)-1)*2^(1+c+1)+2) by
      (unfold v; rewrite !pow2_S; pose proof (Nat.pow_nonzero 2 b);
        pose proof (Nat.pow_nonzero 2 (1+c)); nia).
    finish.
Qed.

Lemma local_YXYX c l:
  l <* ld1 <* ld0^^c <* ld1 <* ld0 = LC (c+3) ((2^c-1)*4+1) l.
Proof.
  rewrite (local_YX c l). change ld0 with (ld0^^1).
  rewrite LC_YX by (pose proof (Nat.pow_nonzero 2 c); cbn [Nat.add Nat.pow]; lia).
  replace (1+c+1+1) with (c+3) by lia.
  replace (((2^c-1)*2+1)*2^1-1) with ((2^c-1)*4+1) by (cbn [Nat.pow]; lia).
  reflexivity.
Qed.

Lemma local_YXY c l:
  l <* ld1 <* ld0^^c <* ld1 = LC (c+2) ((2^c-1)*2) l.
Proof.
  rewrite (local_YX c l), LC_Y by
    (pose proof (Nat.pow_nonzero 2 c); cbn [Nat.add Nat.pow]; lia).
  replace (1+c+1) with (c+2) by lia; reflexivity.
Qed.

Lemma extra_eo_core b c l:
  LC (c+3) 0 (l <* ld0^^b <* ld1 <* <[1;0;1]) <| RC (2^(c+2)-1) -->*
  LC (b+c+5) 0 l <| RC ((2^(b+1)-1)*2^(c+4)-1).
Proof.
  change ld1 with (ld1^^1). rewrite tail_XY.
  pose proof (Nat.pow_nonzero 2 b) as Hb.
  pose proof (Nat.pow_nonzero 2 c) as Hc.
  eapply evstep_trans; [eapply local_tail_finish with (J:=c+3)|].
  - rewrite pow2_S; cbn [Nat.pow]; lia.
  - lia.
  - rewrite !Nat.pow_add_r; cbn [Nat.pow]; lia.
  - rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia.
  - replace (((2^b-1)*2^1*2+1)*2^(c+3)-1+(2^(c+2)-1)*2+2)
      with ((2^(b+1)-1)*2^(c+4)-1) by
      (rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia).
    applys_eq evstep_refl; flia.
Qed.

Lemma extra_ee_core b c l: 1<=b ->
  LC (c+2) 0 (l <* ld0^^b <* ld1 <* <[1;0;1]) <| RC (2^(c+1)+2) -->*
  LC (b+c+4) 0 l <| RC ((2^(b+1)-1)*2^(c+3)+5).
Proof.
  intros Hb. change ld1 with (ld1^^1). rewrite tail_XY.
  assert (Hpb:2<=2^b) by (change (2^1<=2^b); apply Nat.pow_le_mono_r; lia).
  pose proof (Nat.pow_nonzero 2 c) as Hc.
  eapply evstep_trans; [eapply local_tail_finish with (J:=c+4)|].
  - rewrite pow2_S; cbn [Nat.pow]; lia.
  - lia.
  - rewrite !Nat.pow_add_r; cbn [Nat.pow]; lia.
  - rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia.
  - replace (((2^b-1)*2^1*2+1)*2^(c+2)-1+(2^(c+1)+2)*2+2)
      with ((2^(b+1)-1)*2^(c+3)+5) by
      (rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia).
    applys_eq evstep_refl; flia.
Qed.

Lemma D_extra_eo_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) ->
  let s:=a*3+2+q*2+(b+c+5) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1]^^(3+c*2) *> z *> d *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(c+4)-1)*(1+h)+h).
Proof.
  intros Hqh HL Hk; cbn zeta. follow D_tail_eo.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix_local; fold Dbase. rewrite local_YXYX.
  change ([0;0;0;1;0;0] *> 0inf) with (RC 2).
  pose proof (Nat.pow_nonzero 2 c) as Hc.
  follow (RC_calls (c+3) 0 ((2^c-1)*4+1)).
  - rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
  - replace (2+((2^c-1)*4+1)) with (2^(c+2)-1) by
      (rewrite Nat.pow_add_r; cbn [Nat.pow]; lia).
    follow extra_eo_core.
    apply (Dbase_left a q h k (b+c+5) 0 ((2^(b+1)-1)*2^(c+4)-1) l);
      try assumption.
    + pose proof (Nat.pow_nonzero 2 (b+c+5)); lia.
    + rewrite !Nat.pow_add_r; cbn [Nat.pow].
      pose proof (Nat.pow_nonzero 2 b); nia.
Qed.

Lemma D_extra_ee_finish a q h k b c l:
  q+h=1%nat -> 0<a*2+q -> k<2^(a*2+q) -> 1<=b ->
  let s:=a*3+2+q*2+(b+c+4) in
  LC (a*2+q) k l <* ld0 <* [1]^^(4+(a*2+q)*3) {{D}}>
    [1]^^(4+b*2) *> z *> [1]^^(4+c*2) *> z *> d *> 0inf -->*
  LC (a*2+q+s) 0 l <|
    RC (k*2^s+2^(s-1)+((2^(b+1)-1)*2^(c+3)+5)*(1+h)+h).
Proof.
  intros Hqh HL Hk Hb; cbn zeta. follow D_tail_ee.
  replace (4+(a*2+q)*3) with (1+((a*2+q)*3+3)) by lia.
  rewrite rotate_Dprefix_local; fold Dbase. rewrite local_YXY.
  change ([0;0;0;0;0;0;1;0;0] *> 0inf) with (RC 4).
  pose proof (Nat.pow_nonzero 2 c) as Hc.
  follow (RC_calls (c+2) 0 ((2^c-1)*2)).
  - rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
  - replace (4+(2^c-1)*2) with (2^(c+1)+2) by (rewrite pow2_S; lia).
    follow extra_ee_core.
    apply (Dbase_left a q h k (b+c+4) 0 ((2^(b+1)-1)*2^(c+3)+5) l);
      try assumption.
    + pose proof (Nat.pow_nonzero 2 (b+c+4)); lia.
    + rewrite !Nat.pow_add_r; cbn [Nat.pow].
      pose proof (Nat.pow_nonzero 2 b); nia.
Qed.

(* SOC51_BlockQueue *)
Module Queue.
Local Open Scope nat_scope.
Definition cell := (nat*nat)%type.
Definition danger : cell := (0,1).
Definition main (p:cell) := 3 <= fst p /\ fst p*8+9 <= snd p.
Definition allowed (p:cell) := 0 < snd p /\ (fst p=0 \/ separated (fst p) (snd p)).
Definition link (p:cell) (l:list cell) := p=danger ->
  match l with [] => True | q::_ => main q end.

Inductive good : list cell -> Prop :=
| good_nil : good []
| good_cons p l : allowed p -> link p l -> good l -> good (p::l).

Lemma main_allowed p: main p -> allowed p /\ p<>danger.
Proof.
  destruct p as [t u]; intros [Ht Hu]. split.
  - unfold allowed, separated; simpl in *; lia.
  - intro H; inversion H; simpl in *; lia.
Qed.

Lemma good_tail p l: good (p::l) -> good l.
Proof. intro H; inversion H; auto. Qed.

Lemma good_append_main l p r:
  good l -> main p -> good r -> good (l++p::r).
Proof.
  intros Hl Hp Hr. destruct (main_allowed _ Hp) as [Ha Hne]. induction Hl; simpl.
  - constructor; auto. unfold link; intros Heq; contradiction.
  - constructor; auto. unfold link in *. destruct l; simpl in *; auto.
Qed.

Definition weight (p:cell) := fst p+snd p+1.
Fixpoint mass (l:list cell) := match l with [] => 0 | p::r => weight p+mass r end.

Lemma mass_app l r: mass (l++r)=mass l+mass r.
Proof. induction l; simpl; lia. Qed.
Lemma length_mass l: length l <= mass l.
Proof. induction l as [|[t u] l]; simpl; unfold weight in *; simpl in *; lia. Qed.
Lemma mass_skipn n l: mass (skipn n l) <= mass l.
Proof. revert l; induction n; intros [|p l]; simpl; try lia; specialize (IHn l); lia. Qed.
Lemma mass_firstn_strict n l: n < length l -> mass (firstn n l) < mass l.
Proof.
  intros Hn. pose proof (length_mass (skipn n l)).
  rewrite length_skipn in H. rewrite <- (firstn_skipn n l) at 2.
  rewrite mass_app. lia.
Qed.

Inductive cut : list cell -> list cell -> nat -> nat -> Prop :=
| cut_one p l : allowed p -> p<>danger -> cut (p::l) l (weight p) 1
| cut_two p l : main p -> cut (danger::p::l) l (2+weight p) 2.

Lemma cut_exists l: good l -> 2 <= length l ->
  exists r n k, cut l r n k.
Proof.
  intros Hl Hlen. destruct l as [|[t u] l]; simpl in Hlen; try lia.
  inversion Hl; subst.
  destruct (Nat.eq_dec t 0), (Nat.eq_dec u 1); subst.
  - destruct l as [|p l]; simpl in Hlen; try lia.
    exists l, (2+weight p), 2. constructor.
    match goal with H:link _ _ |- _ => apply H; reflexivity end.
  - eexists _, _, _. apply cut_one; auto. unfold danger; congruence.
  - eexists _, _, _. apply cut_one; auto. unfold danger; congruence.
  - eexists _, _, _. apply cut_one; auto. unfold danger; congruence.
Qed.

Lemma cut_good l r n k: good l -> cut l r n k -> good r.
Proof. intros H Hc; inversion Hc; subst; repeat (apply good_tail in H); exact H. Qed.

Lemma cut_spec l r n k: cut l r n k ->
  1 <= k <= 2 /\ r=skipn k l /\ n=mass (firstn k l).
Proof. intros H; destruct H; simpl; repeat split; try reflexivity; unfold weight; simpl; lia. Qed.

Definition advance (l r:list cell) := exists k a, k<=2 /\ r=skipn k l++a.
Inductive path : nat -> list cell -> list cell -> Prop :=
| path_zero l: path 0 l l
| path_next n l r s: path n l r -> advance r s -> path (S n) l s.

Lemma skip_old n k (l r a:list cell): n+k <= length l ->
  skipn k (skipn n l++r)++a = skipn (n+k) l++(r++a).
Proof.
  intros H. rewrite skipn_app, skipn_skipn, length_skipn.
  replace (k-(length l-n)) with 0 by lia. simpl.
  replace (k+n) with (n+k) by lia. symmetry; apply app_assoc.
Qed.

Lemma path_old_prefix n l r: path n l r -> n*2 <= length l ->
  exists k a, k<=n*2 /\ r=skipn k l++a.
Proof.
  intros H; induction H as [l|n l r s Hp IH Ha]; intros Hlen.
  - exists 0, ([]:list cell); simpl. rewrite app_nil_r. auto.
  - destruct IH as [k [a [Hk Hr]]]; try lia.
    destruct Ha as [j [b [Hj Hs]]].
    exists (k+j), (a++b). split; try lia.
    rewrite Hs, Hr, skip_old; auto; lia.
Qed.

Lemma three_round_prefix_bound l r s n k:
  path 3 l r -> 9 <= length l -> cut r s n k -> n < mass l.
Proof.
  intros Hp Hlen Hc.
  destruct (path_old_prefix _ _ _ Hp) as [d [a [Hd Hr]]]; try lia.
  destruct (cut_spec _ _ _ _ Hc) as [Hk [Hs Hn]].
  rewrite Hn, Hr, firstn_app.
  assert (Hshort:k < length (skipn d l)) by (rewrite length_skipn; lia).
  replace (k-length (skipn d l)) with 0 by lia. simpl; rewrite app_nil_r.
  pose proof (mass_firstn_strict _ _ Hshort).
  pose proof (mass_skipn d l). lia.
Qed.

Lemma three_growth a b c d:
  a*5 <= b*2 -> b*5 <= c*2 -> c*5 <= d*2 -> a*125 <= d*8.
Proof. lia. Qed.

Lemma generated_good l r n k p a:
  good l -> cut l r n k -> main p -> good a ->
  k <= 1+length a ->
  good (r++p::a) /\ length l <= length (r++p::a).
Proof.
  intros Hl Hc Hp Ha Hsize. split.
  - exact (good_append_main _ _ _ (cut_good _ _ _ _ Hl Hc) Hp Ha).
  - inversion Hc; subst; rewrite length_app; simpl in *; lia.
Qed.

Lemma cut_large l r n k: cut l r n k -> 3 <= n.
Proof.
  intros H; destruct H as [[t u] l Hallowed Hne|[t u] l Hmain].
  - unfold allowed, danger, weight in *; simpl in *.
    destruct t as [|t], u as [|[|u]]; simpl in *; try lia; congruence.
  - unfold main, weight in *; simpl in *; lia.
Qed.

(* A frame describes the virtual word 1W, including its final one-run. *)
Record frame := Frame { cells:list cell; trailing:nat }.
Definition width f := mass (cells f)+trailing f-1.
Definition edge f g := advance (cells f) (cells g) /\
  width f*5 <= width g*2 /\ length (cells f) <= length (cells g).

Record history f0 f1 f2 f3 : Prop := History {
  edge01: edge f0 f1;
  edge12: edge f1 f2;
  edge23: edge f2 f3;
  old_width: 16 <= width f0;
  old_count: 9 <= length (cells f0);
  tail_bound: trailing f3 <= width f0+8;
  current_good: good (cells f3)
}.

(* This contract is supplied below by the concrete finite return rules.
   In particular it does not assume that the new main cell is safe. *)
Definition emission f g := exists r n k gap a,
  cut (cells f) r n k /\
  cells g=r++(n+trailing f,gap)::a /\ good a /\ k<=1+length a /\
  width f*5 <= width g*2 /\ width f*3 <= gap*2+4 /\ trailing g<=n+8.

Lemma width_mass f: mass (cells f) <= width f+1.
Proof. unfold width; lia. Qed.

Lemma history_path f0 f1 f2 f3: history f0 f1 f2 f3 ->
  path 3 (cells f0) (cells f3).
Proof.
  intros [[H01 _] [H12 _] [H23 _] _ _ _ _].
  eapply path_next; [eapply path_next; [eapply path_next; [constructor|exact H01]|exact H12]|exact H23].
Qed.

Lemma history_prefix f0 f1 f2 f3 r n k:
  history f0 f1 f2 f3 -> cut (cells f3) r n k -> n <= width f0.
Proof.
  intros H Hc.
  pose proof (three_round_prefix_bound _ _ _ _ _
    (history_path _ _ _ _ H) (old_count _ _ _ _ H) Hc).
  pose proof (width_mass f0). lia.
Qed.

Theorem history_next f0 f1 f2 f3 f4:
  history f0 f1 f2 f3 -> emission f3 f4 -> history f1 f2 f3 f4.
Proof.
  intros H [r [n [k [gap [a [Hcut [Hcells [Ha [Hsize [Hg [Hgap Htail]]]]]]]]]]].
  pose proof (history_prefix _ _ _ _ _ _ _ H Hcut) as Hprefix.
  destruct H as [H01 H12 H23 Hw Hcount Htail3 Hgood].
  destruct H01 as [Hp01 [Hg01 Hn01]], H12 as [Hp12 [Hg12 Hn12]],
    H23 as [Hp23 [Hg23 Hn23]].
  assert (Hmain: main (n+trailing f3,gap)).
  { unfold main; simpl; split.
    - pose proof (cut_large _ _ _ _ Hcut); lia.
    - apply (generated_main_bound (width f0) (width f3));
        auto; eapply three_growth; eauto. }
  destruct (generated_good _ _ _ _ _ _ Hgood Hcut Hmain Ha Hsize) as [Hgood4 Hcount4].
  assert (Hg4:good (cells f4)) by (rewrite Hcells; exact Hgood4).
  assert (Hn4:length (cells f3)<=length (cells f4)) by (rewrite Hcells; exact Hcount4).
  constructor; try (split; [assumption|split; assumption]); try lia; auto.
  split; [|split; assumption].
  destruct (cut_spec _ _ _ _ Hcut) as [Hk [Hr Hn]].
  exists k, ((n+trailing f3,gap)::a). split; [lia|]. rewrite Hcells, Hr; reflexivity.
Qed.

Lemma history_ready f0 f1 f2 f3:
  history f0 f1 f2 f3 -> good (cells f3) /\ 9<=length (cells f3).
Proof.
  intros [[_ [_ H01]] [_ [_ H12]] [_ [_ H23]] _ H0 _ Hgood].
  split; [assumption|lia].
Qed.

Definition safe_input (extra:bool) t u :=
  if extra then main (t,u) else allowed (t,u) /\ (t,u)<>danger.

(* The finite return table after expanding Q into runs.  q is the parity
   of L and h its complement.  No power of two or bit list is evaluated.
   The connection to machine return rules is proved after this queue module. *)
Inductive block : bool -> nat -> nat -> nat -> nat -> list cell -> nat -> Prop :=
| block_zero2 l q h: q+h=1 ->
    block false (l*2+q) 0 2 ((l+q)*3-1) [] (1+h)
| block_zero3 l q h: q+h=1 ->
    block false (l*2+q) 0 3 ((l+q)*3-2) [danger] h
| block_zero5 l q h: q+h=1 ->
    block false (l*2+q) 0 5 ((l+q)*3-1) [] (2+h)
| block_zero l q h j p: q+h=1 -> p<=1 -> 1+p<=j ->
    block false (l*2+q) 0 (j*2+2+p) ((l+q)*3-1) [(0,j-p)] (p+h)
| block_short L t u s e: 0<t -> (u=1 \/ u=2) -> e<=1 -> L*3+t+7=s*2+e ->
    block false L t u (s-1-(e+u-1)) [] (e+u-1)
| block_one_odd l q h b: q+h=1 ->
    block false (l*2+q) 1 (b*2+1) ((l+q)*3) [] (b+1+h)
| block_one_even l q h j: q+h=1 ->
    block false (l*2+q) 1 (j*2+2) ((l+q)*3-1) [(0,j-2);danger] h
| block_full l q h a b p e: q+h=1 -> p<=1 -> e<=1 -> 1<=a -> 1<=b -> a+p=e ->
    block false (l*2+q) (a*2+e) (b*2+2-p) ((l+q)*3) [] (b+a+1+h)
| block_split l q h a b p e: q+h=1 -> p<=1 -> e<=1 -> 1<=a -> 1<=b -> e<a+p ->
    block false (l*2+q) (a*2+e) (b*2+2-p) ((l+q)*3) [(b-1,a+p-e)] (1-p+e+h)
| block_extra_odd l q h a b p: q+h=1 -> p<=1 ->
    block true (l*2+q) (a*2+1) (b*2+2-p) ((l+q)*3) [(b-2,1)] (a+3+h)
| block_extra_even_odd l q h a b: q+h=1 ->
    block true (l*2+q) (a*2) (b*2+1) ((l+q)*3) [(b-1,a-1);danger] h
| block_extra_four l q h b: q+h=1 ->
    block true (l*2+q) 4 (b*2+2) ((l+q)*3) [(b,1)] (1+h)
| block_extra_even_even l q h a b: q+h=1 -> 3<=a ->
    block true (l*2+q) (a*2) (b*2+2) ((l+q)*3) [(b-1,a-2);danger] (1+h).

Lemma block_bounds extra L t u gap a E:
  block extra L t u gap a E -> 16<=L -> safe_input extra t u ->
  0<gap /\ L*3<=gap*2+4 /\ L*3<=(gap+mass a+E+1)*2 /\
  E<=t+u+(if extra then 11 else 9) /\ (if extra then 1 else 0)<=length a.
Proof.
  intros H; destruct H; unfold safe_input, main, allowed, separated;
    simpl; unfold weight, danger; simpl; intros; repeat split; try lia.
  destruct p; simpl; lia.
Qed.

Lemma good_one t u: 0<u -> (t=0 \/ separated t u) -> good [(t,u)].
Proof. intros; constructor; [split; assumption|unfold link; auto|constructor]. Qed.
Lemma good_two t u: 0<u -> (t=0 \/ separated t u) -> (t,u)<>danger ->
  good [(t,u);danger].
Proof.
  intros Hu Hs Hne. constructor.
  - split; assumption.
  - unfold link; intros Heq; contradiction.
  - apply good_one; simpl; auto.
Qed.

Lemma block_good extra L t u gap a E:
  block extra L t u gap a E -> safe_input extra t u -> good a.
Proof.
  intros H; destruct H; intros Hsafe;
    unfold safe_input, main, allowed, separated in Hsafe; simpl in Hsafe;
    try solve [constructor].
  all: first [apply good_one; [lia|unfold separated in *; lia]
             |apply good_two; [lia|unfold separated in *; lia|
                unfold danger; intros Heq; inversion Heq; unfold separated in *; lia]].
Qed.

Lemma cut_mass l r n k: cut l r n k -> mass l=n+mass r.
Proof. intros H; destruct H; simpl; unfold danger, weight; simpl; lia. Qed.

Lemma width_generated f r n k gap a E: cut (cells f) r n k ->
  width (Frame (r++(n+trailing f,gap)::a) E) = width f+gap+mass a+E+1.
Proof.
  intros H. pose proof (cut_mass _ _ _ _ H). pose proof (cut_large _ _ _ _ H).
  unfold width; simpl; rewrite mass_app; simpl; unfold weight; simpl. lia.
Qed.

Lemma block_emission f r n k (extra:bool) t u gap a E:
  cut (cells f) r n k -> n=t+u+(if extra then 3 else 1) ->
  k=(if extra then 2 else 1) -> 16<=width f -> safe_input extra t u ->
  block extra (width f) t u gap a E ->
  emission f (Frame (r++(n+trailing f,gap)::a) E).
Proof.
  intros Hcut Hn Hk HL Hsafe Hb.
  destruct (block_bounds _ _ _ _ _ _ _ Hb HL Hsafe) as [Hpos [Hgap [Hg [HE Hcount]]]].
  exists r, n, k, gap, a. split; [exact Hcut|]. split; [reflexivity|].
  split; [exact (block_good _ _ _ _ _ _ _ Hb Hsafe)|].
  split.
  - rewrite Hk. destruct extra; cbn in Hcount |- *; apply le_n_S; auto with arith.
  - split.
    + rewrite (width_generated _ _ _ _ _ _ _ Hcut); lia.
    + cbn [trailing]; split; [assumption|destruct extra; cbn in HE, Hn; lia].
Qed.

Lemma half_decompose n: exists a e, n=a*2+e /\ e<=1.
Proof.
  exists (n/2), (n mod 2).
  pose proof (Nat.div_mod n 2 ltac:(lia)).
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)). lia.
Qed.

Lemma positive_decompose n: 0<n -> exists b p, n=b*2+2-p /\ p<=1.
Proof.
  intros Hn. destruct (half_decompose (n-1)) as [b [e [He Hbit]]].
  exists b, (1-e). lia.
Qed.

Lemma block_exists extra L t u: safe_input extra t u ->
  exists gap a E, block extra L t u gap a E.
Proof.
  intros Hsafe. destruct (half_decompose L) as [l [q [HL Hq]]]. subst L.
  assert (Hpad:q+(1-q)=1) by lia.
  destruct extra.
  - unfold safe_input, main in Hsafe; simpl in Hsafe.
    destruct (half_decompose t) as [a [e [Ht He]]].
    destruct (positive_decompose u) as [b [p [Hu Hp]]]; try lia.
    destruct e as [|[|e]]; try lia.
    + replace t with (a*2) by lia.
      destruct p as [|[|p]]; try lia.
      * replace u with (b*2+2) by lia.
        destruct (Nat.eq_dec a 2).
        -- subst a. eexists _, _, _. eapply block_extra_four; eauto.
        -- eexists _, _, _. eapply block_extra_even_even; eauto; lia.
      * replace u with (b*2+1) by lia.
        eexists _, _, _. eapply block_extra_even_odd; eauto.
    + replace t with (a*2+1) by lia. rewrite Hu.
      eexists _, _, _. eapply block_extra_odd; eauto.
  - unfold safe_input, allowed in Hsafe; simpl in Hsafe.
    destruct (Nat.eq_dec t 0).
    + subst t. assert (Hu2:2<=u).
      { destruct u as [|[|u]]; try lia. exfalso; apply (proj2 Hsafe); reflexivity. }
      destruct (Nat.eq_dec u 2), (Nat.eq_dec u 3), (Nat.eq_dec u 5); subst;
        try solve [eexists _, _, _; first [eapply block_zero2|eapply block_zero3|eapply block_zero5]; eauto].
      destruct (half_decompose (u-2)) as [j [p [Hu Hp]]].
      replace u with (j*2+2+p) by lia.
      eexists _, _, _. eapply block_zero; eauto; lia.
    + destruct (le_dec u 2).
      * destruct (half_decompose ((l*2+q)*3+t+7)) as [s [e [Hs He]]].
        eexists _, _, _. eapply block_short with (s:=s) (e:=e); eauto; lia.
      * destruct (positive_decompose u) as [b [p [Hu Hp]]]; try lia.
        destruct (Nat.eq_dec t 1).
        -- subst t. destruct p as [|[|p]]; try lia.
           ++ replace u with (b*2+2) by lia.
              eexists _, _, _. eapply block_one_even; eauto.
           ++ replace u with (b*2+1) by lia.
              eexists _, _, _. eapply block_one_odd; eauto.
        -- destruct (half_decompose t) as [a [e [Ht He]]].
           rewrite Ht, Hu. destruct (Nat.eq_dec (a+p) e).
           ++ eexists _, _, _. eapply block_full; eauto; lia.
           ++ eexists _, _, _. eapply block_split; eauto; lia.
Qed.

Inductive consume : bool -> nat -> nat -> list cell -> list cell -> Prop :=
| consume_one t u r: consume false t u ((t,u)::r) r
| consume_two t u r: consume true t u (danger::(t,u)::r) r.

Lemma consume_cut extra t u l r: consume extra t u l r -> safe_input extra t u ->
  cut l r (t+u+(if extra then 3 else 1)) (if extra then 2 else 1).
Proof.
  intros H; destruct H; cbn [safe_input]; intros Hsafe.
  - apply cut_one; tauto.
  - replace (t+u+3) with (2+weight (t,u)) by (unfold weight; simpl; lia).
    apply cut_two; assumption.
Qed.

Lemma consume_exists l: good l -> 2<=length l ->
  exists extra t u r, consume extra t u l r /\ safe_input extra t u.
Proof.
  intros Hl Hlen. destruct (cut_exists _ Hl Hlen) as [r [n [k Hcut]]].
  destruct Hcut as [[t u] r Hp Hne|[t u] r Hp].
  - exists false, t, u, r; split; [constructor|split; assumption].
  - exists true, t, u, r; split; [constructor|assumption].
Qed.

Definition block_step f g := exists extra t u r gap a E,
  consume extra t u (cells f) r /\ safe_input extra t u /\
  block extra (width f) t u gap a E /\
  g=Frame (r++(t+u+(if extra then 3 else 1)+trailing f,gap)::a) E.

Lemma block_step_exists f: good (cells f) -> 2<=length (cells f) ->
  exists g, block_step f g.
Proof.
  intros H Hlen. destruct (consume_exists _ H Hlen) as [extra [t [u [r [Hc Hsafe]]]]].
  destruct (block_exists _ (width f) _ _ Hsafe) as [gap [a [E Hb]]].
  eexists. exists extra, t, u, r, gap, a. exists E. repeat split; eauto.
Qed.

Lemma block_step_emission f g: block_step f g -> 16<=width f -> emission f g.
Proof.
  intros [extra [t [u [r [gap [a [E [Hc [Hs [Hb ->]]]]]]]]]] HL.
  eapply block_emission with (k:=if extra then 2 else 1) (extra:=extra) (t:=t) (u:=u);
    eauto using consume_cut.
Qed.

Lemma history_width f0 f1 f2 f3: history f0 f1 f2 f3 -> 16<=width f3.
Proof. intros [[_ [H01 _]] [_ [H12 _]] [_ [H23 _]] H0 _ _ _]; lia. Qed.

Theorem history_progress f0 f1 f2 f3: history f0 f1 f2 f3 ->
  exists f4, block_step f3 f4 /\ history f1 f2 f3 f4.
Proof.
  intros H. destruct (history_ready _ _ _ _ H) as [Hgood Hlen].
  destruct (block_step_exists _ Hgood ltac:(lia)) as [f4 Hstep].
  exists f4; split; [assumption|].
  apply (history_next _ _ _ _ _ H).
  apply block_step_emission; auto. exact (history_width _ _ _ _ H).
Qed.

End Queue.

(* SOC51_Semantics *)
Module Q := Queue.

Lemma digits_unique n v w: Digits n v w -> forall a, Digits n v a -> w=a.
Proof.
  intro H; induction H; intros a Ha; inversion Ha; subst; try reflexivity;
    try (exfalso; lia); f_equal; apply IHDigits; match goal with
    H:Digits _ _ _ |- _ => applys_eq H; flia end.
Qed.

Lemma digits_app n v w j u a: Digits n v w -> Digits j u a ->
  Digits (n+j) (v+2^n*u) (w++a).
Proof.
  intros H Ha; induction H.
  - cbn; replace (u+0) with u by lia; assumption.
  - replace (v*2+2^(1+n)*u) with ((v+2^n*u)*2) by (cbn [Nat.add Nat.pow]; nia).
    apply digits_zero; assumption.
  - replace (v*2+1+2^(1+n)*u) with ((v+2^n*u)*2+1) by (cbn [Nat.add Nat.pow]; nia).
    apply digits_one; assumption.
Qed.

Lemma digits_append_one n v w: Digits n v w ->
  Digits (n+1) (v+2^n) (w++d).
Proof.
  intro H. replace (v+2^n) with (v+2^n*1) by lia.
  apply digits_app; [assumption|apply (digits_one 0 0 []), digits_nil].
Qed.

(* Drop a high bit, insert a low 1, and keep the complete physical tail. *)
Lemma frame_zero_word n v w r: Digits n v w ->
  LC (n+1) 0 ldh <| w *> z *> r -->+
  LC (n+1) 0 ldh <| d *> w *> [1] *> r.
Proof.
  intro H. pose proof (digits_bound _ _ _ H) as Hv.
  destruct (frame_zero (n+1) v (w++z) r (digits_append_zero _ _ _ H)
    ltac:(rewrite pow2_S; lia)) as [a [Ha Hrun]].
  assert (Heq:a=d++w).
  { eapply digits_unique; [exact Ha|]. replace (n+1) with (1+n) by lia.
    apply digits_one; assumption. }
  rewrite Heq, !Str_app_assoc in Hrun; exact Hrun.
Qed.

Lemma frame_one_word n v w r: Digits n v w ->
  LC (n+1) 0 ldh <| w *> d *> z *> r -->+
  LC (n+1) 0 ldh <| d *> w *> z *> [1] *> r.
Proof.
  intro H. pose proof (digits_bound _ _ _ H) as Hv.
  destruct (frame_one (n+1) (v+2^n) (w++d) r (digits_append_one _ _ _ H)
    ltac:(rewrite pow2_S; lia)) as [a [Ha Hrun]].
  replace ((v+2^n)*2+1-2^(n+1)) with (v*2+1) in Ha by (rewrite pow2_S; lia).
  assert (Heq:a=d++w).
  { eapply digits_unique; [exact Ha|]. replace (n+1) with (1+n) by lia.
    apply digits_one; assumption. }
  rewrite Heq, !Str_app_assoc in Hrun; exact Hrun.
Qed.

Lemma frame_D_word n v w r: Digits n v w ->
  LC (n+1) 0 ldh <| w *> d *> r -->+
  LC (n+1) (v*2+1) ldh <* ld0 <* [1]^^(4+(n+1)*3) {{D}}> r.
Proof.
  intro H.
  pose proof (frame_to_D (n+1) (v+2^n) (w++d) r
    (digits_append_one _ _ _ H) ltac:(rewrite pow2_S; lia)) as Hrun.
  replace ((v+2^n)*2+1-2^(n+1)) with (v*2+1) in Hrun by (rewrite pow2_S; lia).
  rewrite Str_app_assoc in Hrun; exact Hrun.
Qed.

Lemma frame_ones t n v w r: Digits n v w ->
  LC (n+t) 0 ldh <| w *> d^^t *> z *> r -->*
  LC (n+t) 0 ldh <| d^^t *> w *> z *> [1]^^t *> r.
Proof.
  revert n v w r; induction t; intros n v w r H.
  - cbn [lpow]; finish.
  - pose proof (digits_append_one _ _ _ H) as Htop.
    pose proof (IHt (n+1) (v+2^n) (w++d) r Htop) as Hrun.
    rewrite !Str_app_assoc in Hrun.
    replace (n+1+t) with (n+S t) in Hrun by lia.
    cbn [lpow]. eapply evstep_trans; [exact Hrun|].
    pose proof (digits_app _ _ _ _ _ _ (digits_ones t) H) as Hlow.
    pose proof (frame_one_word _ _ _ ([1]^^t *> r) Hlow) as Hstep.
    rewrite Str_app_assoc in Hstep.
    replace (t+n+1) with (n+S t) in Hstep by lia.
    eapply evstep_trans; [apply progress_evstep; exact Hstep|].
    finish; rewrite !Str_app_assoc; reflexivity.
Qed.

Lemma frame_zeros u n v w r: Digits n v w ->
  LC (n+u) 0 ldh <| w *> z^^u *> r -->*
  LC (n+u) 0 ldh <| d^^u *> w *> [1]^^u *> r.
Proof.
  revert n v w r; induction u; intros n v w r H.
  - cbn [lpow]; finish.
  - pose proof (digits_append_zero _ _ _ H) as Htop.
    pose proof (IHu (n+1) v (w++z) r Htop) as Hrun.
    rewrite !Str_app_assoc in Hrun.
    replace (n+1+u) with (n+S u) in Hrun by lia.
    cbn [lpow]. eapply evstep_trans; [exact Hrun|].
    pose proof (digits_app _ _ _ _ _ _ (digits_ones u) H) as Hlow.
    pose proof (frame_zero_word _ _ _ ([1]^^u *> r) Hlow) as Hstep.
    rewrite Str_app_assoc in Hstep.
    replace (u+n+1) with (n+S u) in Hstep by lia.
    eapply evstep_trans; [apply progress_evstep; exact Hstep|].
    finish; rewrite !Str_app_assoc; reflexivity.
Qed.

Lemma front_to_D t u j v w r: Digits j v w ->
  let L:=j+1+u+t in let K:=(v+1)*2^(1+u+t)-1 in
  LC L 0 ldh <| w *> d *> z^^u *> d^^t *> z *> r -->+
  LC L K ldh <* ld0 <* [1]^^(4+L*3) {{D}}>
    [1]^^u *> z *> [1]^^t *> r.
Proof.
  intro H; cbn zeta.
  pose proof (digits_append_one _ _ _ H) as Hwd.
  pose proof (digits_app _ _ _ _ _ _ Hwd (digits_zeros u)) as Hmid.
  pose proof (frame_ones t _ _ _ r Hmid) as Hfirst.
  rewrite !Str_app_assoc in Hfirst.
  eapply evstep_progress_trans; [exact Hfirst|].
  pose proof (digits_app _ _ _ _ _ _ (digits_ones t) Hwd) as Hprefix.
  pose proof (frame_zeros u _ _ _ (z *> [1]^^t *> r) Hprefix) as Hsecond.
  rewrite !Str_app_assoc in Hsecond.
  replace (t+(j+1)+u) with (j+1+u+t) in Hsecond by lia.
  eapply evstep_progress_trans; [exact Hsecond|].
  pose proof (digits_app _ _ _ _ _ _ (digits_ones (u+t)) H) as Hlow.
  pose proof (frame_D_word _ _ _ ([1]^^u *> z *> [1]^^t *> r) Hlow) as Hlast.
  rewrite Str_app_assoc, lpow_add, Str_app_assoc in Hlast.
  replace (u+t+j+1) with (j+1+u+t) in Hlast by lia.
  replace ((2^(u+t)-1+2^(u+t)*v)*2+1) with ((v+1)*2^(1+u+t)-1) in Hlast by
    (replace (1+u+t) with (1+(u+t)) by lia;
      pose proof (Nat.pow_nonzero 2 (u+t)); cbn [Nat.add Nat.pow]; nia).
  exact Hlast.
Qed.

Lemma digits_shift_ones r j v w: Digits j v w ->
  Digits (j+r) ((v+1)*2^r-1) (d^^r++w).
Proof.
  intro H. replace (j+r) with (r+j) by lia.
  replace ((v+1)*2^r-1) with (2^r-1+2^r*v) by
    (pose proof (Nat.pow_nonzero 2 r); nia).
  apply digits_app; auto using digits_ones.
Qed.

Lemma zero_blank: z *> 0inf=0inf.
Proof. solve_const0_eq. Qed.

Lemma normal_front_to_D t u j v w: Digits j v w ->
  let L:=j+1+u+t in let K:=(v+1)*2^(1+u+t)-1 in
  LC L 0 ldh <| w *> d *> z^^u *> d^^t *> 0inf -->+
  LC L K ldh <* ld0 <* [1]^^(4+L*3) {{D}}>
    [1]^^u *> z *> [1]^^t *> 0inf.
Proof.
  intro H. pose proof (front_to_D t u _ _ _ 0inf H) as Hrun.
  rewrite zero_blank in Hrun; exact Hrun.
Qed.

(* The exceptional 01 prefix preserves the width and leaves RC(4).
   It is not silently treated as an ordinary capacity-bounded frame. *)
Lemma danger_frame j v w: Digits j v w ->
  LC (j+2) 0 ldh <| w *> d *> z *> 0inf -->+
  LC (j+2) 0 ldh <| d^^2 *> w *> RC 4.
Proof.
  intro H. pose proof (normal_front_to_D 0 1 _ _ _ H) as Hfirst.
  cbn zeta in Hfirst; cbn [lpow] in Hfirst.
  rewrite !Str_app_assoc in Hfirst.
  change (LC (j+1+1+0) 0 ldh <| w *> d *> z *> 0inf -->+
    LC (j+1+1+0) ((v+1)*2^2-1) ldh <* ld0 <*
      [1]^^(4+(j+1+1+0)*3) {{D}}> [1] *> z *> 0inf) in Hfirst.
  rewrite zero_blank in Hfirst |- *.
  replace (j+1+1+0) with (j+2) in Hfirst by lia.
  pose proof (digits_shift_ones 2 _ _ _ H) as HK.
  eapply progress_evstep_trans; [exact Hfirst|].
  pose proof (D_overcapacity_tail _ _ _ ldh HK) as Hlast.
  rewrite Str_app_assoc in Hlast; exact Hlast.
Qed.

Lemma extra_front_to_D t u j v w: Digits j v w ->
  let L:=j+3+u+t in let K:=(v+1)*2^(3+u+t)-1 in
  LC L 0 ldh <| w *> d *> z^^u *> d^^t *> d *> z *> 0inf -->+
  LC L K ldh <* ld0 <* [1]^^(4+L*3) {{D}}>
    [1]^^u *> z *> [1]^^t *> z *> d *> 0inf.
Proof.
  intro H; cbn zeta.
  pose proof (digits_app _ _ _ _ _ _ (digits_append_one _ _ _ H) (digits_zeros u)) as Hmid.
  pose proof (digits_app _ _ _ _ _ _ Hmid (digits_ones t)) as Hhigh.
  pose proof (danger_frame _ _ _ Hhigh) as Hfirst.
  rewrite !Str_app_assoc in Hfirst.
  replace (j+1+u+t+2) with (j+3+u+t) in Hfirst by lia.
  eapply progress_evstep_trans; [exact Hfirst|].
  pose proof (front_to_D t u _ _ _ (z *> d *> 0inf)
    (digits_shift_ones 2 _ _ _ H)) as Hlast.
  rewrite !Str_app_assoc in Hlast.
  replace (j+2+1+u+t) with (j+3+u+t) in Hlast by lia.
  replace (((v+1)*2^2-1+1)*2^(1+u+t)-1) with ((v+1)*2^(3+u+t)-1) in Hlast by
    (replace (3+u+t) with (2+(1+u+t)) by lia;
      rewrite (Nat.pow_add_r 2 2 (1+u+t)); cbn [Nat.pow]; nia).
  apply progress_evstep; exact Hlast.
Qed.

(* The queue stores high bits first, whereas the physical right-hand digits
   are low bits first.  The extra leading 1 in the queue is virtual. *)
Fixpoint runs_word (l:list Q.cell) E : list Sym :=
  match l with
  | [] => d^^E
  | (t,u)::r => runs_word r E ++ z^^u ++ d^^(t+1)
  end.

Fixpoint runs_value (l:list Q.cell) E :=
  match l with
  | [] => 2^E-1
  | (t,u)::r => runs_value r E+2^(Q.mass r+E+u)*(2^(t+1)-1)
  end.

Definition frame_word f :=
  match Q.cells f with
  | [] => d^^(Q.trailing f-1)
  | (t,u)::r => runs_word r (Q.trailing f) ++ z^^u ++ d^^t
  end.
Definition config f := LC (Q.width f) 0 ldh <| frame_word f *> 0inf.

Lemma digits_runs n v w u t: Digits n v w ->
  Digits (n+u+t) (v+2^(n+u)*(2^t-1)) (w++z^^u++d^^t).
Proof.
  intro H. pose proof (digits_app _ _ _ _ _ _ H (digits_zeros u)) as Hz.
  replace (v+2^n*0) with v in Hz by lia.
  pose proof (digits_app _ _ _ _ _ _ Hz (digits_ones t)) as Hd.
  rewrite <-app_assoc in Hd; exact Hd.
Qed.

Lemma runs_value_digits l E: Digits (Q.mass l+E) (runs_value l E) (runs_word l E).
Proof.
  induction l as [|[t u] r IH].
  - apply digits_ones.
  - cbn [Q.mass runs_word runs_value]; unfold Q.weight; cbn [fst snd].
    replace (t+u+1+Q.mass r+E) with (Q.mass r+E+u+(t+1)) by lia.
    exact (digits_runs _ _ _ u (t+1) IH).
Qed.

Lemma runs_digits l E: exists v, Digits (Q.mass l+E) v (runs_word l E).
Proof. eexists; apply runs_value_digits. Qed.

Lemma frame_digits f: Q.cells f<>[] ->
  exists v, Digits (Q.width f) v (frame_word f).
Proof.
  destruct f as [[|[t u] r] E]; [contradiction|intros _].
  destruct (runs_digits r E) as [v Hv].
  exists (v+2^(Q.mass r+E+u)*(2^t-1)).
  unfold Q.width; cbn [Q.cells Q.trailing Q.mass frame_word]; unfold Q.weight; cbn [fst snd].
  replace (t+u+1+Q.mass r+E-1) with (Q.mass r+E+u+t) by lia.
  exact (digits_runs _ _ _ u t Hv).
Qed.

Lemma runs_frame l E: l<>[] ->
  runs_word l E=frame_word (Q.Frame l E)++d.
Proof.
  destruct l as [|[t u] r]; [contradiction|intros _].
  cbn [runs_word frame_word Q.cells Q.trailing].
  rewrite lpow_add; cbn [lpow]; rewrite app_nil_r, !app_assoc; reflexivity.
Qed.

Lemma frame_front t u r E: r<>[] ->
  frame_word (Q.Frame ((t,u)::r) E) =
    frame_word (Q.Frame r E)++d++z^^u++d^^t.
Proof.
  intros Hr. cbn [frame_word Q.cells Q.trailing].
  rewrite (runs_frame r E Hr), !app_assoc; reflexivity.
Qed.

Lemma frame_extra_front t u r E: r<>[] ->
  frame_word (Q.Frame (Q.danger::(t,u)::r) E) =
    frame_word (Q.Frame r E)++d++z^^u++d^^t++d++z.
Proof.
  intro Hr. unfold Q.danger.
  rewrite frame_front by discriminate.
  rewrite frame_front by assumption.
  cbn [lpow]; rewrite !app_nil_r, !app_assoc; reflexivity.
Qed.

Lemma runs_word_app l r E:
  runs_word (l++r) E=runs_word r E++runs_word l 0.
Proof.
  induction l as [|[t u] l IH]; cbn [List.app runs_word lpow].
  - rewrite app_nil_r; reflexivity.
  - rewrite IH, !app_assoc; reflexivity.
Qed.

Lemma runs_word_tail l E:
  runs_word l E=d^^E++runs_word l 0.
Proof.
  induction l as [|[t u] l IH]; cbn [runs_word lpow].
  - rewrite app_nil_r; reflexivity.
  - rewrite IH, !app_assoc; reflexivity.
Qed.

Lemma frame_word_app l r E: l<>[] ->
  frame_word (Q.Frame (l++r) E)=runs_word r E++frame_word (Q.Frame l 0).
Proof.
  destruct l as [|[t u] l]; [contradiction|intros _].
  cbn [List.app frame_word Q.cells Q.trailing].
  rewrite runs_word_app, !app_assoc; reflexivity.
Qed.

Lemma frame_word_tail l E: l<>[] ->
  frame_word (Q.Frame l E)=d^^E++frame_word (Q.Frame l 0).
Proof.
  destruct l as [|[t u] l]; [contradiction|intros _].
  cbn [frame_word Q.cells Q.trailing].
  rewrite runs_word_tail, !app_assoc; reflexivity.
Qed.

Definition patch_word gap a E := runs_word a E++z^^gap++d.
Definition patch_width gap a E := gap+Q.mass a+E+1.
Definition patch_value gap a E := runs_value a E+2^(Q.mass a+E+gap).

Lemma patch_digits gap a E:
  Digits (patch_width gap a E) (patch_value gap a E) (patch_word gap a E).
Proof.
  pose proof (digits_runs _ _ _ gap 1 (runs_value_digits a E)) as H.
  change (2^1-1) with 1%nat in H. rewrite Nat.mul_1_r in H.
  change (d^^1) with d in H.
  unfold patch_width, patch_value, patch_word.
  replace (gap+Q.mass a+E+1) with (Q.mass a+E+gap+1) by lia; exact H.
Qed.

Lemma patch_RC gap a E k:
  patch_word gap a E *> RC k = RC (k*2^(patch_width gap a E)+patch_value gap a E).
Proof.
  rewrite (digits_RC _ _ _ (patch_digits gap a E)). f_equal; lia.
Qed.

Lemma frame_generated r E n gap a E': r<>[] ->
  frame_word (Q.Frame (r++(n+E,gap)::a) E') =
    patch_word gap a E'++d^^n++frame_word (Q.Frame r E).
Proof.
  intro Hr. rewrite frame_word_app by assumption.
  unfold patch_word; cbn [runs_word]. rewrite (frame_word_tail r E Hr).
  replace (n+E+1) with (1+n+E) by lia.
  rewrite !lpow_add; cbn [lpow]; rewrite !app_nil_r, !app_assoc; reflexivity.
Qed.

Lemma consume_width extra t u l r E: Q.consume extra t u l r -> r<>[] ->
  Q.width (Q.Frame l E)=Q.width (Q.Frame r E)+t+u+(if extra then 3 else 1).
Proof.
  intros H Hr. destruct H; destruct r as [|[x y] r]; try contradiction;
    unfold Q.width; cbn [Q.cells Q.trailing Q.mass];
    unfold Q.weight, Q.danger; cbn [fst snd]; lia.
Qed.

Definition D_config (extra:bool) L k t u :=
  LC L k ldh <* ld0 <* [1]^^(4+L*3) {{D}}>
    [1]^^u *> z *> [1]^^t *> (if extra then z *> d *> 0inf else 0inf).

Lemma consume_to_D extra t u l r E v:
  Q.consume extra t u l r -> r<>[] ->
  Digits (Q.width (Q.Frame r E)) v (frame_word (Q.Frame r E)) ->
  config (Q.Frame l E) -->+
  D_config extra (Q.width (Q.Frame l E))
    ((v+1)*2^(t+u+(if extra then 3 else 1))-1) t u.
Proof.
  intros H Hr Hd. pose proof (consume_width _ _ _ _ _ E H Hr) as HW.
  destruct H; unfold config, D_config.
  - rewrite frame_front by assumption. rewrite !Str_app_assoc, HW.
    replace (Q.width (Q.Frame r E)+t+u+1) with
      (Q.width (Q.Frame r E)+1+u+t) by lia.
    replace (t+u+1) with (1+u+t) by lia.
    apply normal_front_to_D; assumption.
  - rewrite frame_extra_front by assumption. rewrite !Str_app_assoc, HW.
    replace (Q.width (Q.Frame r E)+t+u+3) with
      (Q.width (Q.Frame r E)+3+u+t) by lia.
    replace (t+u+3) with (3+u+t) by lia.
    apply extra_front_to_D; assumption.
Qed.

(* This interface concerns only the D return; the prefix rotation and the
   old suffix/new block concatenation are proved here, not assumed. *)
Definition D_returns extra L t u gap a E := forall k, k<2^L ->
  D_config extra L k t u -->*
  LC (L+patch_width gap a E) 0 ldh <| patch_word gap a E *> RC k.

Lemma consume_generated_width extra t u l r E gap a E':
  Q.consume extra t u l r -> r<>[] ->
  Q.width (Q.Frame (r++(t+u+(if extra then 3 else 1)+E,gap)::a) E') =
    Q.width (Q.Frame l E)+patch_width gap a E'.
Proof.
  intros Hc Hr. pose proof (consume_width _ _ _ _ _ E Hc Hr) as HW.
  assert (HM:0<Q.mass r).
  { pose proof (Q.length_mass r). destruct r; cbn in *; contradiction || lia. }
  unfold Q.width in HW |- *; cbn [Q.cells Q.trailing] in HW |- *.
  rewrite Q.mass_app; cbn [Q.mass]; unfold Q.weight, patch_width; cbn [fst snd]; lia.
Qed.

Lemma emission_run extra t u l r E gap a E':
  Q.consume extra t u l r -> r<>[] ->
  D_returns extra (Q.width (Q.Frame l E)) t u gap a E' ->
  config (Q.Frame l E) -->+
  config (Q.Frame (r++(t+u+(if extra then 3 else 1)+E,gap)::a) E').
Proof.
  intros Hc Hr Hreturn.
  destruct (frame_digits (Q.Frame r E) Hr) as [v Hv].
  pose proof (consume_width _ _ _ _ _ E Hc Hr) as HW.
  set (n:=t+u+(if extra then 3 else 1)).
  assert (HW':Q.width (Q.Frame r E)+n=Q.width (Q.Frame l E)) by (unfold n; lia).
  pose proof (digits_shift_ones n _ _ _ Hv) as HK.
  rewrite HW' in HK.
  eapply progress_evstep_trans; [eapply consume_to_D; eassumption|].
  eapply evstep_trans; [apply Hreturn, (digits_bound _ _ _ HK)|].
  pose proof (digits_RC _ _ _ HK 0) as Hword.
  rewrite Nat.mul_0_r, Nat.add_0_r, Str_app_assoc in Hword.
  change (RC 0) with 0inf in Hword.
  fold n. rewrite <-Hword.
  pose proof (consume_generated_width _ _ _ _ _ E gap a E' Hc Hr) as HG.
  fold n in HG. unfold config; rewrite HG.
  rewrite frame_generated by assumption.
  rewrite !Str_app_assoc. unfold patch_width, n.
  applys_eq evstep_refl; flia.
Qed.

Lemma D_return_arithmetic extra L t u gap a E s v:
  s=patch_width gap a E -> patch_value gap a E=2^(s-1)+v ->
  (forall k, k<2^L -> D_config extra L k t u -->*
    LC (L+s) 0 ldh <| RC (k*2^s+2^(s-1)+v)) ->
  D_returns extra L t u gap a E.
Proof.
  intros -> Hv Hrun k Hk. rewrite patch_RC, Hv.
  replace (k*2^(patch_width gap a E)+(2^(patch_width gap a E-1)+v)) with
    (k*2^(patch_width gap a E)+2^(patch_width gap a E-1)+v) by lia.
  apply Hrun; assumption.
Qed.

Lemma D_zero_numeric l q h k j p:
  q+h=1%nat -> 0<l*2+q -> k<2^(l*2+q) -> p<=1 ->
  let s:=l*3+2+q*2+j in
  D_config false (l*2+q) k 0 (2+j*2+p) -->*
  LC (l*2+q+s) 0 ldh <| RC (k*2^s+2^(s-1)+((2^j+p)*(1+h)+h)).
Proof.
  intros Hqh HL Hk Hp; cbn zeta.
  unfold D_config. change (z *> [1]^^0 *> 0inf) with (z *> 0inf).
  rewrite zero_blank.
  pose proof (D_zero_finish l q h k j p ldh Hqh HL Hk Hp) as H.
  cbn zeta in H.
  replace (k*2^(l*3+2+q*2+j)+2^(l*3+2+q*2+j-1)+((2^j+p)*(1+h)+h)) with
    (k*2^(l*3+2+q*2+j)+2^(l*3+2+q*2+j-1)+(2^j+p)*(1+h)+h) by lia.
  exact H.
Qed.

Lemma D_block_zero2 l q h: q+h=1%nat -> 16<=l*2+q ->
  D_returns false (l*2+q) 0 2 ((l+q)*3-1) [] (1+h).
Proof.
  intros Hqh HL.
  eapply D_return_arithmetic with (s:=l*3+2+q*2+0) (v:=(2^0+0)*(1+h)+h).
  - unfold patch_width; cbn [Q.mass]; lia.
  - unfold patch_value; cbn [runs_value Q.mass].
    replace (0+(1+h)+((l+q)*3-1)) with (l*3+2+q*2+0-1) by lia.
    destruct h as [|[|h]]; cbn [Nat.add Nat.pow]; lia.
  - intros k Hk. apply (D_zero_numeric l q h k 0 0); assumption || lia.
Qed.

Lemma D_block_zero3 l q h: q+h=1%nat -> 16<=l*2+q ->
  D_returns false (l*2+q) 0 3 ((l+q)*3-2) [Q.danger] h.
Proof.
  intros Hqh HL.
  eapply D_return_arithmetic with (s:=l*3+2+q*2+0) (v:=(2^0+1)*(1+h)+h).
  - unfold patch_width, Q.danger; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value, Q.danger; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (0+1+1+0+h+((l+q)*3-2)) with (l*3+2+q*2+0-1) by lia.
    destruct h as [|[|h]]; cbn [Nat.add Nat.pow]; lia.
  - intros k Hk. apply (D_zero_numeric l q h k 0 1); assumption || lia.
Qed.

Lemma D_block_zero5 l q h: q+h=1%nat -> 16<=l*2+q ->
  D_returns false (l*2+q) 0 5 ((l+q)*3-1) [] (2+h).
Proof.
  intros Hqh HL.
  eapply D_return_arithmetic with (s:=l*3+2+q*2+1) (v:=(2^1+1)*(1+h)+h).
  - unfold patch_width; cbn [Q.mass]; lia.
  - unfold patch_value; cbn [runs_value Q.mass].
    replace (0+(2+h)+((l+q)*3-1)) with (l*3+2+q*2+1-1) by lia.
    destruct h as [|[|h]]; cbn [Nat.add Nat.pow]; lia.
  - intros k Hk. apply (D_zero_numeric l q h k 1 1); assumption || lia.
Qed.

Lemma D_block_zero l q h j p: q+h=1%nat -> 16<=l*2+q -> p<=1 -> 1+p<=j ->
  D_returns false (l*2+q) 0 (j*2+2+p) ((l+q)*3-1) [(0%nat,j-p)] (p+h).
Proof.
  intros Hqh HL Hp Hj.
  eapply D_return_arithmetic with (s:=l*3+2+q*2+j) (v:=(2^j+p)*(1+h)+h).
  - unfold patch_width; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (0+(j-p)+1+0+(p+h)+((l+q)*3-1)) with (l*3+2+q*2+j-1) by lia.
    replace (0+(p+h)+(j-p)) with (j+h) by lia.
    destruct p as [|[|p]], h as [|[|h]]; try lia;
      cbn [Nat.add Nat.pow]; rewrite ?Nat.add_0_r, ?pow2_S; lia.
  - intros k Hk. replace (j*2+2+p) with (2+j*2+p) by lia.
    apply D_zero_numeric; assumption || lia.
Qed.

Lemma D_block_short L t u s e:
  0<L -> (u=2%nat -> 4<=t) -> 0<t -> (u=1%nat \/ u=2%nat) ->
  e<=1 -> L*3+t+7=s*2+e ->
  D_returns false L t u (s-1-(e+u-1)) [] (e+u-1).
Proof.
  intros HL Hshort Ht Hu He Hs.
  eapply D_return_arithmetic with (s:=s) (v:=2^(e+u-1)-1).
  - unfold patch_width; cbn [Q.mass]; destruct Hu as [->| ->]; lia.
  - unfold patch_value; cbn [runs_value Q.mass].
    replace (0+(e+u-1)+(s-1-(e+u-1))) with (s-1) by
      (destruct Hu as [->| ->]; lia).
    lia.
  - intros k Hk. destruct Hu as [->| ->].
    + destruct e as [|[|e]]; try lia.
      * apply (D_one_finish L k t s 0 ldh); assumption || lia.
      * apply (D_one_finish L k t s 1 ldh); assumption || lia.
    + replace (2^(e+2-1)-1) with (e*2+1) by
        (destruct e as [|[|e]]; [reflexivity|reflexivity|lia]).
      replace (k*2^s+2^(s-1)+(e*2+1)) with (k*2^s+2^(s-1)+e*2+1) by lia.
      apply D_two_finish; assumption || lia.
Qed.

Lemma D_block_one_odd l q h b: q+h=1%nat -> 16<=l*2+q ->
  D_returns false (l*2+q) 1 (3+b*2) ((l+q)*3) [] (b+2+h).
Proof.
  intros Hqh HL. set (s:=l*3+2+q*2+(b+1+1)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^(b+1)-1)*2+1)*(1+h)+h).
  - unfold patch_width, s; cbn [Q.mass]; lia.
  - unfold patch_value; cbn [runs_value Q.mass].
    replace (0+(b+2+h)+(l+q)*3) with (s-1) by (unfold s; lia).
    destruct h as [|[|h]]; try lia; rewrite !Nat.pow_add_r; cbn [Nat.pow];
      pose proof (Nat.pow_nonzero 2 b); nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^(b+1)-1)*2+1)*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^(b+1)-1)*2+1)*(1+h)+h) by lia.
    apply D_odd_one_finish; assumption || lia.
Qed.

Lemma D_block_one_even l q h b: q+h=1%nat -> 16<=l*2+q -> 1<=b ->
  D_returns false (l*2+q) 1 (4+b*2) ((l+q)*3-1) [(0%nat,b-1);Q.danger] h.
Proof.
  intros Hqh HL Hb. set (s:=l*3+2+q*2+(b+1)).
  eapply D_return_arithmetic with (s:=s) (v:=(2^(b+1)+2)*(1+h)+h).
  - unfold patch_width, Q.danger, s; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value, Q.danger; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (0+(b-1)+1+(0+1+1+0)+h+((l+q)*3-1)) with (s-1) by (unfold s; lia).
    replace (0+1+1+0+h+(b-1)) with (b+1+h) by lia.
    destruct h as [|[|h]]; try lia; rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+((2^(b+1)+2)*(1+h)+h)) with
      (k*2^s+2^(s-1)+(2^(b+1)+2)*(1+h)+h) by lia.
    apply D_even_one_finish; assumption || lia.
Qed.

Lemma D_formula_change extra L k t u s v h t' u' s' v':
  t=t' -> u=u' -> s=s' -> v=v' ->
  (D_config extra L k t' u' -->*
    LC (L+s') 0 ldh <| RC (k*2^s'+2^(s'-1)+v'*(1+h)+h)) ->
  D_config extra L k t u -->*
    LC (L+s) 0 ldh <| RC (k*2^s+2^(s-1)+v*(1+h)+h).
Proof. intros -> -> -> -> H; exact H. Qed.

Lemma D_general_numeric l q h k a b p e:
  q+h=1%nat -> 0<l*2+q -> k<2^(l*2+q) -> p<=1 -> e<=1 -> 1<=a -> 1<=b ->
  (a=1%nat -> e=1%nat -> p=0%nat -> 2<=b) ->
  let s:=l*3+2+q*2+(a+b+1) in
  D_config false (l*2+q) k (a*2+e) (b*2+2-p) -->*
  LC (l*2+q+s) 0 ldh <|
    RC (k*2^s+2^(s-1)+((2^b-1)*2^(a+1)+(2^(1-p+e)-1))*(1+h)+h).
Proof.
  intros Hqh HL Hk Hp He Ha Hb Hex; cbn zeta.
  destruct p as [|[|p]], e as [|[|e]]; try lia;
    destruct a as [|a]; try lia; destruct b as [|b]; try lia.
  - destruct a as [|a].
    + eapply D_formula_change with (t':=2) (u':=4+b*2)
        (s':=l*3+2+q*2+(b+0+3)) (v':=(2^(b+1)-1)*4+1); [lia|lia|lia| |].
      * rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_even_two_finish; assumption || lia.
    + eapply D_formula_change with (t':=4+a*2) (u':=4+b*2)
        (s':=l*3+2+q*2+(b+(1+a)+3)) (v':=(2^(b+1)-1)*2^(1+a+2)+1); [lia|lia|lia| |].
      * rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_even_even4_finish; assumption || lia.
  - destruct a as [|a].
    + eapply D_formula_change with (t':=3) (u':=4+b*2)
        (s':=l*3+2+q*2+(b+0+3)) (v':=(2^(b+1)-1)*4+3); [lia|lia|lia| |].
      * rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_even_three_finish; assumption || lia.
    + eapply D_formula_change with (t':=5+a*2) (u':=4+b*2)
        (s':=l*3+2+q*2+(b+(1+a)+3)) (v':=(2^(b+1)-1)*2^(1+a+2)+3); [lia|lia|lia| |].
      * rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_even_odd5_finish; assumption || lia.
  - destruct a as [|[|a]].
    + eapply D_formula_change with (t':=2) (u':=1+S b*2)
        (s':=l*3+2+q*2+(S b+2)) (v':=(2^S b-1)*4); [lia|lia|lia| |].
      * cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_odd_two_finish; assumption || lia.
    + eapply D_formula_change with (t':=4) (u':=1+S b*2)
        (s':=l*3+2+q*2+(S b+3)) (v':=(2^S b-1)*8); [lia|lia|lia| |].
      * cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_odd_four_finish; assumption || lia.
    + eapply D_formula_change with (t':=6+a*2) (u':=3+b*2)
        (s':=l*3+2+q*2+(b+1+(4+a))) (v':=(2^(b+1)-1)*2^(4+a)); [lia|lia|lia| |].
      * rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
      * apply D_odd_even6_finish; assumption || lia.
  - eapply D_formula_change with (t':=3+a*2) (u':=3+b*2)
      (s':=l*3+2+q*2+(b+1+(2+a))) (v':=(2^(b+1)-1)*2^(2+a)+1); [lia|lia|lia| |].
    + rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
    + apply D_odd_odd_finish; assumption || lia.
Qed.

Lemma bit_scale b x f h: h<=1 ->
  2^(f+h)-1+2^(x+h)*(2^b-1)=((2^b-1)*2^x+(2^f-1))*(1+h)+h.
Proof.
  intros Hh. destruct h as [|[|h]]; try lia;
    rewrite !Nat.pow_add_r; cbn [Nat.pow]; pose proof (Nat.pow_nonzero 2 f); nia.
Qed.

Lemma D_block_full l q h a b p e:
  q+h=1%nat -> 16<=l*2+q -> p<=1 -> e<=1 -> 1<=a -> 1<=b -> a+p=e ->
  (a=1%nat -> e=1%nat -> p=0%nat -> 2<=b) ->
  D_returns false (l*2+q) (a*2+e) (b*2+2-p) ((l+q)*3) [] (b+a+1+h).
Proof.
  intros Hqh HL Hp He Ha Hb Hfull Hsafe.
  assert (a=1%nat /\ p=0%nat /\ e=1%nat) as [-> [-> ->]] by lia.
  set (s:=l*3+2+q*2+(1+b+1)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^b-1)*2^(1+1)+(2^(1-0+1)-1))*(1+h)+h).
  - unfold patch_width, s; cbn [Q.mass]; lia.
  - unfold patch_value; cbn [runs_value Q.mass].
    replace (0+(b+1+1+h)+(l+q)*3) with (s-1) by (unfold s; lia).
    destruct h as [|[|h]]; try lia; rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow];
      pose proof (Nat.pow_nonzero 2 b); nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^b-1)*2^(1+1)+(2^(1-0+1)-1))*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^b-1)*2^(1+1)+(2^(1-0+1)-1))*(1+h)+h) by lia.
    apply D_general_numeric; assumption || lia.
Qed.

Lemma D_block_split l q h a b p e:
  q+h=1%nat -> 16<=l*2+q -> p<=1 -> e<=1 -> 1<=a -> 1<=b -> e<a+p ->
  (a=1%nat -> e=1%nat -> p=0%nat -> 2<=b) ->
  D_returns false (l*2+q) (a*2+e) (b*2+2-p) ((l+q)*3) [(b-1,a+p-e)] (1-p+e+h).
Proof.
  intros Hqh HL Hp He Ha Hb Hsplit Hsafe. set (s:=l*3+2+q*2+(a+b+1)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^b-1)*2^(a+1)+(2^(1-p+e)-1))*(1+h)+h).
  - unfold patch_width, s; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (b-1+1) with b by lia.
    replace (b-1+(a+p-e)+1+0+(1-p+e+h)+(l+q)*3) with (s-1) by (unfold s; lia).
    replace (0+(1-p+e+h)+(a+p-e)) with (a+1+h) by lia.
    rewrite (bit_scale b (a+1) (1-p+e) h ltac:(lia)). lia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^b-1)*2^(a+1)+(2^(1-p+e)-1))*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^b-1)*2^(a+1)+(2^(1-p+e)-1))*(1+h)+h) by lia.
    apply D_general_numeric; assumption || lia.
Qed.

Lemma D_extra_odd_numeric l q h k a b p:
  q+h=1%nat -> 0<l*2+q -> k<2^(l*2+q) -> 1<=a -> 1<=b -> p<=1 ->
  let s:=l*3+2+q*2+(a+b+3) in
  D_config true (l*2+q) k (a*2+1) (b*2+2-p) -->*
  LC (l*2+q+s) 0 ldh <|
    RC (k*2^s+2^(s-1)+((2^b-1)*2^(a+3)-1)*(1+h)+h).
Proof.
  intros Hqh HL Hk Ha Hb Hp; cbn zeta.
  destruct a as [|a]; [lia|]. destruct b as [|b]; [lia|].
  destruct p as [|[|p]]; try lia.
  - eapply D_formula_change with (t':=3+a*2) (u':=4+b*2)
      (s':=l*3+2+q*2+(b+a+5)) (v':=(2^(b+1)-1)*2^(a+4)-1); [lia|lia|lia| |].
    + rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
    + apply D_extra_eo_finish; assumption || lia.
  - eapply D_formula_change with (t':=1+S a*2) (u':=3+b*2)
      (s':=l*3+2+q*2+(b+1+(1+S a)+1+1))
      (v':=(2^(b+1)-1)*2^(1+S a+2)-1); [lia|lia|lia| |].
    + rewrite !Nat.pow_add_r; cbn [Nat.add Nat.sub Nat.pow]; nia.
    + apply D_extra_oo_finish; assumption || lia.
Qed.

Lemma D_block_extra_odd l q h a b p:
  q+h=1%nat -> 16<=l*2+q -> 1<=a -> 2<=b -> p<=1 ->
  D_returns true (l*2+q) (a*2+1) (b*2+2-p) ((l+q)*3) [(b-2,1%nat)] (a+3+h).
Proof.
  intros Hqh HL Ha Hb Hp. set (s:=l*3+2+q*2+(a+b+3)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^b-1)*2^(a+3)-1)*(1+h)+h).
  - unfold patch_width, s; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (b-2+1+1+0+(a+3+h)+(l+q)*3) with (s-1) by (unfold s; lia).
    replace (b-2+1) with (b-1) by lia.
    assert (HB:2^b=2*2^(b-1)).
    { replace b with ((b-1)+1) at 1 by lia. rewrite pow2_S; lia. }
    destruct h as [|[|h]]; try lia; rewrite HB, !Nat.pow_add_r;
      cbn [Nat.add Nat.pow]; pose proof (Nat.pow_nonzero 2 a);
      pose proof (Nat.pow_nonzero 2 (b-1)); nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^b-1)*2^(a+3)-1)*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^b-1)*2^(a+3)-1)*(1+h)+h) by lia.
    apply D_extra_odd_numeric; assumption || lia.
Qed.

Lemma D_block_extra_even_odd l q h a b:
  q+h=1%nat -> 16<=l*2+q -> 1<=a -> 1<=b ->
  D_returns true (l*2+q) (a*2) (b*2+1) ((l+q)*3) [(b-1,a-1);Q.danger] h.
Proof.
  intros Hqh HL Ha Hb. set (s:=l*3+2+q*2+(a+b+1)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^b-1)*2^(a+1)+2)*(1+h)+h).
  - unfold patch_width, s, Q.danger; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value, Q.danger; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (b-1+1) with b by lia.
    replace (b-1+(a-1)+1+(0+1+1+0)+h+(l+q)*3) with (s-1) by (unfold s; lia).
    replace (0+1+1+0+h+(a-1)) with (a+1+h) by lia.
    destruct h as [|[|h]]; try lia; rewrite !Nat.pow_add_r; cbn [Nat.add Nat.pow]; nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^b-1)*2^(a+1)+2)*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^b-1)*2^(a+1)+2)*(1+h)+h) by lia.
    eapply D_formula_change with (t':=2+(a-1)*2) (u':=3+(b-1)*2)
      (s':=l*3+2+q*2+((b-1)+1+(1+(a-1))+1))
      (v':=(2^((b-1)+1)-1)*2^(1+(a-1)+1)+2); [lia|lia|unfold s; lia| |].
    + flia.
    + apply D_extra_oe_finish; assumption || lia.
Qed.

Lemma D_block_extra_four l q h b:
  q+h=1%nat -> 16<=l*2+q -> 2<=b ->
  D_returns true (l*2+q) 4 (b*2+2) ((l+q)*3) [(b,1%nat)] (1+h).
Proof.
  intros Hqh HL Hb. set (s:=l*3+2+q*2+(b+3)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^b-1)*8+5)*(1+h)+h).
  - unfold patch_width, s; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (b+1+1+0+(1+h)+(l+q)*3) with (s-1) by (unfold s; lia).
    destruct h as [|[|h]]; try lia; rewrite !Nat.pow_add_r;
      cbn [Nat.add Nat.pow]; pose proof (Nat.pow_nonzero 2 b); nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^b-1)*8+5)*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^b-1)*8+5)*(1+h)+h) by lia.
    eapply D_formula_change with (t':=4+0*2) (u':=4+(b-1)*2)
      (s':=l*3+2+q*2+((b-1)+0+4))
      (v':=(2^((b-1)+1)-1)*2^(0+3)+5); [lia|lia|unfold s; lia| |].
    + change (2^(0+3)) with 8%nat. flia.
    + apply D_extra_ee_finish; assumption || lia.
Qed.

Lemma D_block_extra_even_even l q h a b:
  q+h=1%nat -> 16<=l*2+q -> 3<=a -> 2<=b ->
  D_returns true (l*2+q) (a*2) (b*2+2) ((l+q)*3) [(b-1,a-2);Q.danger] (1+h).
Proof.
  intros Hqh HL Ha Hb. set (s:=l*3+2+q*2+(a+b+1)).
  eapply D_return_arithmetic with (s:=s) (v:=((2^b-1)*2^(a+1)+5)*(1+h)+h).
  - unfold patch_width, s, Q.danger; cbn [Q.mass]; unfold Q.weight; cbn [fst snd]; lia.
  - unfold patch_value, Q.danger; cbn [runs_value Q.mass]; unfold Q.weight; cbn [fst snd].
    replace (b-1+1) with b by lia.
    replace (b-1+(a-2)+1+(0+1+1+0)+(1+h)+(l+q)*3) with (s-1) by (unfold s; lia).
    replace (0+1+1+0+(1+h)+(a-2)) with (a+1+h) by lia.
    destruct h as [|[|h]]; try lia; rewrite !Nat.pow_add_r; cbn [Nat.add Nat.pow]; nia.
  - intros k Hk.
    replace (k*2^s+2^(s-1)+(((2^b-1)*2^(a+1)+5)*(1+h)+h)) with
      (k*2^s+2^(s-1)+((2^b-1)*2^(a+1)+5)*(1+h)+h) by lia.
    eapply D_formula_change with (t':=4+(a-2)*2) (u':=4+(b-1)*2)
      (s':=l*3+2+q*2+((b-1)+(a-2)+4))
      (v':=(2^((b-1)+1)-1)*2^((a-2)+3)+5); [lia|lia|unfold s; lia| |].
    + flia.
    + apply D_extra_ee_finish; assumption || lia.
Qed.

(* The finite prefix need not satisfy the invariant's separation cones.
   These local guards are enough for the same return table to be sound. *)
Definition local_input (extra:bool) t u :=
  if extra then 3<=t /\ 6<=u else
  0<u /\ (u=1%nat -> 0<t) /\ (u=2%nat -> t=0%nat \/ 4<=t) /\
    (t=1%nat -> 3<=u /\ u<>4%nat) /\ (t=3%nat -> u<>4%nat).

Lemma safe_local extra t u: Q.safe_input extra t u -> local_input extra t u.
Proof.
  destruct extra; unfold Q.safe_input, Q.main, Q.allowed, separated, local_input;
    cbn [fst snd].
  - lia.
  - intros [[Hu [Ht|Hsep]] Hne]; [subst t|lia].
    assert (2<=u).
    { destruct u as [|[|u]]; try lia. exfalso; apply Hne; reflexivity. }
    lia.
Qed.

Theorem block_returns_local extra L t u gap a E:
  Q.block extra L t u gap a E -> 16<=L -> local_input extra t u ->
  D_returns extra L t u gap a E.
Proof.
  intros Hblock HL Hsafe. destruct Hblock.
  all: pose proof Hsafe as Hnum; unfold local_input in Hnum.
  - apply D_block_zero2; assumption.
  - apply D_block_zero3; assumption.
  - apply D_block_zero5; assumption.
  - apply D_block_zero; assumption.
  - apply D_block_short; assumption || lia.
  - applys_eq (D_block_one_odd l q h (b-1)); flia.
  - applys_eq (D_block_one_even l q h (j-1)); flia.
  - apply D_block_full; assumption || lia.
  - apply D_block_split; assumption || lia.
  - apply D_block_extra_odd; assumption || lia.
  - apply D_block_extra_even_odd; assumption || lia.
  - apply D_block_extra_four; assumption || lia.
  - apply D_block_extra_even_even; assumption || lia.
Qed.

Theorem block_returns extra L t u gap a E:
  Q.block extra L t u gap a E -> 16<=L -> Q.safe_input extra t u ->
  D_returns extra L t u gap a E.
Proof. intros; apply block_returns_local; auto using safe_local. Qed.

Theorem block_step_spec f g: Q.block_step f g -> 16<=Q.width f ->
  3<=List.length (Q.cells f) -> config f -->+ config g.
Proof.
  destruct f as [l E].
  intros [extra [t [u [r [gap [a [E' [Hc [Hsafe [Hblock ->]]]]]]]]]] HL Hlen.
  cbn [Q.cells Q.trailing] in *.
  eapply emission_run; [exact Hc| |apply block_returns; eassumption].
  intro Hr; subst r; inversion Hc; subst; cbn in Hlen; lia.
Qed.

Theorem history_nonhalt f0 f1 f2 f3: Q.history f0 f1 f2 f3 ->
  ~halts tm (config f3).
Proof.
  intro H. eapply progress_nonhalt_cond with
    (P:=fun f => exists a b c, Q.history a b c f).
  - intros f [a [b [c Hhist]]].
    destruct (Q.history_progress _ _ _ _ Hhist) as [g [Hstep Hnext]].
    exists g; split; [|eauto].
    apply block_step_spec; [assumption|exact (Q.history_width _ _ _ _ Hhist)|].
    destruct (Q.history_ready _ _ _ _ Hhist); lia.
  - eauto.
Qed.

(* SOC51_Init *)
Definition initial0 := Q.Frame [(3,1%nat);Q.danger] 1.
Definition initial1 := Q.Frame [Q.danger;(6,13)] 1.
Definition initial2 := Q.Frame [(23,33);(5,2);Q.danger] 1.

Local Opaque Nat.pow.

Lemma init_frame: c0 -->* config initial0.
Proof. exact init. Qed.

Lemma initial_step0: config initial0 -->+ config initial1.
Proof.
  apply (emission_run false 3 1 [(3,1%nat);Q.danger] [Q.danger] 1 13 [] 1).
  - constructor.
  - discriminate.
  - apply (D_block_short 7 3 1 15 1); lia.
Qed.

(* This one early event consumes both old cells.  Its remaining virtual
   word is just 1, so the ordinary nonempty-queue interface is not used. *)
Lemma initial_step1: config initial1 -->+ config initial2.
Proof.
  pose proof (extra_front_to_D 6 13 0 0 [] digits_nil) as Hfirst.
  cbn zeta in Hfirst. change (0+1)%nat with 1%nat in Hfirst.
  rewrite Nat.mul_1_l in Hfirst.
  change (0+3+13+6)%nat with 22%nat in Hfirst.
  change (3+13+6)%nat with 22%nat in Hfirst.
  eapply progress_evstep_trans; [exact Hfirst|].
  assert (Hr:D_returns true 22 6 13 33 [(5,2);Q.danger] 1).
  { apply (D_block_extra_even_odd 11 0 1 3 6); lia. }
  eapply evstep_trans; [apply Hr, (digits_bound _ _ _ (digits_ones 22))|].
  pose proof (digits_RC _ _ _ (digits_ones 22) 0) as Hw.
  rewrite Nat.mul_0_r, Nat.add_0_r in Hw.
  change (RC 0) with 0inf in Hw. rewrite <-Hw.
  apply evstep_refl.
Qed.

Theorem init_two_frames: c0 -->* config initial2.
Proof.
  eapply evstep_trans; [apply init_frame|].
  eapply evstep_trans; [apply progress_evstep, initial_step0|].
  apply progress_evstep, initial_step1.
Qed.

(* SOC51_Check *)
(* Small binary-integer checker for the finite prefix.  Certificates only
   select one of the already proved block constructors; they add no rules. *)

Module Check.
Open Scope N_scope.
Open Scope bool_scope.
Definition cell := (N*N)%type.
Definition decode_cell (p:cell) : Q.cell := (N.to_nat (fst p),N.to_nat (snd p)).
Definition decode_cells := map decode_cell.
Record frame := Frame { cells:list cell; trailing:N }.
Definition decode f := Q.Frame (decode_cells (cells f)) (N.to_nat (trailing f)).
Fixpoint mass (xs:list cell) :=
  match xs with [] => 0 | (t,u)::xs => t+u+1+mass xs end.
Definition width f := mass (cells f)+trailing f-1.

Lemma mass_spec xs: N.to_nat (mass xs)=Q.mass (decode_cells xs).
Proof.
  induction xs as [|[t u] xs IH]; [reflexivity|].
  change (N.to_nat (t+u+1+mass xs)=(N.to_nat t+N.to_nat u+1+Q.mass (decode_cells xs))%nat).
  rewrite !N2Nat.inj_add, IH; reflexivity.
Qed.
Lemma width_spec f: N.to_nat (width f)=Q.width (decode f).
Proof. unfold width, decode, Q.width; cbn [Q.cells Q.trailing]; rewrite <-mass_spec; lia. Qed.

Inductive certificate :=
| Zero2 (l q h:N) | Zero3 (l q h:N) | Zero5 (l q h:N)
| Zero (l q h j p:N) | Short (L t u s e:N)
| OneOdd (l q h b:N) | OneEven (l q h j:N)
| Full (l q h a b p e:N) | Split (l q h a b p e:N)
| ExtraOdd (l q h a b p:N) | ExtraEvenOdd (l q h a b:N)
| ExtraFour (l q h b:N) | ExtraEvenEven (l q h a b:N).

Record claim := Claim {
  extra:bool; old_width:N; ones:N; zeros:N; gap:N;
  residual:list cell; tail:N; guard:bool
}.
Definition view c :=
  match c with
  | Zero2 l q h => Claim false (l*2+q) 0 2 ((l+q)*3-1) [] (1+h) (N.eqb (q+h) 1)
  | Zero3 l q h => Claim false (l*2+q) 0 3 ((l+q)*3-2) [(0,1)] h (N.eqb (q+h) 1)
  | Zero5 l q h => Claim false (l*2+q) 0 5 ((l+q)*3-1) [] (2+h) (N.eqb (q+h) 1)
  | Zero l q h j p => Claim false (l*2+q) 0 (j*2+2+p) ((l+q)*3-1) [(0,j-p)] (p+h)
      (N.eqb (q+h) 1 && N.leb p 1 && N.leb (1+p) j)
  | Short w t u s e => Claim false w t u (s-1-(e+u-1)) [] (e+u-1)
      (N.ltb 0 t && (N.eqb u 1 || N.eqb u 2) && N.leb e 1 && N.eqb (w*3+t+7) (s*2+e))
  | OneOdd l q h b => Claim false (l*2+q) 1 (b*2+1) ((l+q)*3) [] (b+1+h) (N.eqb (q+h) 1)
  | OneEven l q h j => Claim false (l*2+q) 1 (j*2+2) ((l+q)*3-1) [(0,j-2);(0,1)] h (N.eqb (q+h) 1)
  | Full l q h a b p e => Claim false (l*2+q) (a*2+e) (b*2+2-p) ((l+q)*3) [] (b+a+1+h)
      (N.eqb (q+h) 1 && N.leb p 1 && N.leb e 1 && N.leb 1 a && N.leb 1 b && N.eqb (a+p) e)
  | Split l q h a b p e => Claim false (l*2+q) (a*2+e) (b*2+2-p) ((l+q)*3) [(b-1,a+p-e)] (1-p+e+h)
      (N.eqb (q+h) 1 && N.leb p 1 && N.leb e 1 && N.leb 1 a && N.leb 1 b && N.ltb e (a+p))
  | ExtraOdd l q h a b p => Claim true (l*2+q) (a*2+1) (b*2+2-p) ((l+q)*3) [(b-2,1)] (a+3+h)
      (N.eqb (q+h) 1 && N.leb p 1)
  | ExtraEvenOdd l q h a b => Claim true (l*2+q) (a*2) (b*2+1) ((l+q)*3) [(b-1,a-1);(0,1)] h (N.eqb (q+h) 1)
  | ExtraFour l q h b => Claim true (l*2+q) 4 (b*2+2) ((l+q)*3) [(b,1)] (1+h) (N.eqb (q+h) 1)
  | ExtraEvenEven l q h a b => Claim true (l*2+q) (a*2) (b*2+2) ((l+q)*3) [(b-1,a-2);(0,1)] (1+h)
      (N.eqb (q+h) 1 && N.leb 3 a)
  end.

Ltac checks :=
  repeat match goal with
  | H: (?a && ?b)%bool=true |- _ => apply Bool.andb_true_iff in H; destruct H
  | H: (?a || ?b)%bool=true |- _ => apply Bool.orb_true_iff in H; destruct H
  | H: N.eqb _ _=true |- _ => apply N.eqb_eq in H
  | H: N.leb _ _=true |- _ => apply N.leb_le in H
  | H: N.ltb _ _=true |- _ => apply N.ltb_lt in H
  end.
Ltac numbers :=
  repeat first [rewrite N2Nat.inj_add | rewrite N2Nat.inj_mul | rewrite N2Nat.inj_sub];
  cbn [N.to_nat];
  try change (Pos.to_nat 1) with 1%nat;
  try change (Pos.to_nat 2) with 2%nat;
  try change (Pos.to_nat 3) with 3%nat;
  try change (Pos.to_nat 4) with 4%nat;
  try change (Pos.to_nat 5) with 5%nat;
  try change (Pos.to_nat 7) with 7%nat.

Lemma view_spec c: let v:=view c in guard v=true ->
  Q.block (extra v) (N.to_nat (old_width v)) (N.to_nat (ones v)) (N.to_nat (zeros v))
    (N.to_nat (gap v)) (decode_cells (residual v)) (N.to_nat (tail v)).
Proof.
  destruct c; cbn [view guard extra old_width ones zeros gap residual tail]; intro H; checks;
    unfold decode_cells; cbn [map]; unfold decode_cell; cbn [fst snd]; numbers;
    first [apply Q.block_zero2 |apply Q.block_zero3 |apply Q.block_zero5 |apply Q.block_zero
      |apply Q.block_short |apply Q.block_one_odd |apply Q.block_one_even |apply Q.block_full
      |apply Q.block_split |apply Q.block_extra_odd |apply Q.block_extra_even_odd
      |apply Q.block_extra_four |apply Q.block_extra_even_even]; lia.
Qed.

(* The selector is untrusted: apply_claim checks both its input and guard. *)
Definition suggest (x:bool) L t u :=
  let l:=L/2 in let q:=L mod 2 in let h:=1-q in
  let a:=t/2 in let b:=(u-1)/2 in let p:=u mod 2 in let e:=t mod 2 in
  if x then
    if N.eqb e 1 then ExtraOdd l q h a b p else
    if N.eqb p 1 then ExtraEvenOdd l q h a b else
    if N.eqb a 2 then ExtraFour l q h b else ExtraEvenEven l q h a b
  else if N.eqb t 0 then
    if N.eqb u 2 then Zero2 l q h else
    if N.eqb u 3 then Zero3 l q h else
    if N.eqb u 5 then Zero5 l q h else Zero l q h ((u-2)/2) p
  else if N.leb u 2 then Short L t u ((L*3+t+7)/2) ((L*3+t+7) mod 2)
  else if N.eqb t 1 then
    if N.eqb p 1 then OneOdd l q h b else OneEven l q h ((u-2)/2)
  else if N.eqb (a+p) e then Full l q h a b p e else Split l q h a b p e.

Definition localb (x:bool) t u :=
  if x then N.leb 3 t && N.leb 6 u else
  N.ltb 0 u && (negb (N.eqb u 1) || N.ltb 0 t) &&
    (negb (N.eqb u 2) || N.eqb t 0 || N.leb 4 t) &&
    (negb (N.eqb t 1) || (N.leb 3 u && negb (N.eqb u 4))) &&
    (negb (N.eqb t 3) || negb (N.eqb u 4)).
Lemma localb_spec x t u: localb x t u=true -> local_input x (N.to_nat t) (N.to_nat u).
Proof.
  destruct x; unfold localb, local_input; intro H; checks;
    repeat match goal with H:negb _=true |- _ => apply Bool.negb_true_iff in H end;
    repeat match goal with H:N.eqb _ _=false |- _ => apply N.eqb_neq in H end; lia.
Qed.

Definition apply_claim (x:bool) (t u:N) (r:list cell) f c :=
  let v:=view c in
  if guard v && Bool.eqb x (extra v) && N.eqb (width f) (old_width v) &&
    N.eqb t (ones v) && N.eqb u (zeros v) && N.leb 16 (width f) && localb x t u then
    Some (Frame (r++(t+u+(if x then 3 else 1)+trailing f,gap v)::residual v) (tail v))
  else None.

Lemma apply_claim_spec x t u r f c g:
  Q.consume x (N.to_nat t) (N.to_nat u) (decode_cells (cells f)) (decode_cells r) ->
  r<>[] -> apply_claim x t u r f c=Some g ->
  config (decode f) -[tm]->+ config (decode g).
Proof.
  intros Hc Hr. unfold apply_claim.
  destruct (guard (view c) && Bool.eqb x (extra (view c)) &&
    N.eqb (width f) (old_width (view c)) && N.eqb t (ones (view c)) &&
    N.eqb u (zeros (view c)) && N.leb 16 (width f) && localb x t u) eqn:H;
    [|discriminate].
  intro E; inversion E; subst g; clear E. checks.
  match goal with H:Bool.eqb _ _=true |- _ => apply Bool.eqb_prop in H; subst x end.
  match goal with H:localb _ _ _=true |- _ => apply localb_spec in H end.
  unfold decode; cbn [cells trailing]; unfold decode_cells; rewrite map_app;
    cbn [map]; unfold decode_cell; cbn [fst snd]. numbers.
  replace (N.to_nat (if extra (view c) then 3 else 1)) with
    (if extra (view c) then 3%nat else 1%nat) by (destruct (extra (view c)); reflexivity).
  eapply emission_run; [exact Hc| |].
  - destruct r; [contradiction|discriminate].
  - change (D_returns (extra (view c)) (Q.width (decode f)) (N.to_nat t) (N.to_nat u)
      (N.to_nat (gap (view c))) (decode_cells (residual (view c))) (N.to_nat (tail (view c)))).
    apply block_returns_local; [|rewrite <-width_spec; lia|assumption].
    rewrite <-width_spec.
    match goal with H:width f=old_width _ |- _ => rewrite H end.
    match goal with H:t=ones _ |- _ => rewrite H end.
    match goal with H:u=zeros _ |- _ => rewrite H end.
    apply view_spec; assumption.
Qed.

Definition next f :=
  match cells f with
  | [] => None
  | (t,u)::r =>
    if N.eqb t 0 && N.eqb u 1 then
      match r with
      | (t',u')::p::r' => apply_claim true t' u' (p::r') f (suggest true (width f) t' u')
      | _ => None
      end
    else match r with
      | [] => None
      | _::_ => apply_claim false t u r f (suggest false (width f) t u)
      end
  end.

Lemma next_spec f g: next f=Some g -> config (decode f) -[tm]->+ config (decode g).
Proof.
  unfold next. destruct (cells f) as [|[t u] r] eqn:Hf; [discriminate|].
  destruct (N.eqb t 0 && N.eqb u 1) eqn:H.
  - checks; subst t u. destruct r as [|[t u] r]; [discriminate|].
    destruct r as [|p r]; [discriminate|].
    apply apply_claim_spec; [rewrite Hf; constructor|discriminate].
  - destruct r as [|p r]; [discriminate|].
    apply apply_claim_spec; [rewrite Hf; constructor|discriminate].
Qed.

Definition mainb (p:cell) := N.leb 3 (fst p) && N.leb (fst p*8+9) (snd p).
Definition allowedb (p:cell) := N.ltb 0 (snd p) &&
  (N.eqb (fst p) 0 || N.leb (fst p*8+9) (snd p) || N.leb (snd p*8) (fst p+5)).
Definition linkb (p:cell) (xs:list cell) :=
  if N.eqb (fst p) 0 && N.eqb (snd p) 1 then
    match xs with [] => true | q::_ => mainb q end else true.
Fixpoint goodb xs :=
  match xs with [] => true | p::r => allowedb p && linkb p r && goodb r end.

Lemma mainb_spec p: mainb p=true -> Q.main (decode_cell p).
Proof. destruct p; unfold mainb, Q.main, decode_cell; cbn [fst snd]; intro H; checks; lia. Qed.
Lemma allowedb_spec p: allowedb p=true -> Q.allowed (decode_cell p).
Proof.
  destruct p; unfold allowedb, Q.allowed, separated, decode_cell; cbn [fst snd];
    intro H; checks; lia.
Qed.
Lemma linkb_spec p xs: linkb p xs=true -> Q.link (decode_cell p) (decode_cells xs).
Proof.
  destruct p as [t u]; unfold linkb, Q.link; cbn [fst snd]; intros H Heq.
  inversion Heq; assert (t=0 /\ u=1) as [-> ->] by (unfold decode_cell in *; cbn [fst snd] in *; lia).
  cbn in H. destruct xs as [|p xs]; [exact I|apply mainb_spec; exact H].
Qed.
Lemma goodb_spec xs: goodb xs=true -> Q.good (decode_cells xs).
Proof.
  induction xs as [|p xs IH]; cbn [goodb]; intro H; [constructor|].
  checks; constructor; auto using allowedb_spec, linkb_spec.
Qed.

Fixpoint prefixb (xs ys:list cell) :=
  match xs,ys with
  | [],_ => true
  | (t,u)::xs,(a,b)::ys => N.eqb t a && N.eqb u b && prefixb xs ys
  | _,_ => false
  end.
Lemma prefixb_spec xs ys: prefixb xs ys=true -> exists a, ys=xs++a.
Proof.
  revert ys; induction xs as [|[t u] xs IH]; intros ys; [intros; exists ys; reflexivity|].
  destruct ys as [|[a b] ys]; [discriminate|]. cbn [prefixb]; intro H; checks.
  subst a b. destruct (IH ys ltac:(assumption)) as [r ->]. exists r; reflexivity.
Qed.

Definition advanceb xs ys := prefixb (skipn 1 xs) ys || prefixb (skipn 2 xs) ys.
Lemma advanceb_spec xs ys: advanceb xs ys=true -> Q.advance (decode_cells xs) (decode_cells ys).
Proof.
  unfold advanceb; rewrite Bool.orb_true_iff; intros [H|H];
    destruct (prefixb_spec _ _ H) as [a ->];
    [exists 1%nat, (decode_cells a)|exists 2%nat, (decode_cells a)];
    split; try lia; unfold decode_cells; rewrite map_app, <-skipn_map; reflexivity.
Qed.
Definition edgeb f g := advanceb (cells f) (cells g) && N.leb (width f*5) (width g*2) &&
  Nat.leb (length (cells f)) (length (cells g)).
Lemma edgeb_spec f g: edgeb f g=true -> Q.edge (decode f) (decode g).
Proof.
  unfold edgeb; intro H; checks.
  match goal with H:Nat.leb _ _=true |- _ => apply Nat.leb_le in H end.
  split; [apply advanceb_spec; assumption|split].
  - rewrite <-!width_spec; lia.
  - unfold decode; cbn [Q.cells]; unfold decode_cells; rewrite !length_map; assumption.
Qed.
Definition historyb f0 f1 f2 f3 :=
  edgeb f0 f1 && edgeb f1 f2 && edgeb f2 f3 &&
  N.leb 16 (width f0) && Nat.leb 9 (length (cells f0)) &&
  N.leb (trailing f3) (width f0+8) && goodb (cells f3).
Lemma historyb_spec f0 f1 f2 f3: historyb f0 f1 f2 f3=true ->
  Q.history (decode f0) (decode f1) (decode f2) (decode f3).
Proof.
  unfold historyb; intro H; checks.
  match goal with H:Nat.leb _ _=true |- _ => apply Nat.leb_le in H end.
  constructor; try (apply edgeb_spec; assumption).
  - rewrite <-width_spec; lia.
  - unfold decode; cbn [Q.cells]; unfold decode_cells; rewrite length_map; assumption.
  - rewrite <-width_spec; change (N.to_nat (trailing f3)<=N.to_nat (width f0)+8)%nat; lia.
  - apply goodb_spec; assumption.
Qed.

Fixpoint run (fuel:nat) f0 f1 f2 f3 :=
  match fuel with
  | O => historyb f0 f1 f2 f3
  | S n => match next f3 with Some f4 => run n f1 f2 f3 f4 | None => false end
  end.
Theorem run_spec fuel f0 f1 f2 f3: run fuel f0 f1 f2 f3=true -> ~halts tm (config (decode f3)).
Proof.
  revert f0 f1 f2 f3; induction fuel as [|fuel IH]; intros f0 f1 f2 f3; cbn [run].
  - intro H; eapply history_nonhalt, historyb_spec; exact H.
  - destruct (next f3) as [f4|] eqn:Hnext; [|discriminate]. intro H.
    eapply multistep_nonhalt; [apply progress_evstep, next_spec; exact Hnext|eapply IH; exact H].
Qed.

Definition seed := Frame [(23,33);(5,2);(0,1)] 1.
Lemma seed_nonhalt: ~halts tm (config (decode seed)).
Proof. apply (run_spec 216 seed seed seed seed); vm_check_eq. Qed.

End Check.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init_two_frames|apply Check.seed_nonhalt].
Qed.
End TM51.
