(* BB(2,5): two halting machines. All execution data is generated from c0;
   the final computations use native_check_eq, not external certificates. *)

From BusyCoq Require Import Individual25.
From Coq Require Import String List NArith Lia PeanoNat ZifyNat.
Import ListNotations.

(** Exact accelerated halting verification.  Counts are binary N; normal
    binary/doubling runs are batched, and interrupted calls retain the real
    directed configuration.  No external trajectory certificate is used. *)
Module TM507.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "1".
Definition tm := Eval compute in (TM_from_str "1RB3LA1LA2RB2LB_1LB2RA4RA0RB---").
Notation a := (A, ([] : list Sym)).
Notation b := (B, ([] : list Sym)).
Notation sig := (b,a).
Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=30); reflexivity.

Lemma digit0 : segRLs tm [sig] [] [S1;S1] [S1;S3].
Proof. finite_rule. Qed.
Lemma digit1 : segRLs tm [sig] [sig] [S1;S3] [S1;S1].
Proof. finite_rule. Qed.
Lemma double : segRLs tm [sig] [sig;sig] [S3] [S3].
Proof. finite_rule. Qed.
Lemma run_double n k :
  segRLs tm ([sig]^^k) ([sig]^^(k * 2^n)) ([S3]^^n) ([S3]^^n).
Proof.
  revert k; induction n; intro k.
  - change (segRLs tm ([sig]^^k) ([sig]^^(k*1)) [] []).
    rewrite Nat.mul_1_r; apply segRLs_nil.
  - replace ([S3]^^S n) with ([S3]++[S3]^^n) by reflexivity.
    eapply segRLs_concat.
    + apply (segRLs_wall'' (n:=k) double).
    + change ([sig;sig]^^k) with (([sig]^^2)^^k).
      rewrite <-lpow_mul.
      replace (k * 2 ^ S n) with ((k*2) * 2^n) by (cbn; nia).
      apply IHn.
Qed.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "1".
Definition bit_cells (x : bool) : list Sym := [S1;if x then S3 else S1].
Definition bits_word (bs : list bool) : list Sym := flat_map bit_cells bs.

Lemma bit_pair x : segRLs tm [sig;sig] [sig] (bit_cells x) (bit_cells x).
Proof.
  destruct x; apply BoundedConfig.segRLs_c_spec with (T:=60); reflexivity.
Qed.

Open Scope nat_scope.
Lemma bit_pairs x q :
  segRLs tm ([sig]^^(2*q)) ([sig]^^q) (bit_cells x) (bit_cells x).
Proof.
  pose proof (segRLs_wall'' (n:=q) (bit_pair x)) as H.
  change [sig;sig] with ([sig]^^2) in H.
  rewrite <-lpow_mul in H.
  replace (2*q) with (q*2) by lia. exact H.
Qed.
Lemma bit_false_odd q :
  segRLs tm ([sig]^^(2*q+1)) ([sig]^^q) (bit_cells false) (bit_cells true).
Proof.
  rewrite lpow_add.
  replace ([sig]^^q) with ([sig]^^q++[]) by apply app_nil_r.
  eapply segRLs_trans; [apply bit_pairs|exact digit0].
Qed.
Lemma bit_true_odd q :
  segRLs tm ([sig]^^(2*q+1)) ([sig]^^(q+1)) (bit_cells true) (bit_cells false).
Proof.
  rewrite !lpow_add.
  eapply segRLs_trans; [apply bit_pairs|exact digit1].
Qed.

Open Scope N_scope.
Lemma odd_mod_two n : N.odd n=(n mod 2 =? 1).
Proof. rewrite <-N.bit0_odd,N.bit0_eqb. reflexivity. Qed.

Lemma bit_batch (k : N) (x : bool) :
  segRLs tm ([sig]^^N.to_nat k)
    ([sig]^^N.to_nat ((k+(if x then 1 else 0))/2))
    (bit_cells x) (bit_cells (N.odd (k+(if x then 1 else 0)))).
Proof.
  destruct x.
  - rewrite odd_mod_two.
    destruct (N.eqb_spec (k mod 2) 0) as [He|Ho].
    + assert (Hodd : ((k+1) mod 2 =? 1)=true) by (apply N.eqb_eq; lia).
      assert (Hq : (k+1)/2=k/2) by lia.
      rewrite Hodd,Hq.
      assert (K : k=2*(k/2)) by lia.
      rewrite K at 1. rewrite N2Nat.inj_mul. apply bit_pairs.
    + assert (Hodd : ((k+1) mod 2 =? 1)=false) by (apply N.eqb_neq; lia).
      assert (Hq : (k+1)/2=k/2+1) by lia.
      rewrite Hodd,Hq,N2Nat.inj_add.
      assert (K : k=2*(k/2)+1) by lia.
      rewrite K at 1. rewrite N2Nat.inj_add,N2Nat.inj_mul. apply bit_true_odd.
  - rewrite N.add_0_r,odd_mod_two.
    destruct (N.eqb_spec (k mod 2) 0) as [He|Ho].
    + assert (Hodd : (k mod 2 =? 1)=false) by (apply N.eqb_neq; lia).
      rewrite Hodd. assert (K : k=2*(k/2)) by lia.
      rewrite K at 1. rewrite N2Nat.inj_mul. apply bit_pairs.
    + assert (Hodd : (k mod 2 =? 1)=true) by (apply N.eqb_eq; lia).
      rewrite Hodd. assert (K : k=2*(k/2)+1) by lia.
      rewrite K at 1. rewrite N2Nat.inj_add,N2Nat.inj_mul. apply bit_false_odd.
Qed.

Fixpoint add_bits (k : N) (bs : list bool) : N * list bool :=
  match bs with
  | [] => (k,[])
  | x::bs =>
      let t := k+(if x then 1 else 0) in
      let '(out,bs') := add_bits (t/2) bs in (out,N.odd t::bs')
  end.

Lemma add_bits_sound bs : forall k out bs', add_bits k bs=(out,bs') ->
  segRLs tm ([sig]^^N.to_nat k) ([sig]^^N.to_nat out)
    (bits_word bs) (bits_word bs').
Proof.
  induction bs as [|x bs IH]; intros k out bs' H.
  - inversion H; subst. apply segRLs_nil.
  - cbn [add_bits] in H.
    destruct (add_bits ((k+(if x then 1 else 0))/2) bs) as [out' tail] eqn:E.
    inversion H; subst out bs'; clear H.
    change (segRLs tm ([sig]^^N.to_nat k) ([sig]^^N.to_nat out')
      (bit_cells x++bits_word bs)
      (bit_cells (N.odd (k+(if x then 1 else 0)))++bits_word tail)).
    eapply segRLs_concat; [apply bit_batch|apply IH; exact E].
Qed.

Lemma add_bits_length bs : forall k out bs', add_bits k bs=(out,bs') ->
  List.length bs'=List.length bs.
Proof.
  induction bs as [|x bs IH]; intros k out bs' H.
  - inversion H; reflexivity.
  - cbn [add_bits] in H.
    destruct (add_bits ((k+(if x then 1 else 0))/2) bs) as [out' tail] eqn:E.
    inversion H; subst. cbn [List.length]. f_equal. exact (IH _ _ _ E).
Qed.

Fixpoint bits_value (bs : list bool) : N :=
  match bs with [] => 0 | x::bs => (if x then 1 else 0)+2*bits_value bs end.

Lemma odd_div_two t : t=2*(t/2)+(if N.odd t then 1 else 0).
Proof.
  rewrite odd_mod_two. destruct (N.eqb_spec (t mod 2) 1); lia.
Qed.

Lemma add_bits_value bs : forall k out bs', add_bits k bs=(out,bs') ->
  bits_value bs+k=2^(N.of_nat (List.length bs))*out+bits_value bs'.
Proof.
  induction bs as [|x bs IH]; intros k out bs' H.
  - inversion H; subst. cbn [bits_value List.length]. nia.
  - cbn [add_bits] in H.
    destruct (add_bits ((k+(if x then 1 else 0))/2) bs) as [out' tail] eqn:E.
    inversion H; subst. clear H.
    pose proof (IH _ _ _ E) as HV.
    pose proof (odd_div_two (k+(if x then 1 else 0))) as HK.
    cbn [bits_value List.length]. rewrite Nat2N.inj_succ,N.pow_succ_r'. nia.
Qed.

Lemma bits_value_bound bs : bits_value bs<2^(N.of_nat (List.length bs)).
Proof.
  induction bs as [|x bs IH]; [reflexivity|].
  cbn [bits_value List.length]. rewrite Nat2N.inj_succ,N.pow_succ_r'.
  destruct x; nia.
Qed.

Lemma bits_value_max bs : bits_value bs+1=2^(N.of_nat (List.length bs)) ->
  bs=repeat true (List.length bs).
Proof.
  induction bs as [|x bs IH]; [reflexivity|].
  cbn [bits_value List.length]. rewrite Nat2N.inj_succ,N.pow_succ_r'.
  destruct x; intro H; [|lia]. cbn [repeat]. f_equal. apply IH. lia.
Qed.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "all".
Open Scope N_scope.
Fixpoint capacity (n : nat) : N :=
  match n with O => 1 | S n => 2 * capacity n end.
(* Nearest-head first: the low pending-call bit is adjacent to the child. *)
Fixpoint pending (n : nat) (v : N) : list Sym :=
  match n with
  | O => []
  | S n => (if v mod 2 =? 0 then S0 else S1) :: pending n (v/2)
  end.

Lemma div2_facts v : v = 2*(v/2) + v mod 2 /\ v mod 2 < 2.
Proof. split; [apply N.div_mod|apply N.mod_lt]; discriminate. Qed.
Lemma pending_zero n : pending n 0 = [S0]^^n.
Proof.
  induction n; [reflexivity|].
  change (S0 :: pending n 0 = S0 :: [S0]^^n); rewrite IHn; reflexivity.
Qed.
Lemma pending_step n v : v+1 < capacity n ->
  segLR tm a b (pending n v) (pending n (v+1)).
Proof.
  revert v; induction n as [|n IH]; intros v Hv.
  - cbn [capacity] in Hv; lia.
  - destruct (div2_facts v) as [Ev Rv].
    destruct (div2_facts (v+1)) as [Es Rs].
    destruct (N.eq_dec (v mod 2) 0) as [H0|H1].
    + assert (Hnext : (v+1) mod 2 = 1) by lia.
      assert (Hdiv : (v+1)/2 = v/2) by lia.
      cbn [pending]; rewrite H0, Hnext, Hdiv; cbn.
      intros l r; simpl_tape; execute.
    + assert (Hodd : v mod 2 = 1) by lia.
      assert (Hnext : (v+1) mod 2 = 0) by lia.
      assert (Hdiv : (v+1)/2 = v/2+1) by lia.
      assert (Hsmall : v/2+1 < capacity n) by (cbn [capacity] in Hv; lia).
      cbn [pending]; rewrite Hodd, Hnext, Hdiv; cbn.
      intros l r; simpl_tape. step. follow (IH _ Hsmall). execute.
Qed.

Lemma pending_calls n v k : v+k < capacity n ->
  segLRs tm ([(a,b)]^^N.to_nat k) (pending n v) (pending n (v+k)).
Proof.
  revert v; induction k using N.peano_ind; intros v Hv.
  - rewrite N.add_0_r; constructor.
  - rewrite N2Nat.inj_succ; cbn [lpow].
    replace (v+N.succ k) with ((v+1)+k) by lia.
    econstructor.
    + apply pending_step; lia.
    + apply IHk; lia.
Qed.

Lemma enter_threes n : segRR tm b b ([S3]^^n) ([S0]^^n).
Proof.
  intros l r. apply (shift_rule_R [] tm [S3] [S0] B).
  execute.
Qed.
Lemma enter_binary_carry n : segRR tm b b ([S1;S3]^^n) ([S2;S2]^^n).
Proof.
  intros l r. apply (shift_rule_R [] tm [S1;S3] [S2;S2] B).
  execute.
Qed.

(* Once a child has completed r<2^n normal calls in the pending final parent
   call, this is precisely the physical bit pattern used by the C++ unwinder. *)
Lemma threes_pending n r : r < capacity n ->
  segRR tm b b ([S3]^^n) (pending n 0) /\
  segLRs tm ([(a,b)]^^N.to_nat r) (pending n 0) (pending n r).
Proof.
  intro Hr; split.
  - rewrite pending_zero; apply enter_threes.
  - replace r with (0+r) at 2 by reflexivity.
    apply pending_calls; exact Hr.
Qed.

(* The real B-return microsteps are deliberately not merged with pending_calls. *)
Definition NormalCalls k r r' :=
  sideRLs tm ([sig]^^N.to_nat k) r r'.
Definition OpenCall m (r : list Sym) (c : BoundedConfig.T) :=
  exists mid, NormalCalls m (r *> 0inf) mid /\
    forall l, l {{B}}> mid -[tm]->* BoundedConfig.to_config c l 0inf.
Inductive BreakReason := ReturnB | Budget | Halt.
Inductive BatchOutput :=
| Complete (r : list Sym)
| Break (completed : N) (why : BreakReason) (c : BoundedConfig.T).
Definition ReasonSound why c : Prop :=
  match why with
  | Budget => True
  | Halt => forall l, halted tm (BoundedConfig.to_config c l 0inf)
  | ReturnB =>
      BoundedConfig.sgn c = L /\ BoundedConfig.r c = [] /\ BoundedConfig.s c = B
  end.
Definition BatchSound k r out : Prop :=
  match out with
  | Complete r' => NormalCalls k (r *> 0inf) (r' *> 0inf)
  | Break m why c => m < k /\ OpenCall m r c /\ ReasonSound why c
  end.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "all".
Open Scope N_scope.

Definition frame (w : list Sym) (c : BoundedConfig.T) : BoundedConfig.T :=
  let '(BoundedConfig.Build_T ls rs q d) := c in
  match d with
  | R => BoundedConfig.Build_T (ls ++ w) rs q R
  | L => BoundedConfig.Build_T ls (rs ++ w) q L
  end.
Lemma frame_spec w c l r :
  BoundedConfig.to_config (frame w c) l r =
  BoundedConfig.to_config c (l <* w) r.
Proof. destruct c as [ls rs q []]; cbn [frame BoundedConfig.to_config]; simpl_tape; reflexivity. Qed.

Definition lift_reason why := match why with Halt => Halt | _ => Budget end.
Lemma frame_reason w c why : ReasonSound why c -> ReasonSound (lift_reason why) (frame w c).
Proof.
  destruct why; cbn [ReasonSound lift_reason]; try tauto.
  intros H l; rewrite frame_spec; apply H.
Qed.

Lemma capacity_pos n : 0 < capacity n.
Proof. induction n; cbn [capacity]; lia. Qed.
Lemma capacity_nat n : N.to_nat (capacity n) = (2^n)%nat.
Proof.
  induction n; [reflexivity|]. cbn [capacity].
  rewrite N2Nat.inj_mul, IHn; reflexivity.
Qed.
Lemma capacity_pow n : capacity n = 2^(N.of_nat n).
Proof.
  induction n; [reflexivity|]. cbn [capacity].
  rewrite Nat2N.inj_succ, N.pow_succ_r', IHn; reflexivity.
Qed.

Lemma normal_split x y r r' : NormalCalls (x+y) r r' ->
  exists middle, NormalCalls x r middle /\ NormalCalls y middle r'.
Proof.
  unfold NormalCalls; rewrite N2Nat.inj_add, lpow_add.
  apply sideRLs_split.
Qed.

(* Each successful child call returns A; its suspended left caller then
   advances to the next B-entry. This lemma never changes a return state. *)
Lemma interleave_nat n w w' r r' :
  segLRs tm ([(a,b)]^^n) w w' ->
  sideRLs tm ([sig]^^n) r r' ->
  forall l, l <* w {{B}}> r -[tm]->* l <* w' {{B}}> r'.
Proof.
  revert w w' r r'; induction n as [|n IH]; intros w w' r r' HL HR l.
  - inversion HL; inversion HR; subst; finish.
  - cbn [lpow] in HL, HR.
    inversion HL; subst. inversion HR; subst.
    eapply evstep_trans.
    + apply progress_evstep. exact (H4 (l <* w)).
    + eapply evstep_trans.
      * exact (H5 l r2).
      * exact (IH w2 w' r2 r' H6 H7 l).
Qed.

Lemma run_double_N n k :
  segRLs tm ([sig]^^N.to_nat k) ([sig]^^N.to_nat (k*capacity n))
    ([S3]^^n) ([S3]^^n).
Proof. rewrite N2Nat.inj_mul, capacity_nat; apply run_double. Qed.

Definition lift_three n out :=
  match out with
  | Complete tail => Complete ([S3]^^n ++ tail)
  | Break m why c => Break (m / capacity n) (lift_reason why)
      (frame (pending n (m mod capacity n)) c)
  end.

Lemma lift_three_sound n k tail out :
  BatchSound (k*capacity n) tail out ->
  BatchSound k ([S3]^^n ++ tail) (lift_three n out).
Proof.
  destruct out as [tail'|m why c]; cbn [lift_three BatchSound].
  - intro H. unfold NormalCalls in *; repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat; [apply run_double_N|exact H].
  - intros [Hmk [[mid [Hcalls Hrun]] Hreason]].
    pose proof (capacity_pos n) as Hcap.
    pose proof (N.div_mod m (capacity n) ltac:(lia)) as Hdiv.
    pose proof (N.mod_lt m (capacity n) ltac:(lia)) as Hmod.
    split; [nia|]. split; [|apply frame_reason; exact Hreason].
    assert (Hm : m = (m/capacity n)*capacity n + m mod capacity n) by nia.
    rewrite Hm in Hcalls at 1.
    destruct (normal_split _ _ _ _ Hcalls) as [middle [Hfirst Hrest]].
    exists ([S3]^^n *> middle); split.
    + unfold NormalCalls in *; rewrite Str_app_assoc.
      eapply segRLs_sideRLs_concat; [apply run_double_N|exact Hfirst].
    + intro l; rewrite frame_spec.
      eapply evstep_trans; [apply enter_threes|].
      rewrite <- pending_zero.
      eapply evstep_trans with
        (c':=l <* pending n (m mod capacity n) {{B}}> mid).
      * exact (interleave_nat (N.to_nat (m mod capacity n))
          (pending n 0) (pending n (m mod capacity n)) middle mid
          (proj2 (threes_pending n (m mod capacity n) Hmod)) Hrest l).
      * apply Hrun.
Qed.

Definition before_carry bs m :=
  (m+1)*capacity (length bs) - bits_value bs - 1.
Lemma before_carry_equation bs m :
  bits_value bs + before_carry bs m + 1 = (m+1)*capacity (length bs).
Proof.
  unfold before_carry.
  pose proof (bits_value_bound bs); rewrite <- capacity_pow in H.
  pose proof (capacity_pos (length bs)); nia.
Qed.
Lemma bits_true_word n : bits_word (repeat true n) = [S1;S3]^^n.
Proof.
  induction n; [reflexivity|].
  change ([S1;S3] ++ bits_word (repeat true n) = [S1;S3] ++ [S1;S3]^^n).
  rewrite IHn; reflexivity.
Qed.

Lemma add_before_carry bs m :
  add_bits (before_carry bs m) bs = (m, repeat true (length bs)).
Proof.
  destruct (add_bits (before_carry bs m) bs) as [out bs'] eqn:E.
  pose proof (add_bits_length _ _ _ _ E) as Hlen.
  pose proof (add_bits_value _ _ _ _ E) as Hval.
  pose proof (bits_value_bound bs') as Hbound.
  pose proof (before_carry_equation bs m) as Heq.
  pose proof (capacity_pos (length bs)) as Hcap.
  rewrite Hlen in Hbound; rewrite <- capacity_pow in Hval, Hbound.
  assert (Hout : out = m) by nia.
  assert (Hmax : bits_value bs' + 1 = 2 ^ N.of_nat (length bs')).
  { rewrite Hlen, <- capacity_pow; nia. }
  pose proof (bits_value_max _ Hmax) as Hbs.
  rewrite Hlen in Hbs. subst out bs'; reflexivity.
Qed.
Lemma before_carry_lt bs k out bs' m :
  add_bits k bs = (out,bs') -> m < out -> before_carry bs m < k.
Proof.
  intros E Hm.
  pose proof (add_bits_value _ _ _ _ E) as Hval.
  pose proof (before_carry_equation bs m) as Heq.
  pose proof (capacity_pos (length bs)) as Hcap.
  rewrite <- capacity_pow in Hval; nia.
Qed.

Definition binary_output bs bs' child :=
  match child with
  | Complete tail => Complete (bits_word bs' ++ tail)
  | Break m why c => Break (before_carry bs m) (lift_reason why)
      (frame ([S2;S2]^^length bs) c)
  end.
Lemma binary_compose bs k outgoing bs' tail child :
  add_bits k bs = (outgoing,bs') -> BatchSound outgoing tail child ->
  BatchSound k (bits_word bs ++ tail) (binary_output bs bs' child).
Proof.
  intros E; destruct child as [tail'|m why c]; cbn [binary_output BatchSound].
  - intro H. unfold NormalCalls in *; repeat rewrite Str_app_assoc.
    eapply segRLs_sideRLs_concat; [eapply add_bits_sound; exact E|exact H].
  - intros [Hm [[mid [Hcalls Hrun]] Hreason]].
    split; [eapply before_carry_lt; eauto|].
    split; [|apply frame_reason; exact Hreason].
    exists ([S1;S3]^^length bs *> mid); split.
    + unfold NormalCalls in *; rewrite Str_app_assoc.
      pose proof (add_bits_sound _ _ _ _ (add_before_carry bs m)) as Hb.
      rewrite bits_true_word in Hb.
      eapply segRLs_sideRLs_concat; eauto.
    + intro l; rewrite frame_spec.
      eapply evstep_trans; [apply enter_binary_carry|apply Hrun].
Qed.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "1".
Definition leaf_boundary (c : BoundedConfig.T) : option BatchOutput :=
  match c with
  | BoundedConfig.Build_T xs [] A L => Some (Complete xs)
  | BoundedConfig.Build_T xs [] B L => Some (Break 0%N ReturnB c)
  | _ => None
  end.

(* A missing bounded step at the left edge is a return, not a halt.
   Boundaries are inspected before both the machine and the fuel. *)
Fixpoint run_leaf (fuel : nat) (c : BoundedConfig.T) : BatchOutput :=
  match leaf_boundary c with
  | Some out => out
  | None =>
      match BoundedConfig.step_r0inf tm c with
      | None => Break 0%N Halt c
      | Some c' =>
          match fuel with
          | O => Break 0%N Budget c
          | S f => run_leaf f c'
          end
      end
  end.

Definition one_call (fuel : nat) (r : list Sym) :=
  run_leaf fuel (BoundedConfig.Build_T [] r B R).

Definition LeafSound (c : BoundedConfig.T) (out : BatchOutput) : Prop :=
  match out with
  | Complete r' => forall l0,
      BoundedConfig.to_config c l0 0inf -[tm]->* l0 <{{A}} r' *> 0inf
  | Break m why c' => m=0%N /\
      (forall l0, BoundedConfig.to_config c l0 0inf -[tm]->*
         BoundedConfig.to_config c' l0 0inf) /\ ReasonSound why c'
  end.

Lemma leaf_boundary_domain c : leaf_boundary c=None ->
  BoundedConfig.sgn c=L -> BoundedConfig.r c<>[].
Proof.
  destruct c as [xs ys q d], ys, d, q;
    cbn [leaf_boundary BoundedConfig.sgn BoundedConfig.r]; intros; congruence.
Qed.

Lemma leaf_none_halted c :
  (BoundedConfig.sgn c=L -> BoundedConfig.r c<>[]) ->
  BoundedConfig.step_r0inf tm c=None ->
  forall l0, halted tm (BoundedConfig.to_config c l0 0inf).
Proof.
  destruct c as [xs ys q d]; intros Hbound Hstep l0.
  destruct ys as [|x ys].
  - destruct d.
    + exfalso. apply (Hbound eq_refl). reflexivity.
    + destruct q; discriminate.
  - destruct q,d,x; cbn [BoundedConfig.step_r0inf] in Hstep;
      try discriminate; reflexivity.
Qed.

Lemma leaf_boundary_sound c out : leaf_boundary c=Some out -> LeafSound c out.
Proof.
  destruct c as [xs ys q d], ys, d, q; cbn [leaf_boundary];
    intro H; try discriminate; inversion H; subst; clear H;
    cbn [LeafSound ReasonSound BoundedConfig.sgn BoundedConfig.r BoundedConfig.s].
  - intro l0. apply evstep_refl.
  - split; [reflexivity|]. split; [intro l0; apply evstep_refl|].
    repeat split; reflexivity.
Qed.

Lemma leaf_step_sound c c' out :
  (forall l0, BoundedConfig.to_config c l0 0inf -[tm]->
    BoundedConfig.to_config c' l0 0inf) ->
  LeafSound c' out -> LeafSound c out.
Proof.
  intros Hstep Hout. destruct out as [r'|m why final]; cbn [LeafSound] in *.
  - intro l0. eapply evstep_step; [apply Hstep|apply Hout].
  - destruct Hout as [Hm [HR Hwhy]]. split; [exact Hm|]. split; [|exact Hwhy].
    intro l0. eapply evstep_step; [apply Hstep|apply HR].
Qed.

Lemma run_leaf_sound fuel : forall c, LeafSound c (run_leaf fuel c).
Proof.
  induction fuel as [|fuel IH]; intro c; cbn [run_leaf];
    destruct (leaf_boundary c) as [out|] eqn:EB.
  - apply leaf_boundary_sound. exact EB.
  - destruct (BoundedConfig.step_r0inf tm c) as [c'|] eqn:ES;
      cbn [LeafSound ReasonSound].
    + split; [reflexivity|]. split; [intro l0; apply evstep_refl|exact I].
    + split; [reflexivity|]. split; [intro l0; apply evstep_refl|].
      apply leaf_none_halted; [apply leaf_boundary_domain; exact EB|exact ES].
  - apply leaf_boundary_sound. exact EB.
  - destruct (BoundedConfig.step_r0inf tm c) as [c'|] eqn:ES.
    + eapply leaf_step_sound; [|apply IH].
      pose proof (BoundedConfig.step_r0inf_spec tm c) as HS.
      rewrite ES in HS. exact HS.
    + cbn [LeafSound ReasonSound].
      split; [reflexivity|]. split; [intro l0; apply evstep_refl|].
      apply leaf_none_halted; [apply leaf_boundary_domain; exact EB|exact ES].
Qed.

Lemma one_call_sound fuel r : BatchSound 1%N r (one_call fuel r).
Proof.
  pose proof (run_leaf_sound fuel (BoundedConfig.Build_T [] r B R)) as H.
  unfold one_call. destruct (run_leaf fuel (BoundedConfig.Build_T [] r B R))
    as [r'|m why c] eqn:E; cbn [LeafSound BatchSound] in H |- *.
  - unfold NormalCalls. apply sideRL_1. intro l0.
    apply evstep_progress; [exact (H l0)|discriminate].
  - destruct H as [Hm [HR Hwhy]]. subst m.
    split; [lia|]. split; [|exact Hwhy].
    exists (r *> 0inf). split; [constructor|exact HR].
Qed.

(* A separate global step for a finite window with blanks on both sides.
   Unlike the leaf protocol, its left edge is tape, not a call return. *)
Definition expose_left_blank (c : BoundedConfig.T) : BoundedConfig.T :=
  match c with
  | BoundedConfig.Build_T xs [] q L => BoundedConfig.Build_T xs [S0] q L
  | _ => c
  end.
Definition primitive_step c := BoundedConfig.step_r0inf tm (expose_left_blank c).

Lemma expose_left_blank_config c :
  BoundedConfig.to_config (expose_left_blank c) 0inf 0inf =
  BoundedConfig.to_config c 0inf 0inf.
Proof. destruct c as [xs ys q d], ys, d; reflexivity. Qed.

Lemma expose_left_blank_domain c :
  BoundedConfig.sgn (expose_left_blank c)=L ->
  BoundedConfig.r (expose_left_blank c)<>[].
Proof.
  destruct c as [xs ys q d], ys, d;
    cbn [expose_left_blank BoundedConfig.sgn BoundedConfig.r]; intros; congruence.
Qed.

Lemma primitive_step_spec c :
  match primitive_step c with
  | Some c' => BoundedConfig.to_config c 0inf 0inf -[tm]->
      BoundedConfig.to_config c' 0inf 0inf
  | None => halted tm (BoundedConfig.to_config c 0inf 0inf)
  end.
Proof.
  unfold primitive_step.
  destruct (BoundedConfig.step_r0inf tm (expose_left_blank c)) as [c'|] eqn:E.
  - pose proof (BoundedConfig.step_r0inf_spec tm (expose_left_blank c)) as H.
    rewrite E in H. specialize (H 0inf).
    now rewrite expose_left_blank_config in H.
  - pose proof (leaf_none_halted (expose_left_blank c)
      (expose_left_blank_domain c) E 0inf) as H.
    now rewrite expose_left_blank_config in H.
Qed.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "1".
Record ThreePrefix := mkThreePrefix {
  threes_count : nat;
  threes_capacity : N;
  threes_tail : list Sym
}.

Fixpoint take_threes_full (r:list Sym) : ThreePrefix :=
  match r with
  | S3::r =>
      let p := take_threes_full r in
      mkThreePrefix (S (threes_count p))
        (N.double (threes_capacity p)) (threes_tail p)
  | _ => mkThreePrefix 0 1%N r
  end.

Record BitPrefix := mkBitPrefix {
  prefix_bits : list bool;
  prefix_bits_length : N;
  prefix_bits_capacity : N;
  prefix_bits_tail : list Sym
}.

Definition prefix_bit_cons x p :=
  mkBitPrefix (x::prefix_bits p) (N.succ (prefix_bits_length p))
    (N.double (prefix_bits_capacity p)) (prefix_bits_tail p).

Fixpoint take_bits_full (r:list Sym) : BitPrefix :=
  match r with
  | S1::S1::r => prefix_bit_cons false (take_bits_full r)
  | S1::S3::r => prefix_bit_cons true (take_bits_full r)
  | _ => mkBitPrefix [] 0%N 1%N r
  end.

Definition threes_stopped (r:list Sym) : Prop :=
  match r with S3::_ => False | _ => True end.
Definition bits_stopped (r:list Sym) : Prop :=
  match r with S1::S1::_ | S1::S3::_ => False | _ => True end.

Lemma parse_double n : N.double n = (2*n)%N.
Proof. destruct n; reflexivity. Qed.

Lemma take_threes_full_spec r :
  r = [S3]^^(threes_count (take_threes_full r)) ++ threes_tail (take_threes_full r) /\
  threes_capacity (take_threes_full r) = capacity (threes_count (take_threes_full r)) /\
  threes_stopped (threes_tail (take_threes_full r)).
Proof.
  induction r as [|s r [Hr [Hc Hstop]]]; [repeat split; reflexivity|].
  destruct s; cbn [take_threes_full threes_count threes_capacity threes_tail
    threes_stopped lpow app capacity]; try (repeat split; reflexivity).
  rewrite parse_double, Hc; repeat split; [f_equal; exact Hr|exact Hstop].
Qed.

Lemma take_bits_full_spec r :
  r = bits_word (prefix_bits (take_bits_full r)) ++ prefix_bits_tail (take_bits_full r) /\
  prefix_bits_length (take_bits_full r) = N.of_nat (List.length (prefix_bits (take_bits_full r))) /\
  prefix_bits_capacity (take_bits_full r) = capacity (List.length (prefix_bits (take_bits_full r))) /\
  bits_stopped (prefix_bits_tail (take_bits_full r)).
Proof.
  revert r; fix IH 1; intro r; destruct r as [|s [|t r]].
  - repeat split; reflexivity.
  - destruct s; repeat split; reflexivity.
  - destruct s,t; cbn [take_bits_full prefix_bits prefix_bits_length prefix_bits_capacity
      prefix_bits_tail bits_stopped bits_word flat_map bit_cells prefix_bit_cons];
      try (repeat split; reflexivity).
    all: destruct (IH r) as [Hr [Hlen [Hcap Hstop]]];
      cbn [List.length capacity]; rewrite parse_double, Hlen, Hcap, Nat2N.inj_succ;
      repeat split; try (cbn [bit_cells app]; repeat f_equal; exact Hr); exact Hstop.
Qed.

Close Scope N_scope.
Open Scope nat_scope.
Set Default Goal Selector "1".
Open Scope N_scope.

Lemma calls_add x y r u v :
  NormalCalls x r u -> NormalCalls y u v -> NormalCalls (x+y) r v.
Proof.
  unfold NormalCalls; rewrite N2Nat.inj_add,lpow_add.
  apply sideRLs_trans.
Qed.

Definition after_one out :=
  match out with
  | Complete r => Complete r
  | Break m why c => Break (1+m) why c
  end.
Lemma after_one_sound k r u out :
  NormalCalls 1 (r *> 0inf) (u *> 0inf) ->
  BatchSound k u out -> BatchSound (1+k) r (after_one out).
Proof.
  intros H; destruct out as [v|m why c]; cbn [BatchSound after_one].
  - intro Hu; exact (calls_add _ _ _ _ _ H Hu).
  - intros [Hm [[mid [Hu Hrun]] Hr]]. split; [lia|].
    split; [|exact Hr]. exists mid; split; [|exact Hrun].
    exact (calls_add _ _ _ _ _ H Hu).
Qed.

Definition start r := BoundedConfig.Build_T [] r B R.
Lemma start_sound k r : 0<k -> BatchSound k r (Break 0 Budget (start r)).
Proof.
  intro H; split; [exact H|]. split; [|exact I].
  exists (r *> 0inf); split; [constructor|]. intro l; finish.
Qed.
Lemma break_one_sound k r m why c : 0<k ->
  BatchSound 1 r (Break m why c) -> BatchSound k r (Break m why c).
Proof. intros H [Hm Hr]; split; [lia|exact Hr]. Qed.

Fixpoint batch (fuel:nat) (k:N) (r:list Sym) : BatchOutput :=
  match k with
  | N0 => Complete r
  | _ =>
    match fuel with
    | O => Break 0 Budget (start r)
    | S fuel =>
      match r with
      | S3::_ =>
          let p := take_threes_full r in
          lift_three (threes_count p)
            (batch fuel (k*threes_capacity p) (threes_tail p))
      | S1::S1::_ | S1::S3::_ =>
          let p := take_bits_full r in
          let '(out,bs') := add_bits k (prefix_bits p) in
          binary_output (prefix_bits p) bs' (batch fuel out (prefix_bits_tail p))
      | _ =>
          match one_call 32 r with
          | Complete r' => after_one (batch fuel (k-1) r')
          | Break m why c => Break m why c
          end
      end
    end
  end.

Lemma batch_sound fuel : forall k r, BatchSound k r (batch fuel k r).
Proof.
  induction fuel as [|fuel IH]; intros [|p] r.
  - constructor.
  - apply start_sound; lia.
  - constructor.
  - change (BatchSound (N.pos p) r
      (match r with
       | S3::_ => let z:=take_threes_full r in
           lift_three (threes_count z)
             (batch fuel (N.pos p*threes_capacity z) (threes_tail z))
       | S1::S1::_ | S1::S3::_ => let z:=take_bits_full r in
           let '(out,bs') := add_bits (N.pos p) (prefix_bits z) in
           binary_output (prefix_bits z) bs'
             (batch fuel out (prefix_bits_tail z))
       | _ => match one_call 32 r with
              | Complete u => after_one (batch fuel (N.pos p-1) u)
              | Break m why c => Break m why c end
       end)).
    assert (Hleaf : forall r,
      BatchSound (N.pos p) r
        (match one_call 32 r with
         | Complete u => after_one (batch fuel (N.pos p-1) u)
         | Break m why c => Break m why c end)).
    { intro u. pose proof (one_call_sound 32 u) as H.
      destruct (one_call 32 u) as [v|m why c].
      - replace (N.pos p) with (1+(N.pos p-1)) at 1 by lia.
        eapply after_one_sound; [exact H|apply IH].
      - apply break_one_sound; [lia|exact H]. }
    assert (Hthree : forall u,
      BatchSound (N.pos p) u
        (let z:=take_threes_full u in
         lift_three (threes_count z)
           (batch fuel (N.pos p*threes_capacity z) (threes_tail z)))).
    { intro u. destruct (take_threes_full_spec u) as [E [C _]].
      cbn zeta. rewrite C. rewrite E at 1.
      apply lift_three_sound; apply IH. }
    assert (Hbits : forall u,
      BatchSound (N.pos p) u
        (let z:=take_bits_full u in
         let '(out,bs') := add_bits (N.pos p) (prefix_bits z) in
         binary_output (prefix_bits z) bs'
           (batch fuel out (prefix_bits_tail z)))).
    { intro u. destruct (take_bits_full_spec u) as [E Hrest].
      cbn zeta.
      destruct (add_bits (N.pos p) (prefix_bits (take_bits_full u)))
        as [out bs'] eqn:Hadd.
      rewrite E at 1.
      eapply binary_compose; [exact Hadd|apply IH]. }
    destruct r as [|s r]; [apply Hleaf|].
    destruct s; try apply Hleaf; try apply Hthree.
    destruct r as [|t r]; [apply Hleaf|].
    destruct t; try apply Hleaf; apply Hbits.
Qed.

Definition denote c := BoundedConfig.to_config c 0inf 0inf.
Definition orient c :=
  match c with
  | BoundedConfig.Build_T ls [] q L => BoundedConfig.Build_T [] (S0::ls) q R
  | BoundedConfig.Build_T ls (s::rs) q L => BoundedConfig.Build_T rs (s::ls) q R
  | _ => c end.
Lemma orient_spec c : denote (orient c) = denote c.
Proof. destruct c as [ls rs q []]; destruct rs; reflexivity. Qed.

Definition root_right c : option BoundedConfig.T :=
  match c with
  | BoundedConfig.Build_T l r B R =>
      match batch 64 1 r with
      | Complete r' => Some (BoundedConfig.Build_T r' l A L)
      | Break _ Halt _ => None
      | Break _ _ d => Some (frame l d)
      end
  | _ => primitive_step c
  end.

Lemma open_zero r d : OpenCall 0 r d ->
  forall l, l {{B}}> r *> 0inf -[tm]->* BoundedConfig.to_config d l 0inf.
Proof.
  intros [mid [H Hr]]. inversion H; subst; exact Hr.
Qed.
Lemma root_right_sound c :
  match root_right c with
  | Some d => denote c -[tm]->* denote d
  | None => halts tm (denote c)
  end.
Proof.
  assert (P : forall c,
    match primitive_step c with
    | Some d => denote c -[tm]->* denote d
    | None => halts tm (denote c) end).
  { intro d. pose proof (primitive_step_spec d) as H.
    destruct (primitive_step d); [eauto|apply halted_halts; exact H]. }
  destruct c as [ls rs q dir]; destruct q, dir; try apply P.
  unfold root_right. pose proof (batch_sound 64 1 rs) as H.
  destruct (batch 64 1 rs) as [r'|m why d].
  - cbn [BatchSound NormalCalls] in H.
    inversion H; subst. inversion H6; subst.
    cbn [denote BoundedConfig.to_config].
    apply progress_evstep. apply H5.
  - destruct H as [Hm [Ho Hr]]. assert (m=0) by lia; subst m.
    pose proof (open_zero _ _ Ho) as Hrun. destruct why; cbn [root_right].
    + unfold denote; rewrite frame_spec; apply Hrun.
    + unfold denote; rewrite frame_spec; apply Hrun.
    + eapply halts_evstep; [apply halted_halts; apply Hr|apply Hrun].
Qed.

Definition root c := root_right (orient c).
Lemma root_sound c :
  match root c with
  | Some d => denote c -[tm]->* denote d
  | None => halts tm (denote c) end.
Proof.
  pose proof (root_right_sound (orient c)) as H.
  rewrite orient_spec in H; exact H.
Qed.

Definition initial := BoundedConfig.Build_T [] [] A R.
Definition tick c : BoundedConfig.T + unit :=
  match root c with Some d => inl d | None => inr tt end.
Definition check fuel : bool :=
  match Eqb.N_iter_until tick (inl initial) fuel with
  | inl _ => false | inr _ => true end.
Theorem check_sound fuel : check fuel=true -> halts tm c0.
Proof.
  pose proof (@Eqb.N_iter_until_spec _ _ tick (inl initial) fuel
    (fun c => halts tm (denote c) -> halts tm c0)
    (fun _ => halts tm c0)) as H.
  assert (HS : forall c, (halts tm (denote c) -> halts tm c0) ->
    match tick c with inl d => halts tm (denote d) -> halts tm c0
                      | inr _ => halts tm c0 end).
  { intros c IH. pose proof (root_sound c) as HR.
    unfold tick; destruct (root c).
    - intro HH; apply IH. eapply halts_evstep; eauto.
    - apply IH; exact HR. }
  specialize (H HS ltac:(intro H0; exact H0)).
  unfold check. destruct (Eqb.N_iter_until tick (inl initial) fuel);
    [discriminate|intros _; exact H].
Qed.

Theorem halt : halts tm c0.
Proof. apply (check_sound 600000%N). native_check_eq. Qed.
End TM507.

Close Scope N_scope. Close Scope Z_scope. Close Scope nat_scope.
Open Scope sym_scope. Set Default Goal Selector "1".

(* BB(2,5): original machine 231. The final native check generates all
   signals from c0; no external trajectory or large certificate is used.
   Only the last theorem performs the large halting computation. *)
From BusyCoq Require Import Individual25 FastRev LongitudinalHalt25.
From Coq Require Uint63 PArray.
From Coq Require Import String ZArith NArith List ZifyNat Lia.
Import PrimInt63 ListNotations.
Set Warnings "-abstract-large-number".

Module Columns.
Definition LocalTable := Q -> Sym -> option (Sym * list Q).
Fixpoint feed_acc (tr:LocalTable) qs s acc := match qs with
| [] => Some (s,fast_rev acc)
| q::qs => match tr q s with
  | None => None
  | Some(s,ws) => feed_acc tr qs s (fast_rev_append ws acc)
  end end.
Definition feed tr qs s := feed_acc tr qs s [].

Definition TableSpec tm (tr:LocalTable) := forall q s s' qs,
  tr q s=Some(s',qs) -> segRLs tm (calls [q]) (calls qs) [s] [s'].
Lemma calls_app xs ys : calls (xs++ys)=calls xs++calls ys.
Proof. apply List.map_app. Qed.
Lemma reverse_acc {X} (xs acc:list X) : fast_rev (fast_rev_append xs acc)=fast_rev acc++xs.
Proof. rewrite !fast_rev_spec,fast_rev_append_spec,List.rev_app_distr,List.rev_involutive; reflexivity. Qed.

Lemma feed_acc_spec tm tr (HT:TableSpec tm tr) qs : forall s acc s' ws,
  feed_acc tr qs s acc=Some(s',ws) -> exists out,
    ws=fast_rev acc++out /\ segRLs tm (calls qs) (calls out) [s] [s'].
Proof.
  induction qs as [|q qs IH]; intros s acc s' ws; cbn[feed_acc].
  - intro H; inversion H; subst; exists (@nil Q); split; [rewrite app_nil_r; reflexivity|constructor].
  - destruct (tr q s) as [[s0 out]|] eqn:E; [|discriminate]; intro H.
    destruct (IH _ _ _ _ H) as [rest [EW HR]].
    exists (out++rest); split.
    + rewrite EW,reverse_acc,app_assoc; reflexivity.
    + change (calls (q::qs)) with (calls [q]++calls qs); rewrite calls_app.
      eapply segRLs_trans; [apply HT; exact E|exact HR].
Qed.
Lemma feed_spec tm tr (HT:TableSpec tm tr) qs s s' ws :
  feed tr qs s=Some(s',ws) -> segRLs tm (calls qs) (calls ws) [s] [s'].
Proof. intro H; destruct (@feed_acc_spec tm tr HT qs s [] s' ws H) as [out [-> HR]]; exact HR. Qed.

Lemma calls_pow qs n : calls (qs^^n)=(calls qs)^^n.
Proof. induction n; cbn[lpow]; [reflexivity|rewrite calls_app,IHn; reflexivity]. Qed.
Lemma seg_cycle_pow tm u v w n : segRLs tm u v w w -> segRLs tm (u^^n) (v^^n) w w.
Proof. intro H; induction n; cbn[lpow]; [constructor|eapply segRLs_trans; eauto]. Qed.

End Columns.
Import Columns.

Lemma flow_finite_halt tm pre period n r :
  FlowHalts tm (pre++period^^n) [] r -> FlowHalts tm pre period r.
Proof.
  intros [k H]. assert (E:(@nil Q)^^k=[]).
  { induction k; cbn[lpow]; auto. }
  rewrite E,app_nil_r in H; exists n; exact H.
Qed.

Lemma flow_rotate_return tm u v r r' :
  sideRLs tm (calls u) r r' -> FlowHalts tm [] (v++u) r' ->
  FlowHalts tm [] (u++v) r.
Proof.
  intros HR [n HH]; exists (S n); cbn[app] in HH |- *.
  assert (E:(u++v)^^(S n)=(u++(v++u)^^n)++v).
  { cbn[lpow]; rewrite <-lpow_shift,app_assoc,lpow_rotate_list'; reflexivity. }
  rewrite E,!calls_app.
  apply sideRLs_halt_app_left.
  eapply sideRLs_halt_app_right; eassumption.
Qed.

Module PackedBits.
Fixpoint pcode (xs:list Q) : positive := match xs with
| []=>xH | A::xs=>xO(pcode xs) | B::xs=>xI(pcode xs) end.
Definition code xs := Z.pos(pcode xs).
Fixpoint pword p : list Q := match p with
| xH=>[] | xO p=>A::pword p | xI p=>B::pword p end.
Definition word (x:Uint63.int) := pword (Z.to_pos (Uint63.to_Z x)).
Definition encode xs := Uint63.of_Z (code xs).
Definition Represents (x:Uint63.int) xs := Uint63.to_Z x=code xs.
Definition idx n := Uint63.of_Z (Z.of_nat n).

Lemma pword_code xs : pword(pcode xs)=xs.
Proof. induction xs as [|[] xs IH]; cbn; now try rewrite IH. Qed.
Lemma code_word p : pcode(pword p)=p.
Proof. induction p; cbn; now try rewrite IHp. Qed.
Lemma code_inj x y : code x=code y -> x=y.
Proof.
  unfold code; intro H; apply Pos2Z.inj in H.
  apply (f_equal pword) in H; rewrite !pword_code in H; exact H.
Qed.
Lemma word_spec x xs : Represents x xs -> word x=xs.
Proof. unfold Represents,word,code; intro H; rewrite H; apply pword_code. Qed.
Lemma word_rep x : (0<Uint63.to_Z x)%Z -> Represents x (word x).
Proof.
  intro H; unfold Represents,word,code; rewrite code_word,Z2Pos.id by exact H; reflexivity.
Qed.
Lemma code_cons q xs : code(q::xs)=(2*code xs+match q with A=>0|B=>1 end)%Z.
Proof. destruct q; unfold code; cbn[pcode]; lia. Qed.
Lemma code_bounds xs : (2^Z.of_nat(length xs)<=code xs<2^(1+Z.of_nat(length xs)))%Z.
Proof.
  induction xs as [|q xs IH]; [change (1<=1<2)%Z; lia|].
  rewrite code_cons; cbn[length]; rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by lia.
  replace (1+Z.succ(Z.of_nat(length xs)))%Z with
    (Z.succ(1+Z.of_nat(length xs))) by lia.
  rewrite Z.pow_succ_r by lia; destruct q; lia.
Qed.
Lemma code_pos xs : (0<code xs)%Z.
Proof. unfold code; lia. Qed.
Lemma code_app xs ys :
  code(xs++ys)=(code xs+(code ys-1)*2^Z.of_nat(length xs))%Z.
Proof.
  induction xs as [|q xs IH].
  - change (code ys=1+(code ys-1)*1)%Z; ring.
  -
  cbn[app length]; rewrite !code_cons,IH,Nat2Z.inj_succ,Z.pow_succ_r by lia.
  destruct q; ring.
Qed.
Lemma encode_spec xs : (length xs<=61)%nat -> Represents (encode xs) xs.
Proof.
  intro H; unfold Represents,encode; rewrite Uint63.of_Z_spec.
  apply Z.mod_small; pose proof (code_bounds xs).
  change Uint63.wB with (2^63)%Z.
  assert (2^(1+Z.of_nat(length xs))<=2^63)%Z by (apply Z.pow_le_mono_r; lia).
  pose proof (code_pos xs); lia.
Qed.
Lemma idx_small n : (n<=63)%nat -> Uint63.to_Z(idx n)=Z.of_nat n.
Proof. intro H; unfold idx; rewrite Uint63.of_Z_spec; apply Z.mod_small; cbv[Uint63.wB Uint63.size]; lia. Qed.
Lemma add_small a b : (Uint63.to_Z a+Uint63.to_Z b<Uint63.wB)%Z ->
  Uint63.to_Z(Uint63.add a b)=(Uint63.to_Z a+Uint63.to_Z b)%Z.
Proof.
  intro H; rewrite Uint63.add_spec; apply Z.mod_small.
  pose proof(Uint63.to_Z_bounded a); pose proof(Uint63.to_Z_bounded b); lia.
Qed.

(* Two words of total length at most 60 fit in one machine integer. *)
Definition join (a b n:Uint63.int) :=
  Uint63.add a (Uint63.lsl (Uint63.sub b 1) n).
Lemma join_spec a b n xs ys : Represents a xs -> Represents b ys ->
  Uint63.to_Z n=Z.of_nat(length xs) -> (length xs+length ys<=60)%nat ->
  Represents (join a b n) (xs++ys).
Proof.
  unfold Represents,join; intros EA EB EN HL.
  rewrite Uint63.add_spec,Uint63.lsl_spec,Uint63.sub_spec,EA,EB,EN.
  change (Uint63.to_Z 1) with 1%Z.
  rewrite (Z.mod_small (code ys-1) Uint63.wB) by
    (pose proof(code_pos ys); pose proof(Uint63.to_Z_bounded b); rewrite EB in *; lia).
  rewrite Z.add_mod_idemp_r by apply Uint63.wB_diff_0.
  rewrite <-code_app; apply Z.mod_small.
  pose proof(code_bounds(xs++ys)); pose proof(code_pos(xs++ys)).
  rewrite app_length in *; change Uint63.wB with (2^63)%Z.
  assert (2^(1+Z.of_nat(length xs+length ys))<=2^63)%Z by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

(* Split a long word at a 15-signal boundary.  The two small constants are
   powers of two; all correctness statements remain about arbitrary words. *)
Definition low15 x := Uint63.add (Uint63.mod x 32768) 32768.
Definition high15 x := Uint63.lsr x 15.
Lemma split15_spec x xs : Represents x xs -> (15<=length xs)%nat ->
  Represents (low15 x) (firstn 15 xs) /\ Represents (high15 x) (skipn 15 xs).
Proof.
  intros EX HL.
  assert (EL:length(firstn 15 xs)=15%nat) by (rewrite firstn_length; lia).
  assert (EC:code xs=(code(firstn 15 xs)+(code(skipn 15 xs)-1)*32768)%Z).
  { rewrite <- (firstn_skipn 15 xs) at 1; rewrite code_app,EL; reflexivity. }
  pose proof(code_bounds(firstn 15 xs)) as HB; rewrite EL in HB.
  change (32768<=code(firstn 15 xs)<65536)%Z in HB.
  unfold Represents,low15,high15 in *.
  rewrite Uint63.add_spec,Uint63.mod_spec,Uint63.lsr_spec,EX.
  change (Uint63.to_Z 32768) with 32768%Z.
  change (2^Uint63.to_Z 15)%Z with 32768%Z.
  rewrite EC; split.
  - rewrite Z.mod_add by lia.
    replace (code(firstn 15 xs)) with ((code(firstn 15 xs)-32768)+1*32768)%Z at 1 by ring.
    rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (code(firstn 15 xs)-32768) 32768) by lia.
    replace (code(firstn 15 xs)-32768+32768)%Z with (code(firstn 15 xs)) by ring.
    apply Z.mod_small; change Uint63.wB with 9223372036854775808%Z; lia.
  - rewrite Z.div_add by lia.
    assert (code(firstn 15 xs)/32768=1)%Z by
      (symmetry; apply Z.div_unique with(r:=(code(firstn 15 xs)-32768)%Z); lia).
    lia.
Qed.
Lemma long_split x : Uint63.ltb x 65536=false ->
  word x=word(low15 x)++word(high15 x).
Proof.
  intro E; destruct(Uint63.ltbP x 65536) as [H|H]; [discriminate|].
  change (Uint63.to_Z 65536) with 65536%Z in H.
  assert (HP:(0<Uint63.to_Z x)%Z) by lia.
  pose proof(word_rep x HP) as HR.
  assert (HL:15<=length(word x)).
  { pose proof(code_bounds(word x)) as HB.
    unfold Represents in HR; rewrite <-HR in HB.
    destruct(Nat.le_gt_cases 15 (length(word x))); [assumption|].
    assert (HPow:(2^(1+Z.of_nat(length(word x)))<=2^15)%Z) by (apply Z.pow_le_mono_r; lia).
    change (2^15)%Z with 32768%Z in HPow; lia. }
  destruct(split15_spec x (word x) HR HL) as [HA HB].
  rewrite (word_spec _ _ HA),(word_spec _ _ HB); symmetry; apply firstn_skipn.
Qed.
End PackedBits.

Import PackedBits.

Module PackedBuffer.
Record Block := block {
  w0:Uint63.int; w1:Uint63.int; w2:Uint63.int; w3:Uint63.int;
  w4:Uint63.int; w5:Uint63.int; w6:Uint63.int; w7:Uint63.int;
  w8:Uint63.int; w9:Uint63.int; w10:Uint63.int; w11:Uint63.int;
  w12:Uint63.int; w13:Uint63.int; w14:Uint63.int; w15:Uint63.int }.
Definition fields b := [w0 b;w1 b;w2 b;w3 b;w4 b;w5 b;w6 b;w7 b;
  w8 b;w9 b;w10 b;w11 b;w12 b;w13 b;w14 b;w15 b].
Definition words := flat_map word.
Definition block_words bs := flat_map (fun b=>words(fields b)) bs.
Definition Seq := (list Block * list Uint63.int)%type.
Definition denote (s:Seq) := block_words(fst s)++words(snd s).
Record Buffer := buffer {
  complete:list Block; partial:list Uint63.int; free:nat }.
Definition empty := buffer [] [] 15.
Definition contents b := block_words(fast_rev(complete b))++words(fast_rev(partial b)).
Definition push x b := match free b with
| S n=>buffer(complete b)(x::partial b)n
| O=>match partial b with
  | [a14;a13;a12;a11;a10;a9;a8;a7;a6;a5;a4;a3;a2;a1;a0] =>
    buffer(block a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 x::complete b) [] 15
  | _=>buffer(complete b)(x::partial b)0 end end.
Definition finish b : Seq := (fast_rev(complete b),fast_rev(partial b)).
Lemma words_app xs ys : words(xs++ys)=words xs++words ys.
Proof. apply flat_map_app. Qed.
Lemma blocks_app xs ys : block_words(xs++ys)=block_words xs++block_words ys.
Proof. apply flat_map_app. Qed.
Lemma words_rev x xs : words(fast_rev(x::xs))=words(fast_rev xs)++word x.
Proof.
  rewrite !fast_rev_spec; cbn[rev]; rewrite words_app.
  cbn[words flat_map]; rewrite app_nil_r; reflexivity.
Qed.
Lemma push_simple bs ps n x :
  contents(buffer bs (x::ps) n)=contents(buffer bs ps 0)++word x.
Proof. unfold contents; cbn[complete partial]; rewrite words_rev,app_assoc; reflexivity. Qed.
Lemma push_spec b x : contents(push x b)=contents b++word x.
Proof.
  destruct b as [bs ps n]; destruct n; unfold push; cbn[free partial complete].
  2: apply push_simple.
  do 15 (let a:=fresh "a" in destruct ps as [|a ps]; [apply push_simple|]).
  let a:=fresh "a" in destruct ps as [|a ps]; [|apply push_simple].
  unfold contents; cbn[complete partial]; rewrite !fast_rev_spec; cbn[rev app].
  rewrite blocks_app; cbn[block_words words flat_map fields app].
  repeat rewrite app_nil_r; repeat rewrite app_assoc; reflexivity.
Qed.
Lemma finish_spec b : denote(finish b)=contents b.
Proof. reflexivity. Qed.

(* At most 60 payload bits per word, leaving room for its sentinel. The
   transducer emits at most 30 signals at a time. Flush before overflowing,
   rather than maintaining a length field for every completed word. *)
Record Writer := writer {body:Buffer; pending:Uint63.int; used:Uint63.int}.
Definition initial := writer empty 1%uint63 0%uint63.
Definition written w := contents(body w)++word(pending w).
Definition Valid w := Represents(pending w)(word(pending w)) /\
  Uint63.to_Z(used w)=Z.of_nat(length(word(pending w))) /\
  (length(word(pending w))<=60)%nat.
Definition put x n w :=
  let k:=Uint63.add(used w)n in
  if Uint63.leb k 60%uint63 then writer(body w)(join(pending w)x(used w))k
  else writer(push(pending w)(body w))x n.
Definition close w := finish(push(pending w)(body w)).
Lemma initial_spec : Valid initial /\ written initial=[].
Proof. vm_compute; repeat split; lia. Qed.
Lemma put_spec x n w xs : Valid w -> Represents x xs ->
  Uint63.to_Z n=Z.of_nat(length xs) -> (length xs<=30)%nat ->
  Valid(put x n w) /\ written(put x n w)=written w++xs.
Proof.
  intros [HP [HN HL]] HX NX LX.
  assert (EK:Uint63.to_Z(Uint63.add(used w)n)=
    (Z.of_nat(length(word(pending w)))+Z.of_nat(length xs))%Z).
  { rewrite add_small,HN,NX; [reflexivity|].
    rewrite HN,NX; change Uint63.wB with 9223372036854775808%Z; lia. }
  unfold put; destruct (Uint63.leb(Uint63.add(used w)n)60%uint63) eqn:EL.
  - apply Uint63.leb_spec in EL; rewrite EK in EL.
    change (Uint63.to_Z 60%uint63) with 60%Z in EL.
    assert (HJ:Represents(join(pending w)x(used w))(word(pending w)++xs))
      by (apply join_spec; auto; lia).
    pose proof(word_spec _ _ HJ) as HW.
    unfold Valid,written; cbn[body pending used]; rewrite HW.
    repeat split; try exact HJ; try (rewrite length_app; lia).
    rewrite app_assoc; reflexivity.
  - pose proof(word_spec _ _ HX) as HW.
    unfold Valid,written; cbn[body pending used]; rewrite HW.
    repeat split; try assumption; try lia.
    rewrite push_spec; reflexivity.
Qed.
Lemma close_spec w : denote(close w)=written w.
Proof. unfold close,written; rewrite finish_spec,push_spec; reflexivity. Qed.
End PackedBuffer.

Import PackedBuffer.

Module PackedTable.
Record Entry := entry {next:Sym; output:Uint63.int; width:Uint63.int}.
Record Row := row {at1:option Entry; at2:option Entry; at3:option Entry}.
Definition Table := PArray.array Row.
Definition get (t:Table) x s :=
  if Uint63.ltb x 65536 then
    let r:=PArray.get t x in match s with
    | S1=>at1 r | S2=>at2 r | S3=>at3 r | _=>None end
  else None.

Lemma idx_value n : (Z.of_nat n<Uint63.wB)%Z -> Uint63.to_Z(idx n)=Z.of_nat n.
Proof.
  intro H; unfold idx; rewrite Uint63.of_Z_spec; apply Z.mod_small; lia.
Qed.
Lemma idx_next n : (Z.of_nat(S n)<Uint63.wB)%Z -> Uint63.add(idx n)1=idx(S n).
Proof.
  intro H; apply Uint63.to_Z_inj.
  rewrite Uint63.add_spec,!idx_value by lia.
  change (Uint63.to_Z 1) with 1%Z.
  rewrite Z.mod_small by lia; lia.
Qed.
Fixpoint alln n i (f:Uint63.int->bool) := match n with
| O=>true | S n=>if f i then alln n (Uint63.add i 1) f else false end.
Lemma alln_spec n : forall start f, (Z.of_nat(start+n)<Uint63.wB)%Z ->
  alln n (idx start) f=true -> forall j, start<=j<start+n -> f(idx j)=true.
Proof.
  induction n; intros start f HB H j HJ; [lia|].
  cbn[alln] in H; destruct(f(idx start)) eqn:E; [|discriminate].
  destruct(Nat.eq_dec j start); [subst; exact E|].
  rewrite idx_next in H by lia.
  eapply IHn; [|exact H|]; lia.
Qed.
Definition unidx x := Z.to_nat(Uint63.to_Z x).
Lemma idx_unidx x : idx(unidx x)=x.
Proof.
  unfold idx,unidx; rewrite Z2Nat.id by (pose proof(Uint63.to_Z_bounded x); lia).
  apply Uint63.of_to_Z.
Qed.
Definition size := unidx 65536.
Lemma size_value : Z.of_nat size=65536%Z.
Proof.
  unfold size,unidx; rewrite Z2Nat.id by (pose proof(Uint63.to_Z_bounded 65536); lia).
  reflexivity.
Qed.
Lemma small_index x : Uint63.ltb x 65536=true -> unidx x<size.
Proof.
  rewrite Uint63.ltb_spec; change (Uint63.to_Z 65536) with 65536%Z.
  intro H; unfold size,unidx; change (Uint63.to_Z 65536) with 65536%Z.
  pose proof(Uint63.to_Z_bounded x) as [HX _].
  apply (proj1 (Z2Nat.inj_lt (Uint63.to_Z x) 65536 HX ltac:(lia))); exact H.
Qed.

Definition entry_ok tr s x oe := match oe with
| None=>true
| Some e=>
  if Nat.leb(length(word(output e)))30 then
  if Uint63.eqb(output e)(encode(word(output e))) then
  if Uint63.eqb(width e)(idx(length(word(output e)))) then
  match Columns.feed tr (word x) s with
  | None=>false |Some(s',ys)=>if sym_eqb(next e)s' then
      Eqb.list_eqb q_eqb (word(output e)) ys else false end
  else false else false else false end.
Definition table_ok tr t := alln size 0 (fun x=>
  if entry_ok tr S1 x (get t x S1) then
  if entry_ok tr S2 x (get t x S2) then
  entry_ok tr S3 x (get t x S3) else false else false).
Definition Correct tm x s e :=
  segRLs tm (calls(word x)) (calls(word(output e))) [s] [next e] /\
  Represents(output e)(word(output e)) /\
  Uint63.to_Z(width e)=Z.of_nat(length(word(output e))) /\
  length(word(output e))<=30.
Definition Sound tm t := forall x s e, get t x s=Some e -> Correct tm x s e.
Lemma get_spec tm t x s e : Sound tm t -> get t x s=Some e -> Correct tm x s e.
Proof. auto. Qed.
Lemma entry_ok_spec tm tr s x e : TableSpec tm tr ->
  entry_ok tr s x (Some e)=true -> Correct tm x s e.
Proof.
  intro HT; unfold entry_ok,Correct.
  destruct(Nat.leb(length(word(output e)))30) eqn:EL; [|discriminate].
  destruct(Uint63.eqb(output e)(encode(word(output e)))) eqn:EW; [|discriminate].
  destruct(Uint63.eqb(width e)(idx(length(word(output e))))) eqn:EN; [|discriminate].
  apply Nat.leb_le in EL; apply Uint63.eqb_correct in EW,EN.
  destruct(Columns.feed tr (word x) s) as [[s' ys]|] eqn:EF; [|discriminate].
  destruct(sym_eqb_spec(next e)s') as [ES|ES]; [subst s'|discriminate].
  intro H; destruct(Eqb.list_eqb_spec q_eqb (word(output e)) ys q_eqb_spec); [subst ys|discriminate].
  split; [eapply Columns.feed_spec; eassumption|].
  split; [rewrite EW at 1; apply encode_spec; lia|].
  split; [rewrite EN; apply idx_small; lia|exact EL].
Qed.
Local Opaque size alln.
Lemma table_spec tm tr t : TableSpec tm tr -> table_ok tr t=true -> Sound tm t.
Proof.
  intros HR HT x s e HE; assert (HX:unidx x<size).
  { unfold get in HE; destruct(Uint63.ltb x 65536) eqn:E in HE;
      [apply small_index,E|discriminate HE]. }
  assert (HB:(Z.of_nat(0+size)<Uint63.wB)%Z).
  { cbn[Nat.add]; rewrite size_value; reflexivity. }
  unfold table_ok in HT.
  pose proof(alln_spec size 0 _ HB HT (unidx x) ltac:(lia)) as HH.
  clear HX HT HB; rename HH into HX.
  rewrite idx_unidx in HX.
  destruct(entry_ok tr S1 x (get t x S1)) eqn:E1; [|discriminate].
  destruct(entry_ok tr S2 x (get t x S2)) eqn:E2; [|discriminate].
  destruct s.
  - unfold get in HE; destruct(Uint63.ltb x 65536) in HE; discriminate HE.
  - apply entry_ok_spec with(tr:=tr); [exact HR|rewrite <-HE; exact E1].
  - apply entry_ok_spec with(tr:=tr); [exact HR|rewrite <-HE; exact E2].
  - apply entry_ok_spec with(tr:=tr); [exact HR|rewrite <-HE; exact HX].
  - unfold get in HE; destruct(Uint63.ltb x 65536) in HE; discriminate HE.
Qed.
Local Transparent size alln.

Definition make_entry tr x s := match Columns.feed tr (word x) s with
| None=>None |Some(s',ys)=>Some(entry s' (encode ys)(idx(length ys))) end.
Definition make_row tr x := row(make_entry tr x S1)(make_entry tr x S2)(make_entry tr x S3).
Fixpoint fill n i f (t:Table) := match n with
| O=>t |S n=>fill n (Uint63.add i 1) f (PArray.set t i (f i)) end.
Definition make_table tr := fill size 0 (make_row tr)(PArray.make 65536(row None None None)).
End PackedTable.

Import PackedTable.

Module PackedRun.
Definition Run := Sym -> Writer -> option(Sym*Writer).
Definition unit : Run := fun s w=>Some(s,w).
Definition then_run (f g:Run) : Run := fun s w=>match f s w with
| None=>None |Some(s,w)=>g s w end.
Definition Good tm (f:Run) input := forall s w s' w', Valid w ->
  f s w=Some(s',w') -> Valid w' /\ exists out,
  written w'=written w++out /\
  segRLs tm (calls input) (calls out) [s] [s'].
Lemma unit_spec tm : Good tm unit [].
Proof.
  intros s w s' w' HW E; inversion E; subst; split; [exact HW|].
  exists (@nil Q); split; [rewrite app_nil_r; reflexivity|constructor].
Qed.
Lemma bind_spec tm f g a b : Good tm f a -> Good tm g b -> Good tm(then_run f g)(a++b).
Proof.
  intros HF HG s w s' w' HW; unfold then_run.
  destruct(f s w) as [[s0 w0]|] eqn:E; [|discriminate].
  intro H; destruct(HF _ _ _ _ HW E) as [H0 [x [HX RX]]].
  destruct(HG _ _ _ _ H0 H) as [H1 [y [HY RY]]].
  split; [exact H1|]; exists(x++y); split.
  - rewrite HY,HX,app_assoc; reflexivity.
  - rewrite !calls_app; eapply segRLs_trans; eassumption.
Qed.
Fixpoint fold {X} (step:X->Run) (xs:list X) s w : option(Sym*Writer) := match xs with
| []=>Some(s,w)
| x::xs=>match step x s w with None=>None |Some(s,w)=>fold step xs s w end end.
Lemma fold_spec tm X (step:X->Run) decode xs :
  (forall x, Good tm (step x)(decode x)) -> Good tm(fold step xs)(flat_map decode xs).
Proof.
  intro H; induction xs; [apply unit_spec|].
  change (Good tm(then_run(step a)(fold step xs))(decode a++flat_map decode xs)).
  apply bind_spec; auto.
Qed.

Definition small t x : Run := fun s w=>match PackedTable.get t x s with
| None=>None |Some e=>Some(next e,put(output e)(width e)w) end.
Lemma small_spec tm t x : Sound tm t -> Good tm(small t x)(word x).
Proof.
  intros HT s w s' w' HW; unfold small.
  destruct(PackedTable.get t x s) as [e|] eqn:E; [|discriminate].
  intro H; inversion H; subst.
  destruct(get_spec tm t x s e HT E) as [HR [HE [HN HL]]].
  destruct(put_spec _ _ _ _ HW HE HN HL) as [HV HC].
  split; [exact HV|]; exists(word(output e)); auto.
Qed.
Fixpoint one fuel t x : Run := match fuel with
| O=>fun _ _=>None
| S fuel=>if Uint63.ltb x 65536 then small t x
  else then_run(small t (low15 x))(one fuel t (high15 x)) end.
Lemma one_spec fuel tm t x : Sound tm t -> Good tm(one fuel t x)(word x).
Proof.
  intro HT; revert x; induction fuel; intro x; cbn[one].
  - intros s w s' w' HW H; discriminate.
  - destruct(Uint63.ltb x 65536) eqn:E; [apply small_spec,HT|].
    rewrite(long_split x E); apply bind_spec; [apply small_spec,HT|apply IHfuel].
Qed.
Definition words_run t := fold(one 5 t).
Definition block_run t b := words_run t (fields b).
Definition seq_run t (s:Seq) := then_run(fold(block_run t)(fst s))(words_run t(snd s)).
Lemma words_spec tm t xs : Sound tm t -> Good tm(words_run t xs)(words xs).
Proof. intro H; apply fold_spec; intro x; apply one_spec,H. Qed.
Lemma block_spec tm t b : Sound tm t -> Good tm(block_run t b)(words(fields b)).
Proof. apply words_spec. Qed.
Lemma seq_spec tm t s : Sound tm t -> Good tm(seq_run t s)(denote s).
Proof.
  intro H; unfold seq_run,denote; apply bind_spec.
  - apply fold_spec; intro b; apply block_spec,H.
  - apply words_spec,H.
Qed.

(* A cursor consists of at most one partly consumed block and a short list
   of immutable slabs. Rotating a period only appends the consumed prefix
   to that SHORT slab list; it does not copy the large list of records. *)
Record Cursor := cursor {front:list Q; slabs:list Seq}.
Definition read c := front c++flat_map denote(slabs c).
Definition of_seq s := cursor [] [s].
Definition append_seq c s := cursor(front c)(slabs c++[s]).
Lemma of_seq_spec s : read(of_seq s)=denote s.
Proof. unfold read,of_seq; cbn[front slabs flat_map app]; rewrite app_nil_r; reflexivity. Qed.
Lemma append_seq_spec c s : read(append_seq c s)=read c++denote s.
Proof.
  unfold read,append_seq; cbn[front slabs]; rewrite flat_map_app; cbn[flat_map].
  rewrite app_nil_r,app_assoc; reflexivity.
Qed.
Definition atom q : Uint63.int := match q with A=>2 |B=>3 end.
Definition atoms_run t := fold(fun q=>small t (atom q)).
Lemma atom_spec q : word(atom q)=[q].
Proof. destruct q; reflexivity. Qed.
Lemma atoms_spec tm t xs : Sound tm t -> Good tm(atoms_run t xs)xs.
Proof.
  intro H; induction xs; cbn[atoms_run fold]; [apply unit_spec|].
  change (Good tm(then_run(small t(atom a))(atoms_run t xs))([a]++xs)).
  apply bind_spec; [rewrite <-atom_spec; apply small_spec,H|exact IHxs].
Qed.
Definition run t c := then_run(atoms_run t(front c))(fold(seq_run t)(slabs c)).
Lemma run_spec tm t c : Sound tm t -> Good tm(run t c)(read c).
Proof.
  intro H; unfold run,read; apply bind_spec; [apply atoms_spec,H|].
  apply fold_spec; intro s; apply seq_spec,H.
Qed.
Definition transform t s c := match run t c s initial with
| None=>None |Some(s,w)=>Some(s,of_seq(close w)) end.
Lemma transform_spec tm t s c s' c' : Sound tm t ->
  transform t s c=Some(s',c') ->
  segRLs tm(calls(read c))(calls(read c'))[s][s'].
Proof.
  intros HT; unfold transform; destruct(run t c s initial) as [[s0 w]|] eqn:E; [|discriminate].
  intro H; inversion H; subst.
  destruct(run_spec tm t c HT _ _ _ _ (proj1 initial_spec) E) as [HW [out [HO HR]]].
  rewrite of_seq_spec,close_spec,HO,(proj2 initial_spec); exact HR.
Qed.

Fixpoint take_word (ss:list Seq) : option(Uint63.int*list Seq) := match ss with
| []=>None
| (b::bs,ws)::ss=>Some(w0 b,([],tl(fields b))::(bs,ws)::ss)
| ([],x::ws)::ss=>Some(x,([],ws)::ss)
| ([],[])::ss=>take_word ss end.
Lemma take_word_spec ss x ss' : take_word ss=Some(x,ss') ->
  flat_map denote ss=word x++flat_map denote ss'.
Proof.
  revert x ss'; induction ss as [|[bs ws] ss IH]; intros x ss'; [discriminate|].
  destruct bs as [|b bs].
  - destruct ws as [|y ws].
    + cbn[take_word]; intro E; specialize(IH _ _ E); exact IH.
    + cbn[take_word]; intro E; inversion E; subst.
      unfold denote,block_words,words; cbn[flat_map fst snd app]; rewrite app_assoc; reflexivity.
  - cbn[take_word]; intro E; inversion E; subst.
    unfold denote,block_words,words; cbn[flat_map fst snd fields tl app].
    repeat rewrite app_assoc; reflexivity.
Qed.
Fixpoint pop fuel c : option(Q*Cursor) := match fuel with
| O=>None
| S fuel=>match front c with
  | q::qs=>Some(q,cursor qs(slabs c))
  | []=>match take_word(slabs c) with
    | None=>None
    | Some(x,ss)=>match word x with
      | []=>pop fuel(cursor [] ss)
      | q::qs=>Some(q,cursor qs ss) end end end end.
Lemma pop_spec fuel c q c' : pop fuel c=Some(q,c') -> read c=q::read c'.
Proof.
  revert c q c'; induction fuel; intros [qs ss] q c'; [discriminate|].
  destruct qs as [|a qs]; cbn[pop front slabs].
  - destruct(take_word ss) as [[x ss']|] eqn:EW; [|discriminate].
    pose proof(take_word_spec _ _ _ EW) as HW.
    destruct(word x) as [|a qs] eqn:EX.
    + intro H; specialize(IHfuel _ _ _ H); unfold read in *; cbn[front slabs app] in *.
      rewrite HW; exact IHfuel.
    + intro E; inversion E; subst; unfold read; cbn[front slabs app].
      rewrite HW; reflexivity.
  - intro E; inversion E; subst; reflexivity.
Qed.
End PackedRun.

Import PackedRun.

Module PackedCheck.
Definition cycle t s c := match run t c s initial with
| None=>None
| Some(s1,w)=>if sym_eqb s1 s then Some(of_seq(close w)) else
  match run t c s1 w with
  | None=>None |Some(s2,w)=>if sym_eqb s2 s then Some(of_seq(close w)) else None end end.
Definition cross (finite:bool) t s c := if finite then
  match transform t s c with None=>None|Some(_,c)=>Some c end else cycle t s c.
Definition rotate c acc := append_seq c ([],map atom(fast_rev acc)).
Inductive WarmResult := Failed | Halt | Ready (r:side) (c:Cursor).
Definition pick (fin:bool) base c (acc:list Q) := match pop 16 c with
| Some(q,c')=>Some(q,c',acc)
| None=>if fin then None else match read c with
  | _::_=>None |[]=>match pop 16 base with
    | None=>None |Some(q,c')=>Some(q,c',[]) end end end.
Fixpoint warm tm T n (finite:bool) base c acc r := match n with
| O=>Ready r (if finite then c else rotate c acc)
| S n=>match pick finite base c acc with
  | None=>Failed
  | Some(q,c',acc)=>match sideRL_halt_rec tm [] r q T with
    | Halted=>Halt
    | Returned A r'=>warm tm T n finite base c' (q::acc) r'
    | _=>Failed end end end.
Inductive Action := Lower (n:nat) | Warm (n:nat) | Finite.
Record State := state {finite:bool; tape:side; input:Cursor}.
Fixpoint lower n t r c finite := match n with
| O=>Some(r,c)
| S n=>match r with s>>r=>match cross finite t s c with
  | None=>None |Some c=>lower n t r c finite end end end.
Fixpoint execute tm t T program st : bool := match program with
| []=>false
| a::program=>match a with
  | Finite=>execute tm t T program(state true(tape st)(input st))
  | Lower n=>match lower n t(tape st)(input st)(finite st) with
    | None=>false |Some(r,c)=>execute tm t T program(state(finite st)r c) end
  | Warm n=>match warm tm T n (finite st)(input st)(input st)[](tape st) with
    | Failed=>false |Halt=>true
    | Ready r c=>execute tm t T program(state(finite st)r c) end end end.

End PackedCheck.
Import PackedCheck.

Module PackedSound.
Definition Flow tm (fin:bool) qs r := if fin then FlowHalts tm qs [] r else FlowHalts tm [] qs r.
Lemma nil_power n : (@nil Q)^^n=[].
Proof. induction n; cbn[lpow]; auto. Qed.
Lemma finite_halt tm qs r : Flow tm true qs r <-> sideRLs_halt tm(calls qs)r.
Proof.
  split.
  - intros [n H]; rewrite nil_power,app_nil_r in H; exact H.
  - intro H; exists 0%nat; rewrite app_nil_r; exact H.
Qed.
Lemma restrict tm qs r : Flow tm true qs r -> Flow tm false qs r.
Proof. intro H; apply flow_finite_halt with(n:=1%nat); cbn[lpow app]; rewrite app_nil_r; exact H. Qed.
Lemma first_halt tm fin q qs r : (forall l,halts tm(l {{q}}> r)) -> Flow tm fin(q::qs)r.
Proof.
  intro H; destruct fin.
  - apply finite_halt; constructor 1; exact H.
  - exists 1%nat; cbn[lpow app]; rewrite app_nil_r; constructor 1; exact H.
Qed.
Lemma returned tm fin q qs r r' : sideRL tm(q,[])(A,[])r r' ->
  Flow tm fin(if fin then qs else qs++[q])r' -> Flow tm fin(q::qs)r.
Proof.
  intros HR HH; destruct fin.
  - apply finite_halt in HH; apply finite_halt; econstructor 2; eauto.
  - eapply flow_rotate_return with(u:=[q])(v:=qs); [|exact HH].
    econstructor; [exact HR|constructor].
Qed.
Lemma finite_column tm p out s s' r :
  segRLs tm(calls p)(calls out)[s][s'] ->
  Flow tm true out r -> Flow tm true p(s>>r).
Proof.
  intros HS HH; apply finite_halt in HH; apply finite_halt.
  exact(@segRLs_sideRLs_halt_concat tm _ _ [s] [s'] r HS HH).
Qed.
Lemma periodic_column tm p out s r k :
  segRLs tm(calls(p^^k))(calls out)[s][s] ->
  Flow tm false out r -> Flow tm false p(s>>r).
Proof.
  intros HS [n HH]; exists(n*k); cbn[app] in HH |- *.
  eapply (@segRLs_sideRLs_halt_concat tm _ _ [s] [s] r); [|exact HH].
  rewrite lpow_mul,!calls_pow; apply seg_cycle_pow.
  rewrite <-calls_pow; exact HS.
Qed.
Lemma cycle_spec tm t s c c' r : Sound tm t -> cycle t s c=Some c' ->
  Flow tm false(read c')r -> Flow tm false(read c)(s>>r).
Proof.
  intros HT; unfold cycle.
  destruct(run t c s initial) as [[s1 w1]|] eqn:E1; [|discriminate].
  destruct(run_spec tm t c HT _ _ _ _ (proj1 initial_spec) E1) as [HV1 [x [HX RX]]].
  rewrite (proj2 initial_spec) in HX; cbn[app] in HX.
  destruct(sym_eqb_spec s1 s) as [EQ|NE]; [subst s1|].
  - intro E; inversion E; subst c'; rewrite of_seq_spec,close_spec,HX; intro H.
    eapply periodic_column with(k:=1%nat); [|exact H].
    cbn[lpow]; rewrite app_nil_r; exact RX.
  - destruct(run t c s1 w1) as [[s2 w2]|] eqn:E2; [|discriminate].
    destruct(sym_eqb_spec s2 s) as [EQ|NE2]; [subst s2|discriminate].
    intro E; inversion E; subst c'.
    destruct(run_spec tm t c HT _ _ _ _ HV1 E2) as [HV2 [y [HY RY]]].
    rewrite of_seq_spec,close_spec,HY,HX; intro H.
    eapply periodic_column with(k:=2%nat); [|exact H].
    cbn[lpow]; rewrite app_nil_r,!calls_app; eapply segRLs_trans; eassumption.
Qed.
Lemma cross_spec tm fin t s c c' r : Sound tm t -> cross fin t s c=Some c' ->
  Flow tm fin(read c')r -> Flow tm fin(read c)(s>>r).
Proof.
  intro HT; destruct fin; cbn[cross].
  - destruct(transform t s c) as [[s' out]|] eqn:E; [|discriminate].
    intro H; inversion H; subst; apply finite_column with(s':=s').
    eapply transform_spec; eassumption.
  - apply cycle_spec,HT.
Qed.
Lemma lower_spec tm n t : Sound tm t -> forall r c fin r' c',
  PackedCheck.lower n t r c fin=Some(r',c') ->
  Flow tm fin(read c')r' -> Flow tm fin(read c)r.
Proof.
  intro HT; induction n; intros [s r] c fin r' c'; cbn[PackedCheck.lower].
  - intro E; inversion E; subst; trivial.
  - destruct(cross fin t s c) as [out|] eqn:E; [|discriminate].
    intros EL HH; eapply cross_spec; [exact HT|exact E|].
    eapply IHn; eassumption.
Qed.

Lemma atoms_words xs : words(map atom xs)=xs.
Proof. induction xs; cbn[map words flat_map]; [reflexivity|rewrite atom_spec,IHxs; reflexivity]. Qed.
Lemma rotate_spec c acc : read(rotate c acc)=read c++fast_rev acc.
Proof.
  unfold rotate; rewrite append_seq_spec; unfold denote; cbn[fst snd block_words flat_map app].
  rewrite atoms_words; reflexivity.
Qed.
Definition Future (fin:bool) c acc := if fin then read c else read c++fast_rev acc.
Definition Inv (fin:bool) base c acc := fin=false -> read base=fast_rev acc++read c.
Lemma next_future fin c acc q : Future fin c(q::acc)=
  if fin then Future fin c acc else Future fin c acc++[q].
Proof. destruct fin; unfold Future; [reflexivity|rewrite fast_rev_cons,app_assoc; reflexivity]. Qed.
Lemma pick_spec fin base c acc q c' acc' : Inv fin base c acc ->
  pick fin base c acc=Some(q,c',acc') ->
  Inv fin base c'(q::acc') /\ Future fin c acc=q::Future fin c' acc'.
Proof.
  intros HI; unfold pick; destruct(pop 16 c) as [[q0 c0]|] eqn:EP.
  - intro E; inversion E; subst.
    pose proof(pop_spec _ _ _ _ EP) as HP; split.
    + intro HF; rewrite (HI HF),HP,fast_rev_cons,<-app_assoc; reflexivity.
    + unfold Future; destruct fin; rewrite HP; reflexivity.
  - destruct fin; [discriminate|].
    destruct(read c) as [|a xs] eqn:EC; [|discriminate].
    destruct(pop 16 base) as [[q0 c0]|] eqn:EB; [|discriminate].
    intro E; inversion E; subst.
    pose proof(pop_spec _ _ _ _ EB) as HB; split.
    + intro HF; exact HB.
    + unfold Future; rewrite EC; cbn[app]; rewrite app_nil_r.
      specialize(HI eq_refl); rewrite EC,app_nil_r in HI; rewrite <-HI; exact HB.
Qed.
Definition WarmHalts tm fin result := match result with
| Failed=>False |Halt=>True |Ready r c=>Flow tm fin(read c)r end.
Lemma warm_spec tm T n fin base : forall c acc r, Inv fin base c acc ->
  WarmHalts tm fin(warm tm T n fin base c acc r) -> Flow tm fin(Future fin c acc)r.
Proof.
  induction n; intros c acc r HI; cbn[warm].
  - destruct fin; cbn[WarmHalts]; [trivial|rewrite rotate_spec; trivial].
  - destruct(pick fin base c acc) as [[[q c'] acc']|] eqn:EP; [|contradiction].
    destruct(pick_spec _ _ _ _ _ _ _ HI EP) as [HI' HF].
    pose proof(sideRL_halt_rec_spec tm T [] r q) as HS.
    destruct(sideRL_halt_rec tm [] r q T) as [|q' r'|] eqn:ER; cbn[result_spec] in HS.
    + contradiction.
    + destruct q'; [|contradiction]; intro H.
      specialize(IHn _ _ _ HI' H); rewrite HF.
      eapply returned; [exact HS|rewrite <-next_future; exact IHn].
    + intro H; rewrite HF; apply first_halt; exact HS.
Qed.
Lemma warm_start_spec tm T n fin c r :
  WarmHalts tm fin(warm tm T n fin c c [] r) -> Flow tm fin(read c)r.
Proof.
  intro H; pose proof(warm_spec tm T n fin c c [] r ltac:(intros _; reflexivity) H) as HH.
  unfold Future in HH; destruct fin; [exact HH|rewrite app_nil_r in HH; exact HH].
Qed.
Lemma execute_spec tm t T program : Sound tm t -> forall st,
  execute tm t T program st=true -> Flow tm(finite st)(read(input st))(tape st).
Proof.
  intro HT; induction program as [|a program IH]; intros [fin r c]; [discriminate|].
  destruct a as [n|n|]; cbn[execute finite tape input].
  - destruct(PackedCheck.lower n t r c fin) as [[r' c']|] eqn:E; [|discriminate].
    intro H; apply IH in H; eapply lower_spec; eassumption.
  - destruct(warm tm T n fin c c [] r) eqn:E; try discriminate.
    + intro H; apply warm_start_spec with(T:=T)(n:=n); rewrite E; exact I.
    + intro H; apply IH in H.
      apply warm_start_spec with(T:=T)(n:=n); rewrite E; exact H.
  - intro H; apply IH in H; destruct fin; [exact H|apply restrict,H].
Qed.
End PackedSound.
Import PackedSound.

Open Scope sym_scope.
Module TM231.
Definition tm := Eval compute in (TM_from_str "1RB4RA1LA4RB2LA_2LB3LA1RB2RA---").
Definition left n := 0inf <* <[1;4;4]^^n.
Definition emitter_left n := left n << 1.
Definition emit_period := [B;A;B;A;B].
Definition seed := [3;2].

Definition tr : LocalTable := fun q s => match q,s with
| A,0=>Some(2,[B;A]) | A,1=>Some(2,[A]) | A,2=>Some(1,[])
| A,3=>Some(2,[B]) | A,4=>Some(2,[])
| B,0=>None | B,1=>Some(3,[]) | B,2=>Some(2,[B;A])
| B,3=>Some(1,[A]) | B,4=>None end.
Lemma tr_spec : TableSpec tm tr.
Proof.
  intros q s s' qs; destruct q,s; cbn[tr]; intro H; inversion H; subst;
    apply BoundedConfig.segRLs_c_spec with (T:=10); reflexivity.
Qed.

Lemma emit1 n r : emitter_left n <{{A}} r -[tm]->+ left n << 4 {{A}}> r.
Proof. unfold emitter_left; es. Qed.
Lemma emit2 n r : left n << 4 <{{A}} r -[tm]->+ left n <* <[1;1] {{B}}> r.
Proof. unfold left; es. Qed.
Lemma emit3 n r : left n <* <[1;1] <{{A}} r -[tm]->+ left n <* <[1;4] {{A}}> r.
Proof. es. Qed.
Lemma emit4 n r : left n <* <[1;4] <{{A}} r -[tm]->+ left (1+n) {{B}}> r.
Proof. unfold left; es. Qed.
Lemma emit5 n r : left (1+n) <{{A}} r -[tm]->+ emitter_left (1+n) {{B}}> r.
Proof. unfold left,emitter_left; es. Qed.

Lemma left_round n : LeftRun tm [A;B;A;B;B] (emitter_left n) (emitter_left (1+n)).
Proof.
  econstructor; [apply emit1|]. econstructor; [apply emit2|].
  econstructor; [apply emit3|]. econstructor; [apply emit4|].
  econstructor; [apply emit5|constructor].
Qed.
Lemma init : c0 -[tm]->* emitter_left 0 {{B}}> seed *> 0inf.
Proof. unfold emitter_left,left,seed; es. Qed.
Lemma from_flow : FlowHalts tm [] emit_period (seed *> 0inf) -> halts tm c0.
Proof.
  intro H; eapply halts_evstep; [|exact init].
  eapply (@left_period_halt tm B [A;B;A;B] emitter_left).
  - apply left_round.
  - exact H.
Qed.

Definition table := make_table tr.
Lemma table_valid : table_ok tr table=true.
Proof. native_check_eq. Qed.
Definition run_check t T program :=
  execute tm t T program (state false(seed*>0inf)(cursor emit_period [])).
Lemma check_spec t T program : Sound tm t -> run_check t T program=true -> halts tm c0.
Proof.
  intros HT H; apply from_flow.
  exact(execute_spec tm t T program HT _ H).
Qed.

(* A short batching schedule, not a certificate: the evaluator checks each
   period return and right-side call. At Finite it keeps one future period. *)
Definition schedule := [Warm 10000;Lower 32;Warm 10000;Lower 33;
  Warm 10000;Lower 24;Warm 10000;Lower 24;Warm 10000;Lower 27;
  Warm 10000;Lower 26;Finite;Lower 8;Warm 10000;Lower 30;
  Warm 10000;Lower 25;Warm 10000].

Theorem halt: halts tm c0.
Proof.
  apply(check_spec table 10000 schedule).
  - apply table_spec with(tr:=tr); [apply tr_spec|exact table_valid].
  - native_check_eq.
Qed.
End TM231.

Print Assumptions TM507.halt.
Print Assumptions TM231.halt.
