(* The machine repeatedly converts a binary counter between shifted digit
   encodings. The invariant records the spare amplifier space and the
   positions of protected one bits.

   Every wall satisfying the invariant makes positive progress to another
   wall. An inductive zero-bit bound on the recursive counter deficit
   preserves a marker after subtraction at arbitrary conversion depth.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Require BusyCoq.Individual62.
Require BusyCoq.DivModCases.
Require BusyCoq.Longitudinal.
Require BusyCoq.ES_v3.
Require String.
Require List.
Require PeanoNat.
Require Lia.
Require BusyCoq.BinaryCounter_v2.
Require NArith.
Require BusyCoq.SimplTape.
Require BusyCoq.ES_v2.
Require Bool.

Module WallInvariant.
(* A candidate wall invariant for a shift-overflow counter.
   The closure theorem is developed separately.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module WallInvariant.

Definition mtm := Eval compute in
  (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").

Fixpoint normal (bs:list bool) : list Sym :=
  match bs with
  | [] => []
  | b::bs => (if b then [1;0;0;0;0] else [0;0;0;0;0]) ++ normal bs
  end.

Fixpoint shifted (bs:list bool) : list Sym :=
  match bs with
  | [] => []
  | b::bs => (if b then [0;0;0;0;1] else [0;0;0;0;0]) ++ shifted bs
  end.

Definition wall (w:list Sym) : (Q*tape)%type :=
  (0inf <* <[1;1]) <* [0] {{A}}> w *> 0inf.

Definition E n bs := wall ([1;1]^^n ++ shifted bs).
Definition Ed n bs := wall ([1;1]^^n ++ shifted bs ++ [0;0;0;1;0]).
Definition O n bs := wall ([1;1]^^n ++ [1] ++ normal bs).
Definition Od n bs := wall ([1;1]^^n ++ [1] ++ normal bs ++ [0;0;0;0;1]).

Definition marked (parity:nat) (bs:list bool) :=
  exists pre post, bs = pre ++ true::post /\ (length pre mod 2 = parity)%nat.

Definition first_zero (bs:list bool) := exists rest, bs = false::rest.

Inductive invariant : (Q*tape)%type -> Prop :=
| InvE n bs :
    (length bs+2 <= n)%nat -> marked 1 bs -> invariant (E n bs)
| InvEd n bs :
    (length bs+3 <= n)%nat -> invariant (Ed n bs)
| InvO n bs :
    (length bs <= n)%nat -> first_zero bs -> In true bs -> invariant (O n bs)
| InvOd n bs :
    (length bs+1 <= n)%nat -> first_zero bs -> marked 0 bs -> invariant (Od n bs).

End WallInvariant.
End WallInvariant.

Module StrongInvariant.
(* Wall predicates retaining the digit information needed after conversion.
   Their global preservation is developed separately.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module StrongInvariant.
Module W := WallInvariant.WallInvariant.
Open Scope nat.

Definition odd_first bs :=
 exists u tail, bs=repeat false (u*2+1)++true::tail.
Definition adjacent_first bs :=
 exists u tail, 0<u /\ bs=repeat false u++true::true::tail.
Definition close_even_first bs :=
 exists a tail i, 0<a /\ bs=repeat false (10*a)++true::tail /\
 nth i bs false=true /\ i mod 2=1 /\ i<=14*a+3.
Definition digit_guard bs := odd_first bs \/ adjacent_first bs \/ close_even_first bs.

Inductive strong : (Q*tape)%type -> Prop :=
| StrongE n bs : length bs+2<=n -> digit_guard bs -> strong (W.E n bs)
| StrongEd n bs : (length bs+3=n \/ length bs+2=n) ->
    W.marked 1 bs -> strong (W.Ed n bs).

Lemma nth_true_split bs i : nth i bs false=true ->
 exists pre post, bs=pre++true::post /\ length pre=i.
Proof.
 gen i. induction bs as [|b bs IH]; intros i H; destruct i; cbn[nth] in H.
 - discriminate.
 - discriminate.
 - subst b. exists (@nil bool),bs. split; reflexivity.
 - destruct (IH i H) as [pre [post [E Hp]]].
   exists (b::pre),post. cbn[app length]. split; [rewrite E;reflexivity|lia].
Qed.

Lemma nth_true_marked bs i : nth i bs false=true -> i mod 2=1 -> W.marked 1 bs.
Proof.
 intros H Hp. destruct (nth_true_split bs i H) as [pre [post [E Hlen]]].
 exists pre,post. split; [exact E|rewrite Hlen;exact Hp].
Qed.

Lemma guard_marked bs : digit_guard bs -> W.marked 1 bs.
Proof.

 intros [[u [tail E]]|[[u [tail [Hu E]]]|[a [tail [i [Ha [E [Hbit [Hodd Hbound]]]]]]]]].
 - subst bs. exists (repeat false (u*2+1)),tail. split; [reflexivity|].
   rewrite repeat_length. lia.
 - subst bs. destruct (mod2 u) as [v Ev|v Ev]; subst u.
   + exists (repeat false (v*2)++[true]),tail. split.
     * rewrite <-app_assoc. reflexivity.
     * rewrite length_app,repeat_length. cbn[length]. lia.
   + exists (repeat false (1+v*2)),(true::tail). split; [reflexivity|].
     rewrite repeat_length. lia.
 - apply (nth_true_marked bs i); assumption.
Qed.

Lemma nth_append_true bs cs i : nth i bs false=true -> nth i (bs++cs) false=true.
Proof.
 intro H. destruct (nth_true_split bs i H) as [pre [post [E Hlen]]].
 assert (Hi:i<length bs) by (rewrite E,length_app;cbn[length];lia).
 rewrite app_nth1 by exact Hi. exact H.
Qed.

Lemma guard_append bs cs : digit_guard bs -> digit_guard (bs++cs).
Proof.

 intros [[u [tail E]]|[[u [tail [Hu E]]]|[a [tail [i [Ha [E [Hbit [Hodd Hbound]]]]]]]]].
 - left. exists u,(tail++cs). rewrite E,<-app_assoc. reflexivity.
 - right. left. exists u,(tail++cs). split; [exact Hu|].
   rewrite E,<-app_assoc. reflexivity.
 - right. right. exists a,(tail++cs),i. repeat split; try assumption.
   + rewrite E,<-app_assoc. reflexivity.
   + apply nth_append_true. exact Hbit.
Qed.

Lemma initial_guard : digit_guard [false;true;false;true].
Proof. left. exists 0,[false;true]. reflexivity. Qed.

Print Assumptions guard_marked.
Print Assumptions guard_append.
End StrongInvariant.
End StrongInvariant.

Module LocalPasses.
(* Local pass laws for a shift-overflow counter.
   Adapted from mxdys's SOCSSv5, for the table with F1 = 1RC.
   These lemmas alone do not prove nonhalting.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import BusyCoq.Longitudinal BusyCoq.ES_v3.
Import BusyCoq.DivModCases.
Import String List PeanoNat NArith Lia.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac cat :=
  eapply segRLs_sideRLs_concat ||
  eapply segRLs_concat.

Ltac tr :=
  eapply sideRLs_trans ||
  eapply segRLs_trans.

Ltac cat1 H :=
  cat; [apply H|].

Ltac wal := apply segRLs_wall''; esc.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Ltac seg_nil :=
  repeat (rewrite Nat.mul_1_r || rewrite Nat.add_sub);
  apply segRLs_nil.

Module Mirrored.

Definition local_tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").

Notation "c -->* c'" := (c -[ local_tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ local_tm ]->+ c') (at level 40).

Notation ld := [1;1].
Notation d0 := [0;0;0;0;0].
Notation d1 := [1;0;0;0;0].
Notation d1' := [0;0;0;0;1].


Notation hR := (A,[0]).
Notation hRx := (C,[]).
Notation hL := (C,[0]).
Notation h := [(hR,hL)].
Notation hx := [(hRx,hL)].
Notation hR' := (A,[]).
Notation hL' := (B,[]).
Notation h' := [(hR',hL')].

Open Scope nat.

Lemma ld_Incs k:
  segRLs local_tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  am 1 2 k 0 0.
Qed.

Lemma d0_Incs k:
  segRLs local_tm (h'^^(k*2)) (h'^^k) d0 d0.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma d01_Incs k:
  segRLs local_tm (h'^^(k*2+1)) (h'^^k) d0 d1.
Proof.
  am 2 1 k 1 0.
Qed.

Lemma d10_Incs k:
  segRLs local_tm (h'^^(k*2+1)) (h'^^(k+1)) d1 d0.
Proof.
  am 2 1 k 1 1.
Qed.

Lemma d1_Incs k:
  segRLs local_tm (h'^^(k*2)) (h'^^k) d1 d1.
Proof.
  am 2 1 k 0 0.
Qed.

Lemma m0_Incs k:
  segRLs local_tm (h^^k) (h'^^k) [] [].
Proof.
  wal.
Qed.

Lemma lds_Incs k n:
  segRLs local_tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  induction n.
  1: seg_nil.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  cat1 IHn.
  rewrite Nat.pow_add_r.
  applys_eq ld_Incs; flia.
Qed.

Lemma lds_Incs' k n:
  segRLs local_tm (h^^k) (h'^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  rewrite <-(app_nil_r (ld^^n)).
  cat1 lds_Incs.
  wal.
Qed.

Lemma d0s_Incs k n:
  segRLs local_tm (h'^^(k*2^n)) (h'^^k) (d0^^n) (d0^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn.
    applys_eq d0_Incs; flia.
Qed.

Lemma d01s_Incs k n:
  segRLs local_tm (h'^^((k+1)*2^n-1)) (h'^^k) (d0^^n) (d1^^n).
Proof.
  gen k.
  induction n; intros.
  - seg_nil.
  - cbn[Nat.pow lpow].
    cat.
    2: apply IHn.
    applys_eq d01_Incs; flia.
Qed.


Open Scope sym.
Notation lh := (0inf<*<[1;1]).

Lemma BigStep r r':
  sideRLs local_tm (h^^1) r r' ->
  lh {{{ (hR,R) }}} r -->+
  lh {{{ (hR,R) }}} [1]*>r'.
Proof.
  intros.
  eapply sideRLs_1 in H.
  follow10 H.
  er.
Qed.

Print Assumptions ld_Incs.
Print Assumptions d01s_Incs.
Print Assumptions BigStep.
End Mirrored.

Definition local_tm := Eval compute in
  (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC").
End LocalPasses.

Module OddNormal.
(* The first conversion of an odd wall with ordinary binary digits.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module OddNormal.
Definition mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation ld := [1;1].
Notation h := [((A,[0]),(C,[0]))].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].
Notation hx := [((C,[]),(C,[0]))].

Notation one := [1].
Notation z3 := [0;0;0].
Open Scope nat.

Lemma c_zero_even k :
 segRLs mtm (x^^(k*2)) (x^^k) a a.
Proof. am 2 1 k 0 0. Qed.
Lemma c_zero_odd k :
 segRLs mtm (x^^(k*2+1)) (x^^k) a c.
Proof. am 2 1 k 1 0. Qed.
Lemma c_one_even k :
 segRLs mtm (x^^(k*2)) (x^^k) c c.
Proof. am 2 1 k 0 0. Qed.
Lemma c_one_odd k :
 segRLs mtm (x^^(k*2+1)) (x^^(k+1)) c a.
Proof. am 2 1 k 1 1. Qed.

Lemma d_zero_even k :
 segRLs mtm (y^^(k*2)) (y^^k) a a.
Proof. am 2 1 k 0 0. Qed.
Lemma d_zero_odd k :
 segRLs mtm (y^^(k*2+1)) (y^^k) a d.
Proof. am 2 1 k 1 0. Qed.
Lemma d_one_even k :
 segRLs mtm (y^^(k*2)) (y^^k) d d.
Proof. am 2 1 k 0 0. Qed.
Lemma d_one_odd k :
 segRLs mtm (y^^(k*2+1)) (y^^(k+1)) d a.
Proof. am 2 1 k 1 1. Qed.

Lemma one_pair : segRLs mtm (h^^2) x one one.
Proof. esc. Qed.

Lemma one_pairs k : segRLs mtm (h^^(k*2)) (x^^k) one one.
Proof.
 induction k.
 - cbn. constructor.
 - replace (S k*2) with (2+k*2)%nat by lia.
   rewrite lpow_add.
   change (segRLs mtm (h^^2 ++ h^^(k*2)) (x++x^^k) one one).
   eapply segRLs_trans; [apply one_pair|apply IHk].
Qed.

Lemma c_zeros_allones k n :
 segRLs mtm (x^^((k+1)*2^n-1)) (x^^k) (a^^n) (c^^n).
Proof.
 gen k.
 induction n; intros.
 - cbn [Nat.pow lpow].
   replace ((k+1)*1-1)%nat with k by lia.
   apply segRLs_nil.
 - cbn [Nat.pow lpow].
   eapply segRLs_concat.
   2: apply IHn.
   pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
   replace ((k+1)*(2*2^n)-1)%nat with (((k+1)*2^n-1)*2+1)%nat by nia.
   apply c_zero_odd.
Qed.

Lemma prime_first u :
 segRLs mtm (h^^((2^u-1)*2)) []
  (one++a^^u) (one++c^^u).
Proof.
 eapply segRLs_concat.
 - apply one_pairs.
 - pose proof (c_zeros_allones 0 u) as H.
   cbn [Nat.add Nat.mul lpow] in H.
   rewrite Nat.add_0_r in H.
   exact H.
Qed.

Lemma one_expand k :
 segRLs mtm (h^^(1+k)) (hx++h^^(1+k*2)) one ld.
Proof.
 replace (h^^(1+k)) with (h++h^^k) by reflexivity.
 replace (hx++h^^(1+k*2)) with ((hx++h)++h^^(k*2)).
 2: cbn [lpow]; reflexivity.
 eapply @segRLs_trans with (w2:=ld).
 - esc.
 - apply LocalPasses.Mirrored.ld_Incs.
Qed.

Lemma first_conversion u :
 segRLs mtm hx [] (c^^u++b) (one^^(5*u+1)++z3).
Proof.
 induction u.
 - cbn [lpow]. esc.
 - replace (5*S u+1) with (5+(5*u+1)) by lia.
   rewrite lpow_add.
   cbn [lpow].
   change (segRLs mtm hx [] (c ++ (c^^u++b)) ((one^^5) ++ (one^^(5*u+1)++z3))).
   eapply segRLs_concat.
   2: exact IHu.
   esc.
Qed.

Lemma odd_first_reduction u k r r' :
 sideRLs mtm (h^^(1+k*2))
  (one^^(5*u+1) *> z3 *> r) r' ->

 sideRLs mtm (h^^((2^u-1)*2+(1+k)))
  (one *> a^^u *> b *> r) (ld *> r').
Proof.
 intro H.
 rewrite lpow_add.
 eapply @sideRLs_trans with (r2:=one *> c^^u *> b *> r).
 - eapply @segRLs_sideRLs_concat with
     (w1:=one++a^^u) (w2:=one++c^^u) (ls2:=[]).
   + apply prime_first.
   + constructor.
 - eapply segRLs_sideRLs_concat.
   + apply one_expand.
   + eapply @sideRLs_trans with (r2:=one^^(5*u+1) *> z3 *> r).
     * repeat rewrite <-Str_app_assoc.
       eapply @segRLs_sideRLs_concat with
        (w1:=c^^u++b) (w2:=one^^(5*u+1)++z3) (ls2:=[]).
       -- apply first_conversion.
       -- constructor.
     * exact H.
Qed.

Print Assumptions prime_first.
Print Assumptions first_conversion.
Print Assumptions odd_first_reduction.
End OddNormal.
End OddNormal.

Module CounterRules.
(* Two-counter rules for a shift-overflow machine.
   The binary-counter interface follows mxdys's SOC_2_5_v1.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia PeanoNat String List.
Open Scope sym.

Module CounterRules.

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.

Ltac follow_rule H :=
  intros;
  epose proof H as HX;
  cbn[Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *;
  follow10 HX;
  repeat (simpl_rotate || simpl_tape);
  finish.
Definition local_tm := Eval compute in
 (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").
Notation "c -->* c'" := (c -[local_tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[local_tm]->+ c') (at level 40).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma left_increment l r n :
 l <* ld0 <* ld1^^n <| r -->+
 l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma right_increment l r n :
 l |> rd1^^n *> [0] *> r -->+
 l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma left_overflow r n :
 ldh <* ld1^^n <| r -->+
 ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.

Lemma left_counter len n r :
 1+n < 2^len ->
 LC len (1+n) <| r -->+
 LC len n |> r.
Proof.
 intros H.
 apply LBinDec_spec; try lia.
 follow_rule left_increment.
Qed.

Lemma right_counter n l :
 l |> RC n -->+
 l <| RC (1+n).
Proof.
 apply RBinInc_spec.
 follow_rule right_increment.
Qed.

Lemma counter_round len n m :
 1+n < 2^len ->
 LC len (1+n) |> RC m -->+
 LC len n |> RC (1+m).
Proof.
 intros H.
 eapply progress_trans.
 - apply right_counter.
 - apply left_counter; exact H.
Qed.

Lemma counter_rounds len n m k :
 n+k < 2^len ->
 LC len (n+k) |> RC m -->*
 LC len n |> RC (m+k).
Proof.
 gen n m.
 induction k; intros n m H.
 - repeat rewrite Nat.add_0_r. finish.
 - replace (n+S k) with (1+(n+k)) by lia.
   apply progress_evstep.
   eapply progress_evstep_trans.
   + apply counter_round. lia.
   + replace (m+S k) with ((1+m)+k) by lia.
     apply IHk. lia.
Qed.

Print Assumptions left_increment.
Print Assumptions right_increment.
Print Assumptions left_overflow.
Print Assumptions counter_rounds.
End CounterRules.
End CounterRules.

Module CounterBatch.
(* Composing a right-pass certificate with the left counter.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import CounterRules.CounterRules WallInvariant.WallInvariant.
Open Scope sym.

Module CounterBatch.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).
Notation p := [((A,[]),(B,[]))].

Lemma left_one len k :
  (1+k < 2^len)%nat ->
  sideLR mtm (B,[]) (A,[])
    (LC len (1+k) <* [0;1]) (LC len k <* [0;1]).
Proof.
  intros Hk r.
  assert (H : (LC len (1+k) <* [0;1]) <{{B}} r -[mtm]->+
              LC len (1+k) <| r) by esx.
  follow10 H.
  apply progress_evstep, left_counter. exact Hk.
Qed.

Lemma left_one_flip len k :
  (1+k < 2^len)%nat ->
  sideRL (flip mtm) (B,[]) (A,[])
    (LC len (1+k) <* [0;1]) (LC len k <* [0;1]).
Proof.
  intros Hk r.
  exact (flip_progress mtm _ _ (left_one len k Hk r)).
Qed.

Lemma left_batch len k amount :
  (k+amount < 2^len)%nat ->
  sideRLs (flip mtm) ([((B,[]),(A,[]))]^^amount)
    (LC len (k+amount) <* [0;1]) (LC len k <* [0;1]).
Proof.
  gen k. induction amount; intros k Hk.
  - rewrite Nat.add_0_r. constructor.
  - replace (k+S amount)%nat with (1+(k+amount))%nat by lia.
    cbn [lpow app]. econstructor.
    + apply left_one_flip. lia.
    + apply IHamount. lia.
Qed.

Lemma right_pass_batch len k amount r r' :
  (k+amount < 2^len)%nat ->
  sideRLs mtm (p^^amount) r r' ->
  LC len (k+amount) |> r -[mtm]->* LC len k |> r'.
Proof.
  intros Hk Hr.
  exact (sideRLs_concat_1 Hr (left_batch len k amount Hk)).
Qed.

Print Assumptions right_pass_batch.
End CounterBatch.
End CounterBatch.

Module CounterFinish.
(* Returning from an ordinary counter to a wall configuration.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v3 BusyCoq.DivModCases.
Import CounterRules WallInvariant.
Import String List PeanoNat NArith Lia.
Import CounterRules.CounterRules WallInvariant.WallInvariant.
Open Scope sym.

Module CounterFinish.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma return_wall n r :
  LC n 0 <| r -[mtm]->+
  (0inf <* <[1;1]) <* [0] {{A}}> ([1] *> [1;1]^^n *> r).
Proof.
  unfold LC. rewrite BinDec_O.
  esx.
Qed.

Lemma counter_finish n k r :
  (k < 2^n)%nat ->
  LC n k |> RC r -[mtm]->+
  (0inf <* <[1;1]) <* [0] {{A}}> ([1] *> [1;1]^^n *> RC (r+k+1)).
Proof.
  intro Hk.
  eapply evstep_progress_trans.
  - applys_eq (counter_rounds n 0 r k Hk).
  - eapply progress_trans.
    + apply right_counter.
    + replace (1+(r+k))%nat with (r+k+1)%nat by lia.
      apply return_wall.
Qed.

Open Scope nat.

Fixpoint digits (n v:nat) : list bool :=
  match n with
  | 0 => []
  | S n => (v mod 2 =? 1) :: digits n (v/2)
  end.

Lemma digits_length n v : length (digits n v) = n.
Proof. gen v. induction n; cbn; intros; auto. Qed.

Lemma digits_even n v : digits (S n) (v*2) = false::digits n v.
Proof.
  cbn [digits]. rewrite Nat.mod_mul, Nat.div_mul by lia. reflexivity.
Qed.

Lemma digits_odd n v : digits (S n) (v*2+1) = true::digits n v.
Proof.
  cbn [digits].
  rewrite Nat.add_comm, Nat.mod_add by lia.
  replace ((1+v*2)/2) with v by (rewrite Nat.div_add; lia).
  reflexivity.
Qed.

Lemma digits_normal n v :
  v < 2^n -> normal (digits n v) *> 0inf = RC v.
Proof.
  gen v. induction n; intros v Hv.
  - cbn in Hv. assert (v=0) by lia. subst. reflexivity.
  - destruct (mod2 v); subst.
    + rewrite digits_even. cbn [normal].
      rewrite Str_app_assoc, IHn by (cbn in Hv; lia).
      unfold RC. rewrite BinInc_mul2. reflexivity.
    + rewrite Nat.add_comm. rewrite digits_odd. cbn [normal].
      rewrite Str_app_assoc, IHn by (cbn in Hv; lia).
      unfold RC. rewrite BinInc_mul2add1. reflexivity.
Qed.

Print Assumptions return_wall.
Print Assumptions counter_finish.
Print Assumptions digits_normal.
End CounterFinish.
End CounterFinish.

Module BoundaryRules.
(* Boundary rules for a shift-overflow counter.
   The unchanged conversion interfaces follow mxdys's SOC_2_5_v1.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import NArith Lia PeanoNat String List.
Open Scope sym.

Module BoundaryRules.

Lemma unrotate_ten n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
 a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
 [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof. simpl_rotate. reflexivity. Qed.

Ltac rw_unrotate_0 ::=
 (rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 || rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite unrotate_ten).

Definition local_tm := Eval compute in
 (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RC").
Notation "c -->* c'" := (c -[local_tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[local_tm]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation rd1 := [1;0;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma gap0_even l r n:
 l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma gap0_odd l r n:
 l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.

Lemma gap2_even l r n:
 l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma gap2_odd l r n:
 l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
 l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.
Proof. es. Qed.

Lemma gap3_forward l r n:
 l |> rd1^^n *> [1;0;0;0;1;0;0;0;0] *> r -->+
 l <* [0;1] <* [1]^^(n*5+9) {{A}}> r.
Proof. es. Qed.

Lemma gap3_zero l r n:
 l |> rd1^^n *> [1;0;0;0;1;0;0;0;0;0] *> r -->+
 l <| [0]^^(n*5+9) *> [1] *> r.
Proof. es. Qed.

Lemma gap1_reaches_D1 l r n:
 l |> rd1^^n *> [1;0;1] *> r -->*
 l <* [0;1] <* [1]^^(n*5+2) {{D}}> [1] *> r.
Proof. es. Qed.

Notation hp := [((A,[0]),(C,[0]))].
Notation cp := [((C,[]),(B,[]))].
Notation xp := [((C,[]),(C,[0]))].
Notation dz := [0;0;0;0;0].
Notation ds := [0;0;0;0;1].
Notation ones5 := [1;1;1;1;1].

Ltac bounded :=
 apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.

Lemma conversion_digit:
 segRLs local_tm xp xp ds ones5.
Proof. bounded. Qed.

Lemma conversion_stop:
 segRLs local_tm xp [] rd1 [1;0;0;0].
Proof. bounded. Qed.

Lemma conversion_digits n:
 segRLs local_tm xp xp (ds^^n) (ones5^^n).
Proof.
 induction n.
 - cbn[lpow]. apply segRLs_nil.
 - cbn[lpow]. eapply segRLs_concat.
   + apply conversion_digit.
   + exact IHn.
Qed.

Lemma conversion_stopped n:
 segRLs local_tm xp [] (ds^^n ++ rd1) (ones5^^n ++ [1;0;0;0]).
Proof.
 eapply segRLs_concat.
 - apply conversion_digits.
 - apply conversion_stop.
Qed.

Lemma odd_prefix_x_one:
 segRLs local_tm hp (xp++hp) [1] [1;1].
Proof. bounded. Qed.

Lemma even_prefix_two:
 segRLs local_tm hp (hp^^2) [1;1] [1;1].
Proof. bounded. Qed.

Lemma even_prefix_many k:
 segRLs local_tm (hp^^k) (hp^^(k*2)) [1;1] [1;1].
Proof.
 induction k.
 - cbn[lpow]. constructor.
 - replace (S k) with (1+k) at 1 by lia.
   replace (S k*2) with (2+k*2) by lia.
   repeat rewrite lpow_add.
   eapply segRLs_trans.
   + apply even_prefix_two.
   + exact IHk.
Qed.

Lemma odd_prefix_x k:
 segRLs local_tm (hp^^(k+1)) (xp++hp^^(k*2+1)) [1] [1;1].
Proof.
 replace (k+1) with (1+k) by lia.
 replace (k*2+1) with (1+k*2) by lia.
 repeat rewrite lpow_add.
 replace (xp ++ hp ^^ 1 ++ hp ^^ (k * 2))
   with ((xp++hp)++hp^^(k*2)) by (cbn[lpow]; repeat rewrite app_nil_r; symmetry; apply app_assoc).
 eapply segRLs_trans.
 - apply odd_prefix_x_one.
 - apply even_prefix_many.
Qed.

Lemma odd_prefix_c_two:
 segRLs local_tm (hp^^2) cp [1] [1].
Proof. bounded. Qed.

Lemma odd_prefix_c k:
 segRLs local_tm (hp^^(k*2)) (cp^^k) [1] [1].
Proof.
 induction k.
 - cbn[lpow]. constructor.
 - replace (S k*2) with (2+k*2) by lia.
   replace (S k) with (1+k) by lia.
   repeat rewrite lpow_add.
   eapply segRLs_trans.
   + apply odd_prefix_c_two.
   + exact IHk.
Qed.

Lemma c_zero_two:
 segRLs local_tm (cp^^2) cp dz dz.
Proof. bounded. Qed.

Lemma c_zero_one:
 segRLs local_tm cp [] dz ds.
Proof. bounded. Qed.

Lemma c_zero_even k:
 segRLs local_tm (cp^^(k*2)) (cp^^k) dz dz.
Proof.
 induction k.
 - cbn[lpow]. constructor.
 - replace (S k*2) with (2+k*2) by lia.
   replace (S k) with (1+k) by lia.
   repeat rewrite lpow_add.
   eapply segRLs_trans.
   + apply c_zero_two.
   + exact IHk.
Qed.

Lemma c_zero_odd k:
 segRLs local_tm (cp^^(k*2+1)) (cp^^k) dz ds.
Proof.
 rewrite lpow_add.
 replace (cp^^k : list (DH0*DH0)) with (cp^^k++[] : list (DH0*DH0)) by apply app_nil_r.
 eapply segRLs_trans.
 - apply c_zero_even.
 - cbn[lpow]. apply c_zero_one.
Qed.

Lemma c_fill_zeros k n:
 segRLs local_tm (cp^^((k+1)*2^n-1)) (cp^^k) (dz^^n) (ds^^n).
Proof.
 gen k. induction n; intros.
 - cbn[Nat.pow lpow].
   replace ((k+1)*1-1) with k by lia.
   apply segRLs_nil.
 - cbn[Nat.pow lpow].
   eapply segRLs_concat.
   2: apply IHn.
   pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
   replace ((k+1)*(2*2^n)-1) with (((k+1)*2^n-1)*2+1) by nia.
   apply c_zero_odd.
Qed.

Lemma before_conversion j:
 segRLs local_tm (hp^^((2^j-1)*2)) []
   ([1]++dz^^j) ([1]++ds^^j).
Proof.
 eapply segRLs_concat.
 - apply odd_prefix_c.
 - pose proof (c_fill_zeros 0 j) as H.
   cbn[lpow] in H.
   replace ((0+1)*2^j-1) with (2^j-1) in H by lia.
   exact H.
Qed.

Lemma conversion_side j r:
 sideRLs local_tm xp (ds^^j *> rd1 *> r) (ones5^^j *> [1;0;0;0] *> r).
Proof.
 repeat rewrite <-Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply conversion_stopped.
 - constructor.
Qed.

Lemma odd_conversion j q r r':
 sideRLs local_tm (hp^^(q*2+1)) (ones5^^j *> [1;0;0;0] *> r) r' ->
 sideRLs local_tm (hp^^((2^j-1)*2+q+1))
   ([1] *> dz^^j *> rd1 *> r) ([1;1] *> r').
Proof.
 intro H.
 replace ((2^j-1)*2+q+1) with ((2^j-1)*2+(q+1)) by lia.
 rewrite lpow_add.
 eapply @sideRLs_trans with (r2:=[1] *> ds^^j *> rd1 *> r).
 - eapply @segRLs_sideRLs_concat with
     (w1:=[1]++dz^^j) (w2:=[1]++ds^^j) (ls2:=[]).
   + apply before_conversion.
   + constructor.
 - eapply segRLs_sideRLs_concat.
   + apply odd_prefix_x.
   + eapply sideRLs_trans.
     * apply conversion_side.
     * exact H.
Qed.

Print Assumptions gap0_even.
Print Assumptions gap0_odd.
Print Assumptions gap2_even.
Print Assumptions gap2_odd.
Print Assumptions gap3_forward.
Print Assumptions gap3_zero.
Print Assumptions gap1_reaches_D1.
Print Assumptions conversion_stopped.
Print Assumptions odd_prefix_x.
Print Assumptions odd_prefix_c.
Print Assumptions c_fill_zeros.
Print Assumptions odd_conversion.
End BoundaryRules.
End BoundaryRules.

Module OddFuel.
(* Counter-fuel rules for the odd-wall conversion.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.BinaryCounter_v2 BusyCoq.ES_v3.
Import LocalPasses OddNormal CounterRules CounterBatch CounterFinish BoundaryRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations CounterRules.CounterRules CounterBatch.CounterBatch.
Open Scope sym.

Module OddFuel.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation one := [1].
Notation ld := [1;1].
Notation lh := (0inf <* <[1;1]).
Notation zero := [0].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation g0 := [1;1;0;0;0;0].
Notation g2 := [1;0;0;1;0;0;0;0].
Notation t3 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma scan_ones n r :
 lh <* zero {{A}}> (ld^^n *> r) -[mtm]->*
 LC n (2^n-1) |> r.
Proof.

 unfold LC. rewrite BinDec_full.
 esx.
Qed.

Definition grown k z := (2*k+1)*2^z-1.

Lemma grown_bound L k z :
 k < 2^L -> grown k z+1 < 2^(L+1+z).
Proof.

 intro Hk. unfold grown.
 rewrite Nat.pow_add_r, Nat.pow_add_r.
 cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia.
Qed.

Lemma grow_left L k z :
 k < 2^L ->
 LC L k <* ld1 <* ld0^^z = LC (L+1+z) (grown k z).
Proof.

 intro Hk. unfold LC, grown.
 replace (2*k) with (k*2) by lia.
 rewrite BinDec_mulpow2sub1.
 - reflexivity.
 - rewrite Nat.pow_add_r, Nat.pow_add_r. cbn [Nat.pow].
   pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia.
Qed.

Lemma p_one_pairs k : segRLs mtm (p^^(k*2)) (x^^k) one one.
Proof.

 induction k.
 - cbn [lpow]. constructor.
 - replace (S k*2) with (2+k*2) by lia.
   rewrite lpow_add.
   change (segRLs mtm (p^^2++p^^(k*2)) (x++x^^k) one one).
   eapply @segRLs_trans with (w2:=one).
   + esc.
   + exact IHk.
Qed.

Lemma prime_one u :
 segRLs mtm (p^^((2^u-1)*2)) [] (one++a^^u) (one++c^^u).
Proof.

 eapply segRLs_concat.
 - apply p_one_pairs.
 - pose proof (OddNormal.c_zeros_allones 0 u) as H.
   cbn [Nat.add Nat.mul lpow] in H.
   rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma prime_gap0 u r :
 sideRLs mtm (p^^((2^u-1)*2))
   (one *> a^^u *> b *> r)
   (b^^u *> g0 *> r).
Proof.

 assert (E : one++c^^u++b = b^^u++g0).
 { induction u.
   - reflexivity.
   - cbn [lpow] in *. cbn [app] in *. congruence. }
 repeat rewrite <-Str_app_assoc.
 rewrite <-E. repeat rewrite Str_app_assoc.
 eapply @segRLs_sideRLs_concat with (w1:=one++a^^u) (w2:=one++c^^u) (ls2:=[]).
 - apply prime_one.
 - constructor.
Qed.

Lemma p_third_one : segRLs mtm p [] d t3.
Proof. esc. Qed.

Lemma prime_gap2 u r :
 sideRLs mtm (p^^(2^(u+1)-1))
   (a^^u *> d *> z3 *> r)
   (b^^u *> g2 *> r).
Proof.

 eapply @segRLs_sideRLs_concat with (ls2:=p).
 - applys_eq (LocalPasses.Mirrored.d01s_Incs 1 u).
   rewrite Nat.pow_add_r. cbn [Nat.pow]. flia.
 - change (sideRLs mtm p (d *> z3 *> r) (t3 *> z3 *> r)).
   eapply @segRLs_sideRLs_concat with (ls2:=[]).
   + apply p_third_one.
   + constructor.
Qed.

Lemma convert_gap0_even L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2) *> g0 *> r -[mtm]->+
 LC (L+1+v*5) (grown k (v*5)) |> r4 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap0_even.
Qed.

Lemma convert_gap0_odd L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2+1) *> g0 *> r -[mtm]->+
 LC (L+1+(v*5+3)) (grown k (v*5+3)) |> z3 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap0_odd.
Qed.

Lemma convert_gap2_even L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2) *> g2 *> r -[mtm]->+
 LC (L+1+(v*5+1)) (grown k (v*5+1)) |> r4 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap2_even.
Qed.

Lemma convert_gap2_odd L k v r :
 k < 2^L ->
 LC L k |> b^^(v*2+1) *> g2 *> r -[mtm]->+
 LC (L+1+(v*5+4)) (grown k (v*5+4)) |> z3 *> r.
Proof.

 intro Hk. rewrite <-grow_left by exact Hk.
 apply BoundaryRules.gap2_odd.
Qed.

Lemma right_pass_finish n k r r' :
 k < 2^n -> sideRLs mtm (p^^(k+1)) r r' ->
 LC n k |> r -[mtm]->+
 lh <* zero {{A}}> (one *> ld^^n *> r').
Proof.

 intros Hk Hr. rewrite lpow_add in Hr.
 destruct (sideRLs_split Hr) as [middle [Hfirst Hlast]].
 eapply evstep_progress_trans.
 - replace k with (0+k) at 1 by lia.
   apply right_pass_batch.
   + cbn [Nat.add]. exact Hk.
   + exact Hfirst.
 - eapply progress_trans.
   + exact (sideRLs_1 _ _ _ _ _ Hlast (LC n 0 <* ([0;1]%sym))).
   + eapply progress_trans.
     * assert (H : (LC n 0 <* ([0;1]%sym)) <{{B}} r' -[mtm]->+
         LC n 0 <{{C}} ([0;1]%sym) *> r') by esx.
       exact H.
     * apply CounterFinish.return_wall.
Qed.

Print Assumptions scan_ones.
Print Assumptions prime_gap0.
Print Assumptions prime_gap2.
Print Assumptions convert_gap2_odd.
End OddFuel.
End OddFuel.

Module CDPasses.
(* A context-pass addition law for the third-position digit encoding.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses.
Import String List PeanoNat NArith Lia.
Import ListNotations.
Open Scope sym.

Module CDPasses.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation a := [0;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].

Definition bitval (b:bool) : nat := if b then 1 else 0.
Definition third_digit (b:bool) : list Sym := if b then d else a.
Definition fourth_digit (b:bool) : list Sym := if b then c else a.
Fixpoint third (bs:list bool) : list Sym :=
 match bs with [] => [] | b::bs => third_digit b ++ third bs end.
Fixpoint fourth (bs:list bool) : list Sym :=
 match bs with [] => [] | b::bs => fourth_digit b ++ fourth bs end.

Fixpoint value (bs:list bool) : nat :=
 match bs with [] => 0 | b::bs => bitval b + 2*value bs end.
Fixpoint any (bs:list bool) : bool :=
 match bs with [] => false | b::bs => orb b (any bs) end.

Definition mass (pending:bool) (n:nat) : list (DH0*DH0) :=
 if pending then y ++ x^^(n-1) else x^^n.

Open Scope nat.
Lemma c_zero_even k : segRLs mtm (x^^(k*2)) (x^^k) a a.
Proof. am 2 1 k 0 0. Qed.
Lemma c_zero_odd k : segRLs mtm (x^^(k*2+1)) (x^^k) a c.
Proof. am 2 1 k 1 0. Qed.
Lemma c_phase_hit : segRLs mtm x y d a.
Proof. esc. Qed.
Lemma d_zero : segRLs mtm y [] a d.
Proof. esc. Qed.
Lemma d_one : segRLs mtm y y d a.
Proof. esc. Qed.

Lemma c_phase_even k : k<>0 ->
 segRLs mtm (x^^(k*2)) (y++x^^(k-1)) d c.
Proof.

 intro H.
 replace (k*2) with (1+((k-1)*2+1)) by lia.
 rewrite lpow_add.
 eapply segRLs_trans.
 - apply c_phase_hit.
 - apply c_zero_odd.
Qed.
Lemma c_phase_odd k :
 segRLs mtm (x^^(k*2+1)) (y++x^^k) d a.
Proof.

 replace (k*2+1) with (1+k*2) by lia.
 rewrite lpow_add.
 eapply segRLs_trans.
 - apply c_phase_hit.
 - apply c_zero_even.
Qed.
Lemma dc_zero_even k : k<>0 ->
 segRLs mtm (y++x^^(k*2)) (y++x^^(k-1)) a c.
Proof.

 intro H.
 eapply @segRLs_trans with (ls2:=[]) (w2:=d).
 - apply d_zero.
 - apply c_phase_even; exact H.
Qed.
Lemma dc_zero_odd k :
 segRLs mtm (y++x^^(k*2+1)) (y++x^^k) a a.
Proof.

 eapply @segRLs_trans with (ls2:=[]) (w2:=d).
 - apply d_zero.
 - apply c_phase_odd.
Qed.
Lemma dc_one_even k :
 segRLs mtm (y++x^^(k*2)) (y++x^^k) d a.
Proof.

 eapply segRLs_trans.
 - apply d_one.
 - apply c_zero_even.
Qed.
Lemma dc_one_odd k :
 segRLs mtm (y++x^^(k*2+1)) (y++x^^k) d c.
Proof.

 eapply segRLs_trans.
 - apply d_one.
 - apply c_zero_odd.
Qed.

Lemma mass_even k old bit : k<>0 ->
 segRLs mtm (mass old (k*2)) (mass (orb old bit) k)
   (third_digit bit) (fourth_digit bit).
Proof.

 intro H. destruct old,bit; unfold mass,third_digit,fourth_digit; cbn[orb].
 - replace (k*2-1) with ((k-1)*2+1) by lia. apply dc_one_odd.
 - replace (k*2-1) with ((k-1)*2+1) by lia. apply dc_zero_odd.
 - apply c_phase_even; exact H.
 - apply c_zero_even.
Qed.
Lemma mass_odd k old bit : k<>0 ->
 segRLs mtm (mass old (1+k*2)) (mass (orb old bit) (k+bitval bit))
   (third_digit bit) (fourth_digit (negb bit)).

Proof.

 intro H. destruct old,bit; unfold mass,third_digit,fourth_digit,bitval; cbn[orb negb].
 - replace (1+k*2-1) with (k*2) by lia.
   replace (k+1-1) with k by lia. apply dc_one_even.
 - replace (1+k*2-1) with (k*2) by lia.
   rewrite Nat.add_0_r. apply dc_zero_even; exact H.
 - replace (k+1-1) with k by lia.
   replace (1+k*2) with (k*2+1) by lia. apply c_phase_odd.
 - rewrite Nat.add_0_r.
   replace (1+k*2) with (k*2+1) by lia. apply c_zero_odd.

Qed.

Lemma value_bound bs : value bs < 2^length bs.
Proof.

 induction bs as [|b bs IH]; cbn[length value Nat.pow]; [lia|].
 destruct b; cbn[bitval]; nia.
Qed.

Lemma mass_digits bs old n :
 2^length bs <= n ->
 exists out carry,
 length out = length bs /\
 2^length bs*carry+value out = n+value bs /\
 1<=carry /\
 segRLs mtm (mass old n) (mass (orb old (any bs)) carry)
   (third bs) (fourth out).
Proof.

 gen old n. induction bs as [|bit bs IH]; intros old n Hn.
 - exists (@nil bool),n. cbn[length value third fourth any Nat.pow].
   repeat split; try lia.
   replace (orb old false) with old by (destruct old; reflexivity).
   apply segRLs_nil.
 - assert (Hp:0<2^length bs).
   { pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); lia. }
   cbn[length Nat.pow] in Hn.
   destruct (mod2 n) as [q E|q E]; subst n.

   + assert (Hq:2^length bs<=q) by nia.
     destruct (IH (orb old bit) q Hq) as [out [carry [Hlen [Hv [Hcarry Hseg]]]]].
     exists (bit::out),carry.
     cbn[length value third fourth any Nat.pow].
     repeat split; try lia; try nia.

     replace (orb old (orb bit (any bs))) with (orb (orb old bit) (any bs))
       by (destruct old,bit; reflexivity).
     eapply segRLs_concat.
     * apply mass_even. nia.
     * exact Hseg.
   + assert (Hq:2^length bs<=q) by nia.
     assert (Hnext:2^length bs<=q+bitval bit) by lia.
     destruct (IH (orb old bit) (q+bitval bit) Hnext)
       as [out [carry [Hlen [Hv [Hcarry Hseg]]]]].
     exists (negb bit::out),carry.

     cbn[length value third fourth any Nat.pow].
     repeat split; try lia.

     * destruct bit; cbn[bitval negb] in *; nia.
     * replace (orb old (orb bit (any bs))) with (orb (orb old bit) (any bs))
         by (destruct old,bit; reflexivity).
       eapply segRLs_concat.
       -- apply mass_odd. nia.
       -- exact Hseg.
Qed.

Definition terminal (pending:bool) : list Sym := if pending then d else c.

Lemma flush_one old :
 sideRLs mtm (mass old 1) 0inf (terminal old *> 0inf).
Proof. destruct old; unfold mass,terminal; cbn[lpow]; esc. Qed.

Lemma mass_flush budget old n :
 0<n<2^budget ->
 exists out : list bool,
 length out < budget /\
 value out+2^length out=n /\
 sideRLs mtm (mass old n) 0inf (fourth out *> terminal old *> 0inf).
Proof.

 gen old n. induction budget as [|budget IH]; intros old n Hn.
 - cbn[Nat.pow] in Hn. lia.
 - destruct (Nat.eq_dec n 1) as [E|E].
   + subst n. exists (@nil bool). cbn[length value fourth Nat.pow].
     repeat split; try lia. apply flush_one.
   + assert (Hn2:2<=n) by lia.
     cbn[Nat.pow] in Hn.
     destruct (mod2 n) as [q He|q He]; subst n.
     * assert (Hq:0<q<2^budget) by nia.
       destruct (IH old q Hq) as [out [Hlen [Hv Hseg]]].

       exists (false::out).
       cbn[length value fourth Nat.pow bitval fourth_digit].
       repeat split; try lia; try nia.

       rewrite Str_app_assoc.
       replace 0inf with (a *> 0inf) at 1 by (st; reflexivity).
       eapply segRLs_sideRLs_concat.
       -- pose proof (mass_even q old false ltac:(lia)) as H.
          rewrite Bool.orb_false_r in H. exact H.
       -- exact Hseg.
     * assert (Hq:0<q<2^budget) by nia.
       destruct (IH old q Hq) as [out [Hlen [Hv Hseg]]].
       exists (true::out).
       cbn[length value fourth Nat.pow bitval fourth_digit].

       repeat split; try lia; try nia.

       rewrite Str_app_assoc.
       replace 0inf with (a *> 0inf) at 1 by (st; reflexivity).
       eapply segRLs_sideRLs_concat.
       -- pose proof (mass_odd q old false ltac:(lia)) as H.
          rewrite Bool.orb_false_r in H. cbn[bitval negb] in H.
          rewrite Nat.add_0_r in H. exact H.
       -- exact Hseg.
Qed.

Lemma value_append left right :
 value (left++right)=value left+2^length left*value right.
Proof.

 induction left as [|b left IH]; cbn[app length value Nat.pow]; [lia|].
 rewrite IH. nia.
Qed.
Lemma fourth_append left right :
 fourth (left++right)=fourth left++fourth right.
Proof.

 induction left as [|b left IH]; cbn[app fourth]; [reflexivity|].
 rewrite IH,app_assoc. reflexivity.
Qed.

Lemma mass_full bs old n z :
 2^length bs<=n -> n+value bs<2^(length bs+z) ->
 exists out : list bool,
 length out<length bs+z /\
 value out+2^length out=n+value bs /\
 sideRLs mtm (mass old n) (third bs *> 0inf)
   (fourth out *> terminal (orb old (any bs)) *> 0inf).
Proof.

 intros Hn Hbound.
 destruct (mass_digits bs old n Hn)
   as [low [carry [Hlen [Hv [Hcarry Hseg]]]]].
 assert (Hp:0<2^length bs).
 { pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); lia. }
 assert (Hc:0<carry<2^z).
 { rewrite Nat.pow_add_r in Hbound. nia. }
 destruct (mass_flush z (orb old (any bs)) carry Hc)
   as [high [Hhigh [Hvalue Hflush]]].
 exists (low++high).
 rewrite length_app,value_append,Hlen,Nat.pow_add_r.

 split; [lia|]. split; [nia|].
 rewrite fourth_append,Str_app_assoc.

 eapply segRLs_sideRLs_concat; eauto.
Qed.

Print Assumptions mass_even.
Print Assumptions mass_odd.
Print Assumptions mass_digits.
Print Assumptions mass_flush.
Print Assumptions mass_full.
End CDPasses.
End CDPasses.

Module OddImage.
(* Exact images of odd-wall conversions, with arithmetic bounds explicit.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses OddFuel CDPasses CounterRules CounterBatch WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Module OddImage.
Module W := WallInvariant.WallInvariant.
Module F := OddFuel.OddFuel.
Module CD := CDPasses.CDPasses.
Module CR := CounterRules.CounterRules.
Module Batch := CounterBatch.CounterBatch.
Notation mtm := W.mtm.
Open Scope sym.

Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation ld := [1;1].
Notation one := [1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma normal_app bs cs : W.normal (bs++cs)=W.normal bs++W.normal cs.
Proof.


 induction bs as [|bit bs IH]; cbn[W.normal app]; [reflexivity|].
 rewrite IH,app_assoc. reflexivity.
Qed.
Lemma normal_zeros n : W.normal (repeat false n)=a^^n.
Proof. induction n; [reflexivity|].
 change (a++W.normal (repeat false n)=a++a^^n). rewrite IHn. reflexivity. Qed.
Lemma phase_three_word bs : z3++W.normal bs=CD.third bs++z3.
Proof.


 induction bs as [|bit bs IH]; [reflexivity|].
 destruct bit; cbn[W.normal CD.third CD.third_digit app]; rewrite <-IH; reflexivity.
Qed.
Lemma phase_three bs : z3 *> W.normal bs *> 0inf=CD.third bs *> 0inf.
Proof.


 rewrite <-Str_app_assoc,phase_three_word,Str_app_assoc. st. reflexivity.
Qed.

Lemma leading_one_C t bs out terminal :
 sideRLs mtm (x^^t) (CD.third bs *> 0inf) (CD.fourth out *> terminal *> 0inf) ->
 sideRLs mtm (p^^(t*2)) (r4 *> W.normal bs *> 0inf)
   (one *> CD.fourth out *> terminal *> 0inf).
Proof.


 intro H.
 change (sideRLs mtm (p^^(t*2)) (one *> z3 *> W.normal bs *> 0inf)
   (one *> CD.fourth out *> terminal *> 0inf)).
 rewrite phase_three.
 eapply segRLs_sideRLs_concat.
 - apply F.p_one_pairs.
 - exact H.
Qed.

Lemma fuel_C_image L k t bs budget :
 k<2^L -> k+1=t*2 ->
 2^length bs<=t -> t+CD.value bs<2^(length bs+budget) ->
 exists out,
 length out<length bs+budget /\
 CD.value out+2^length out=t+CD.value bs /\
 CR.LC L k |> r4 *> W.normal bs *> 0inf -[mtm]->+
 W.wall (ld^^(L+1)++CD.fourth out++CD.terminal (CD.any bs)).
Proof.


 intros Hk Ht Hmin Hmax.
 destruct (CD.mass_full bs false t budget Hmin Hmax)
   as [out [Hlen [Hval Hrun]]].
 cbn[CD.mass orb] in Hrun.
 exists out. repeat split; try assumption.
 pose proof (leading_one_C t bs out (CD.terminal (CD.any bs)) Hrun) as HR.
 rewrite <-Ht in HR.
 pose proof (F.right_pass_finish L k _ _ Hk HR) as Hfinish.
 unfold W.wall.
 applys_eq Hfinish; ut; st; simpl_rotate; reflexivity.
Qed.

Definition first_fuel n u := 2^n-1-(2^u-1)*2.

Lemma first_fuel_bounds n u : u+1<=n ->
 first_fuel n u+(2^u-1)*2=2^n-1 /\
 first_fuel n u<2^n.
Proof.


 intro Hn. unfold first_fuel.
 assert (Hpow:2^(u+1)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in Hpow. cbn[Nat.pow] in Hpow.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
Qed.

Lemma initial_even_entry n v bs : v*2+1<=n ->
 W.O n (repeat false (v*2)++true::bs) -[mtm]->+
 CR.LC (n+1+v*5) (F.grown (first_fuel n (v*2)) (v*5)) |>
 r4 *> W.normal bs *> 0inf.
Proof.


 intro Hn.
 destruct (first_fuel_bounds n (v*2) Hn) as [He Hb].
 unfold W.O,W.wall.
 rewrite normal_app,normal_zeros.
 cbn[W.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply F.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He.
     apply Batch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply F.prime_gap0.
   + apply F.convert_gap0_even. exact Hb.
Qed.

Definition first_mass n v :=
 (2*first_fuel n (v*2)+1)*2^(v*5-1).

Lemma first_mass_fuel n v : 0<v ->
 F.grown (first_fuel n (v*2)) (v*5)+1=first_mass n v*2.
Proof.


 intro Hv. unfold F.grown,first_mass.
 assert (He:v*5=(v*5-1)+1) by lia.
 rewrite He at 1. rewrite Nat.pow_add_r. cbn[Nat.pow].
 pose proof (Nat.pow_nonzero 2 (v*5-1) ltac:(lia)). nia.
Qed.

Lemma initial_even_image n v bs budget :
 0<v -> v*2+1<=n ->
 2^length bs<=first_mass n v ->
 first_mass n v+CD.value bs<2^(length bs+budget) ->
 exists out,
 length out<length bs+budget /\
 CD.value out+2^length out=first_mass n v+CD.value bs /\
 W.O n (repeat false (v*2)++true::bs) -[mtm]->+
 W.wall (ld^^(n+v*5+2)++CD.fourth out++CD.terminal (CD.any bs)).
Proof.


 intros Hv Hn Hmin Hmax.
 destruct (first_fuel_bounds n (v*2) Hn) as [He Hb].
 assert (Hgrown:F.grown (first_fuel n (v*2)) (v*5)<2^(n+1+v*5)).
 { pose proof (F.grown_bound n (first_fuel n (v*2)) (v*5) Hb). lia. }
 destruct (fuel_C_image (n+1+v*5) (F.grown (first_fuel n (v*2)) (v*5))
   (first_mass n v) bs budget Hgrown (first_mass_fuel n v Hv) Hmin Hmax)
   as [out [Hlen [Hval Hrun]]].
 exists out. repeat split; try assumption.
 replace (n+v*5+2) with ((n+1+v*5)+1) by lia.

 eapply progress_trans.
 - apply initial_even_entry; exact Hn.
 - exact Hrun.
Qed.

Print Assumptions fuel_C_image.
Print Assumptions initial_even_entry.
Print Assumptions initial_even_image.
End OddImage.
End OddImage.

Module OddRecursion.
(* Recursive gap-two conversion rules for odd ordinary walls.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses OddFuel OddImage CounterRules CounterBatch WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Module OddRecursion.
Module W := WallInvariant.WallInvariant.

Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module CR := CounterRules.CounterRules.
Module Batch := CounterBatch.CounterBatch.
Notation mtm := W.mtm.
Open Scope sym.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation d := [0;0;0;1;0].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma initial_odd_entry n v bs : v*2+2<=n ->
 W.O n (repeat false (v*2+1)++true::bs) -[mtm]->+
 CR.LC (n+1+(v*5+3)) (F.grown (I.first_fuel n (v*2+1)) (v*5+3)) |>
 z3 *> W.normal bs *> 0inf.
Proof.

 intro Hn.
 destruct (I.first_fuel_bounds n (v*2+1) ltac:(lia)) as [He Hb].
 unfold W.O,W.wall.
 rewrite I.normal_app,I.normal_zeros.
 cbn[W.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply F.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He.
     apply Batch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply F.prime_gap0.
   + apply F.convert_gap0_odd. exact Hb.
Qed.

Lemma zero_rotate u : z3++a^^u++b=a^^u++d++z3.
Proof.

 induction u.
 - reflexivity.
 - cbn[lpow]. change (a++(z3++a^^u++b)=a++(a^^u++d++z3)).
   rewrite IHu. reflexivity.
Qed.

Lemma zero_rotate_side u r : z3 *> a^^u *> b *> r=a^^u *> d *> z3 *> r.
Proof.

 pose proof (f_equal (fun w => w *> r) (zero_rotate u)) as E.
 cbv beta in E. repeat rewrite Str_app_assoc in E. exact E.
Qed.

Lemma zero_prime L k u bs r : k+(2^(u+1)-1)<2^L ->
 CR.LC L (k+(2^(u+1)-1)) |> z3 *> W.normal (repeat false u++true::bs) *> r
 -[mtm]->*
 CR.LC L k |> b^^u *> ([1;0;0;1;0;0;0;0]%sym) *> W.normal bs *> r.
Proof.

 intro Hk. rewrite I.normal_app,I.normal_zeros.
 cbn[W.normal]. repeat rewrite Str_app_assoc.
 rewrite zero_rotate_side.
 apply Batch.right_pass_batch; [exact Hk|].
 apply F.prime_gap2.
Qed.

Lemma zero_even_step L k v bs r : k+(2^(v*2+1)-1)<2^L ->
 CR.LC L (k+(2^(v*2+1)-1)) |>
 z3 *> W.normal (repeat false (v*2)++true::bs) *> r -[mtm]->+
 CR.LC (L+1+(v*5+1)) (F.grown k (v*5+1)) |> r4 *> W.normal bs *> r.
Proof.

 intro Hk. eapply evstep_progress_trans.
 - apply zero_prime. exact Hk.
 - apply F.convert_gap2_even. lia.
Qed.

Lemma zero_odd_step L k v bs r : k+(2^(v*2+2)-1)<2^L ->
 CR.LC L (k+(2^(v*2+2)-1)) |>
 z3 *> W.normal (repeat false (v*2+1)++true::bs) *> r -[mtm]->+
 CR.LC (L+1+(v*5+4)) (F.grown k (v*5+4)) |> z3 *> W.normal bs *> r.
Proof.

 intro Hk. replace (v*2+2) with ((v*2+1)+1) in * by lia.
 eapply evstep_progress_trans.
 - apply zero_prime. exact Hk.
 - apply F.convert_gap2_odd. lia.
Qed.

Lemma grown_odd k z : 0<z -> F.grown k z mod 2=1.
Proof.

 intro Hz. unfold F.grown.
 destruct z as [|z]; [lia|].
 cbn[Nat.pow].
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)).
 replace ((2*k+1)*(2*2^z)-1) with (((2*k+1)*2^z-1)*2+1) by nia.
 rewrite Nat.add_comm,Nat.mod_add by lia. reflexivity.
Qed.

Lemma remaining_lower k u m : 2^(u+1+m)-1<=k ->
 2^(u+1)-1<=k /\
 2^(u+1)*(2^m-1)<=k-(2^(u+1)-1).
Proof.

 intro Hk. rewrite Nat.pow_add_r in Hk.
 pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)). nia.
Qed.

Lemma grown_lower k u m z :
 2^(u+1)*(2^m-1)<=k -> 0<z -> 2^m-1<=F.grown k z.
Proof.

 intros Hk Hz. unfold F.grown.
 pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).
 assert (Htwo:2<=2^z).
 { destruct z; [lia|]. cbn[Nat.pow]. pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia. }
 nia.
Qed.

Print Assumptions initial_odd_entry.
Print Assumptions zero_even_step.
Print Assumptions zero_odd_step.
End OddRecursion.
End OddRecursion.

Module OddRoute.
(* Finite conversion paths through an ordinary digit word.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import OddFuel OddImage OddRecursion CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Module OddRoute.
Module W := WallInvariant.WallInvariant.
Module F := OddFuel.OddFuel.
Module R := OddRecursion.OddRecursion.
Module CR := CounterRules.CounterRules.
Notation mtm := W.mtm.
Open Scope sym.
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].

Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Inductive route : nat -> nat -> list bool -> nat -> nat -> list bool -> Prop :=
| RouteEven L k v tail :
 route L (k+(2^(v*2+1)-1)) (repeat false (v*2)++true::tail)
   (L+1+(v*5+1)) (F.grown k (v*5+1)) tail
| RouteOdd L k v tail L' k' rest :
 route (L+1+(v*5+4)) (F.grown k (v*5+4)) tail L' k' rest ->
 route L (k+(2^(v*2+2)-1)) (repeat false (v*2+1)++true::tail)
   L' k' rest.

Lemma route_run L k bs L' k' rest r :
 route L k bs L' k' rest -> k<2^L ->
 CR.LC L k |> z3 *> W.normal bs *> r -[mtm]->+
 CR.LC L' k' |> r4 *> W.normal rest *> r.
Proof.


 intros H. induction H; intro Hk.
 - apply R.zero_even_step. exact Hk.
 - eapply progress_trans.
   + apply R.zero_odd_step. exact Hk.
   + apply IHroute.
     pose proof (F.grown_bound L k (v*5+4) ltac:(lia)). lia.
Qed.

Lemma route_bound L k bs L' k' rest :
 route L k bs L' k' rest -> k<2^L -> k'+1<2^L' /\ k' mod 2=1.
Proof.


 intros H. induction H; intro Hk.
 - split.
   + apply F.grown_bound. lia.
   + apply R.grown_odd. lia.
 - apply IHroute. pose proof (F.grown_bound L k (v*5+4) ltac:(lia)). lia.
Qed.

Lemma route_dimensions L k bs L' k' rest :
 route L k bs L' k' rest ->
 exists j, length bs=2*j+1+length rest /\ L'=L+5*j+2.
Proof.


 intro H. induction H.
 - exists v. rewrite length_app,repeat_length. cbn[length]. lia.
 - destruct IHroute as [j [Hlen HL]].
   exists (v+1+j). rewrite length_app,repeat_length. cbn[length]. lia.
Qed.

Lemma first_true bs : In true bs -> exists u tail, bs=repeat false u++true::tail.
Proof.


 induction bs as [|b bs IH]; intro H.
 - inversion H.
 - destruct b.
   + exists 0,bs. reflexivity.
   + destruct H as [H|H]; [discriminate|].
     destruct (IH H) as [u [tail E]].
     exists (S u),tail. cbn[repeat]. rewrite E. reflexivity.
Qed.

Lemma marked_true bs : W.marked 0 bs -> In true bs.
Proof.


 intros [pre [post [E Hp]]]. rewrite E.
 apply in_or_app. right. cbn. auto.
Qed.

Lemma marked_drop_pair b bs : W.marked 0 (false::b::bs) -> W.marked 0 bs.
Proof.


 intros [pre [post [E Hp]]].
 destruct pre as [|a [|a' pre]].
 - discriminate E.
 - cbn[length] in Hp. discriminate Hp.
 - inversion E; subst.
   exists pre,post. split; [reflexivity|].
   cbn[length] in Hp.
   replace (S (S (length pre))) with (length pre+1*2) in Hp by lia.
   rewrite Nat.mod_add in Hp by lia. exact Hp.
Qed.

Lemma marked_after_odd v bs :
 W.marked 0 (repeat false (v*2+1)++true::bs) -> W.marked 0 bs.
Proof.


 induction v; intro H.
 - cbn[repeat] in H. apply (marked_drop_pair true bs H).
 - replace (S v*2+1) with (S (S (v*2+1))) in H by lia.
   cbn[repeat app] in H.
   apply IHv. eapply marked_drop_pair. exact H.
Qed.

Lemma grown_lower_double k u m z :
 2^(u+1)*(2^m-1)<=k -> 0<z -> 2^(m+1)-1<=F.grown k z.
Proof.


 intros Hk Hz. unfold F.grown.
 rewrite Nat.pow_add_r. cbn[Nat.pow].
 assert (Hu:2<=2^(u+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow].
   pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia. }
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).
 assert (Htwo:2<=2^z).
 { destruct z; [lia|]. cbn[Nat.pow]. pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia. }
 nia.
Qed.

Lemma marked_route_bounded bound :
 forall bs L k,
 length bs<=bound -> W.marked 0 bs -> 2^length bs-1<=k ->
 exists L' k' rest,
 route L k bs L' k' rest /\ 2^(length rest+1)-1<=k'.
Proof.


 induction bound as [|bound IH]; intros bs L k Hlen Hmark Hfuel.
 - assert (bs=[]) by (apply length_zero_iff_nil; lia). subst bs.
   destruct (marked_true [] Hmark).
 - destruct (first_true bs (marked_true bs Hmark)) as [u [tail E]]. subst bs.
   rewrite length_app,repeat_length in Hlen,Hfuel. cbn[length] in Hlen,Hfuel.
   replace (u+S (length tail)) with (u+1+length tail) in Hfuel by lia.
   destruct (R.remaining_lower k u (length tail) Hfuel) as [Hprime Hremain].
   set (rem:=k-(2^(u+1)-1)).

   assert (Hdecomp:k=rem+(2^(u+1)-1)) by (unfold rem; lia).
   destruct (mod2 u) as [v Eu|v Eu]; subst u.
   + exists (L+1+(v*5+1)),(F.grown rem (v*5+1)),tail.
     split.
     * rewrite Hdecomp. constructor.
     * apply (grown_lower_double rem (v*2) (length tail) (v*5+1)); [exact Hremain|lia].
   + replace (1+v*2) with (v*2+1) in * by lia.
     assert (HremainR:2^((v*2+1)+1)*(2^length tail-1)<=rem).
     { unfold rem. replace (1+v*2) with (v*2+1) by lia. exact Hremain. }

     assert (Htail:W.marked 0 tail) by (apply marked_after_odd in Hmark; exact Hmark).
     assert (Hremain':2^length tail-1<=F.grown rem (v*5+4)).
     { apply (R.grown_lower rem (v*2+1) (length tail) (v*5+4)); [exact HremainR|lia]. }
     destruct (IH tail (L+1+(v*5+4)) (F.grown rem (v*5+4)) ltac:(lia) Htail Hremain')
       as [L' [k' [rest [Hroute Hlower]]]].
     exists L',k',rest. split; [|exact Hlower].
     rewrite Hdecomp. replace ((v*2+1)+1) with (v*2+2) by lia.

     apply RouteOdd. exact Hroute.
Qed.

Lemma marked_route L k bs :
 W.marked 0 bs -> 2^length bs-1<=k ->
 exists L' k' rest,
 route L k bs L' k' rest /\ 2^(length rest+1)-1<=k'.
Proof.


 intros Hmark Hfuel.
 apply (marked_route_bounded (length bs) bs L k); [lia|exact Hmark|exact Hfuel].
Qed.

Lemma zero_marked_exit L k bs r :
 W.marked 0 bs -> 2^length bs-1<=k -> k<2^L ->
 exists L' k' rest j,
 route L k bs L' k' rest /\
 length bs=2*j+1+length rest /\ L'=L+5*j+2 /\
 2^(length rest+1)-1<=k' /\ k'+1<2^L' /\ k' mod 2=1 /\
 CR.LC L k |> z3 *> W.normal bs *> r -[mtm]->+
 CR.LC L' k' |> r4 *> W.normal rest *> r.
Proof.


 intros Hmark Hfuel Hbound.
 destruct (marked_route L k bs Hmark Hfuel) as [L' [k' [rest [Hroute Hlower]]]].
 destruct (route_dimensions _ _ _ _ _ _ Hroute) as [j [Hlen HL]].
 destruct (route_bound _ _ _ _ _ _ Hroute Hbound) as [Hb Ho].
 exists L',k',rest,j. repeat split; try assumption.
 apply route_run; assumption.
Qed.

Print Assumptions route_run.
Print Assumptions zero_marked_exit.
End OddRoute.
End OddRoute.

Module OddMarkedEntry.
(* Reaching the C-pass phase from a marked odd wall.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import OddFuel OddImage OddRecursion OddRoute CounterRules CounterBatch WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.
Module OddMarkedEntry.
Module W := WallInvariant.WallInvariant.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module R := OddRecursion.OddRecursion.
Module P := OddRoute.OddRoute.
Module CR := CounterRules.CounterRules.
Module Batch := CounterBatch.CounterBatch.
Notation mtm := W.mtm.
Open Scope sym.
Notation ld := [1;1].
Notation one := [1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Definition odd_wall n bs r :=
 (0inf <* <[1;1]) <* [0] {{A}}> (ld^^n *> one *> W.normal bs *> r).
Open Scope nat.

Lemma even_entry n v bs r : v*2+1<=n ->
 odd_wall n (repeat false (v*2)++true::bs) r -[mtm]->+
 CR.LC (n+1+v*5) (F.grown (I.first_fuel n (v*2)) (v*5)) |>
 r4 *> W.normal bs *> r.
Proof.


 intro Hn. destruct (I.first_fuel_bounds n (v*2) Hn) as [He Hb].
 unfold odd_wall. rewrite I.normal_app,I.normal_zeros.
 cbn[W.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply F.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He. apply Batch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply F.prime_gap0.
   + apply F.convert_gap0_even. exact Hb.
Qed.

Lemma odd_entry n v bs r : v*2+2<=n ->
 odd_wall n (repeat false (v*2+1)++true::bs) r -[mtm]->+
 CR.LC (n+1+(v*5+3)) (F.grown (I.first_fuel n (v*2+1)) (v*5+3)) |>
 z3 *> W.normal bs *> r.
Proof.


 intro Hn. destruct (I.first_fuel_bounds n (v*2+1) ltac:(lia)) as [He Hb].
 unfold odd_wall. rewrite I.normal_app,I.normal_zeros.
 cbn[W.normal]. repeat rewrite Str_app_assoc.
 eapply evstep_progress_trans.
 - apply F.scan_ones.
 - eapply evstep_progress_trans.
   + rewrite <-He. apply Batch.right_pass_batch.
     * rewrite He. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
     * apply F.prime_gap0.
   + apply F.convert_gap0_odd. exact Hb.
Qed.

Lemma initial_margin n u m z :
 u+m+2<=n -> 3<=z ->
 2^(m+3)-1<=F.grown (I.first_fuel n u) z.
Proof.


 intros Hn Hz.
 destruct (I.first_fuel_bounds n u ltac:(lia)) as [He Hb].
 assert (Hcap:2^(u+m+2)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 repeat rewrite Nat.pow_add_r in Hcap. cbn[Nat.pow] in Hcap.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).
 assert (Hk:2^m<=I.first_fuel n u) by nia.
 assert (Hzpow:8<=2^z).
 { change (2^3<=2^z). apply Nat.pow_le_mono_r; lia. }
 unfold F.grown. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma route_margin extra L k bs L' k' rest :
 P.route L k bs L' k' rest ->
 2^(length bs+extra)-1<=k -> 2^(length rest+extra)-1<=k'.
Proof.


 intro Hroute. induction Hroute; intro Hfuel.
 - rewrite length_app,repeat_length in Hfuel. cbn[length] in Hfuel.
   replace (v*2+S (length tail)+extra) with (v*2+1+(length tail+extra)) in Hfuel by lia.
   destruct (R.remaining_lower (k+(2^(v*2+1)-1)) (v*2) (length tail+extra) Hfuel)
     as [_ Hremain].
   rewrite Nat.add_sub in Hremain.
   apply (R.grown_lower k (v*2) (length tail+extra) (v*5+1)); [exact Hremain|lia].
 - apply IHHroute.
   rewrite length_app,repeat_length in Hfuel. cbn[length] in Hfuel.

   replace (v*2+1+S (length tail)+extra) with ((v*2+1)+1+(length tail+extra)) in Hfuel by lia.
   replace (v*2+2) with ((v*2+1)+1) in Hfuel by lia.
   destruct (R.remaining_lower (k+(2^((v*2+1)+1)-1)) (v*2+1) (length tail+extra) Hfuel)
     as [_ Hremain].
   rewrite Nat.add_sub in Hremain.
   apply (R.grown_lower k (v*2+1) (length tail+extra) (v*5+4)); [exact Hremain|lia].
Qed.

Lemma marked_entry n bs r :
 W.first_zero bs -> W.marked 0 bs -> length bs+1<=n ->
 exists L k rest j,
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+3)-1<=k /\
 odd_wall n bs r -[mtm]->+ CR.LC L k |> r4 *> W.normal rest *> r.
Proof.


 intros Hzero Hmark Hlen.
 destruct (P.first_true bs (P.marked_true bs Hmark)) as [u [tail E]]. subst bs.
 rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
 assert (Hu:0<u).
 { destruct Hzero as [rest Hzero]. destruct u; [discriminate Hzero|lia]. }
 destruct (mod2 u) as [v Eu|v Eu]; subst u.
 - exists (n+1+v*5),(F.grown (I.first_fuel n (v*2)) (v*5)),tail,v.
   rewrite length_app,repeat_length. cbn[length].
   repeat split.
   + lia.
   + lia.

   + apply R.grown_odd. lia.
   + apply F.grown_bound. apply I.first_fuel_bounds. lia.
   + apply initial_margin; lia.
   + apply even_entry. lia.
 - replace (1+v*2) with (v*2+1) in * by lia.
   assert (Htail:W.marked 0 tail) by (apply P.marked_after_odd in Hmark; exact Hmark).
   set (L0:=n+1+(v*5+3)).
   set (k0:=F.grown (I.first_fuel n (v*2+1)) (v*5+3)).
   assert (Hmargin:2^(length tail+3)-1<=k0) by (unfold k0; apply initial_margin; lia).
   assert (Hbasic:2^length tail-1<=k0).
   { assert (2^length tail<=2^(length tail+3)) by (apply Nat.pow_le_mono_r; lia). lia. }

   assert (Hcap:k0+1<2^L0).
   { unfold k0,L0. apply F.grown_bound. apply I.first_fuel_bounds. lia. }
   destruct (P.marked_route L0 k0 tail Htail Hbasic)
     as [L' [k' [rest [Hroute Hlower]]]].
   destruct (P.route_dimensions _ _ _ _ _ _ Hroute) as [j [Hdim HL]].
   destruct (P.route_bound _ _ _ _ _ _ Hroute ltac:(lia)) as [Hbound Hodd].
   exists L',k',rest,(v+1+j).
   rewrite length_app,repeat_length. cbn[length].
   repeat split.
   + lia.
   + unfold L0 in HL. lia.

   + exact Hodd.
   + exact Hbound.
   + apply (route_margin 3 _ _ _ _ _ _ Hroute Hmargin).
   + eapply progress_trans.
     * apply odd_entry. lia.
     * apply P.route_run; [exact Hroute|]. change (k0<2^L0). lia.
Qed.

Print Assumptions initial_margin.
Print Assumptions route_margin.
Print Assumptions marked_entry.
End OddMarkedEntry.
End OddMarkedEntry.

Module MarkedTrace.
(* Exact conversion histories from marked odd walls.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import OddFuel OddImage OddRecursion OddRoute OddMarkedEntry CounterRules WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module MarkedTrace.
Module W := WallInvariant.WallInvariant.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module R := OddRecursion.OddRecursion.
Module P := OddRoute.OddRoute.
Module M := OddMarkedEntry.OddMarkedEntry.
Module CR := CounterRules.CounterRules.
Notation mtm := W.mtm.
Open Scope sym.
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Inductive wall_route : nat -> list bool -> nat -> nat -> list bool -> Prop :=
| WallEven n v tail :
 wall_route n (repeat false (v*2)++true::tail)
  (n+1+v*5) (F.grown (I.first_fuel n (v*2)) (v*5)) tail
| WallOdd n v tail L k rest :
 P.route (n+1+(v*5+3)) (F.grown (I.first_fuel n (v*2+1)) (v*5+3)) tail L k rest ->
 wall_route n (repeat false (v*2+1)++true::tail) L k rest.

Lemma first_zero_prefix u tail :
 W.first_zero (repeat false u++true::tail) -> 0<u.
Proof.

 intros [rest E]. destruct u; [discriminate E|lia].
Qed.

Lemma initial_margin4 n u m z :
 u+m+2<=n -> 3<=z -> 2^(m+4)-1<=F.grown (I.first_fuel n u) z.
Proof.

 intros Hn Hz.
 destruct (I.first_fuel_bounds n u ltac:(lia)) as [He Hb].

 assert (Hcap:2^(u+m+2)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 repeat rewrite Nat.pow_add_r in Hcap. cbn[Nat.pow] in Hcap.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 m ltac:(lia)).

 assert (Hk:2^m<=I.first_fuel n u) by nia.

 assert (Hzpow:8<=2^z).
 { change (2^3<=2^z). apply Nat.pow_le_mono_r; lia. }
 unfold F.grown. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma route_dimensions n bs L k rest : wall_route n bs L k rest ->
 exists j, length bs=2*j+1+length rest /\ L=n+5*j+1.
Proof.

 intro Hroute. destruct Hroute.
 - exists v. rewrite length_app,repeat_length. cbn[length]. split; lia.
 - destruct (P.route_dimensions _ _ _ _ _ _ H) as [j [Hlen HL]].
   exists (v+1+j). rewrite length_app,repeat_length. cbn[length]. split; lia.
Qed.

Lemma route_run n bs L k rest r :
 wall_route n bs L k rest -> length bs+1<=n ->
 M.odd_wall n bs r -[mtm]->+ CR.LC L k |> r4 *> W.normal rest *> r.
Proof.

 intros Hroute Hlen. destruct Hroute.
 - apply M.even_entry. rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen. lia.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   eapply progress_trans.
   + apply M.odd_entry. lia.
   + apply P.route_run; [exact H|].
     pose proof (F.grown_bound n (I.first_fuel n (v*2+1)) (v*5+3)
       ltac:(apply I.first_fuel_bounds; lia)). lia.
Qed.

Lemma route_bounds n bs L k rest :
 wall_route n bs L k rest -> W.first_zero bs -> length bs+1<=n ->
 k+1<2^L /\ k mod 2=1.
Proof.

 intros Hroute Hzero Hlen. destruct Hroute.
 - apply first_zero_prefix in Hzero.
   rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   split.
   + apply F.grown_bound. apply I.first_fuel_bounds. lia.
   + apply R.grown_odd. lia.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   apply (P.route_bound _ _ _ _ _ _ H).
   pose proof (F.grown_bound n (I.first_fuel n (v*2+1)) (v*5+3)
     ltac:(apply I.first_fuel_bounds; lia)). lia.
Qed.

Lemma route_margin4 n bs L k rest :
 wall_route n bs L k rest -> W.first_zero bs -> length bs+1<=n ->
 2^(length rest+4)-1<=k.
Proof.

 intros Hroute Hzero Hlen. destruct Hroute.
 - apply first_zero_prefix in Hzero.
   rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   apply initial_margin4; lia.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   apply (M.route_margin 4 _ _ _ _ _ _ H).
   apply initial_margin4; lia.
Qed.

Lemma marked_route_exists n bs :
 W.first_zero bs -> W.marked 0 bs -> length bs+1<=n ->
 exists L k rest, wall_route n bs L k rest.
Proof.

 intros Hzero Hmark Hlen.
 destruct (P.first_true bs (P.marked_true bs Hmark)) as [u [tail E]]. subst bs.
 rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
 destruct (mod2 u) as [v Eu|v Eu]; subst u.
 - eexists; eexists; eexists. constructor.
 - replace (1+v*2) with (v*2+1) in * by lia.

   assert (Htail:W.marked 0 tail) by (apply P.marked_after_odd in Hmark; exact Hmark).
   set (L0:=n+1+(v*5+3)).
   set (k0:=F.grown (I.first_fuel n (v*2+1)) (v*5+3)).

   assert (Hmargin:2^(length tail+4)-1<=k0) by (unfold k0; apply initial_margin4; lia).

   assert (Hbasic:2^length tail-1<=k0).
   { assert (2^length tail<=2^(length tail+4)) by (apply Nat.pow_le_mono_r; lia). lia. }
   destruct (P.marked_route L0 k0 tail Htail Hbasic)
     as [L [k [rest [Hroute Hlower]]]].
   exists L,k,rest. apply WallOdd. exact Hroute.
Qed.

Lemma marked_entry_trace n bs r :
 W.first_zero bs -> W.marked 0 bs -> length bs+1<=n ->
 exists L k rest j,
 wall_route n bs L k rest /\
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+4)-1<=k /\
 M.odd_wall n bs r -[mtm]->+ CR.LC L k |> r4 *> W.normal rest *> r.
Proof.

 intros Hzero Hmark Hlen.
 destruct (marked_route_exists n bs Hzero Hmark Hlen) as [L [k [rest Hroute]]].
 destruct (route_dimensions _ _ _ _ _ Hroute) as [j [Hdim HL]].
 destruct (route_bounds _ _ _ _ _ Hroute Hzero Hlen) as [Hbound Hodd].
 exists L,k,rest,j. repeat split; try assumption.
 - apply (route_margin4 _ _ _ _ _ Hroute Hzero Hlen).
 - apply route_run; assumption.
Qed.

Print Assumptions initial_margin4.
Print Assumptions marked_entry_trace.
End MarkedTrace.
End MarkedTrace.

Module OdDeficit.
(* Exact fuel deficits carried by a reachable odd-wall conversion path.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import OddFuel OddImage OddRoute MarkedTrace.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module OdDeficit.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module R := OddRoute.OddRoute.
Module M := MarkedTrace.MarkedTrace.

Lemma grown_complete k z : F.grown k z+1=(2*k+1)*2^z.
Proof. unfold F.grown. pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia. Qed.

Lemma step_deficit L k D u z :
 k+(2^(u+1)-1)+1+D=2^L ->
 F.grown k z+1+D*2^(z+1)+(2^(u+2)-1)*2^z=2^(L+1+z).
Proof.

 intro H. rewrite grown_complete.
 repeat rewrite Nat.pow_add_r in *. cbn[Nat.pow] in *.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma correction_bound u z :
 0<(2^(u+2)-1)*2^z<2^(u+2+z).
Proof.

 repeat rewrite Nat.pow_add_r. cbn[Nat.pow].
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma route_deficit L k bs L' k' rest :
 R.route L k bs L' k' rest ->
 forall D, k+1+D=2^L ->
 exists j c,
 length bs=2*j+1+length rest /\ L'=L+5*j+2 /\
 0<c<2^(7*j+3) /\
 k'+1+D*2^(5*j+2)+c=2^L'.
Proof.

 intro Hr. induction Hr; intros D HD.
 - exists v,((2^(v*2+2)-1)*2^(v*5+1)).
   split; [rewrite length_app,repeat_length; cbn[length]; lia|].
   split; [lia|]. split.
   + pose proof (correction_bound (v*2) (v*5+1)) as H.
     replace (v*2+2+(v*5+1)) with (7*v+3) in H by lia. exact H.
   + replace (5*v+2) with ((v*5+1)+1) by lia.
     apply step_deficit. exact HD.
 - set (c0:=(2^(v*2+3)-1)*2^(v*5+4)).
   set (D0:=D*2^(v*5+5)+c0).

   assert (HD0:F.grown k (v*5+4)+1+D0=2^(L+1+(v*5+4))).
   { unfold D0,c0.
     replace (v*5+5) with ((v*5+4)+1) by lia.
     replace (v*2+3) with ((v*2+1)+2) by lia.
     rewrite Nat.add_assoc. apply step_deficit.
     replace (v*2+1+1) with (v*2+2) by lia. exact HD. }

   destruct (IHHr D0 HD0) as [j [c [Hlen [HL [Hc HE]]]]].
   exists (v+1+j),(c0*2^(5*j+2)+c).
   split; [rewrite length_app,repeat_length; cbn[length]; lia|].
   split; [lia|]. split.
   + assert (Hc0:0<c0<2^(7*v+7)).
     { unfold c0. pose proof (correction_bound (v*2+1) (v*5+4)) as H.
       replace (v*2+1+2+(v*5+4)) with (7*v+7) in H by lia.
       replace (v*2+1+2) with (v*2+3) in H by lia. exact H. }

     assert (Hprod:c0*2^(5*j+2)<2^(7*v+5*j+9)).
     { replace (7*v+5*j+9) with ((7*v+7)+(5*j+2)) by lia.
       rewrite (Nat.pow_add_r 2 (7*v+7) (5*j+2)).
       pose proof (Nat.pow_nonzero 2 (5*j+2) ltac:(lia)). nia. }

     assert (Hp1:2^(7*v+5*j+9)<=2^(7*(v+1+j)+2)) by
       (apply Nat.pow_le_mono_r; lia).

     assert (Hp2:2^(7*j+3)<=2^(7*(v+1+j)+2)) by
       (apply Nat.pow_le_mono_r; lia).
     replace (7*(v+1+j)+3) with (1+(7*(v+1+j)+2)) by lia.
     rewrite (Nat.pow_add_r 2 1 (7*(v+1+j)+2)). cbn[Nat.pow]. split; lia.
   + assert (HP:2^(5*(v+1+j)+2)=2^(v*5+5)*2^(5*j+2)).
     { rewrite <-Nat.pow_add_r. f_equal. lia. }
     rewrite HP. unfold D0 in HE. nia.
Qed.

Lemma initial_deficit n u z :
 u+1<=n ->
 F.grown (I.first_fuel n u) z+1+(2^(u+2)-3)*2^z=2^(n+1+z).
Proof.

 intro Hn. pose proof (I.first_fuel_bounds n u Hn) as [HE HB].
 rewrite grown_complete.
 repeat rewrite Nat.pow_add_r in *. cbn[Nat.pow] in *.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma initial_even_deficit n v tail :
 length (repeat false (v*2)++true::tail)+1<=n ->
 F.grown (I.first_fuel n (v*2)) (v*5)+1+
   (2^(v*2+2)-3)*2^(v*5)=2^(n+1+v*5).
Proof.

 intro H. apply initial_deficit.
 rewrite length_app,repeat_length in H. cbn[length] in H. lia.
Qed.

Lemma initial_odd_route_deficit n v tail L k rest :
 R.route (n+1+(v*5+3)) (F.grown (I.first_fuel n (v*2+1)) (v*5+3))
   tail L k rest ->
 length (repeat false (v*2+1)++true::tail)+1<=n ->
 exists j c,
 length tail=2*j+1+length rest /\ L=n+5*(v+1+j)+1 /\
 0<c<2^(7*j+3) /\
 k+1+(2^(v*2+3)-3)*2^(5*(v+1+j))+c=2^L.
Proof.

 intros Hr Hn.

 assert (Hu:v*2+1+1<=n).
 { rewrite length_app,repeat_length in Hn. cbn[length] in Hn. lia. }
 pose proof (initial_deficit n (v*2+1) (v*5+3) Hu) as HD.
 destruct (route_deficit _ _ _ _ _ _ Hr ((2^(v*2+1+2)-3)*2^(v*5+3)) HD)
  as [j [c [Hlen [HL [Hc HE]]]]].
 exists j,c. split; [exact Hlen|]. split; [lia|]. split; [exact Hc|].
 replace (v*2+1+2) with (v*2+3) in HE by lia.

 assert (HP:2^(5*(v+1+j))=2^(v*5+3)*2^(5*j+2)).
 { rewrite <-Nat.pow_add_r. f_equal. lia. }
 rewrite HP. nia.
Qed.

Print Assumptions route_deficit.
Print Assumptions initial_even_deficit.
Print Assumptions initial_odd_route_deficit.
End OdDeficit.
End OdDeficit.

Module RouteMarkerBound.
(* A marked even-position digit bounds a conversion route.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import OddRoute.
Import List PeanoNat Lia.
Import ListNotations OddRoute.OddRoute.
Open Scope nat.

Module RouteMarkerBound.
Lemma prefix_true_index u tail i :
 nth i (repeat false u++true::tail) false=true -> u<=i.
Proof.
 intro H. destruct (Nat.le_gt_cases u i); [assumption|].
 rewrite app_nth1 in H by (rewrite repeat_length; lia).
 rewrite nth_repeat in H. discriminate.
Qed.

Lemma prefix_tail_nth u tail i : u<i ->
 nth i (repeat false u++true::tail) false=true ->
 nth (i-u-1) tail false=true.
Proof.
 intros Hi H. rewrite app_nth2 in H by (rewrite repeat_length; lia).
 rewrite repeat_length in H.
 replace (i-u) with (S (i-u-1)) in H by lia.
 cbn[nth] in H. exact H.
Qed.

Lemma route_known_even L k bs L' k' rest :
 route L k bs L' k' rest ->
 forall i, nth i bs false=true -> i mod 2=0 ->
 length bs<=i+1+length rest.
Proof.

 intro Hroute. induction Hroute; intros i Hnth Hpar.
 - pose proof (prefix_true_index (v*2) tail i Hnth).
   rewrite length_app,repeat_length. cbn[length]. lia.
 - pose proof (prefix_true_index (v*2+1) tail i Hnth) as Hlow.
   assert (Hstrict:v*2+1<i).
   { destruct (Nat.eq_dec i (v*2+1)) as [E|E]; [|lia].
     subst i. rewrite Nat.add_comm,Nat.mod_add in Hpar by lia. discriminate. }

   pose proof (prefix_tail_nth (v*2+1) tail i Hstrict Hnth) as Htail.
   assert (Hpar':(i-(v*2+1)-1) mod 2=0).
   { replace i with ((i-(v*2+1)-1)+(v+1)*2) in Hpar by lia.
     rewrite Nat.mod_add in Hpar by lia. exact Hpar. }
   pose proof (IHHroute (i-(v*2+1)-1) Htail Hpar') as Hbound.
   rewrite length_app,repeat_length. cbn[length]. lia.
Qed.

Lemma route_known_even_bound L k bs L' k' rest j i :
 route L k bs L' k' rest ->
 length bs=2*j+1+length rest ->
 nth i bs false=true -> i mod 2=0 -> 2*j<=i.
Proof.
 intros Hr Hlen Hnth Hpar.
 pose proof (route_known_even _ _ _ _ _ _ Hr i Hnth Hpar). lia.
Qed.

Print Assumptions route_known_even_bound.
End RouteMarkerBound.
End RouteMarkerBound.

Module GuardedRoute.
(* The strong digit guard retains a bounded correction in the conversion fuel.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import StrongInvariant WallInvariant MarkedTrace OddRoute OddFuel OddImage.
Import OdDeficit RouteMarkerBound.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module GuardedRoute.
Module S := StrongInvariant.StrongInvariant.
Module W := WallInvariant.WallInvariant.
Module M := MarkedTrace.MarkedTrace.
Module P := OddRoute.OddRoute.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module D := OdDeficit.OdDeficit.
Module B := RouteMarkerBound.RouteMarkerBound.

Definition good_deficit j delta :=
 (1<=j /\ delta=(2^(2*j+2)-3)*2^(5*j)) \/
 (exists u c, 2<=j /\ u+1<=2*j /\ c<2^(5*j-5) /\
  delta=(2^(u+2)-3)*2^(5*j)+c).

Definition source_data n bs :=
 exists L k rest j delta,
 M.wall_route n bs L k rest /\
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k+1+delta=2^L /\ good_deficit j delta.

Lemma package n bs L k rest j delta :
 M.wall_route n bs L k rest -> L=n+5*j+1 ->
 k+1+delta=2^L -> good_deficit j delta -> source_data n bs.
Proof.

 intros Hr HL HD HG.
 destruct (M.route_dimensions _ _ _ _ _ Hr) as [j0 [Hlen HL0]].
 assert (j0=j) by lia. subst j0.
 exists L,k,rest,j,delta. repeat split; assumption.
Qed.

Lemma direct_data n j tail :
 1<=j -> length (repeat false (j*2)++true::tail)+1<=n ->
 source_data n (repeat false (j*2)++true::tail).
Proof.

 intros Hj Hlen.
 eapply package with (L:=n+1+j*5)
  (k:=F.grown (I.first_fuel n (j*2)) (j*5)) (rest:=tail) (j:=j)
  (delta:=(2^(2*j+2)-3)*2^(5*j)).
 - constructor.
 - lia.

 - replace (2*j) with (j*2) by lia. replace (5*j) with (j*5) by lia.
   apply (D.initial_even_deficit n j tail); exact Hlen.
 - left. split; [exact Hj|reflexivity].
Qed.

Lemma routed_data n v tail L k rest r :
 P.route (n+1+(v*5+3)) (F.grown (I.first_fuel n (v*2+1)) (v*5+3))
  tail L k rest ->
 length (repeat false (v*2+1)++true::tail)+1<=n ->
 length tail=2*r+1+length rest ->
 2<=v+1+r -> 7*r+3<=5*(v+1+r)-5 ->
 source_data n (repeat false (v*2+1)++true::tail).
Proof.

 intros Hr Hn Hlen Hj Hsmall.
 destruct (D.initial_odd_route_deficit _ _ _ _ _ _ Hr Hn)
  as [r0 [c [Hlen0 [HL [Hc HE]]]]].
 assert (r0=r) by lia. subst r0.
 eapply package with (L:=L) (k:=k) (rest:=rest) (j:=v+1+r)
  (delta:=(2^(v*2+3)-3)*2^(5*(v+1+r))+c).

 - constructor. exact Hr.
 - exact HL.
 - lia.
 - right. exists (v*2+1),c. repeat split; try lia.
   + eapply Nat.lt_le_trans; [exact (proj2 Hc)|]. apply Nat.pow_le_mono_r; lia.
   + replace (v*2+1+2) with (v*2+3) by lia. reflexivity.
Qed.

Lemma adjacent_data n v tail :
 1<=v -> length (repeat false (v*2+1)++true::true::tail)+1<=n ->
 source_data n (repeat false (v*2+1)++true::true::tail).
Proof.

 intros Hv Hn.
 set (L0:=n+1+(v*5+3)).
 set (k0:=F.grown (I.first_fuel n (v*2+1)) (v*5+3)).
 assert (Hk:1<=k0).
 { unfold k0,F.grown.
   assert (8<=2^(v*5+3)) by (change (2^3<=2^(v*5+3)); apply Nat.pow_le_mono_r; lia).
   nia. }

 assert (Hr:P.route L0 k0 (true::tail) (L0+1+1) (F.grown (k0-1) 1) tail).
 { replace k0 with ((k0-1)+(2^(0*2+1)-1)) at 1 by (cbn[Nat.pow]; lia).
   change (P.route L0 ((k0-1)+(2^(0*2+1)-1))
     (repeat false (0*2)++true::tail) (L0+1+(0*5+1))
     (F.grown (k0-1) (0*5+1)) tail).
   constructor. }
 apply (routed_data n v (true::tail) (L0+1+1) (F.grown (k0-1) 1) tail 0).

 - exact Hr.
 - exact Hn.
 - cbn[length]. lia.
 - lia.
 - lia.
Qed.

Lemma odd_index_even_tail a i :
 10*a<i -> i mod 2=1 -> (i-10*a-1) mod 2=0.
Proof.

 intros Hi Hp. destruct (mod2 (i-10*a-1)) as [t He|t He].
 - rewrite He,Nat.mod_mul by lia. reflexivity.
 - assert (Ei:i=(5*a+t+1)*2) by lia.
   rewrite Ei,Nat.mod_mul in Hp by lia. discriminate.
Qed.

Lemma close_data n a tail i :
 0<a -> length (repeat false (10*a+1)++true::tail)+1<=n ->
 nth i (repeat false (10*a)++true::tail) false=true ->
 i mod 2=1 -> i<=14*a+3 ->
 source_data n (repeat false (10*a+1)++true::tail).
Proof.

 intros Ha Hn Hbit Hp Hbound.
 assert (Hi:10*a<i).
 { pose proof (B.prefix_true_index (10*a) tail i Hbit) as Hlo.
   destruct (Nat.eq_dec i (10*a)) as [E|E]; [|lia].
   rewrite E in Hp. replace (10*a) with ((5*a)*2) in Hp by lia.
   rewrite Nat.mod_mul in Hp by lia. discriminate. }

 pose proof (B.prefix_tail_nth (10*a) tail i Hi Hbit) as Htail.
 pose proof (odd_index_even_tail a i Hi Hp) as Heven.
 assert (Hmark:W.marked 0 tail).
 { destruct (S.nth_true_split tail (i-10*a-1) Htail) as [pre [post [E Hlen]]].
   exists pre,post. split; [exact E|rewrite Hlen;exact Heven]. }
 set (L0:=n+1+((5*a)*5+3)).
 set (k0:=F.grown (I.first_fuel n ((5*a)*2+1)) ((5*a)*5+3)).

 assert (Hmargin:2^(length tail+4)-1<=k0).
 { unfold k0. apply M.initial_margin4.
   - rewrite length_app,repeat_length in Hn. cbn[length] in Hn. lia.
   - lia. }
 assert (Hbasic:2^length tail-1<=k0).
 { assert (2^length tail<=2^(length tail+4)) by (apply Nat.pow_le_mono_r; lia). lia. }
 destruct (P.marked_route L0 k0 tail Hmark Hbasic) as [L [k [rest [Hr Hlower]]]].

 destruct (P.route_dimensions _ _ _ _ _ _ Hr) as [r [Hlen HL]].
 pose proof (B.route_known_even_bound _ _ _ _ _ _ r (i-10*a-1) Hr Hlen Htail Heven) as Hrbound.
 assert (Hrsmall:r<=2*a+1) by lia.
 replace (10*a+1) with ((5*a)*2+1) by lia.
 apply (routed_data n (5*a) tail L k rest r).
 - exact Hr.
 - replace ((5*a)*2+1) with (10*a+1) by lia. exact Hn.

 - exact Hlen.
 - lia.
 - lia.
Qed.

Lemma prepend_repeat u tail : false::(repeat false u++tail)=repeat false (u+1)++tail.
Proof. replace (u+1) with (S u) by lia. reflexivity. Qed.

Lemma guard_source n bs :
 length bs+2<=n -> S.digit_guard bs -> source_data n (false::bs).
Proof.

 intros Hn HG.
 destruct HG as [[u [tail E]]|[[u [tail [Hu E]]]|[a [tail [i [Ha [E [Hbit [Hp Hib]]]]]]]]].
 - subst bs. rewrite prepend_repeat.
   replace (u*2+1+1) with ((u+1)*2) by lia.
   apply direct_data; [lia|].
   rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.

 - subst bs. rewrite prepend_repeat.
   destruct (mod2 u) as [v He|v He]; subst u.
   + apply adjacent_data; [lia|].
     rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.
   + replace (1+v*2+1) with ((v+1)*2) by lia.
     apply direct_data; [lia|].
     rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.

 - subst bs. rewrite prepend_repeat.
   apply (close_data n a tail i); try assumption.
   rewrite length_app,repeat_length in Hn |-*. cbn[length] in *. lia.
Qed.

Print Assumptions guard_source.
End GuardedRoute.
End GuardedRoute.

Module CounterBits.
(* Binary digits and the parity marker in a wall configuration.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import CounterRules CounterFinish WallInvariant.
Import String List PeanoNat NArith Lia.
Import CounterRules.CounterRules CounterFinish.CounterFinish WallInvariant.WallInvariant.
Open Scope nat.

Module CounterBits.
Fixpoint value (bs:list bool) : nat :=
  match bs with [] => 0 | b::bs => (if b then 1 else 0) + 2*value bs end.

Lemma digits_value n v : v < 2^n -> value (digits n v) = v.
Proof.
  gen v. induction n; intros v Hv.
  - cbn in Hv. assert (v=0) by lia. subst. reflexivity.
  - destruct (mod2 v); subst.
    + rewrite digits_even. cbn [value]. rewrite IHn by (cbn in Hv; lia). lia.
    + rewrite Nat.add_comm. rewrite digits_odd. cbn [value].
      rewrite IHn by (cbn in Hv; lia). lia.
Qed.

Lemma value_nonzero bs : value bs <> 0 -> In true bs.
Proof.
  induction bs as [|b bs IH]; cbn; intros H.
  - contradiction.
  - destruct b; [left; reflexivity|]. right. apply IH. lia.
Qed.

Lemma digits_split n i v :
  i <= n -> digits n v = digits i v ++ digits (n-i) (v/2^i).
Proof.
  gen n v. induction i; intros n v Hi.
  - cbn [digits Nat.pow]. rewrite Nat.sub_0_r, Nat.div_1_r. reflexivity.
  - destruct n; [lia|]. cbn [digits Nat.sub Nat.pow].
    rewrite IHi by lia.
    rewrite Nat.div_div by (pose proof (Nat.pow_nonzero 2 i ltac:(lia)); lia).
    reflexivity.
Qed.

Lemma digits_marked n v i q :
  i < n -> v/2^i = q*2+1 -> marked (i mod 2) (digits n v).
Proof.
  intros Hin Hq.
  rewrite (digits_split n i v) by lia.
  rewrite Hq.
  replace (n-i) with (S (n-i-1)) by lia.
  rewrite digits_odd.
  exists (digits i v), (digits (n-i-1) q).
  split; [reflexivity|]. rewrite digits_length. reflexivity.
Qed.

Lemma marked_shift_odd n q i :
  i < n -> i mod 2 = 1 -> marked 1 (digits n ((q*2+1)*2^i)).
Proof.
  intros Hin Hi.
  pose proof (digits_marked n ((q*2+1)*2^i) i q Hin) as Hm.
  rewrite Hi in Hm. apply Hm.
  rewrite Nat.div_mul by (apply Nat.pow_nonzero; lia). reflexivity.
Qed.

Lemma marked_remainder n v i q r :
  i<n -> r<2^i -> v=(q*2+1)*2^i+r ->
  marked (i mod 2) (digits n v).
Proof.
  intros Hi Hr Hv. apply (digits_marked n v i q Hi).
  rewrite Hv, Nat.add_comm, Nat.div_add by (apply Nat.pow_nonzero; lia).
  rewrite Nat.div_small by exact Hr. lia.
Qed.

Open Scope sym.

Lemma shifted_normal_word bs :
  [0;0;0;0] ++ normal bs = shifted bs ++ [0;0;0;0].
Proof.
  induction bs as [|b bs IH].
  - reflexivity.
  - destruct b; cbn [normal shifted app]; rewrite <-IH; reflexivity.
Qed.

Lemma shifted_normal bs :
  [0;0;0;0] *> normal bs *> 0inf = shifted bs *> 0inf.
Proof.
  rewrite <-Str_app_assoc, shifted_normal_word, Str_app_assoc.
  st. reflexivity.
Qed.

Lemma numeric_even n v :
  (0 < v)%nat -> (v*2 < 2^n)%nat ->
  invariant ((0inf <* <[1;1]) <* [0] {{A}}>
             ([1] *> [1;1]^^n *> RC (v*2))).
Proof.

  intros Hv Hbound.
  rewrite <- (digits_normal n (v*2) Hbound).
  replace ([1] *> [1;1]^^n *> normal (digits n (v*2)) *> 0inf)
    with ([1;1]^^n *> [1] *> normal (digits n (v*2)) *> 0inf)
    by (simpl_rotate; reflexivity).
  replace ([1;1]^^n *> [1] *> normal (digits n (v*2)) *> 0inf)
    with (([1;1]^^n ++ [1] ++ normal (digits n (v*2))) *> 0inf)
    by (repeat rewrite Str_app_assoc; reflexivity).
  change (invariant (O n (digits n (v*2)))).

  apply InvO.
  - rewrite digits_length. lia.
  - destruct n; [cbn in Hbound; lia|].
    rewrite digits_even. eexists. reflexivity.
  - apply value_nonzero. rewrite digits_value by exact Hbound. lia.
Qed.

Lemma numeric_odd n v :
  (v < 2^n)%nat -> marked 1 (digits n v) ->
  invariant ((0inf <* <[1;1]) <* [0] {{A}}>
             ([1] *> [1;1]^^(n+1) *> RC (v*2+1))).
Proof.

  intros Hv Hmark.
  unfold RC. rewrite BinInc_mul2add1.
  change (invariant ((0inf <* <[1;1]) <* [0] {{A}}>
    ([1] *> [1;1]^^(n+1) *> [1;0;0;0;0] *> RC v))).
  rewrite <- (digits_normal n v Hv).
  replace ([1] *> [1;1]^^(n+1) *> [1;0;0;0;0] *> normal (digits n v) *> 0inf)
    with ([1;1]^^(n+2) *> [0;0;0;0] *> normal (digits n v) *> 0inf)
    by (replace (n+2)%nat with ((n+1)+1)%nat by lia; st; simpl_rotate; reflexivity).
  rewrite shifted_normal.

  replace ([1;1]^^(n+2) *> shifted (digits n v) *> 0inf)
    with (([1;1]^^(n+2) ++ shifted (digits n v)) *> 0inf)
    by (rewrite Str_app_assoc; reflexivity).
  change (invariant (E (n+2) (digits n v))).
  apply InvE.
  - rewrite digits_length. lia.
  - exact Hmark.
Qed.

Lemma numeric_even_value n t :
  (0<t)%nat -> (t<2^n)%nat -> (t mod 2=0)%nat ->
  invariant ((0inf <* <[1;1]) <* [0] {{A}}>
             ([1] *> [1;1]^^n *> RC t)).
Proof.
  intros Ht Hb He.
  destruct (mod2 t); subst.
  - apply numeric_even; lia.
  - rewrite Nat.mod_add in He by lia. discriminate.
Qed.

Lemma counter_finish_even n k r :
  (k<2^n)%nat -> (0<r+k+1)%nat -> (r+k+1<2^n)%nat ->
  ((r+k+1) mod 2=0)%nat ->
  exists c, (LC n k <* [0;1] {{A}}> RC r) -[mtm]->+ c /\ invariant c.
Proof.
  intros Hk Hpos Hb He. eexists. split.
  - apply counter_finish; exact Hk.
  - apply numeric_even_value; assumption.
Qed.

Print Assumptions digits_marked.
Print Assumptions numeric_even.
Print Assumptions numeric_odd.
Print Assumptions counter_finish_even.
End CounterBits.
End CounterBits.

Module MarkerArithmetic.
(* Preserving a low binary digit through a distant carry.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits CounterFinish WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits CounterFinish.CounterFinish WallInvariant.WallInvariant.
Open Scope nat.

Module MarkerArithmetic.
Lemma value_bound bs : value bs<2^(length bs).
Proof.
 induction bs as [|b bs IH]; cbn [value length Nat.pow]; [lia|].
 destruct b; nia.
Qed.

Lemma digits_value_inverse bs : digits (length bs) (value bs)=bs.
Proof.
 induction bs as [|b bs IH]; [reflexivity|].
 destruct b; cbn [length value].
 - replace (1+2*value bs) with (value bs*2+1) by lia.
   rewrite digits_odd, IH. reflexivity.
 - replace (0+2*value bs) with (value bs*2) by lia.
   rewrite digits_even, IH. reflexivity.
Qed.

Lemma marked_value_remainder bs i q low :
 i<length bs -> low<2^i -> value bs=(q*2+1)*2^i+low ->
 marked (i mod 2) bs.
Proof.
 intros Hi Hlow Heq.
 rewrite <-(digits_value_inverse bs).
 apply (marked_remainder (length bs) (value bs) i q low); assumption.
Qed.

Lemma marked_residue bs i r :
 i<length bs -> r<2^i -> value bs mod 2^(i+1)=2^i+r ->
 marked (i mod 2) bs.
Proof.
 intros Hi Hr He.
 pose proof (Nat.div_mod (value bs) (2^(i+1)) (Nat.pow_nonzero 2 (i+1) ltac:(lia))) as Hdiv.
 apply (marked_value_remainder bs i (value bs/2^(i+1)) r); [exact Hi|exact Hr|].
 rewrite He in Hdiv. rewrite Nat.pow_add_r in *.
 cbn [Nat.pow] in *. nia.
Qed.

Lemma power_multiple low high : low<=high ->
 2^high=2^(high-low)*2^low.
Proof.
 intro H. rewrite <-Nat.pow_add_r. f_equal. lia.
Qed.

Lemma carry_width bs j big v :
 0<big -> value bs+2^(length bs)=big*2^j+v -> j<=length bs.
Proof.
 intros Hbig Heq. pose proof (value_bound bs) as Hv.
 destruct (Nat.le_gt_cases j (length bs)); [assumption|].
 assert (Hp:2^(length bs+1)<=2^j) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in Hp. cbn [Nat.pow] in Hp.
 pose proof (Nat.pow_nonzero 2 j ltac:(lia)). nia.
Qed.

Lemma low_marker_preserved bs v i q r j big :
 0<big -> i<j -> r<2^i -> v=(q*2+1)*2^i+r ->
 value bs+2^(length bs)=big*2^j+v -> marked (i mod 2) bs.
Proof.
 intros Hbig Hij Hr Hv Heq.
 pose proof (carry_width bs j big v Hbig Heq) as Hlen.
 apply (marked_residue bs i r); [lia|exact Hr|].

 rewrite (power_multiple (i+1) (length bs)) in Heq by lia.
 rewrite (power_multiple (i+1) j) in Heq by lia.
 replace (big*(2^(j-(i+1))*2^(i+1))+v) with
   (v+(big*2^(j-(i+1)))*2^(i+1)) in Heq by nia.
 apply (f_equal (fun n=>n mod 2^(i+1))) in Heq.
 rewrite !Nat.mod_add in Heq by (apply Nat.pow_nonzero; lia).
 rewrite Heq, Hv.

 replace ((q*2+1)*2^i+r) with ((2^i+r)+q*2^(i+1)) by
   (rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
 rewrite Nat.mod_add by (apply Nat.pow_nonzero; lia).
 apply Nat.mod_small. rewrite Nat.pow_add_r. cbn [Nat.pow]. lia.
Qed.

Print Assumptions low_marker_preserved.
End MarkerArithmetic.
End MarkerArithmetic.

Module GapMarker.
(* A small subtraction preserves an odd-position binary marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits MarkerArithmetic WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits MarkerArithmetic.MarkerArithmetic WallInvariant.WallInvariant.
Open Scope nat.

Module GapMarker.
Lemma marked_residue_auto bs i r :
 r<2^i -> value bs mod 2^(i+1)=2^i+r -> marked (i mod 2) bs.
Proof.
 intros Hr He. apply (marked_residue bs i r); [|exact Hr|exact He].
 destruct (Nat.lt_ge_cases i (length bs)); [assumption|].
 pose proof (value_bound bs) as Hv.
 assert (Hp:2^length bs<=2^i) by (apply Nat.pow_le_mono_r; lia).
 assert (Hsmall:value bs<2^(i+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }
 rewrite Nat.mod_small in He by exact Hsmall. lia.
Qed.

Lemma complement_residue v d c :
 0<c -> c<d -> (v+c) mod d=0 -> v mod d=d-c.
Proof.
 intros Hc Hcd Hsum.
 rewrite Nat.add_mod, (Nat.mod_small c d Hcd) in Hsum by lia.
 pose proof (Nat.mod_upper_bound v d ltac:(lia)) as Hv.
 pose proof (Nat.div_mod (v mod d+c) d ltac:(lia)) as Hdiv.
 rewrite Hsum in Hdiv.
 assert ((v mod d+c)/d=1) by nia. nia.
Qed.

Lemma subtraction_marker_at bs A J D c i :
 J<=A -> i<J -> J-2<=i -> i mod 2=1 ->
 0<c -> c<2^(J-2) ->
 value bs+c+D*2^J=2^A -> marked 1 bs.
Proof.

 intros HJA Hi Hlo Hpar Hc Hsmall Heq.
 assert (Hci:c<2^i).
 { assert (2^(J-2)<=2^i) by (apply Nat.pow_le_mono_r; lia). lia. }
 assert (Hcd:c<2^(i+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }

 assert (Hsum:(value bs+c) mod 2^(i+1)=0).
 { rewrite (power_multiple (i+1) A), (power_multiple (i+1) J) in Heq by lia.
   replace (D*(2^(J-(i+1))*2^(i+1))) with
     ((D*2^(J-(i+1)))*2^(i+1)) in Heq by nia.
   apply (f_equal (fun n=>n mod 2^(i+1))) in Heq.
   rewrite Nat.mod_add,Nat.mod_mul in Heq by (apply Nat.pow_nonzero; lia).
   exact Heq. }
 pose proof (complement_residue (value bs) (2^(i+1)) c Hc Hcd Hsum) as Hmod.
 pose proof (marked_residue_auto bs i (2^i-c)) as Hmark.
 rewrite Hpar in Hmark. apply Hmark; [lia|].
 rewrite Hmod, Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma small_subtraction_marker bs A B J c :
 3<=J -> 3<=B -> 0<c -> c<2^(J-2) ->
 value bs+c+(2^B-3)*2^J=2^A -> marked 1 bs.
Proof.

 intros HJ HB Hc Hsmall Heq.
 assert (HpowB:8<=2^B).
 { change (2^3<=2^B). apply Nat.pow_le_mono_r; lia. }
 assert (HJA:J<=A).
 { destruct (Nat.le_gt_cases J A); [assumption|].
   assert (2^A<2^J) by (apply Nat.pow_lt_mono_r; lia).
   pose proof (Nat.pow_nonzero 2 J ltac:(lia)). nia. }
 destruct (mod2 J) as [a E|a E]; subst J.
 - apply (subtraction_marker_at bs A (a*2) (2^B-3) c (a*2-1)); try assumption; try lia.
 - apply (subtraction_marker_at bs A (1+a*2) (2^B-3) c (1+a*2-2)); try assumption; try lia.
Qed.

Print Assumptions small_subtraction_marker.
End GapMarker.
End GapMarker.

Module MultiGapMarker.
(* Marker digits below several distant subtraction terms.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits MarkerArithmetic GapMarker WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits MarkerArithmetic.MarkerArithmetic GapMarker.GapMarker WallInvariant.WallInvariant.
Open Scope nat.

Module MultiGapMarker.
Lemma positive_subtraction_marker bs A J D c :
 3<=J -> 0<D -> 0<c -> c<2^(J-2) ->
 value bs+c+D*2^J=2^A -> marked 1 bs.
Proof.

 intros HJ HD Hc Hsmall Heq.
 assert (HJA:J<=A).
 { destruct (Nat.le_gt_cases J A); [assumption|].
   assert (2^A<2^J) by (apply Nat.pow_lt_mono_r; lia).
   pose proof (Nat.pow_nonzero 2 J ltac:(lia)). nia. }
 destruct (mod2 J) as [a E|a E]; subst J.
 - apply (subtraction_marker_at bs A (a*2) D c (a*2-1)); try assumption; lia.
 - apply (subtraction_marker_at bs A (1+a*2) D c (1+a*2-2)); try assumption; lia.
Qed.

Lemma two_gap_marker bs A J K D E c :
 0<D -> 0<E -> 3<=Nat.min J K ->
 0<c -> c<2^(Nat.min J K-2) ->
 value bs+c+D*2^J+E*2^K=2^A -> marked 1 bs.
Proof.

 intros HD HE Hmin Hc Hsmall Heq.
 set (m:=Nat.min J K) in *.
 assert (HmJ:m<=J) by (unfold m; apply Nat.le_min_l).
 assert (HmK:m<=K) by (unfold m; apply Nat.le_min_r).
 apply (positive_subtraction_marker bs A m
   (D*2^(J-m)+E*2^(K-m)) c); try assumption.
 - pose proof (Nat.pow_nonzero 2 (J-m) ltac:(lia)).
   pose proof (Nat.pow_nonzero 2 (K-m) ltac:(lia)). nia.
 - rewrite (power_multiple m J HmJ), (power_multiple m K HmK) in Heq.
   nia.
Qed.

Print Assumptions two_gap_marker.
End MultiGapMarker.
End MultiGapMarker.

Module MagnitudeMarker.
(* A sufficiently large binary word contains an odd-position marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits CounterFinish MarkerArithmetic WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits CounterFinish.CounterFinish MarkerArithmetic.MarkerArithmetic WallInvariant.WallInvariant.
Open Scope nat.

Module MagnitudeMarker.
Lemma value_app bs cs : value (bs++cs)=value bs+2^length bs*value cs.
Proof.
 induction bs as [|b bs IH]; [cbn;lia|].
 cbn[value length app Nat.pow]. rewrite IH. destruct b; nia.
Qed.

Lemma same_value_marker bs cs : value bs=value cs -> marked 1 bs -> marked 1 cs.
Proof.

 intros He [pre [post [E Hpar]]]. subst bs.
 pose proof (value_bound pre) as Hp.
 assert (Hvalue:value cs=(value post*2+1)*2^length pre+value pre).
 { rewrite value_app in He. cbn[value] in He. nia. }
 assert (Hindex:length pre<length cs).
 { destruct (Nat.lt_ge_cases (length pre) (length cs)); [assumption|].
   pose proof (value_bound cs).
   assert (2^length cs<=2^length pre) by (apply Nat.pow_le_mono_r; lia). nia. }
 rewrite <-Hpar.
 apply (marked_value_remainder cs (length pre) (value post) (value pre)); assumption.
Qed.

Lemma add_two_marker b c bs : marked 1 bs -> marked 1 (b::c::bs).
Proof.
 intros [pre [post [E Hp]]]. subst bs.
 exists (b::c::pre),post. split; [reflexivity|].
 cbn[length]. replace (S (S (length pre))) with (length pre+1*2) by lia.
 rewrite Nat.mod_add by lia. exact Hp.
Qed.

Lemma marker_or_bound : forall bs,
 marked 1 bs \/ 3*value bs<2^(length bs+1).
Proof.

 fix IH 1. intro bs. destruct bs as [|b [|c bs]].
 - right. cbn. lia.
 - right. destruct b; cbn; lia.
 - destruct c.
   + left. exists [b],bs. split; reflexivity.
   + destruct (IH bs) as [Hm|Hb].
     * left. apply add_two_marker. exact Hm.
     * right. cbn[value length].
       replace (S (S (length bs))+1) with ((length bs+1)+2) by lia.
       rewrite Nat.pow_add_r. cbn[Nat.pow]. destruct b; nia.
Qed.

Lemma magnitude_marker bs A :
 value bs<2^A -> 2^(A+1)<3*value bs -> marked 1 bs.
Proof.

 intros Hv Hlarge.
 pose proof (digits_value A (value bs) Hv) as Hvalue.
 destruct (marker_or_bound (digits A (value bs))) as [Hm|Hb].
 - apply (same_value_marker (digits A (value bs)) bs Hvalue Hm).
 - rewrite digits_length,Hvalue in Hb. lia.
Qed.

Print Assumptions magnitude_marker.
End MagnitudeMarker.
End MagnitudeMarker.

Module OdEvenMarker.
(* The even-position ordinary successor of an odd defective wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits WallInvariant MultiGapMarker MagnitudeMarker.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module OdEvenMarker.
Module CB := CounterBits.CounterBits.
Module W := WallInvariant.WallInvariant.
Module G := MultiGapMarker.MultiGapMarker.
Module M := MagnitudeMarker.MagnitudeMarker.

Lemma power_positive n : 0<2^n.
Proof. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia. Qed.

Lemma minus_three_positive u : 0<2^(u+2)-3.
Proof. rewrite Nat.pow_add_r. cbn[Nat.pow]. pose proof (power_positive u). nia. Qed.

Lemma scaled_minus_three u J :
 (2^(u+2)-3)*2^J<2^(u+2+J).
Proof.

 rewrite (Nat.pow_add_r 2 (u+2) J).
 pose proof (power_positive J). pose proof (minus_three_positive u). nia.
Qed.

Lemma terminal_small m T : T<=6*2^m -> 2*T-1<2^(m+4).
Proof.

 intro H. rewrite Nat.pow_add_r. cbn[Nat.pow]. pose proof (power_positive m). nia.
Qed.

Lemma sum_small J x y :
 3<=J -> x<2^(J-3) -> y<2^(J-3) -> x+y<2^(J-2).
Proof.

 intros HJ Hx Hy. replace (J-2) with ((J-3)+1) by lia.
 rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma three_small J x y z :
 4<=J -> x<2^(J-4) -> y<2^(J-4) -> z<2^(J-4) ->
 x+y+z<2^(J-2).
Proof.

 intros HJ Hx Hy Hz. replace (J-2) with ((J-4)+2) by lia.
 rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma magnitude_from_parts bs A x y z t :
 6<=A -> x<2^(A-2) -> y<2^(A-6) -> z<2^(A-6) -> t<2^(A-6) ->
 0<x+y+z+t -> CB.value bs+x+y+z+t=2^A -> W.marked 1 bs.
Proof.

 intros HA Hx Hy Hz Ht Hpos HE.

 assert (HP:2^A=64*2^(A-6)).
 { replace A with ((A-6)+6) at 1 by lia. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }

 assert (HPx:2^(A-2)=16*2^(A-6)).
 { replace (A-2) with ((A-6)+4) by lia. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }
 apply M.magnitude_marker with (A:=A).
 - pose proof (power_positive (A-6)). rewrite HP in *. rewrite HPx in Hx. lia.
 - rewrite Nat.pow_add_r. cbn[Nat.pow].
   rewrite HP in *. rewrite HPx in Hx.
   pose proof (power_positive (A-6)). lia.
Qed.

Lemma reachable_even_marker bs a j m u C T :
 2<=j -> u+1<=2*j -> m<=4*a -> 0<T -> T<=6*2^m ->
 C<2^(5*j-5) ->
 CB.value bs+(C+2*T-1)+
  (2^(u+2)-3)*2^(5*j)+(2^(10*a+6)-3)*2^(25*a+9)=2^(m+7*j+3) ->
 W.marked 1 bs.
Proof.

 intros Hj Hu Hm HT HTb HC HE.
 set (J:=5*j). set (K:=25*a+9). set (A:=m+7*j+3).
 set (D:=2^(u+2)-3). set (E:=2^(10*a+6)-3).
 set (F:=D*2^J). set (Q:=E*2^K).
 set (c:=C+2*T-1).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEpos:0<E).
 { unfold E. replace (10*a+6) with ((10*a+4)+2) by lia.
   apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; lia).

 assert (HK:4<=K) by (unfold K; lia).

 assert (Hc:0<c) by (unfold c; lia).

 assert (HF:F<2^(7*j+1)).
 { unfold F,D,J. eapply Nat.lt_le_trans.
   - apply scaled_minus_three.
   - apply Nat.pow_le_mono_r; clear -Hu Hj; lia. }

 assert (HQ:Q<2^(35*a+15)).
 { unfold Q,E,K. replace (10*a+6) with ((10*a+4)+2) by lia.
   pose proof (scaled_minus_three (10*a+4) (25*a+9)) as H.
   replace (10*a+4+2+(25*a+9)) with (35*a+15) in H by lia. exact H. }

 assert (HTs:2*T-1<2^(m+4)) by (apply terminal_small; exact HTb).

 assert (HEq:CB.value bs+c+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (7*j) (25*a+4)) as [Hsmall|Hlarge].
 - assert (HF':F<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HC':C<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HT':2*T-1<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }
   apply (G.positive_subtraction_marker bs A K E (c+F)).
   + clear -HK. lia.
   + exact HEpos.
   + clearbody F c. clear -Hc. lia.
   + replace (c+F) with (C+(2*T-1)+F) by (unfold c; clearbody F; clear -HT; lia).
     apply three_small; assumption.
   + unfold Q in HEq. clear -HEq. lia.
 - destruct (Nat.le_gt_cases j (5*a+2)) as [Hmiddle|Hbig].
   + assert (HCJ:C<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTJ:2*T-1<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcJ:c<2^(J-2)).
     { replace c with (C+(2*T-1)) by (unfold c; clear -HT; lia). apply sum_small; assumption. }

     assert (HCK:C<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTK:2*T-1<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcK:c<2^(K-2)).
     { replace c with (C+(2*T-1)) by (unfold c; clear -HT; lia). apply sum_small; try assumption; clear -HK; lia. }
     apply (G.two_gap_marker bs A J K D E c); try assumption.
     * apply Nat.min_glb; clear -HJ HK; lia.
     * destruct (Nat.le_ge_cases J K).
       -- rewrite Nat.min_l by assumption. exact HcJ.
       -- rewrite Nat.min_r by assumption. exact HcK.
   + assert (HA:6<=A) by (unfold A; lia).

     assert (HFA:F<2^(A-2)).
     { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HCA:C<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HTA:2*T-1<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HQA:Q<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HQ|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }
     apply (magnitude_from_parts bs A F C (2*T-1) Q); try assumption.
     all: clearbody F Q; unfold c in HEq; clear -HEq HT; lia.
Qed.

Print Assumptions reachable_even_marker.
End OdEvenMarker.
End OdEvenMarker.

Module OdOddMarker.
(* The odd-position ordinary successor of an odd defective wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits WallInvariant MultiGapMarker MagnitudeMarker OdEvenMarker.
Import List PeanoNat Lia.
Import ListNotations OdEvenMarker.OdEvenMarker.
Open Scope nat.

Module OdOddMarker.
Module CB := CounterBits.CounterBits.
Module W := WallInvariant.WallInvariant.
Module G := MultiGapMarker.MultiGapMarker.
Module M := MagnitudeMarker.MagnitudeMarker.

Lemma terminal_small_odd m T : 1<=m -> T<=6*2^m -> T+3<2^(m+3).
Proof.

 intros Hm HT. assert (2<=2^m) by (change (2^1<=2^m); apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma reachable_odd_marker bs a j m u C T :
 2<=j -> u+1<=2*j -> 1<=m<=4*a+2 -> 0<T -> T<=6*2^m ->
 C<2^(5*j-6) ->
 CB.value bs+(C+T+3)+
  (2^(u+2)-3)*2^(5*j-1)+(2^(10*a+11)-3)*2^(25*a+24)=2^(m+7*j+2) ->
 W.marked 1 bs.
Proof.

 intros Hj Hu Hm HT HTb HC HE.
 set (J:=5*j-1). set (K:=25*a+24). set (A:=m+7*j+2).
 set (D:=2^(u+2)-3). set (E:=2^(10*a+11)-3).
 set (F:=D*2^J). set (Q:=E*2^K).
 set (c:=C+T+3).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEpos:0<E).
 { unfold E. replace (10*a+11) with ((10*a+9)+2) by lia.
   apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; lia).

 assert (HK:4<=K) by (unfold K; lia).

 assert (Hc:0<c) by (unfold c; lia).

 assert (HF:F<2^(7*j)).
 { unfold F,D,J. eapply Nat.lt_le_trans.
   - apply scaled_minus_three.
   - apply Nat.pow_le_mono_r; clear -Hu Hj; lia. }

 assert (HQ:Q<2^(35*a+35)).
 { unfold Q,E,K. replace (10*a+11) with ((10*a+9)+2) by lia.
   pose proof (scaled_minus_three (10*a+9) (25*a+24)) as H.
   replace (10*a+9+2+(25*a+24)) with (35*a+35) in H by lia. exact H. }

 assert (HTs:T+3<2^(m+3)) by (apply terminal_small_odd; [lia|exact HTb]).

 assert (HEq:CB.value bs+c+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (7*j) (25*a+20)) as [Hsmall|Hlarge].
 - assert (HF':F<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HC':C<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }

   assert (HT':T+3<2^(K-4)).
   { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hsmall Hj Hu Hm; lia. }
   apply (G.positive_subtraction_marker bs A K E (c+F)).
   + clear -HK. lia.
   + exact HEpos.
   + clearbody F c. clear -Hc. lia.
   + replace (c+F) with (C+(T+3)+F) by (unfold c; clearbody F; clear -HT; lia).
     apply three_small; assumption.
   + unfold Q in HEq. clear -HEq. lia.
 - destruct (Nat.le_gt_cases j (5*a+5)) as [Hmiddle|Hbig].
   + assert (HCJ:C<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTJ:T+3<2^(J-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold J; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcJ:c<2^(J-2)).
     { replace c with (C+(T+3)) by (unfold c; clear -HT; lia). apply sum_small; assumption. }

     assert (HCK:C<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HTK:T+3<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold K; clear -Hj Hlarge Hmiddle Hm; lia. }

     assert (HcK:c<2^(K-2)).
     { replace c with (C+(T+3)) by (unfold c; clear -HT; lia). apply sum_small; try assumption; clear -HK; lia. }
     apply (G.two_gap_marker bs A J K D E c); try assumption.
     * apply Nat.min_glb; clear -HJ HK; lia.
     * destruct (Nat.le_ge_cases J K).
       -- rewrite Nat.min_l by assumption. exact HcJ.
       -- rewrite Nat.min_r by assumption. exact HcK.
   + assert (HA:6<=A) by (unfold A; lia).

     assert (HFA:F<2^(A-2)).
     { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HCA:C<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HC|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HTA:T+3<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HTs|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }

     assert (HQA:Q<2^(A-6)).
     { eapply Nat.lt_le_trans; [exact HQ|]. apply Nat.pow_le_mono_r; unfold A; clear -Hj Hbig Hm Hu; lia. }
     apply (magnitude_from_parts bs A F C (T+3) Q); try assumption.
     all: clearbody F Q; unfold c in HEq; clear -HEq HT; lia.
Qed.

Print Assumptions reachable_odd_marker.
End OdOddMarker.
End OdOddMarker.

Module OdDirectMarker.
(* Marker preservation when the first marked odd-wall digit is encountered directly.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import CounterBits WallInvariant MultiGapMarker OdEvenMarker OdOddMarker.
Import List PeanoNat Lia.
Import ListNotations OdEvenMarker.OdEvenMarker OdOddMarker.OdOddMarker.
Open Scope nat.

Module OdDirectMarker.
Module CB := CounterBits.CounterBits.
Module W := WallInvariant.WallInvariant.
Module G := MultiGapMarker.MultiGapMarker.

Lemma direct_even_marker bs a j m T :
 1<=j -> m<=4*a -> 0<T -> T<=6*2^m ->
 CB.value bs+(2*T-1)+(2^(2*j+2)-3)*2^(5*j)+
  (2^(10*a+6)-3)*2^(25*a+9)=2^(m+7*j+3) -> W.marked 1 bs.
Proof.

 intros Hj Hm HT HTb HE.
 set (J:=5*j). set (K:=25*a+9). set (A:=m+7*j+3).
 set (D:=2^(2*j+2)-3). set (E:=2^(10*a+6)-3).
 set (F:=D*2^J). set (Q:=E*2^K).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEp:0<E).
 { unfold E. replace (10*a+6) with ((10*a+4)+2) by lia. apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; clear -Hj; lia).

 assert (HK:3<=K) by (unfold K; lia).

 assert (HTs:2*T-1<2^(m+4)) by (apply terminal_small; exact HTb).

 assert (HEq:CB.value bs+(2*T-1)+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (m+6) (5*j)) as [Hsmall|Hlarge].
 - apply (G.two_gap_marker bs A J K D E (2*T-1)); try assumption.
   + apply Nat.min_glb; assumption.
   + clear -HT. lia.
   + assert (Hmin:m+6<=Nat.min J K).
     { apply Nat.min_glb; unfold J,K; clear -Hsmall Hm; lia. }
     eapply Nat.lt_le_trans; [exact HTs|].
     apply Nat.pow_le_mono_r; clear -Hmin; lia.
 - destruct a as [|a].
   + assert (m=0) by lia. subst m.

     assert (j=1) by lia. subst j.
     change (CB.value bs+(2*T-1)+13*32+61*512=1024) in HE.
     clear -HE. lia.
   + assert (HF:F<2^(7*j+2)).
     { unfold F,D,J. pose proof (scaled_minus_three (2*j) (5*j)) as H.
       replace (2*j+2+5*j) with (7*j+2) in H by lia. exact H. }

     assert (HFK:F<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HF|].
       apply Nat.pow_le_mono_r; unfold K; clear -Hj Hm Hlarge; lia. }

     assert (HTK:2*T-1<2^(K-3)).
     { eapply Nat.lt_le_trans; [exact HTs|].
       apply Nat.pow_le_mono_r; unfold K; clear -Hm; lia. }
     apply (G.positive_subtraction_marker bs A K E ((2*T-1)+F)); try assumption.
     * clearbody F. clear -HT. lia.
     * apply sum_small; assumption.
     * unfold Q in HEq. clear -HEq. lia.
Qed.

Lemma direct_odd_marker bs a j m T :
 1<=j -> 1<=m<=4*a+2 -> 0<T -> T<=6*2^m ->
 CB.value bs+(T+3)+(2^(2*j+2)-3)*2^(5*j-1)+
  (2^(10*a+11)-3)*2^(25*a+24)=2^(m+7*j+2) -> W.marked 1 bs.
Proof.

 intros Hj Hm HT HTb HE.
 set (J:=5*j-1). set (K:=25*a+24). set (A:=m+7*j+2).
 set (D:=2^(2*j+2)-3). set (E:=2^(10*a+11)-3).
 set (F:=D*2^J). set (Q:=E*2^K).

 assert (HD:0<D) by (unfold D; apply minus_three_positive).

 assert (HEp:0<E).
 { unfold E. replace (10*a+11) with ((10*a+9)+2) by lia. apply minus_three_positive. }

 assert (HJ:3<=J) by (unfold J; clear -Hj; lia).

 assert (HK:3<=K) by (unfold K; lia).

 assert (HTs:T+3<2^(m+3)) by (apply terminal_small_odd; [lia|exact HTb]).

 assert (HEq:CB.value bs+(T+3)+F+Q=2^A) by exact HE.
 destruct (Nat.le_gt_cases (m+6) (5*j)) as [Hsmall|Hlarge].
 - apply (G.two_gap_marker bs A J K D E (T+3)); try assumption.
   + apply Nat.min_glb; assumption.
   + lia.
   + assert (Hmin:m+5<=Nat.min J K).
     { apply Nat.min_glb; unfold J,K; clear -Hsmall Hm; lia. }
     eapply Nat.lt_le_trans; [exact HTs|].
     apply Nat.pow_le_mono_r; clear -Hmin; lia.
 - assert (HF:F<2^(7*j+1)).
   { unfold F,D,J. eapply Nat.lt_le_trans; [apply scaled_minus_three|].
     apply Nat.pow_le_mono_r; clear -Hj; lia. }

   assert (HFK:F<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact HF|].
     apply Nat.pow_le_mono_r; unfold K; clear -Hj Hm Hlarge; lia. }

   assert (HTK:T+3<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact HTs|].
     apply Nat.pow_le_mono_r; unfold K; clear -Hm; lia. }
   apply (G.positive_subtraction_marker bs A K E ((T+3)+F)); try assumption.
   + lia.
   + apply sum_small; assumption.
   + unfold Q in HEq. clear -HEq. lia.
Qed.

Print Assumptions direct_even_marker.
Print Assumptions direct_odd_marker.
End OdDirectMarker.
End OdDirectMarker.

Module ExceptionalPasses.
(* Exceptional pass laws for a shift-overflow counter.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored.
Open Scope sym.

Module Exceptional.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dc := [0;0;0;0;1].
Notation dd := [1;0;0;0;1].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].

Lemma shifted_two : segRLs mtm (p^^2) x dc da.
Proof. esc. Qed.

Lemma shifted_even k :
  segRLs mtm (p^^(2*k+2)) (x ++ p^^k) dc da.
Proof.
  replace (2*k+2) with (2+k*2) by lia.
  rewrite lpow_add.
  eapply segRLs_trans.
  - apply shifted_two.
  - apply d0_Incs.
Qed.

Lemma shifted_odd k :
  segRLs mtm (p^^(2*k+3)) (x ++ p^^k) dc db.
Proof.
  replace (2*k+3) with (2+(k*2+1)) by lia.
  rewrite lpow_add.
  eapply segRLs_trans.
  - apply shifted_two.
  - apply d01_Incs.
Qed.

Lemma exception_zero : segRLs mtm x [] da dc.
Proof. esc. Qed.

Lemma exception_one : segRLs mtm (x ++ p) [] da dd.
Proof. esc. Qed.

Lemma exception_even k :
  segRLs mtm (x ++ p^^(2*k+2)) (x ++ p^^k) da da.
Proof.
  eapply @segRLs_trans with (ls2:=[]) (ls4:=x ++ p^^k).
  - apply exception_zero.
  - apply shifted_even.
Qed.

Lemma exception_odd k :
  segRLs mtm (x ++ p^^(2*k+3)) (x ++ p^^k) da db.
Proof.
  eapply @segRLs_trans with (ls2:=[]) (ls4:=x ++ p^^k).
  - apply exception_zero.
  - apply shifted_odd.
Qed.

Lemma exception_shifted : segRLs mtm x x dc da.
Proof. esc. Qed.

Lemma exception_shifted_even k :
  segRLs mtm (x ++ p^^(k*2)) (x ++ p^^k) dc da.
Proof.
  eapply segRLs_trans.
  - apply exception_shifted.
  - apply d0_Incs.
Qed.

Lemma exception_shifted_odd k :
  segRLs mtm (x ++ p^^(k*2+1)) (x ++ p^^k) dc db.
Proof.
  eapply segRLs_trans.
  - apply exception_shifted.
  - apply d01_Incs.
Qed.

Lemma exception_zeros k n :
  segRLs mtm (x ++ p^^((k+2)*2^n-2)) (x ++ p^^k) (da^^n) (da^^n).
Proof.
  gen k.
  induction n; intros.
  - cbn [Nat.pow lpow].
    replace ((k+2)*1-2) with k by lia.
    apply segRLs_nil.
  - cbn [Nat.pow lpow].
    eapply segRLs_concat.
    2: apply IHn.
    pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
    replace ((k+2)*(2*2^n)-2) with (2*((k+2)*2^n-2)+2) by nia.
    apply exception_even.
Qed.

Lemma exception_shifteds k n :
  segRLs mtm (x ++ p^^(k*2^n)) (x ++ p^^k) (dc^^n) (da^^n).
Proof.
  gen k.
  induction n; intros.
  - cbn [Nat.pow lpow].
    replace (k*1) with k by lia.
    apply segRLs_nil.
  - cbn [Nat.pow lpow].
    eapply segRLs_concat.
    2: apply IHn.
    replace (k*(2*2^n)) with ((k*2^n)*2) by nia.
    apply exception_shifted_even.
Qed.

Print Assumptions exception_zeros.
Print Assumptions exception_shifteds.
End Exceptional.
End ExceptionalPasses.

Module PhaseE.
(* A complete wall pass through shifted digits.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses ExceptionalPasses WallInvariant.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored ExceptionalPasses.Exceptional.
Open Scope sym.

Module PhaseE.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dc := [0;0;0;0;1].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].

Fixpoint shifted (bs:list bool) : list sym :=
 match bs with
 | [] => []
 | b::t => (if b then dc else da) ++ shifted t
 end.

Fixpoint normal (bs:list bool) : list sym :=
 match bs with
 | [] => []
 | b::t => (if b then db else da) ++ normal t
 end.

Fixpoint lag (b:bool) (bs:list bool) : list bool :=
 match bs with [] => [] | c::t => b::lag c t end.

Fixpoint finalbit (b:bool) (bs:list bool) : bool :=
 match bs with [] => b | c::t => finalbit c t end.

Definition xp (n:nat) (b:bool) : list (DH0*DH0) := x ++ p^^(2^n-2+(if b then 1 else 0)).

Open Scope nat.

Lemma normal_app a b : normal (a++b) = normal a ++ normal b.
Proof.
 induction a; cbn; [reflexivity|].
 rewrite IHa, app_assoc; reflexivity.
Qed.

Lemma lag_final b bs : lag b bs ++ [finalbit b bs] = b::bs.
Proof.
 gen b. induction bs; intros; cbn; [reflexivity|].
 rewrite IHbs; reflexivity.
Qed.

Lemma digit_shift n previous bit :
 n<>0 ->
 segRLs mtm (xp (S n) previous) (xp n bit)
   (if bit then dc else da) (if previous then db else da).
Proof.
 intro Hn.
 assert (Hpow: 2 <= 2^n).
 { destruct n; [lia|]. cbn [Nat.pow].
   pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia. }
 unfold xp.
 destruct previous, bit; cbn [Nat.pow].
 - applys_eq (exception_shifted_odd (2^n-1)); flia.
 - applys_eq (exception_odd (2^n-2)); flia.
 - applys_eq (exception_shifted_even (2^n-1)); flia.
 - applys_eq (exception_even (2^n-2)); flia.
Qed.

Lemma digits_shift n previous bs :
 n<>0 ->
 segRLs mtm (xp (length bs+n) previous) (xp n (finalbit previous bs))
   (shifted bs) (normal (lag previous bs)).
Proof.
 gen previous.
 induction bs; intros; cbn [length shifted normal lag finalbit].
 - apply segRLs_nil.
 - eapply segRLs_concat.
   + apply digit_shift. change (length bs+n<>0). lia.
   + apply IHbs; exact H.
Qed.

Lemma exception_blank : sideRLs mtm x 0inf (dc *> 0inf).
Proof. esc. Qed.

Lemma flush_zeros n :
 sideRLs mtm (xp (n+1) false) 0inf (da^^n *> dc *> 0inf).
Proof.
 unfold xp.
 replace (2^(n+1)-2+0) with ((0+2)*2^n-2) by
   (rewrite Nat.pow_add_r; cbn; lia).
 replace 0inf with (da^^n *> 0inf) at 1 by
   (rewrite lpow_all0 by solve_const0_eq; reflexivity).
 eapply @segRLs_sideRLs_concat with (w1:=da^^n) (ls2:=x).
 - apply exception_zeros.
 - apply exception_blank.
Qed.

Lemma flush n b :
 sideRLs mtm (xp (n+2) b) 0inf ((if b then db else da) *> da^^n *> dc *> 0inf).
Proof.
 replace (n+2) with (S (n+1)) by lia.
 replace 0inf with (da *> 0inf) at 1 by (st; reflexivity).
 eapply @segRLs_sideRLs_concat with (w1:=da) (ls2:=xp (n+1) false).
 - apply digit_shift; lia.
 - apply flush_zeros.
Qed.

Lemma normal_lag b bs :
 normal (lag b bs) ++ (if finalbit b bs then db else da) =
 (if b then db else da) ++ normal bs.
Proof.
 replace (if finalbit b bs then db else da) with
   (normal [finalbit b bs]) by (cbn [normal]; rewrite app_nil_r; reflexivity).
 rewrite <-normal_app, lag_final. reflexivity.
Qed.

Lemma digits_flush n previous bs :
 sideRLs mtm (xp (length bs+n+2) previous) (shifted bs *> 0inf)
   ((if previous then db else da) *> normal bs *> da^^n *> dc *> 0inf).
Proof.
 replace (length bs+n+2) with (length bs+(n+2)) by lia.
 rewrite <-Str_app_assoc.
 rewrite <-normal_lag, Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply digits_shift; lia.
 - apply flush.
Qed.

Lemma shifted_suffix u bs n :
 sideRLs mtm (p^^(2^(u+length bs+n+3)))
   (da^^u *> dc *> shifted bs *> 0inf)
   (da^^(u+1) *> db *> normal bs *> da^^n *> dc *> 0inf).
Proof.

 replace (da^^(u+1)) with (da^^u ++ da) by
   (rewrite lpow_add; cbn [lpow]; rewrite app_nil_r; reflexivity).
 rewrite Str_app_assoc.
 eapply @segRLs_sideRLs_concat with (ls2:=p^^(2^(length bs+n+3))).
 - applys_eq (d0s_Incs (2^(length bs+n+3)) u).
   repeat rewrite Nat.pow_add_r. flia.

 - eapply @segRLs_sideRLs_concat with (ls2:=xp (length bs+n+2) true).
   + unfold xp.
     assert (Hpow: 2<=2^(length bs+n+2)).
     { rewrite Nat.pow_add_r. cbn [Nat.pow].
       pose proof (Nat.pow_nonzero 2 (length bs+n) ltac:(lia)); nia. }

     replace (length bs+n+3) with (S (length bs+n+2)) by lia.
     cbn [Nat.pow].
     applys_eq (shifted_even (2^(length bs+n+2)-1)); flia.
   + apply digits_flush.
Qed.

Open Scope sym.

Lemma even_wall u bs n :
 let k := u+length bs+n+3 in
 (0inf <* <[1;1]) <* [0] {{A}}> ([1;1]^^k *> da^^u *> dc *> shifted bs *> 0inf)
 -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}> ([1] *> [1;1]^^k *> da^^(u+1) *> db *> normal bs *> da^^n *> dc *> 0inf).
Proof.
 cbn zeta.
 apply BigStep.
 eapply segRLs_sideRLs_concat.
 - apply lds_Incs'.
 - rewrite Nat.mul_1_l. apply shifted_suffix.
Qed.

Module W := WallInvariant.WallInvariant.
Open Scope nat.

Lemma shifted_app a b : shifted (a++b) = shifted a ++ shifted b.
Proof.
 induction a; cbn; [reflexivity|].
 rewrite IHa, app_assoc; reflexivity.
Qed.

Lemma shifted_zeros n : shifted (repeat false n) = da^^n.
Proof. induction n; cbn [repeat shifted lpow]; congruence. Qed.

Lemma normal_zeros n : normal (repeat false n) = da^^n.
Proof. induction n; cbn [repeat normal lpow]; congruence. Qed.

Lemma first_true bs :
 In true bs -> exists u t, bs = repeat false u ++ true::t.
Proof.
 induction bs as [|a bs IH]; intro H.
 - inversion H.
 - destruct a.
   + exists 0, bs. reflexivity.
   + destruct H as [H|H]; [discriminate|].
     destruct (IH H) as [u [t E]].
     exists (S u), t. cbn [repeat]. rewrite E. reflexivity.
Qed.

Definition output_bits n bs := false :: bs ++ repeat false (n-length bs-2).

Lemma phase_E n bs :
 length bs+2 <= n -> In true bs ->
 W.E n bs -[mtm]->+ W.Od n (output_bits n bs).
Proof.

 intros Hlen Hin.
 destruct (first_true bs Hin) as [u [t E]]. subst bs.
 rewrite length_app, repeat_length in Hlen. cbn [length] in Hlen.
 set (padding := n-length (repeat false u ++ true::t)-2).
 assert (Hk:n=u+length t+padding+3).
 { unfold padding. rewrite length_app, repeat_length. cbn [length]. lia. }

 pose proof (even_wall u t padding) as Hrun.
 cbn zeta in Hrun. rewrite <-Hk in Hrun.
 unfold W.E, W.Od, W.wall, output_bits.
 change W.shifted with shifted.
 change W.normal with normal.
 fold padding.
 rewrite shifted_app, shifted_zeros.

 cbn [shifted normal].
 repeat rewrite normal_app.
 repeat rewrite normal_zeros.
 cbn [normal].
 applys_eq Hrun; ut; st; simpl_rotate; reflexivity.
Qed.

Lemma output_length n bs :
 length bs+2<=n -> length (output_bits n bs)+1=n.
Proof.
 intro H. unfold output_bits. cbn [length].
 rewrite length_app, repeat_length. lia.
Qed.

Lemma output_first_zero n bs : W.first_zero (output_bits n bs).
Proof. exists (bs ++ repeat false (n-length bs-2)). reflexivity. Qed.

Lemma output_marked n bs :
 W.marked 1 bs -> W.marked 0 (output_bits n bs).
Proof.
 intros [pre [post [E Hparity]]].
 exists (false::pre), (post ++ repeat false (n-length bs-2)).
 split.
 - unfold output_bits. rewrite E. cbn. rewrite <-app_assoc. reflexivity.
 - cbn [length].
   replace (S (length pre)) with (length pre+1) by lia.
   rewrite Nat.add_mod by lia. rewrite Hparity. reflexivity.
Qed.

Lemma phase_E_invariant n bs :
 length bs+2<=n -> W.marked 1 bs ->
 exists c, W.E n bs -[mtm]->+ c /\ W.invariant c.
Proof.
 intros Hlen Hmark.
 exists (W.Od n (output_bits n bs)). split.
 - apply phase_E; [exact Hlen|].
   destruct Hmark as [pre [post [E Hp]]]. rewrite E.
   apply in_or_app. right. cbn. auto.
 - apply W.InvOd.
   + pose proof (output_length n bs Hlen). lia.
   + apply output_first_zero.
   + apply output_marked; exact Hmark.
Qed.

Print Assumptions digits_shift.
Print Assumptions flush.
Print Assumptions even_wall.
Print Assumptions phase_E_invariant.
End PhaseE.
End PhaseE.

Module PhaseEd.
(* Shifted digits followed by a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape.
Import LocalPasses ExceptionalPasses PhaseE CounterRules.
Import BoundaryRules CounterBatch CounterFinish WallInvariant.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored ExceptionalPasses.Exceptional PhaseE.PhaseE.
Open Scope sym.

Module PhaseEd.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dd := [0;0;0;1;0].
Notation dd1 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].

Fixpoint fuel (bs:list bool) : nat :=
 match bs with
 | [] => 3
 | b::t => 2*fuel t + (if b then 1 else 3)
 end.

Fixpoint value (bs:list bool) : nat :=
 match bs with [] => 0 | b::t => (if b then 1 else 0)+2*value t end.

Open Scope nat.

Lemma defect_carry :
 sideRLs mtm (x ++ p^^3) (dd *> 0inf) (db *> dd1 *> 0inf).
Proof. esc. Qed.

Lemma carried_prefix bs :
 segRLs mtm (x ++ p^^(fuel bs)) (x ++ p^^3) (shifted bs) (db^^(length bs)).
Proof.
 induction bs as [|b bs IH].
 - cbn [fuel shifted length lpow]. apply segRLs_nil.
 - cbn [fuel shifted length lpow].
   eapply segRLs_concat.
   + destruct b.
     * applys_eq (exception_shifted_odd (fuel bs)); flia.
     * apply exception_odd.
   + exact IH.
Qed.

Lemma ordinary_prefix bs :
 In true bs ->
 segRLs mtm (p^^(fuel bs+2)) (x ++ p^^3) (shifted bs) (db^^(length bs)).
Proof.
 induction bs as [|b bs IH]; intro H.
 - inversion H.
 - destruct b; cbn [fuel shifted length lpow].
   + eapply segRLs_concat.
     * applys_eq (shifted_odd (fuel bs)); flia.
     * apply carried_prefix.
   + eapply segRLs_concat.
     * applys_eq (d01_Incs (fuel bs+2)); flia.
     * apply IH. destruct H as [H|H]; [discriminate|exact H].
Qed.

Lemma nonzero_preconversion bs :
 In true bs ->
 sideRLs mtm (p^^(fuel bs+2)) (shifted bs *> dd *> 0inf)
   (db^^(length bs+1) *> dd1 *> 0inf).
Proof.
 intro H.
 replace (db^^(length bs+1)) with (db^^(length bs) ++ db) by
   (rewrite lpow_add; cbn [lpow]; rewrite app_nil_r; reflexivity).
 rewrite Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply ordinary_prefix; exact H.
 - apply defect_carry.
Qed.

Lemma fuel_value bs : fuel bs+2*value bs+3 = 6*2^(length bs).
Proof.
 induction bs as [|b bs IH].
 - reflexivity.
 - destruct b; cbn [fuel value length Nat.pow] in *; nia.
Qed.

Lemma value_bound bs : value bs < 2^(length bs).
Proof.
 induction bs as [|b bs IH].
 - cbn; lia.
 - destruct b; cbn [value length Nat.pow]; nia.
Qed.

Lemma fuel_bound bs : fuel bs+3 <= 6*2^(length bs).
Proof. pose proof (fuel_value bs). lia. Qed.

Lemma fuel_positive bs : 3<=fuel bs.
Proof. induction bs as [|b bs IH]; cbn [fuel]; [lia|destruct b; lia]. Qed.

Lemma fuel_fits n bs : length bs+3<=n -> fuel bs+3 < 2^n.
Proof.
 intro Hn.
 pose proof (fuel_bound bs).
 assert (2^(length bs+3)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in H0.
 cbn [Nat.pow] in H0.
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)). nia.
Qed.

Module CR := CounterRules.CounterRules.
Module BR := BoundaryRules.BoundaryRules.
Module CB := CounterBatch.CounterBatch.
Module CF := CounterFinish.CounterFinish.
Module W := WallInvariant.WallInvariant.
Open Scope sym.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma even_wall_counter n r :
 (0inf <* <[1;1]) <* [0] {{A}}> ([1;1]^^n *> r) -[mtm]->*
 CR.LC n (2^n-1) |> r.
Proof.
 unfold CR.LC. rewrite BinDec_full. esx.
Qed.

Lemma shifted_rank_bound len k s :
 (k<2^len)%nat -> ((k*2+1)*2^s-1 < 2^(len+1+s))%nat.
Proof.
 intro Hk. repeat rewrite Nat.pow_add_r. cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
Qed.

Lemma gap2_even_counter len k a :
 (k<2^len)%nat ->
 CR.LC len k |> db^^(a*2) *> dd1 *> 0inf -[mtm]->+
 CR.LC (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) |> CR.RC 1.
Proof.
 intro Hk.
 unfold CR.LC, CR.RC.
 rewrite BinDec_mulpow2sub1 by (apply shifted_rank_bound; exact Hk).
 rewrite BinInc_1.
 applys_eq (BR.gap2_even (CR.LC len k) 0inf a); ut; st; reflexivity.
Qed.

Lemma gap2_odd_counter len k a :
 (k<2^len)%nat ->
 CR.LC len k |> db^^(a*2+1) *> dd1 *> 0inf -[mtm]->+
 CR.LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> CR.RC 0.
Proof.
 intro Hk.
 unfold CR.LC, CR.RC.
 rewrite BinDec_mulpow2sub1 by (apply shifted_rank_bound; exact Hk).
 rewrite BinInc_O.
 applys_eq (BR.gap2_odd (CR.LC len k) 0inf a); ut; st; reflexivity.
Qed.

Lemma gap2_even_wall len k a :
 (k<2^len)%nat ->
 CR.LC len k |> db^^(a*2) *> dd1 *> 0inf -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1] *> [1;1]^^(len+1+(a*5+1)) *> CR.RC ((k*2+1)*2^(a*5+1)+1)).
Proof.
 intro Hk.
 eapply progress_trans.
 - apply gap2_even_counter; exact Hk.
 - applys_eq (CF.counter_finish (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) 1).
   + pose proof (Nat.pow_nonzero 2 (a*5+1) ltac:(lia)). flia.
   + apply shifted_rank_bound; exact Hk.
Qed.

Lemma gap2_odd_wall len k a :
 (k<2^len)%nat ->
 CR.LC len k |> db^^(a*2+1) *> dd1 *> 0inf -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1] *> [1;1]^^(len+1+(a*5+4)) *> CR.RC ((k*2+1)*2^(a*5+4))).
Proof.
 intro Hk.
 eapply progress_trans.
 - apply gap2_odd_counter; exact Hk.
 - applys_eq (CF.counter_finish (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) 0).
   + pose proof (Nat.pow_nonzero 2 (a*5+4) ltac:(lia)). flia.
   + apply shifted_rank_bound; exact Hk.
Qed.

Lemma nonzero_counter_entry n bs :
 (length bs+3<=n)%nat -> In true bs ->
 W.Ed n bs -[mtm]->*
 CR.LC n (2^n-fuel bs-3) |> db^^(length bs+1) *> dd1 *> 0inf.
Proof.
 intros Hlen Hin.
 pose proof (fuel_fits n bs Hlen) as Hfits.
 unfold W.Ed, W.wall.
 change W.shifted with shifted.
 repeat rewrite Str_app_assoc.
 eapply evstep_trans.
 - apply even_wall_counter.
 - replace (2^n-1)%nat with ((2^n-fuel bs-3)+(fuel bs+2))%nat by lia.
   apply CB.right_pass_batch.
   + lia.
   + apply nonzero_preconversion; exact Hin.
Qed.

Open Scope nat.

Lemma shifted_value_bound len k s :
 k<2^len -> (k*2+1)*2^s < 2^(len+1+s).
Proof.
 intro Hk. repeat rewrite Nat.pow_add_r. cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
Qed.

Lemma remaining_bound n bs :
 length bs+3<=n -> 2^n-fuel bs-3 < 2^n.
Proof.
 intro Hn. pose proof (fuel_fits n bs Hn). lia.
Qed.

Lemma remaining_decomposition n bs :
 length bs+3<=n ->
 exists q, 2^n-fuel bs-3 = (q*2+1)*2^(length bs+1)+2*value bs.
Proof.
 intro Hn.
 pose proof (fuel_value bs) as Hfuel.
 pose proof (fuel_fits n bs Hn) as Hfits.
 set (d:=n-length bs-2).
 assert (Hd:0<d) by (unfold d; lia).
 assert (He:n=length bs+2+d) by (unfold d; lia).
 assert (Hp:2<=2^d).
 { destruct d; [lia|]. cbn [Nat.pow].
   pose proof (Nat.pow_nonzero 2 d ltac:(lia)); nia. }
 exists (2^d-2).
 rewrite He at 1.
 repeat rewrite Nat.pow_add_r.
 cbn [Nat.pow].
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)). nia.
Qed.

Lemma remaining_lower_bound n bs :
 length bs+3<=n -> 0 < 2^n-fuel bs-3.
Proof.
 intro Hn.
 destruct (remaining_decomposition n bs Hn) as [q E].
 rewrite E. pose proof (Nat.pow_nonzero 2 (length bs+1) ltac:(lia)). nia.
Qed.

Print Assumptions nonzero_preconversion.
Print Assumptions fuel_value.
Print Assumptions even_wall_counter.
Print Assumptions gap2_even_wall.
Print Assumptions gap2_odd_wall.
Print Assumptions nonzero_counter_entry.
Print Assumptions remaining_decomposition.
End PhaseEd.
End PhaseEd.

Module EdEvenOrbit.
(* Two wall steps from an even wall with a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2.
Import PhaseEd OddImage CounterBits CounterFinish CounterRules.
Import MarkerArithmetic WallInvariant CDPasses.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdEvenOrbit.
Module PE := PhaseEd.PhaseEd.
Module OI := OddImage.OddImage.
Module CD := CDPasses.CDPasses.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module MA := MarkerArithmetic.MarkerArithmetic.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.
Open Scope nat.

Lemma first_mass_bounds n v width k :
 0<v -> v*2+2<=n -> width<=n -> k<2^width ->
 2^width<=OI.first_mass n v /\
 OI.first_mass n v+k<2^(n+v*5+1).
Proof.

 intros Hv Hn Hw Hk.
 destruct (OI.first_fuel_bounds n (v*2) ltac:(lia)) as [He Hf].
 assert (Hscale:2^(v*2)*4<=2^n).
 { pose proof (Nat.pow_le_mono_r 2 (v*2+2) n ltac:(lia) Hn) as H.
   rewrite Nat.pow_add_r in H. cbn [Nat.pow] in H. exact H. }
 assert (Hpositive:0<2^(v*2)).
 { pose proof (Nat.pow_nonzero 2 (v*2) ltac:(lia)); lia. }
 assert (Hbase:2^n<=2*OI.first_fuel n (v*2)+1) by nia.
 assert (Hpow:0<2^(v*5-1)).
 { pose proof (Nat.pow_nonzero 2 (v*5-1) ltac:(lia)); lia. }
 assert (Hwidth:2^width<=2^n) by (apply Nat.pow_le_mono_r; lia).

 split.
 - unfold OI.first_mass. nia.
 - pose proof (PE.shifted_value_bound n (OI.first_fuel n (v*2)) (v*5-1) Hf) as Hb.
   replace (n+1+(v*5-1)) with (n+v*5) in Hb by lia.
   unfold OI.first_mass.
   assert (Hsmall:2^n<=2^(n+v*5)) by (apply Nat.pow_le_mono_r; lia).
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

Lemma any_true bs : In true bs -> CD.any bs=true.
Proof.
 induction bs as [|b bs IH]; cbn [CD.any]; intro H; [contradiction|].
 destruct b; [reflexivity|]. apply IH. destruct H as [H|H]; [discriminate|exact H].
Qed.

Open Scope sym.
Notation ld := [1;1].
Notation da := [0;0;0;0;0].

Lemma normal_shift_odd width k u : (k<2^width)%nat ->
 W.normal (repeat false u++true::CF.digits width k) *> 0inf =
 CR.RC ((k*2+1)*2^u).
Proof.
 intro Hk. rewrite OI.normal_app,OI.normal_zeros.
 cbn [W.normal]. repeat rewrite Str_app_assoc.
 rewrite CF.digits_normal by exact Hk.
 unfold CR.RC. rewrite BinInc_mulpow2,BinInc_mul2add1. reflexivity.
Qed.

Lemma even_image_marker n v width k i q r :
 (0<v)%nat -> (v*2+2<=n)%nat -> (width<=n)%nat -> (k<2^width)%nat ->
 (i<v*5-1)%nat -> (i mod 2=1)%nat -> (r<2^i)%nat ->
 (k=(q*2+1)*2^i+r)%nat ->
 exists out,
 (length out+2<=n+v*5+2)%nat /\ W.marked 1 out /\
 W.O n (repeat false (v*2)++true::CF.digits width k) -[mtm]->+
 W.Ed (n+v*5+2) out.
Proof.

 intros Hv Hn Hw Hk Hi Hodd Hr Hdecomp.
 destruct (first_mass_bounds n v width k Hv Hn Hw Hk) as [Hmin Hmax].
 assert (Hlength:(width+(n+v*5+1-width)=n+v*5+1)%nat) by lia.
 assert (Hvalue:CD.value (CF.digits width k)=k).
 { change (CB.value (CF.digits width k)=k). apply CB.digits_value; exact Hk. }
 assert (Hmin':(2^length (CF.digits width k)<=OI.first_mass n v)%nat).
 { rewrite CF.digits_length. exact Hmin. }
 assert (Hmax':(OI.first_mass n v+CD.value (CF.digits width k)<
   2^(length (CF.digits width k)+(n+v*5+1-width)))%nat).
 { rewrite CF.digits_length,Hvalue,Hlength. exact Hmax. }

 destruct (OI.initial_even_image n v (CF.digits width k)
   (n+v*5+1-width) Hv ltac:(lia) Hmin' Hmax')
   as [out [Hlen [Hval Hrun]]].
 rewrite CF.digits_length,Hlength in Hlen.
 rewrite Hvalue in Hval.
 assert (Hnonzero:(k<>0)%nat).
 { pose proof (Nat.pow_nonzero 2 i ltac:(lia)). nia. }
 assert (Hany:CD.any (CF.digits width k)=true).
 { apply any_true. apply CB.value_nonzero. rewrite CB.digits_value by exact Hk.
   exact Hnonzero. }
 rewrite Hany in Hrun. cbn [CD.terminal] in Hrun.

 exists out. split; [lia|]. split.
 - rewrite <-Hodd.
   apply (MA.low_marker_preserved out k i q r (v*5-1)
     (2*OI.first_fuel n (v*2)+1)); try lia.
   change (CB.value out+2^length out=OI.first_mass n v+k)%nat in Hval.
   exact Hval.
 - exact Hrun.
Qed.

Lemma Ed_even_valuation_image n bs b :
 (length bs=4*b)%nat -> (length bs+3<=n)%nat -> In true bs ->
 exists out,
 (length out+2<=n+35*b+17)%nat /\ W.marked 1 out /\
 W.Ed n bs -[mtm]->+ W.Ed (n+35*b+17) out.
Proof.

 intros Hlength Hn Hin.
 set (k:=(2^n-PE.fuel bs-3)%nat).
 assert (Hk:(k<2^n)%nat) by (unfold k; apply PE.remaining_bound; exact Hn).
 destruct (PE.remaining_decomposition n bs Hn) as [q Hdecomp].
 fold k in Hdecomp. rewrite Hlength in Hdecomp.
 pose proof (PE.value_bound bs) as Hsmall. rewrite Hlength in Hsmall.
 assert (Hr:(2*PE.value bs<2^(4*b+1))%nat).
 { rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }

 destruct (even_image_marker (n+10*b+5) (5*b+2) n k (4*b+1) q
   (2*PE.value bs) ltac:(lia) ltac:(lia) ltac:(lia) Hk ltac:(lia)
   ltac:(rewrite Nat.add_mod, Nat.mul_mod by lia; reflexivity) Hr Hdecomp)
   as [out [Hlen [Hmark Hrun]]].
 replace (n+10*b+5+(5*b+2)*5+2)%nat with (n+35*b+17)%nat in * by lia.
 exists out. split; [exact Hlen|]. split; [exact Hmark|].
 eapply progress_trans; [|exact Hrun].

 pose proof (PE.nonzero_counter_entry n bs Hn Hin) as Hentry.
 fold k in Hentry.
 replace (length bs+1)%nat with ((b*2)*2+1)%nat in Hentry by lia.
 pose proof (PE.gap2_odd_wall n k (b*2) Hk) as Hwall.

 assert (Hstart:W.Ed n bs -[mtm]->+
   (0inf <* <[1;1]) <* [0] {{A}}>
     ([1] *> ld^^(n+10*b+5) *> CR.RC ((k*2+1)*2^((5*b+2)*2)))).
 { replace (n+10*b+5)%nat with (n+1+((b*2)*5+4))%nat by lia.
   replace ((5*b+2)*2)%nat with ((b*2)*5+4)%nat by lia.
   eapply evstep_progress_trans; eassumption. }
 unfold W.O,W.wall.
 repeat rewrite Str_app_assoc.
 rewrite normal_shift_odd by exact Hk.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.

Print Assumptions first_mass_bounds.
Print Assumptions even_image_marker.
Print Assumptions Ed_even_valuation_image.
End EdEvenOrbit.
End EdEvenOrbit.

Module EdOddOrbit.
(* Entry into the recursive odd-gap branch from a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2.
Import PhaseEd OddImage OddFuel OddRecursion EdEvenOrbit.
Import CounterBits CounterFinish CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddOrbit.
Module PE := PhaseEd.PhaseEd.
Module OI := OddImage.OddImage.
Module F := OddFuel.OddFuel.
Module R := OddRecursion.OddRecursion.
Module EO := EdEvenOrbit.EdEvenOrbit.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.
Open Scope nat.

Lemma first_fuel_half n u : u+2<=n ->
 2^n<=2*OI.first_fuel n u+1.
Proof.
 intro Hn.
 destruct (OI.first_fuel_bounds n u ltac:(lia)) as [He Hf].
 assert (Hscale:2^u*4<=2^n).
 { pose proof (Nat.pow_le_mono_r 2 (u+2) n ltac:(lia) Hn) as H.
   rewrite Nat.pow_add_r in H. cbn [Nat.pow] in H. exact H. }
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma grown_first_lower n u width z : u+2<=n -> width<=n ->
 2^width-1<=F.grown (OI.first_fuel n u) z.
Proof.
 intros Hn Hw.
 pose proof (first_fuel_half n u Hn).
 assert (2^width<=2^n) by (apply Nat.pow_le_mono_r; lia).
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)).
 unfold F.grown. nia.
Qed.

Lemma deficit_after_prime L k deficit u z :
 k+deficit+1=2^L -> 2^(u+1)-1<=k ->
 F.grown (k-(2^(u+1)-1)) z+
   (2*deficit+2^(u+2)-1)*2^z+1=2^(L+1+z).
Proof.
 intros Hleft Hprime.
 assert (Hp:0<2^(u+1)).
 { pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)); lia. }
 assert (Hz:0<2^z).
 { pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia. }
 assert (Hu:2^(u+2)=2^(u+1)*2).
 { replace (u+2) with ((u+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }
 assert (HL:2^(L+1+z)=2^L*2*2^z).
 { rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia. }
 unfold F.grown. rewrite Hu,HL. nia.
Qed.

Open Scope sym.
Notation ld := [1;1].
Notation z3 := [0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Definition source_rank n bs := (2^n-PE.fuel bs-3)%nat.
Definition initial_width n b := (n+35*b+34)%nat.
Definition initial_rank n b :=
 F.grown (OI.first_fuel (n+10*b+10) (10*b+9)) (25*b+23).

Lemma Ed_odd_valuation_entry n bs b :
 (length bs=4*b+2)%nat -> (length bs+3<=n)%nat -> In true bs ->
 W.Ed n bs -[mtm]->+
 CR.LC (initial_width n b) (initial_rank n b) |>
 z3 *> W.normal (CF.digits n (source_rank n bs)) *> 0inf.
Proof.

 intros Hlength Hn Hin.
 set (k:=source_rank n bs).
 assert (Hk:(k<2^n)%nat).
 { unfold k,source_rank. apply PE.remaining_bound; exact Hn. }
 pose proof (R.initial_odd_entry (n+10*b+10) (5*b+4)
   (CF.digits n k) ltac:(lia)) as Hodd.
 replace ((5*b+4)*2+1)%nat with (10*b+9)%nat in Hodd by lia.
 replace ((5*b+4)*5+3)%nat with (25*b+23)%nat in Hodd by lia.
 replace (n+10*b+10+1+(25*b+23))%nat with (initial_width n b) in Hodd by
   (unfold initial_width; lia).
 fold (initial_rank n b) in Hodd.
 eapply progress_trans; [|exact Hodd].

 pose proof (PE.nonzero_counter_entry n bs Hn Hin) as Hentry.
 change (2^n-PE.fuel bs-3)%nat with (source_rank n bs) in Hentry.
 fold k in Hentry.
 replace (length bs+1)%nat with ((b*2+1)*2+1)%nat in Hentry by lia.
 pose proof (PE.gap2_odd_wall n k (b*2+1) Hk) as Hwall.
 assert (Hstart:W.Ed n bs -[mtm]->+
   (0inf <* <[1;1]) <* [0] {{A}}>
     ([1] *> ld^^(n+10*b+10) *> CR.RC ((k*2+1)*2^(10*b+9)))).
 { replace (n+10*b+10)%nat with (n+1+((b*2+1)*5+4))%nat by lia.
   replace (10*b+9)%nat with ((b*2+1)*5+4)%nat by lia.
   eapply evstep_progress_trans; eassumption. }

 unfold W.O,W.wall.
 repeat rewrite Str_app_assoc.
 rewrite EO.normal_shift_odd by exact Hk.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.

Lemma Ed_odd_entry_fuel n bs b :
 (length bs=4*b+2)%nat -> (length bs+3<=n)%nat ->
 (2^length (CF.digits n (source_rank n bs))-1<=initial_rank n b)%nat /\
 (initial_rank n b<2^initial_width n b)%nat /\
 (initial_rank n b mod 2=1)%nat.
Proof.

 intros Hlength Hn.
 rewrite CF.digits_length.
 unfold initial_rank,initial_width.
 split.
 - apply grown_first_lower; lia.
 - split.
   + pose proof (OI.first_fuel_bounds (n+10*b+10) (10*b+9) ltac:(lia)) as [_ Hf].
     pose proof (F.grown_bound (n+10*b+10)
       (OI.first_fuel (n+10*b+10) (10*b+9)) (25*b+23) Hf) as Hbound.
     replace (n+10*b+10+1+(25*b+23))%nat with (n+35*b+34)%nat in Hbound by lia.
     lia.
   + apply R.grown_odd. lia.
Qed.

Lemma source_even_marker n bs :
 (length bs+5<=n)%nat -> (length bs mod 2=0)%nat ->
 W.marked 0 (CF.digits n (source_rank n bs)).
Proof.

 intros Hn Hpar.
 set (m:=length bs).
 set (d:=(n-m-5)%nat).
 assert (He:(n=m+5+d)%nat) by (unfold d,m; lia).
 pose proof (PE.fuel_value bs) as Hfuel.
 pose proof (PE.value_bound bs) as Hvalue.
 pose proof (PE.fuel_fits n bs ltac:(lia)) as Hfits.
 fold m in Hfuel,Hvalue.
 assert (Hp:(0<2^m)%nat).
 { pose proof (Nat.pow_nonzero 2 m ltac:(lia)); lia. }
 assert (Hd:(0<2^d)%nat).
 { pose proof (Nat.pow_nonzero 2 d ltac:(lia)); lia. }
 assert (Hbig:(2^n=2^m*32*2^d)%nat).
 { rewrite He. rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia. }
 assert (Hbit:(2^(m+4)=2^m*16)%nat).
 { rewrite Nat.pow_add_r. reflexivity. }

 pose proof (CB.marked_remainder n (source_rank n bs) (m+4)
   (2^d-1) (10*2^m+2*PE.value bs) ltac:(lia)) as Hmark.
 replace ((m+4) mod 2)%nat with 0%nat in Hmark by
   (rewrite Nat.add_mod by lia; unfold m; rewrite Hpar; reflexivity).
 apply Hmark.
 - rewrite Hbit. nia.
 - unfold source_rank. rewrite Hbig,Hbit in *. nia.
Qed.

Print Assumptions deficit_after_prime.
Print Assumptions Ed_odd_valuation_entry.
Print Assumptions Ed_odd_entry_fuel.
Print Assumptions source_even_marker.
End EdOddOrbit.
End EdOddOrbit.

Module CounterH.
(* Pairing contextual amplifier passes with a finite left counter.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import CounterRules CounterFinish WallInvariant.
Import List PeanoNat Lia.
Import ListNotations CounterRules.CounterRules WallInvariant.WallInvariant.
Open Scope sym.

Module CounterH.
Notation h := [((A,[0]),(C,[0]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).

Lemma left_one len k :
 (1+k<2^len)%nat ->
 sideLR mtm (C,[0]) (A,[0])
   (LC len (1+k) <* [1]) (LC len k <* [1]).
Proof.
 intros Hk r.
 assert (H : (LC len (1+k)<*[1]) <{{C}} [0]*>r -[mtm]->+
   LC len (1+k) <| r) by esx.
 follow10 H. apply progress_evstep, left_counter. exact Hk.
Qed.

Lemma left_one_flip len k :
 (1+k<2^len)%nat ->
 sideRL (flip mtm) (C,[0]) (A,[0])
   (LC len (1+k) <* [1]) (LC len k <* [1]).
Proof.
 intros Hk r. exact (flip_progress mtm _ _ (left_one len k Hk r)).
Qed.

Lemma left_batch len k amount :
 (k+amount<2^len)%nat ->
 sideRLs (flip mtm) ([((C,[0]),(A,[0]))]^^amount)
   (LC len (k+amount)<*[1]) (LC len k<*[1]).
Proof.
 gen k. induction amount; intros k Hk.
 - rewrite Nat.add_0_r. constructor.
 - replace (k+S amount)%nat with (1+(k+amount))%nat by lia.
   cbn[lpow app]. econstructor.
   + apply left_one_flip. lia.
   + apply IHamount. lia.
Qed.

Lemma right_h_batch len k amount r r' :
 (k+amount<2^len)%nat -> sideRLs mtm (h^^amount) r r' ->
 LC len (k+amount) |> r -[mtm]->* LC len k |> r'.
Proof.
 intros Hk Hr.
 exact (sideRLs_concat_1 Hr (left_batch len k amount Hk)).
Qed.

Lemma right_h_finish n k r r' :
 (k<2^n)%nat -> sideRLs mtm (h^^(k+1)) r r' ->
 LC n k |> r -[mtm]->+
 (0inf<*<[1;1])<*[0] {{A}}> ([1]*>[1;1]^^n*>r').
Proof.

 intros Hk Hr. rewrite lpow_add in Hr.
 destruct (sideRLs_split Hr) as [middle [Hfirst Hlast]].
 eapply evstep_progress_trans.
 - replace k with (0+k)%nat at 1 by lia.
   apply right_h_batch; [exact Hk|exact Hfirst].
 - eapply progress_trans.
   + exact (sideRLs_1 _ _ _ _ _ Hlast (LC n 0<*[1])).
   + eapply progress_trans.
     * assert (H : (LC n 0<*[1]) <{{C}} [0]*>r' -[mtm]->+
         LC n 0 <| r') by esx. exact H.
     * apply CounterFinish.CounterFinish.return_wall.
Qed.

Print Assumptions right_h_finish.
End CounterH.
End CounterH.

Module BlankPasses.
(* Exact pass counts on a blank right side.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses CounterRules CounterFinish CounterBits WallInvariant.
Import String List PeanoNat NArith Lia.
Import ListNotations.
Open Scope sym.

Module BlankPasses.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module CR := CounterRules.CounterRules.
Module CF := CounterFinish.CounterFinish.
Module CB := CounterBits.CounterBits.
Module W := WallInvariant.WallInvariant.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation p := [((A,[]),(B,[]))].
Notation x := [((C,[]),(B,[]))].
Notation h := [((A,[0]),(C,[0]))].
Definition shifted_counter n := BinInc c n.

Lemma ordinary_increment l r n:
 l {{A}}> b^^n *> a *> r -[mtm]->+
 l <{{B}} a^^n *> b *> r.
Proof. esx. Qed.
Lemma shifted_increment l r n:
 l {{C}}> c^^n *> a *> r -[mtm]->+
 l <{{B}} a^^n *> c *> r.
Proof. esx. Qed.

Lemma ordinary_step n:
 sideRLs mtm p (CR.RC n) (CR.RC (1+n)).
Proof.

 econstructor.
 2: constructor.
 unfold sideRL. intros l.
 change (l <* [] {{A}}> CR.RC n -[mtm]->+ l <{{B}} [] *> CR.RC (1+n)).
 unfold CR.RC. apply RBinInc_spec.
 intros l0 r0 n0. cbn[Str_app BinaryCounter.d0 length repeat].
 apply ordinary_increment.
Qed.
Lemma shifted_step n:
 sideRLs mtm x (shifted_counter n) (shifted_counter (1+n)).
Proof.

 econstructor.
 2: constructor.
 unfold sideRL. intros l.
 change (l <* [] {{C}}> shifted_counter n -[mtm]->+
   l <{{B}} [] *> shifted_counter (1+n)).
 unfold shifted_counter. apply RBinInc_spec.
 intros l0 r0 n0. cbn[Str_app BinaryCounter.d0 length repeat].
 apply shifted_increment.
Qed.

Open Scope nat.
Lemma ordinary_blank n:
 sideRLs mtm (p^^n) 0inf (CR.RC n).
Proof.

 induction n.
 - change (sideRLs mtm [] 0inf 0inf). constructor.
 - replace (S n) with (n+1) at 1 by lia. rewrite lpow_add.
   replace (S n) with (1+n) by lia.
   eapply sideRLs_trans.
   + exact IHn.
   + apply ordinary_step.
Qed.
Lemma shifted_blank n:
 sideRLs mtm (x^^n) 0inf (shifted_counter n).
Proof.

 induction n.
 - change (sideRLs mtm [] 0inf 0inf). constructor.
 - replace (S n) with (n+1) at 1 by lia. rewrite lpow_add.
   replace (S n) with (1+n) by lia.
   eapply sideRLs_trans.
   + exact IHn.
   + apply shifted_step.
Qed.

Lemma digits_shifted n v:
 v<2^n -> W.shifted (CF.digits n v) *> 0inf=shifted_counter v.
Proof.

 gen v. induction n; intros v Hv.
 - cbn in Hv. assert (v=0) by lia. subst. reflexivity.
 - destruct (mod2 v); subst.
   + rewrite CF.digits_even. cbn[W.shifted].
     rewrite Str_app_assoc,IHn by (cbn in Hv; lia).
     unfold shifted_counter. rewrite BinInc_mul2. reflexivity.
   + rewrite Nat.add_comm,CF.digits_odd. cbn[W.shifted].
     rewrite Str_app_assoc,IHn by (cbn in Hv; lia).
     unfold shifted_counter. rewrite BinInc_mul2add1. reflexivity.
Qed.
Lemma shifted_counter_rotate n v:
 v<2^n -> shifted_counter v=([0;0;0;0]%sym) *> CR.RC v.
Proof.

 intro H.
 rewrite <- (digits_shifted n v H), <- (CF.digits_normal n v H).
 symmetry. apply CB.shifted_normal.
Qed.

Lemma even_ones k n:
 sideRLs mtm (h^^k) (([1;1]%sym)^^n *> 0inf)
   (([1;1]%sym)^^n *> CR.RC (k*2^n)).
Proof.

 eapply segRLs_sideRLs_concat.
 - apply LocalPasses.Mirrored.lds_Incs'.
 - apply ordinary_blank.
Qed.

Print Assumptions ordinary_blank.
Print Assumptions shifted_blank.
Print Assumptions shifted_counter_rotate.
Print Assumptions even_ones.
End BlankPasses.
End BlankPasses.

Module EndpointClasses.
(* Classifying the numeric endpoints of the two terminal conversions.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses CounterH CounterRules CounterFinish CounterBits.
Import BlankPasses WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module EndpointClasses.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module CH := CounterH.CounterH.
Module CR := CounterRules.CounterRules.
Module CF := CounterFinish.CounterFinish.
Module CB := CounterBits.CounterBits.
Module BP := BlankPasses.BlankPasses.
Module W := WallInvariant.WallInvariant.
Notation one := [1].
Notation ld := [1;1].
Notation z := [0].
Notation lh := (0inf<*<[1;1]).
Notation h := [((A,[0]),(C,[0]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma coefficient_bound L T q :
 0<T -> 2*(T+q)<=2^L -> q*4+3<2^(L+1).
Proof. intros. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. Qed.

Lemma budget_positive L T q :
 0<T -> 2*(T+q)<=2^L -> 0<L.
Proof. intros. destruct L; [cbn in *; lia|lia]. Qed.

Lemma adjacent_marked n q s :
 s+1<n -> W.marked 1 (CF.digits n ((q*4+3)*2^s)).
Proof.

 intro Hn.
 destruct (Nat.eq_dec (s mod 2) 1) as [Hs|Hs].
 - replace (q*4+3) with ((q*2+1)*2+1) by lia.
   apply CB.marked_shift_odd; lia.
 - assert (H0:s mod 2=0) by
    (pose proof (Nat.mod_upper_bound s 2 ltac:(lia)); lia).
   assert (H1:(s+1) mod 2=1).
   { rewrite Nat.add_mod by lia. rewrite H0. reflexivity. }
   rewrite <-H1 at 1.
   apply (CB.marked_remainder n ((q*4+3)*2^s) (s+1) q (2^s)).
   + exact Hn.
   + rewrite Nat.pow_add_r. cbn[Nat.pow].
     pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.

   + rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
Qed.

Lemma numeric_bound L T q s :
 0<T -> 2*(T+q)<=2^L -> (q*4+3)*2^s<2^(L+s+1).
Proof.

 intros HT HB. pose proof (coefficient_bound L T q HT HB).
 replace (L+s+1) with (L+1+s) by lia.
 rewrite Nat.pow_add_r.
 pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
Qed.

Lemma shifted_numeric n v :
 v<2^n -> W.marked 1 (CF.digits n v) ->
 W.invariant (lh<*z {{A}}> (ld^^(n+2) *> BP.shifted_counter v)).
Proof.

 intros Hv Hm. rewrite <- (BP.digits_shifted n v Hv).
 repeat rewrite <-Str_app_assoc.
 change (W.invariant (W.E (n+2) (CF.digits n v))).
 apply W.InvE.
 - rewrite CF.digits_length. lia.
 - exact Hm.
Qed.

Lemma shifted_endpoint L T q s :
 0<T -> 2*(T+q)<=2^L ->
 W.invariant (lh<*z {{A}}>
   (ld^^(L+s+3) *> BP.shifted_counter ((q*4+3)*2^s))).
Proof.

 intros HT HB.
 replace (L+s+3) with ((L+s+1)+2) by lia.
 apply shifted_numeric.
 - apply numeric_bound with (T:=T); assumption.
 - apply adjacent_marked.
   pose proof (budget_positive L T q HT HB). lia.
Qed.

Lemma ordinary_endpoint L T q s :
 0<T -> 0<s -> 2*(T+q)<=2^L ->
 W.invariant (lh<*z {{A}}>
  (one *> ld^^(L+s+1) *> CR.RC ((q*4+3)*2^s))).
Proof.

 intros HT Hs HB.
 apply CB.numeric_even_value.
 - pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia.
 - apply numeric_bound with (T:=T); assumption.
 - destruct s; [lia|].
   cbn[Nat.pow]. replace ((q*4+3)*(2*2^s)) with
    (((q*4+3)*2^s)*2) by nia.
   apply Nat.mod_mul; lia.
Qed.

Lemma even_word L s :
 one++ld^^L++ld++ld^^(s+1)++one=ld^^(L+s+3).
Proof.

 change (one^^1++(one^^2)^^L++one^^2++(one^^2)^^(s+1)++one^^1
  =(one^^2)^^(L+s+3)).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.
Lemma odd_word L s :
 one++ld^^L++ld++ld^^s=one++ld^^(L+s+1).
Proof.

 change (one++ld^^L++ld^^1++ld^^s=one++ld^^(L+s+1)).
 repeat rewrite <-lpow_add. f_equal. f_equal. lia.
Qed.

Lemma counter_shifted L k T q s r :
 k<2^L -> k+1=2*(T+q) -> 0<T ->
 sideRLs mtm (h^^(k+1)) r
  (ld *> ld^^(s+1) *> one *> BP.shifted_counter ((q*4+3)*2^s)) ->
 exists out, CR.LC L k |> r -[mtm]->+ out /\ W.invariant out.
Proof.

 intros Hk HE HT Hr.
 exists (lh<*z {{A}}> (ld^^(L+s+3) *> BP.shifted_counter ((q*4+3)*2^s))).
 split.
 - pose proof (CH.right_h_finish L k r _ Hk Hr) as H.
   repeat rewrite <-Str_app_assoc in H.
   rewrite <-app_assoc,<-app_assoc,<-app_assoc,even_word in H.
   exact H.
 - apply shifted_endpoint with (T:=T); [exact HT|lia].
Qed.

Lemma counter_ordinary L k T q s r :
 k<2^L -> k+1=2*(T+q) -> 0<T -> 0<s ->
 sideRLs mtm (h^^(k+1)) r
  (ld *> ld^^s *> CR.RC ((q*4+3)*2^s)) ->
 exists out, CR.LC L k |> r -[mtm]->+ out /\ W.invariant out.
Proof.

 intros Hk HE HT Hs Hr.
 exists (lh<*z {{A}}> (one *> ld^^(L+s+1) *> CR.RC ((q*4+3)*2^s))).
 split.
 - pose proof (CH.right_h_finish L k r _ Hk Hr) as H.
   repeat rewrite <-Str_app_assoc in H.
   rewrite <-app_assoc,<-app_assoc,odd_word,Str_app_assoc in H.
   exact H.
 - apply ordinary_endpoint with (T:=T); [exact HT|exact Hs|lia].
Qed.

Print Assumptions adjacent_marked.
Print Assumptions shifted_endpoint.
Print Assumptions ordinary_endpoint.
Print Assumptions counter_shifted.
Print Assumptions counter_ordinary.
End EndpointClasses.
End EndpointClasses.

Module OddDefectTail.
(* Terminal conversion of the odd defective wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses BoundaryRules CDPasses OddNormal.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module OddDefectTail.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module CD := CDPasses.CDPasses.
Module BR := BoundaryRules.BoundaryRules.
Notation a := [0;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].
Notation hx := [((C,[]),(C,[0]))].
Notation terminal_word := [0;0;0;0;0;0;0;1].
Notation q2 := [0;0;1].
Notation ones5 := [1;1;1;1;1].
Notation one := [1].
Notation ld := [1;1].
Notation three := [1;1;1].
Open Scope nat.

Lemma value_zero bs :
 CD.value bs=0 -> bs=repeat false (length bs).
Proof.

 induction bs as [|b bs IH]; intro H; cbn[length repeat]; [reflexivity|].
 destruct b; cbn[CD.value CD.bitval] in H; [lia|].
 f_equal. apply IH. lia.
Qed.
Lemma value_full bs :
 CD.value bs=2^length bs-1 -> bs=repeat true (length bs).
Proof.

 induction bs as [|b bs IH]; intro H; cbn[length repeat]; [reflexivity|].
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)).
 destruct b; cbn[CD.value CD.bitval length Nat.pow] in H.
 - f_equal. apply IH. nia.
 - lia.
Qed.
Lemma value_positive_any bs :
 0<CD.value bs -> CD.any bs=true.
Proof.

 induction bs as [|b bs IH]; intro H; cbn[CD.value CD.bitval] in H; [lia|].
 destruct b; cbn[CD.any CD.bitval] in *; [reflexivity|].
 apply IH. nia.
Qed.
Lemma third_zeros n : CD.third (repeat false n)=a^^n.
Proof. induction n; [reflexivity|]. change (a++CD.third(repeat false n)=a++a^^n). now rewrite IHn. Qed.
Lemma fourth_ones n : CD.fourth (repeat true n)=c^^n.
Proof. induction n; [reflexivity|]. change (c++CD.fourth(repeat true n)=c++c^^n). now rewrite IHn. Qed.

Lemma tail_five:
 sideRLs mtm (CD.mass true 5) (terminal_word *> 0inf)
   (c^^2 *> q2 *> 0inf).
Proof. unfold CD.mass. cbn[lpow]. esc. Qed.

Lemma prime_positive bs :
 0<CD.value bs ->
 sideRLs mtm (x^^(6*2^length bs-CD.value bs-1))
  (CD.third bs *> terminal_word *> 0inf)
  (c^^(length bs+2) *> q2 *> 0inf).
Proof.

 intro Hvpos.
 pose proof (CD.value_bound bs) as Hvbound.
 assert (Hp:0<2^length bs).
 { pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); lia. }
 assert (Hn:2^length bs<=6*2^length bs-CD.value bs-1) by nia.
 destruct (CD.mass_digits bs false (6*2^length bs-CD.value bs-1) Hn)
  as [low [carry [Hlen [Hval [Hcarry Hseg]]]]].
 pose proof (CD.value_bound low) as Hlowbound.
 rewrite Hlen in Hlowbound.
 assert (Hfive:carry=5) by nia. subst carry.
 assert (Hfull:CD.value low=2^length low-1) by (rewrite Hlen; nia).

 apply value_full in Hfull.
 rewrite Hfull,Hlen,fourth_ones in Hseg.
 unfold CD.mass at 1 in Hseg.
 rewrite Bool.orb_false_l,value_positive_any in Hseg by exact Hvpos.
 rewrite lpow_add,Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - exact Hseg.
 - apply tail_five.
Qed.

Lemma prime_zero bs :
 CD.value bs=0 ->
 sideRLs mtm (x^^(2^(length bs+1)-1))
  (CD.third bs *> terminal_word *> 0inf)
  (c^^(length bs+1) *> q2 *> 0inf).
Proof.

 intro Hv.
 pose proof (value_zero bs Hv) as E.
 assert (Ht:CD.third bs=a^^length bs).
 { rewrite E,third_zeros,repeat_length. reflexivity. }
 rewrite Ht.
 replace (terminal_word *> 0inf) with (a *> q2 *> 0inf) by reflexivity.
 rewrite <-Str_app_assoc.
 replace (a^^length bs++a) with (a^^(length bs+1)) by
  (rewrite lpow_add; cbn[lpow]; rewrite app_nil_r; reflexivity).
 eapply @segRLs_sideRLs_concat with (ls2:=[]).
 - pose proof (BR.c_fill_zeros 0 (length bs+1)) as H.
   cbn[Nat.add Nat.mul lpow] in H. rewrite Nat.add_0_r in H.

   rewrite lpow_add in H. cbn[lpow] in H. rewrite app_nil_r in H. exact H.
 - constructor.
Qed.

Lemma final_x:
 sideRLs mtm hx (q2 *> 0inf) (three *> 0inf).
Proof. esc. Qed.
Lemma convert_tail g:
 sideRLs mtm hx (c^^g *> q2 *> 0inf)
  (ones5^^g *> three *> 0inf).
Proof.

 eapply segRLs_sideRLs_concat.
 - apply BR.conversion_digits.
 - apply final_x.
Qed.

Lemma positive_exit bs :
 0<CD.value bs ->
 sideRLs mtm (x^^(6*2^length bs-CD.value bs-1)++hx)
  (CD.third bs *> terminal_word *> 0inf)
  (ones5^^(length bs+2) *> three *> 0inf).
Proof.

 intro H. eapply sideRLs_trans.
 - apply prime_positive; exact H.
 - apply convert_tail.
Qed.
Lemma zero_exit bs :
 CD.value bs=0 ->
 sideRLs mtm (x^^(2^(length bs+1)-1)++hx)
  (CD.third bs *> terminal_word *> 0inf)
  (ones5^^(length bs+1) *> three *> 0inf).
Proof.

 intro H. eapply sideRLs_trans.
 - apply prime_zero; exact H.
 - apply convert_tail.
Qed.

Definition demand bs :=
 if Nat.eqb (CD.value bs) 0 then 2^(length bs+1)
 else 6*2^length bs-CD.value bs.
Definition converted_digits bs :=
 if Nat.eqb (CD.value bs) 0 then length bs+1 else length bs+2.

Lemma prime bs :
 sideRLs mtm (x^^(demand bs-1))
  (CD.third bs *> terminal_word *> 0inf)
  (c^^converted_digits bs *> q2 *> 0inf).
Proof.

 unfold demand,converted_digits.
 destruct (Nat.eqb_spec (CD.value bs) 0).
 - apply prime_zero; exact e.
 - apply prime_positive; lia.
Qed.

Notation h := [((A,[0]%sym),(C,[0]%sym))].
Lemma odd_terminal_reduction bs q r' :
 sideRLs mtm (h^^(1+q*2))
  (ones5^^converted_digits bs *> three *> 0inf) r' ->
 sideRLs mtm (h^^((demand bs-1)*2+(1+q)))
  (one *> CD.third bs *> terminal_word *> 0inf) (ld *> r').
Proof.

 intro H. rewrite lpow_add.
 eapply @sideRLs_trans with
   (r2:=one *> c^^converted_digits bs *> q2 *> 0inf).
 - eapply segRLs_sideRLs_concat.
   + apply OddNormal.OddNormal.one_pairs.
   + apply prime.
 - eapply segRLs_sideRLs_concat.
   + apply OddNormal.OddNormal.one_expand.
   + eapply sideRLs_trans.
     * apply convert_tail.
     * exact H.
Qed.

Print Assumptions prime_positive.
Print Assumptions prime_zero.
Print Assumptions positive_exit.
Print Assumptions zero_exit.
Print Assumptions odd_terminal_reduction.
End OddDefectTail.
End OddDefectTail.

Module OddDefectFinish.
(* Numeric endpoints of the defective terminal conversion.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses OddNormal OddDefectTail BlankPasses CDPasses CounterRules WallInvariant.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module OddDefectFinish.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module T := OddDefectTail.OddDefectTail.
Module BP := BlankPasses.BlankPasses.
Module CD := CDPasses.CDPasses.
Module CR := CounterRules.CounterRules.
Module W := WallInvariant.WallInvariant.
Notation a := [0;0;0;0;0].
Notation b := [1;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation z3 := [0;0;0].
Notation one := [1].
Notation ld := [1;1].
Notation three := [1;1;1].
Notation ones5 := [1;1;1;1;1].
Notation terminal_word := [0;0;0;0;0;0;0;1].
Notation h := [((A,[0]),(C,[0]))].
Notation x := [((C,[]),(B,[]))].
Open Scope nat.

Lemma demand_positive bs : 0<T.demand bs.
Proof.
 unfold T.demand.
 pose proof (CD.value_bound bs).
 pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)).
 destruct (Nat.eqb (CD.value bs) 0).
 - rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
 - nia.
Qed.

Lemma ones_even w :
 ones5^^(w*2)++three = ld^^(w*5+1)++one.
Proof.
 change ((one^^5)^^(w*2)++one^^3 = (one^^2)^^(w*5+1)++one^^1).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.
Lemma ones_odd w :
 ones5^^(w*2+1)++three = ld^^(w*5+4).
Proof.
 change ((one^^5)^^(w*2+1)++one^^3 = (one^^2)^^(w*5+4)).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma odd_ones k n :
 sideRLs mtm (h^^k) (ld^^(n+1) *> one *> 0inf)
  (ld^^(n+1) *> one *> BP.shifted_counter (k*2^n)).
Proof.
 eapply segRLs_sideRLs_concat.
 - apply LocalPasses.Mirrored.lds_Incs.
 - replace (k*2^(n+1)) with ((k*2^n)*2) by
    (rewrite Nat.pow_add_r; cbn[Nat.pow]; nia).
   eapply segRLs_sideRLs_concat.
   + apply OddNormal.OddNormal.one_pairs.
   + apply BP.shifted_blank.
Qed.

Lemma finish_even bs w q :
 T.converted_digits bs=w*2 ->
 sideRLs mtm (h^^(2*(T.demand bs+q)))
   (one *> CD.third bs *> terminal_word *> 0inf)
   (ld *> ld^^(w*5+1) *> one *>
      BP.shifted_counter ((q*4+3)*2^(w*5))).
Proof.
 intro Hg.
 pose proof (demand_positive bs).
 replace (2*(T.demand bs+q)) with
   ((T.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply T.odd_terminal_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_even,Str_app_assoc.
 apply odd_ones.
Qed.

Lemma finish_odd bs w q :
 T.converted_digits bs=w*2+1 ->
 sideRLs mtm (h^^(2*(T.demand bs+q)))
   (one *> CD.third bs *> terminal_word *> 0inf)
   (ld *> ld^^(w*5+4) *> CR.RC ((q*4+3)*2^(w*5+4))).
Proof.
 intro Hg.
 pose proof (demand_positive bs).
 replace (2*(T.demand bs+q)) with
   ((T.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply T.odd_terminal_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_odd.
 apply BP.even_ones.
Qed.


Lemma third_normal bs : z3++W.normal bs=CD.third bs++z3.
Proof.
 induction bs as [|b bs IH]; [reflexivity|].
 destruct b; cbn[W.normal CD.third CD.third_digit app] in *;
 rewrite <-IH; reflexivity.
Qed.
Lemma third_normal_side bs :
 z3 *> W.normal bs *> c *> 0inf=CD.third bs *> terminal_word *> 0inf.
Proof.
 rewrite <-Str_app_assoc,third_normal,Str_app_assoc. reflexivity.
Qed.
Lemma prefix_even u : one^^(5*(u*2)+1)=ld^^(u*5)++one.
Proof.
 change (one^^(5*(u*2)+1)=(one^^2)^^(u*5)++one^^1).
 rewrite <-lpow_mul,<-lpow_add. f_equal. lia.
Qed.

Lemma first_even_reduction u k bs r' :
 sideRLs mtm (h^^((1+k*2)*2^(u*5)))
   (one *> CD.third bs *> terminal_word *> 0inf) r' ->
 sideRLs mtm (h^^((2^(u*2)-1)*2+(1+k)))
   (one *> a^^(u*2) *> b *> W.normal bs *> c *> 0inf)
   (ld *> ld^^(u*5) *> r').
Proof.
 intro H. apply OddNormal.OddNormal.odd_first_reduction.
 rewrite prefix_even,Str_app_assoc,third_normal_side.
 eapply segRLs_sideRLs_concat.
 - apply LocalPasses.Mirrored.lds_Incs.
 - exact H.
Qed.

Print Assumptions first_even_reduction.

Print Assumptions finish_even.
Print Assumptions finish_odd.
End OddDefectFinish.
End OddDefectFinish.

Module TightTail.
(* The terminal conversion in a tight displaced-digit wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses BoundaryRules.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TightTail.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation tail := [0;0;0;1;0;0;1;0].
Notation ones := [1;1;1;1;1;1;1].
Notation xp := [((C,[]),(C,[0]))].
Notation yp := [((D,[]),(C,[0]))].

Lemma terminal_C : segRLs mtm xp [] tail ones.
Proof.
 apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Qed.

Lemma terminal_D : segRLs mtm yp [] tail ones.
Proof.
 apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.
Qed.

Print Assumptions terminal_C.
Print Assumptions terminal_D.
End TightTail.
End TightTail.

Module TightPrimer.
(* First special return at the terminal of a tight displaced-digit wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses CDPasses BoundaryRules TightTail OddNormal.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TightPrimer.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module CD := CDPasses.CDPasses.
Notation a := [0;0;0;0;0].
Notation c := [0;0;0;0;1].
Notation d := [0;0;0;1;0].
Notation one := [1].
Notation ld := [1;1].
Notation ones5 := [1;1;1;1;1].
Notation ones7 := [1;1;1;1;1;1;1].
Notation tail := [0;0;0;1;0;0;1;0].
Notation x := [((C,[]),(B,[]))].
Notation y := [((D,[]),(B,[]))].
Notation hx := [((C,[]),(C,[0]))].
Notation hy := [((D,[]),(C,[0]))].
Notation h := [((A,[0]),(C,[0]))].

Definition special (old:bool) : list (DH0*DH0) := if old then hy else hx.
Definition departure (old:bool) (n:nat) : list (DH0*DH0) :=
 match n with
 | O => special old
 | S k => (if old then y else x) ++ x^^k ++ hx
 end.
Open Scope nat.

Lemma departure_positive old n : n<>0 ->
 departure old n=CD.mass old n++hx.
Proof. destruct n; [lia|]. intro H. destruct old; cbn[departure CD.mass Nat.sub lpow]; rewrite ?Nat.sub_0_r; reflexivity. Qed.
Lemma departure_false n : departure false n=x^^n++hx.
Proof. destruct n; reflexivity. Qed.

Lemma conversion_digit : segRLs mtm hx hx c ones5.
Proof. esc. Qed.

Lemma digit_exit k old bit :
 segRLs mtm (departure old ((k+1)*2-CD.bitval bit-1))
   (departure (orb old bit) k) (CD.third_digit bit) ones5.
Proof.

 destruct k as [|k].
 - destruct old,bit; cbn[departure special CD.bitval CD.third_digit orb lpow]; esc.
 - rewrite departure_positive by
    (destruct bit; cbn[CD.bitval]; lia).
   rewrite departure_positive by lia.
   eapply segRLs_trans.
   2: apply conversion_digit.
   destruct bit.
   + cbn[CD.bitval CD.third_digit orb].
     replace ((S k+1)*2-1-1) with (S k*2) by lia.
     apply CD.mass_even; lia.
   + cbn[CD.bitval CD.third_digit orb].
     replace ((S k+1)*2-0-1) with (1+S k*2) by lia.

     pose proof (CD.mass_odd (S k) old false ltac:(lia)) as H.
     cbn[CD.bitval CD.third_digit CD.fourth_digit negb] in H.
     rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma digits_exit bs old :
 segRLs mtm (departure old (2^length bs-CD.value bs-1))
  (special (orb old (CD.any bs))) (CD.third bs) (ones5^^length bs).
Proof.

 gen old. induction bs as [|bit bs IH]; intro old.
 - cbn[CD.third CD.value CD.any length Nat.pow departure].
   replace (orb old false) with old by (destruct old; reflexivity).
   apply segRLs_nil.
 - pose proof (CD.value_bound bs) as Hv.
   cbn[CD.third CD.value CD.any length Nat.pow lpow].
   replace (2*2^length bs-(CD.bitval bit+2*CD.value bs)-1)
    with (((2^length bs-CD.value bs-1)+1)*2-CD.bitval bit-1)
    by (destruct bit; cbn[CD.bitval]; nia).
   replace (orb old (orb bit (CD.any bs)))
    with (orb (orb old bit) (CD.any bs)) by (destruct old,bit; reflexivity).

   eapply segRLs_concat.
   + apply digit_exit.
   + apply IH.
Qed.

Lemma terminal old : segRLs mtm (special old) [] tail ones7.
Proof.

 destruct old; unfold special.
 - apply TightTail.TightTail.terminal_D.
 - apply TightTail.TightTail.terminal_C.
Qed.

Lemma exit_side bs old :
 sideRLs mtm (departure old (2^length bs-CD.value bs-1))
  (CD.third bs *> tail *> 0inf) (ones5^^length bs *> ones7 *> 0inf).
Proof.

 eapply segRLs_sideRLs_concat.
 - apply digits_exit.
 - eapply segRLs_sideRLs_concat.
   + apply terminal.
   + constructor.
Qed.

Lemma exit_C bs :
 sideRLs mtm (x^^(2^length bs-CD.value bs-1)++hx)
  (CD.third bs *> tail *> 0inf) (ones5^^length bs *> ones7 *> 0inf).
Proof. rewrite <-departure_false. apply exit_side. Qed.

Definition demand bs := 2^length bs-CD.value bs.

Lemma one_sequence k q :
 segRLs mtm (h^^(k*2+(1+q))) (x^^k++hx++h^^(1+q*2)) one ld.
Proof.

 rewrite lpow_add.
 eapply segRLs_trans.
 - apply OddNormal.OddNormal.one_pairs.
 - apply OddNormal.OddNormal.one_expand.
Qed.

Lemma odd_reduction bs q r' :
 sideRLs mtm (h^^(1+q*2)) (ones5^^length bs *> ones7 *> 0inf) r' ->
 sideRLs mtm (h^^((demand bs-1)*2+(1+q)))
  (one *> CD.third bs *> tail *> 0inf) (ld *> r').
Proof.

 intro H.
 eapply segRLs_sideRLs_concat.
 - apply one_sequence.
 - rewrite app_assoc.
   eapply sideRLs_trans.
   + apply exit_C.
   + exact H.
Qed.

Print Assumptions digits_exit.
Print Assumptions exit_C.
Print Assumptions odd_reduction.
End TightPrimer.
End TightPrimer.

Module TightFinish.
(* Numeric endpoints after the tight-terminal conversion.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses TightPrimer OddDefectFinish BlankPasses CDPasses CounterRules.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TightFinish.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module T := TightPrimer.TightPrimer.
Module BP := BlankPasses.BlankPasses.
Module CD := CDPasses.CDPasses.
Module CR := CounterRules.CounterRules.
Notation one := [1].
Notation ld := [1;1].
Notation ones5 := [1;1;1;1;1].
Notation ones7 := [1;1;1;1;1;1;1].
Notation tail := [0;0;0;1;0;0;1;0].
Notation h := [((A,[0]),(C,[0]))].
Open Scope nat.

Lemma demand_positive bs : 0<T.demand bs.
Proof. unfold T.demand. pose proof (CD.value_bound bs). lia. Qed.

Lemma ones_even w :
 ones5^^(w*2)++ones7 = ld^^(w*5+3)++one.
Proof.
 change ((one^^5)^^(w*2)++one^^7 = (one^^2)^^(w*5+3)++one^^1).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.
Lemma ones_odd w :
 ones5^^(w*2+1)++ones7 = ld^^(w*5+6).
Proof.
 change ((one^^5)^^(w*2+1)++one^^7 = (one^^2)^^(w*5+6)).
 repeat rewrite <-lpow_mul. repeat rewrite <-lpow_add. f_equal. lia.
Qed.

Lemma finish_even bs w q :
 length bs=w*2 ->
 sideRLs mtm (h^^(2*(T.demand bs+q)))
  (one *> CD.third bs *> tail *> 0inf)
  (ld *> ld^^(w*5+3) *> one *>
   BP.shifted_counter ((q*4+3)*2^(w*5+2))).
Proof.
 intro Hg. pose proof (demand_positive bs).
 replace (2*(T.demand bs+q)) with
  ((T.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply T.odd_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_even,Str_app_assoc.
 replace (w*5+3) with ((w*5+2)+1) by lia.
 apply OddDefectFinish.OddDefectFinish.odd_ones.
Qed.

Lemma finish_odd bs w q :
 length bs=w*2+1 ->
 sideRLs mtm (h^^(2*(T.demand bs+q)))
  (one *> CD.third bs *> tail *> 0inf)
  (ld *> ld^^(w*5+6) *> CR.RC ((q*4+3)*2^(w*5+6))).
Proof.
 intro Hg. pose proof (demand_positive bs).
 replace (2*(T.demand bs+q)) with
  ((T.demand bs-1)*2+(1+(1+q*2))) by lia.
 apply T.odd_reduction.
 replace (1+(1+q*2)*2) with (q*4+3) by lia.
 rewrite Hg,<-Str_app_assoc,ones_odd.
 apply BP.even_ones.
Qed.

Print Assumptions finish_even.
Print Assumptions finish_odd.
End TightFinish.
End TightFinish.

Module TerminalClosure.
(* Closing either terminal phase from an odd finite counter budget.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import LocalPasses CounterRules CounterH CDPasses EndpointClasses WallInvariant BlankPasses.
Import OddDefectTail OddDefectFinish TightPrimer TightFinish.
Import String List PeanoNat Lia.
Import ListNotations.
Open Scope sym.

Module TerminalClosure.
Notation mtm := LocalPasses.Mirrored.local_tm.
Module CR := CounterRules.CounterRules.
Module CD := CDPasses.CDPasses.
Module EC := EndpointClasses.EndpointClasses.
Module OT := OddDefectTail.OddDefectTail.
Module OF := OddDefectFinish.OddDefectFinish.
Module TT := TightPrimer.TightPrimer.
Module TF := TightFinish.TightFinish.
Module W := WallInvariant.WallInvariant.
Module CH := CounterH.CounterH.
Module BP := BlankPasses.BlankPasses.
Notation one := [1].

Notation ld := [1;1].
Notation z := [0].
Notation lh := (0inf<*<[1;1]).
Notation defect := [0;0;0;0;0;0;0;1].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma split_budget k T :
 k mod 2=1 -> 2*T<=k+1 -> exists q, k+1=2*(T+q).
Proof.

 intros Ho Hb. destruct (mod2 k) as [j He|j He]; subst k.
 - rewrite Nat.mod_mul in Ho by lia. discriminate.
 - exists (j+1-T). lia.
Qed.

Lemma defect_counter L k bs :
 k<2^L -> k mod 2=1 -> 2*OT.demand bs<=k+1 ->
 exists out,
  CR.LC L k |> one *> CD.third bs *> defect *> 0inf -[mtm]->+ out /\
  W.invariant out.
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (OT.demand bs) Ho Hb) as [q HE].
 destruct (mod2 (OT.converted_digits bs)) as [w Hg|w Hg].
 - eapply EC.counter_shifted with (T:=OT.demand bs) (q:=q) (s:=w*5).
   + exact Hk.
   + exact HE.
   + apply OF.demand_positive.
   + rewrite HE. apply OF.finish_even. exact Hg.
 - eapply EC.counter_ordinary with (T:=OT.demand bs) (q:=q) (s:=w*5+4).
   + exact Hk.
   + exact HE.
   + apply OF.demand_positive.
   + lia.
   + rewrite HE. apply OF.finish_odd. lia.
Qed.

Lemma tight_counter L k bs :
 k<2^L -> k mod 2=1 -> 2*TT.demand bs<=k+1 ->
 exists out,
  CR.LC L k |> one *> CD.third bs *> tight *> 0inf -[mtm]->+ out /\
  W.invariant out.
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (TT.demand bs) Ho Hb) as [q HE].
 destruct (mod2 (length bs)) as [w Hg|w Hg].
 - eapply EC.counter_shifted with (T:=TT.demand bs) (q:=q) (s:=w*5+2).
   + exact Hk.
   + exact HE.
   + apply TF.demand_positive.
   + replace (w*5+2+1) with (w*5+3) by lia.
     rewrite HE. apply TF.finish_even. exact Hg.
 - eapply EC.counter_ordinary with (T:=TT.demand bs) (q:=q) (s:=w*5+6).
   + exact Hk.
   + exact HE.
   + apply TF.demand_positive.

   + lia.
   + rewrite HE. apply TF.finish_odd. lia.
Qed.


Definition even_wall L s q : (Q*tape)%type :=
 lh<*z {{A}}> (ld^^(L+s+3) *> BP.shifted_counter ((q*4+3)*2^s)).
Definition odd_wall L s q : (Q*tape)%type :=
 lh<*z {{A}}> (one *> ld^^(L+s+1) *> CR.RC ((q*4+3)*2^s)).

Lemma counter_shifted_exact L k q s r :
 k<2^L ->
 sideRLs mtm ([((A,[0]%sym),(C,[0]%sym))]^^(k+1)) r
  (ld *> ld^^(s+1) *> one *> BP.shifted_counter ((q*4+3)*2^s)) ->
 CR.LC L k |> r -[mtm]->+ even_wall L s q.
Proof.

 intros Hk Hr. unfold even_wall.
 pose proof (CH.right_h_finish L k r _ Hk Hr) as H.
 repeat rewrite <-Str_app_assoc in H.
 rewrite <-app_assoc,<-app_assoc,<-app_assoc,EC.even_word in H. exact H.
Qed.

Lemma counter_ordinary_exact L k q s r :
 k<2^L ->
 sideRLs mtm ([((A,[0]%sym),(C,[0]%sym))]^^(k+1)) r
  (ld *> ld^^s *> CR.RC ((q*4+3)*2^s)) ->
 CR.LC L k |> r -[mtm]->+ odd_wall L s q.
Proof.

 intros Hk Hr. unfold odd_wall.
 pose proof (CH.right_h_finish L k r _ Hk Hr) as H.
 repeat rewrite <-Str_app_assoc in H.
 rewrite <-app_assoc,<-app_assoc,EC.odd_word,Str_app_assoc in H. exact H.
Qed.

Lemma defect_counter_cases L k bs :
 k<2^L -> k mod 2=1 -> 2*OT.demand bs<=k+1 ->
 exists q,
  k+1=2*(OT.demand bs+q) /\ q*4+3<2^(L+1) /\
  ((exists w, OT.converted_digits bs=w*2 /\
    CR.LC L k |> one *> CD.third bs *> defect *> 0inf -[mtm]->+
      even_wall L (w*5) q /\ W.invariant (even_wall L (w*5) q)) \/
   (exists w, OT.converted_digits bs=w*2+1 /\
    CR.LC L k |> one *> CD.third bs *> defect *> 0inf -[mtm]->+
      odd_wall L (w*5+4) q)).
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (OT.demand bs) Ho Hb) as [q HE].
 pose proof (OF.demand_positive bs) as HT.
 assert (HB:2*(OT.demand bs+q)<=2^L) by lia.
 exists q. split; [exact HE|]. split.
 - apply EC.coefficient_bound with (T:=OT.demand bs); assumption.
 - destruct (mod2 (OT.converted_digits bs)) as [w Hg|w Hg].
   + left. exists w. split; [exact Hg|]. split.
     * apply counter_shifted_exact; [exact Hk|].
       rewrite HE. apply OF.finish_even. exact Hg.

     * unfold even_wall. apply EC.shifted_endpoint with (T:=OT.demand bs); assumption.
   + right. exists w. split; [lia|].
     apply counter_ordinary_exact; [exact Hk|].
     rewrite HE. apply OF.finish_odd. lia.
Qed.

Lemma tight_counter_cases L k bs :
 k<2^L -> k mod 2=1 -> 2*TT.demand bs<=k+1 ->
 exists q,
  k+1=2*(TT.demand bs+q) /\ q*4+3<2^(L+1) /\
  ((exists w, length bs=w*2 /\
    CR.LC L k |> one *> CD.third bs *> tight *> 0inf -[mtm]->+
      even_wall L (w*5+2) q /\ W.invariant (even_wall L (w*5+2) q)) \/
   (exists w, length bs=w*2+1 /\
    CR.LC L k |> one *> CD.third bs *> tight *> 0inf -[mtm]->+
      odd_wall L (w*5+6) q)).
Proof.

 intros Hk Ho Hb.
 destruct (split_budget k (TT.demand bs) Ho Hb) as [q HE].
 pose proof (TF.demand_positive bs) as HT.
 assert (HB:2*(TT.demand bs+q)<=2^L) by lia.
 exists q. split; [exact HE|]. split.
 - apply EC.coefficient_bound with (T:=TT.demand bs); assumption.
 - destruct (mod2 (length bs)) as [w Hg|w Hg].
   + left. exists w. split; [exact Hg|]. split.
     * apply counter_shifted_exact; [exact Hk|].
       replace (w*5+2+1) with (w*5+3) by lia.
       rewrite HE. apply TF.finish_even. exact Hg.

     * unfold even_wall. apply EC.shifted_endpoint with (T:=TT.demand bs); assumption.
   + right. exists w. split; [lia|].
     apply counter_ordinary_exact; [exact Hk|].
     rewrite HE. apply TF.finish_odd. lia.
Qed.

Print Assumptions defect_counter_cases.
Print Assumptions tight_counter_cases.

Print Assumptions defect_counter.
Print Assumptions tight_counter.
End TerminalClosure.
End TerminalClosure.

Module OddAdjacent.
(* The next wall image when an ordinary counter begins with adjacent ones.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2.
Import OddFuel OddImage OddRecursion EdEvenOrbit EdOddOrbit.
Import CounterRules CounterFinish CounterBits CDPasses TerminalClosure WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module OddAdjacent.
Module W := WallInvariant.WallInvariant.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module R := OddRecursion.OddRecursion.
Module EE := EdEvenOrbit.EdEvenOrbit.
Module EO := EdOddOrbit.EdOddOrbit.
Module CR := CounterRules.CounterRules.
Module CF := CounterFinish.CounterFinish.
Module CB := CounterBits.CounterBits.
Module CD := CDPasses.CDPasses.
Module TC := TerminalClosure.TerminalClosure.
Notation mtm := W.mtm.
Open Scope sym.
Notation r4 := [1;0;0;0].
Notation ld := [1;1].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Definition odd_rank n v :=
 F.grown (F.grown (I.first_fuel n (v*2+1)) (v*5+3)-1) 1.
Definition odd_mass n v :=
 (2*I.first_fuel n (v*2+1)+1)*2^(v*5+4)-3.

Lemma odd_rank_bound n v : v*2+2<=n ->
 odd_rank n v+1<2^(n+v*5+6).
Proof.

 intro Hn.
 pose proof (F.grown_bound n (I.first_fuel n (v*2+1)) (v*5+3)
   ltac:(apply I.first_fuel_bounds; lia)) as Hfirst.
 unfold odd_rank.
 replace (n+v*5+6) with ((n+1+(v*5+3))+1+1) by lia.
 apply F.grown_bound. lia.
Qed.

Lemma odd_mass_rank n v : odd_rank n v+1=odd_mass n v*2.
Proof.

 unfold odd_rank,odd_mass,F.grown.

 assert (Hz:8<=2^(v*5+3)).
 { change (2^3<=2^(v*5+3)). apply Nat.pow_le_mono_r; lia. }
 replace (v*5+4) with ((v*5+3)+1) by lia.
 rewrite (Nat.pow_add_r 2 (v*5+3) 1). cbn[Nat.pow]. nia.
Qed.

Lemma odd_entry n v bs : v*2+2<=n ->
 W.O n (repeat false (v*2+1)++true::true::bs) -[mtm]->+
 CR.LC (n+v*5+6) (odd_rank n v) |> r4 *> W.normal bs *> 0inf.
Proof.

 intro Hn.
 set (L0:=n+1+(v*5+3)).
 set (k0:=F.grown (I.first_fuel n (v*2+1)) (v*5+3)).

 assert (Hk:k0+1<2^L0).
 { unfold k0,L0. apply F.grown_bound. apply I.first_fuel_bounds. lia. }

 assert (Hpos:1<=k0).
 { unfold k0,F.grown.

   assert (8<=2^(v*5+3)) by (change (2^3<=2^(v*5+3)); apply Nat.pow_le_mono_r; lia).
   nia. }

 assert (Hbefore:(k0-1)+(2^(0*2+1)-1)<2^L0) by
   (change ((k0-1)+1<2^L0); lia).
 pose proof (R.zero_even_step L0 (k0-1) 0 bs 0inf Hbefore) as Hsecond.
 cbn[Nat.mul Nat.add Nat.pow Nat.sub repeat app] in Hsecond.
 replace (k0-1+1) with k0 in Hsecond by lia.
 change (CR.LC L0 k0 |> ([0;0;0]%sym) *> W.normal (true::bs) *> 0inf -[mtm]->+
   CR.LC (L0+1+1) (F.grown (k0-1) 1) |> r4 *> W.normal bs *> 0inf) in Hsecond.
 unfold odd_rank.
 replace (n+v*5+6) with (L0+1+1) by (unfold L0; lia).
 fold k0.
 eapply progress_trans; [apply R.initial_odd_entry; exact Hn|exact Hsecond].
Qed.

Lemma odd_mass_bounds n v width q :
 v*2+3<=n -> width<=n -> q<2^width ->
 2^width<=odd_mass n v /\ odd_mass n v+q<2^(n+v*5+6).
Proof.

 intros Hn Hw Hq.
 pose proof (EO.first_fuel_half n (v*2+1) ltac:(lia)) as Hfirst.

 assert (Hwidth:2^width<=2^n) by (apply Nat.pow_le_mono_r; lia).

 assert (Hz:16<=2^(v*5+4)) by (change (2^4<=2^(v*5+4)); apply Nat.pow_le_mono_r; lia).
 pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as Hpos.
 split.
 - unfold odd_mass. nia.
 - pose proof (odd_rank_bound n v ltac:(lia)) as Hb.
   rewrite odd_mass_rank in Hb.

   assert (Hqmass:q<odd_mass n v) by (unfold odd_mass; nia).
   lia.
Qed.

Lemma odd_image n v bs budget :
 v*2+2<=n -> 2^length bs<=odd_mass n v ->
 odd_mass n v+CD.value bs<2^(length bs+budget) ->
 exists out,
 length out<length bs+budget /\
 CD.value out+2^length out=odd_mass n v+CD.value bs /\
 W.O n (repeat false (v*2+1)++true::true::bs) -[mtm]->+
 W.wall (ld^^(n+v*5+7)++CD.fourth out++CD.terminal (CD.any bs)).
Proof.

 intros Hn Hmin Hmax.
 pose proof (odd_rank_bound n v Hn) as Hb.
 destruct (I.fuel_C_image (n+v*5+6) (odd_rank n v) (odd_mass n v)
   bs budget ltac:(lia) (odd_mass_rank n v) Hmin Hmax)
   as [out [Hlen [Hval Hrun]]].
 exists out. repeat split; try assumption.
 replace (n+v*5+7) with ((n+v*5+6)+1) by lia.
 eapply progress_trans; [apply odd_entry; exact Hn|exact Hrun].
Qed.

Print Assumptions odd_entry.
Print Assumptions odd_image.
End OddAdjacent.
End OddAdjacent.

Module TerminalSuccessor.
(* Exact displaced-digit successors of the two ordinary terminal endpoints.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2.
Import OddImage OddAdjacent EdEvenOrbit CounterRules CounterFinish CounterBits CDPasses TerminalClosure WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module TerminalSuccessor.
Module W := WallInvariant.WallInvariant.
Module I := OddImage.OddImage.
Module A := OddAdjacent.OddAdjacent.
Module EE := EdEvenOrbit.EdEvenOrbit.
Module CR := CounterRules.CounterRules.
Module CF := CounterFinish.CounterFinish.
Module CB := CounterBits.CounterBits.
Module CD := CDPasses.CDPasses.
Module TC := TerminalClosure.TerminalClosure.
Notation mtm := W.mtm.
Open Scope nat.

Lemma coefficient_parts L q : q*4+3<2^(L+1) ->
 0<L /\ q<2^L /\ q*2+1<2^L.
Proof.

 intro H. assert (HL:0<L) by (destruct L; cbn in H; lia).
 rewrite Nat.pow_add_r in H. cbn[Nat.pow] in H. repeat split; lia.
Qed.

Lemma first_coefficient n u : u+2<=n ->
 2^n+3<=2*I.first_fuel n u+1.
Proof.

 intro Hn. destruct (I.first_fuel_bounds n u ltac:(lia)) as [He Hb].

 assert (Hcap:2^(u+2)<=2^n) by (apply Nat.pow_le_mono_r; lia).
 rewrite Nat.pow_add_r in Hcap. cbn[Nat.pow] in Hcap.
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia.
Qed.

Lemma first_mass_lower n v : 0<v -> v*2+2<=n ->
 2^(n+v*5-1)<=I.first_mass n v.
Proof.

 intros Hv Hn. pose proof (first_coefficient n (v*2) Hn).
 unfold I.first_mass.
 replace (n+v*5-1) with (n+(v*5-1)) by lia.
 rewrite Nat.pow_add_r. nia.
Qed.

Lemma odd_mass_lower n v : v*2+3<=n ->
 2^(n+v*5+4)<=A.odd_mass n v.
Proof.

 intro Hn. pose proof (first_coefficient n (v*2+1) ltac:(lia)).
 unfold A.odd_mass.
 replace (n+v*5+4) with (n+(v*5+4)) by lia.
 rewrite (Nat.pow_add_r 2 n (v*5+4)).
 pose proof (Nat.pow_nonzero 2 (v*5+4) ltac:(lia)). nia.
Qed.

Lemma mass_length out base mass :
 CD.value out+2^length out=mass -> 2^base<=mass -> mass<2^(base+2) ->
 length out=base \/ length out=base+1.
Proof.

 intros He Hlo Hhi. pose proof (CD.value_bound out) as Hv.

 assert (Hlower:base<=length out).
 { destruct (Nat.le_gt_cases base (length out)); [assumption|].

   assert (2^(length out+1)<=2^base) by (apply Nat.pow_le_mono_r; lia).
   rewrite Nat.pow_add_r in H0. cbn[Nat.pow] in H0. lia. }

 assert (Hupper:length out<base+2).
 { destruct (Nat.lt_ge_cases (length out) (base+2)); [assumption|].

   assert (2^(base+2)<=2^length out) by (apply Nat.pow_le_mono_r; lia). lia. }
 lia.
Qed.

Lemma ordinary_source L s q : q*4+3<2^(L+1) ->
 TC.odd_wall L s q=
 W.O (L+s+1) (repeat false s++true::CF.digits L (q*2+1)).
Proof.

 intro H. destruct (coefficient_parts L q H) as [HL [Hq Htail]].
 unfold TC.odd_wall,W.O,W.wall. repeat rewrite Str_app_assoc.
 rewrite EE.normal_shift_odd by exact Htail.
 replace ((q*2+1)*2+1) with (q*4+3) by lia.
 simpl_rotate. reflexivity.
Qed.

Lemma ordinary_source_adjacent L s q : q*4+3<2^(L+1) ->
 TC.odd_wall L s q=
 W.O (L+s+1) (repeat false s++true::true::CF.digits L q).
Proof.

 intro H. destruct (coefficient_parts L q H) as [HL [Hq Htail]].

 assert (Htail':q*2+1<2^(S L)) by (cbn[Nat.pow]; lia).
 pose proof (EE.normal_shift_odd (S L) (q*2+1) s Htail') as Henc.
 rewrite CF.digits_odd in Henc.
 replace ((q*2+1)*2+1) with (q*4+3) in Henc by lia.
 unfold TC.odd_wall,W.O,W.wall. repeat rewrite Str_app_assoc.
 rewrite Henc. simpl_rotate. reflexivity.
Qed.

Lemma ordinary_even_image L v q :
 0<v -> q*4+3<2^(L+1) ->
 exists out,
 (length out+3=L+v*7+3 \/ length out+2=L+v*7+3) /\
 2^(L+v*7)<=I.first_mass (L+v*2+1) v+(q*2+1) /\
 I.first_mass (L+v*2+1) v+(q*2+1)<2^(L+v*7+2) /\
 CD.value out+2^length out=I.first_mass (L+v*2+1) v+(q*2+1) /\
 TC.odd_wall L (v*2) q -[mtm]->+ W.Ed (L+v*7+3) out.
Proof.

 intros Hv Hcoef. destruct (coefficient_parts L q Hcoef) as [HL [Hq Htail]].
 set (n:=L+v*2+1).
 destruct (EE.first_mass_bounds n v L (q*2+1) Hv ltac:(unfold n; lia)
   ltac:(unfold n; lia) Htail) as [Hmin Hmax].

 assert (Hlen:L+(n+v*5+1-L)=n+v*5+1) by (unfold n; lia).

 assert (Hvalue:CD.value (CF.digits L (q*2+1))=q*2+1).
 { change (CB.value (CF.digits L (q*2+1))=q*2+1). apply CB.digits_value; exact Htail. }
 destruct (I.initial_even_image n v (CF.digits L (q*2+1)) (n+v*5+1-L)
   Hv ltac:(unfold n; lia)
   ltac:(rewrite CF.digits_length; exact Hmin)
   ltac:(rewrite CF.digits_length,Hvalue,Hlen; exact Hmax))
   as [out [Hlength [Hmass Hrun]]].
 rewrite Hvalue in Hmass.

 assert (Hany:CD.any (CF.digits L (q*2+1))=true).
 { apply EE.any_true,CB.value_nonzero. rewrite CB.digits_value by exact Htail. lia. }
 rewrite Hany in Hrun. cbn[CD.terminal] in Hrun.

 assert (Hlow:2^(L+v*7)<=I.first_mass n v+(q*2+1)).
 { pose proof (first_mass_lower n v Hv ltac:(unfold n; lia)).
   replace (n+v*5-1) with (L+v*7) in H by (unfold n; lia). lia. }
 replace (n+v*5+1) with (L+v*7+2) in Hmax by (unfold n; lia).
 pose proof (mass_length out (L+v*7) _ Hmass Hlow Hmax) as Hd.
 exists out. repeat split; try assumption; try lia.
 rewrite ordinary_source by exact Hcoef. fold n.
 replace (L+v*7+3) with (n+v*5+2) by (unfold n; lia).
 exact Hrun.
Qed.

Lemma ordinary_odd_image L v q :
 0<q -> q*4+3<2^(L+1) ->
 exists out,
 (length out+3=L+v*7+9 \/ length out+2=L+v*7+9) /\
 2^(L+v*7+6)<=A.odd_mass (L+v*2+2) v+q /\
 A.odd_mass (L+v*2+2) v+q<2^(L+v*7+8) /\
 CD.value out+2^length out=A.odd_mass (L+v*2+2) v+q /\
 TC.odd_wall L (v*2+1) q -[mtm]->+ W.Ed (L+v*7+9) out.
Proof.

 intros Hqpos Hcoef. destruct (coefficient_parts L q Hcoef) as [HL [Hq Htail]].
 set (n:=L+v*2+2).
 destruct (A.odd_mass_bounds n v L q ltac:(unfold n; lia) ltac:(unfold n; lia) Hq)
   as [Hmin Hmax].

 assert (Hlen:L+(n+v*5+6-L)=n+v*5+6) by (unfold n; lia).

 assert (Hvalue:CD.value (CF.digits L q)=q).
 { change (CB.value (CF.digits L q)=q). apply CB.digits_value; exact Hq. }
 destruct (A.odd_image n v (CF.digits L q) (n+v*5+6-L)
   ltac:(unfold n; lia) ltac:(rewrite CF.digits_length; exact Hmin)
   ltac:(rewrite CF.digits_length,Hvalue,Hlen; exact Hmax))
   as [out [Hlength [Hmass Hrun]]].
 rewrite Hvalue in Hmass.

 assert (Hany:CD.any (CF.digits L q)=true).
 { apply EE.any_true,CB.value_nonzero. rewrite CB.digits_value by exact Hq. lia. }
 rewrite Hany in Hrun. cbn[CD.terminal] in Hrun.

 assert (Hlow:2^(L+v*7+6)<=A.odd_mass n v+q).
 { pose proof (odd_mass_lower n v ltac:(unfold n; lia)).
   replace (n+v*5+4) with (L+v*7+6) in H by (unfold n; lia). lia. }
 replace (n+v*5+6) with (L+v*7+8) in Hmax by (unfold n; lia).
 pose proof (mass_length out (L+v*7+6) _ Hmass Hlow ltac:(replace (L+v*7+6+2) with (L+v*7+8) by lia; exact Hmax)) as Hd.
 exists out. repeat split; try assumption; try lia.
 rewrite ordinary_source_adjacent by exact Hcoef.
 replace (L+(v*2+1)+1) with n by (unfold n; lia).
 replace (L+v*7+9) with (n+v*5+7) by (unfold n; lia).
 exact Hrun.
Qed.

Print Assumptions ordinary_even_image.
Print Assumptions ordinary_odd_image.
End TerminalSuccessor.
End TerminalSuccessor.

Module RouteDeficit.
(* A bound on the arithmetic correction accumulated by a conversion route.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import OddRoute OddFuel EdOddOrbit.
Import String List PeanoNat Lia.
Import ListNotations.

Module RouteDeficit.
Module F := OddFuel.OddFuel.
Module R := OddRoute.OddRoute.
Open Scope nat.

Lemma step_deficit L k deficit u z :
 k+(2^(u+1)-1)+deficit+1=2^L ->
 exists correction,
 F.grown k z+deficit*2^(z+1)+correction+1=2^(L+z+1) /\
 correction<2^(z+u+2).
Proof.

 intro Hleft.
 exists ((2^(u+2)-1)*2^z).
 assert (Hp:0<2^(u+1)).
 { pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)); lia. }
 assert (Hz:0<2^z).
 { pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia. }

 assert (Hu:2^(u+2)=2^(u+1)*2).
 { replace (u+2) with ((u+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }
 assert (Hgrow:2^(z+1)=2^z*2) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Htotal:2^(L+z+1)=2^L*2^z*2).
 { rewrite !Nat.pow_add_r. reflexivity. }
 assert (Hbound:2^(z+u+2)=2^(u+2)*2^z).
 { replace (z+u+2) with ((u+2)+z) by lia. apply Nat.pow_add_r. }
 split.
 - unfold F.grown. rewrite Hu,Hgrow,Htotal. nia.
 - rewrite Hbound. pose proof (Nat.pow_nonzero 2 (u+2) ltac:(lia)). nia.
Qed.

Lemma route_deficit L k bs L' k' rest :
 R.route L k bs L' k' rest ->
 forall deficit, k+deficit+1=2^L ->
 exists j correction,
 length bs=2*j+1+length rest /\ L'=L+5*j+2 /\
 k'+deficit*2^(5*j+2)+correction+1=2^L' /\
 correction<2^(7*j+3).
Proof.

 intro Hroute. induction Hroute; intros deficit Hleft.
 - destruct (step_deficit L k deficit (v*2) (v*5+1) Hleft)
     as [e [He Hb]].
   exists v,e.
   rewrite length_app,repeat_length. cbn [length].
   replace (v*5+1+1) with (5*v+2) in He by lia.
   replace (L+(v*5+1)+1) with (L+1+(v*5+1)) in He by lia.
   replace (v*5+1+v*2+2) with (7*v+3) in Hb by lia.
   repeat split; try lia; exact He.

 - replace (v*2+2) with ((v*2+1)+1) in Hleft by lia.
   destruct (step_deficit L k deficit (v*2+1) (v*5+4) Hleft)
     as [e [He Hb]].
   replace (v*5+4+1) with (5*v+5) in He by lia.
   replace (L+(v*5+4)+1) with (L+1+(v*5+4)) in He by lia.
   replace (v*5+4+(v*2+1)+2) with (7*v+7) in Hb by lia.

   assert (Hleft':F.grown k (v*5+4)+(deficit*2^(5*v+5)+e)+1=
     2^(L+1+(v*5+4))) by lia.
   destruct (IHHroute (deficit*2^(5*v+5)+e) Hleft')
     as [j [f [Hlen [HL [Hend Hf]]]]].

   exists (v+1+j),(e*2^(5*j+2)+f).
   rewrite length_app,repeat_length. cbn [length].
   split; [lia|]. split; [lia|].

   assert (Hg:2^(5*(v+1+j)+2)=2^(5*v+5)*2^(5*j+2)).
   { replace (5*(v+1+j)+2) with ((5*v+5)+(5*j+2)) by lia.
     apply Nat.pow_add_r. }
   split.
   + rewrite Hg. nia.

   + assert (Hpos:0<2^(5*j+2)).
     { pose proof (Nat.pow_nonzero 2 (5*j+2) ltac:(lia)); lia. }
     assert (Hfirst:e*2^(5*j+2)<2^(7*v+5*j+9)).
     { assert (Hproduct:2^(7*v+5*j+9)=2^(7*v+7)*2^(5*j+2)).
       { replace (7*v+5*j+9) with ((7*v+7)+(5*j+2)) by lia.
         apply Nat.pow_add_r. }
       rewrite Hproduct. nia. }

     assert (Hone:2^(7*v+5*j+9)<=2^(7*(v+1+j)+2)).
     { apply Nat.pow_le_mono_r; lia. }
     assert (Htwo:2^(7*j+3)<=2^(7*(v+1+j)+2)).
     { apply Nat.pow_le_mono_r; lia. }
     assert (Hlast:2^(7*(v+1+j)+3)=2^(7*(v+1+j)+2)*2).
     { replace (7*(v+1+j)+3) with ((7*(v+1+j)+2)+1) by lia.
       rewrite Nat.pow_add_r. reflexivity. }
     rewrite Hlast. nia.
Qed.

Print Assumptions step_deficit.
Print Assumptions route_deficit.

Lemma route_suffix L k bs L' k' rest :
 R.route L k bs L' k' rest -> exists pre, bs=pre++rest.
Proof.
 intro H. induction H.
 - exists (repeat false (v*2)++[true]). rewrite <-app_assoc. reflexivity.
 - destruct IHroute as [pre E].
   exists (repeat false (v*2+1)++true::pre).
   rewrite E,<-app_assoc. reflexivity.
Qed.

End RouteDeficit.
End RouteDeficit.

Module MarkedDeficit.
(* Bounding the deficit retained by an exact marked-wall conversion path.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import OddFuel OddImage MarkedTrace RouteDeficit WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module MarkedDeficit.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module M := MarkedTrace.MarkedTrace.
Module RD := RouteDeficit.RouteDeficit.
Open Scope nat.

Definition initial_deficit u z := (2^(u+2)-3)*2^z.

Lemma initial_balance n u z : u+1<=n ->
 F.grown (I.first_fuel n u) z+initial_deficit u z+1=2^(n+1+z).
Proof.

 intro Hn. destruct (I.first_fuel_bounds n u Hn) as [He Hb].
 unfold F.grown,initial_deficit.
 rewrite !Nat.pow_add_r. cbn[Nat.pow].
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 z ltac:(lia)). nia.
Qed.

Lemma initial_bound u z : initial_deficit u z<2^(u+2+z).
Proof.

 unfold initial_deficit. rewrite (Nat.pow_add_r 2 (u+2) z).

 assert (Hpos:0<2^z) by (pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia).

 assert (Hu:3<2^(u+2)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow].
   pose proof (Nat.pow_nonzero 2 u ltac:(lia)). nia. }
 nia.
Qed.

Lemma wall_deficit n bs L k rest :
 M.wall_route n bs L k rest -> length bs+1<=n ->
 exists j deficit,
 length bs=2*j+1+length rest /\ L=n+5*j+1 /\
 k+deficit+1=2^L /\ deficit<2^(7*j+2).
Proof.

 intros Hroute Hlen. destruct Hroute.
 - exists v,(initial_deficit (v*2) (v*5)).
   rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   rewrite length_app,repeat_length. cbn[length].
   repeat split; try lia.
   + apply initial_balance. lia.
   + replace (7*v+2) with (v*2+2+v*5) by lia. apply initial_bound.
 - rewrite length_app,repeat_length in Hlen. cbn[length] in Hlen.
   set (d0:=initial_deficit (v*2+1) (v*5+3)).

   assert (Hbalance:F.grown (I.first_fuel n (v*2+1)) (v*5+3)+d0+1=
     2^(n+1+(v*5+3))) by (unfold d0; apply initial_balance; lia).
   destruct (RD.route_deficit _ _ _ _ _ _ H d0 Hbalance)
     as [j [correction [Hdim [HL [Hend Hcorr]]]]].
   exists (v+1+j),(d0*2^(5*j+2)+correction).
   rewrite length_app,repeat_length. cbn[length].
   split; [lia|]. split; [lia|]. split; [lia|].

   assert (Hd0:d0<2^(7*v+6)).
   { unfold d0. replace (7*v+6) with ((v*2+1)+2+(v*5+3)) by lia.
     apply initial_bound. }

   assert (Hprod:d0*2^(5*j+2)<2^(7*v+5*j+8)).
   { replace (7*v+5*j+8) with ((7*v+6)+(5*j+2)) by lia.
     rewrite (Nat.pow_add_r 2 (7*v+6) (5*j+2)). pose proof (Nat.pow_nonzero 2 (5*j+2) ltac:(lia)). nia. }

   assert (Hone:2^(7*v+5*j+8)<=2^(7*(v+1+j)+1)).
   { apply Nat.pow_le_mono_r; lia. }

   assert (Htwo:2^(7*j+3)<=2^(7*(v+1+j)+1)).
   { apply Nat.pow_le_mono_r; lia. }
   replace (7*(v+1+j)+2) with ((7*(v+1+j)+1)+1) by lia.
   rewrite (Nat.pow_add_r 2 (7*(v+1+j)+1) 1). cbn[Nat.pow]. nia.
Qed.

Lemma wall_deficit_at n bs L k rest j :
 M.wall_route n bs L k rest -> length bs+1<=n ->
 length bs=2*j+1+length rest ->
 exists deficit, k+deficit+1=2^L /\ deficit<2^(7*j+2).
Proof.

 intros Hroute Hlen Hdim.
 destruct (wall_deficit _ _ _ _ _ Hroute Hlen)
   as [j0 [d [Hdim0 [HL [Hbalance Hb]]]]].

 assert (j0=j) by lia. subst j0. exists d. auto.
Qed.

Lemma tight_coefficient_bound n bs L k rest j T q :
 M.wall_route n (false::bs) L k rest -> length bs+2=n ->
 length bs=2*j+length rest ->
 T<=2^length rest -> k+1=2*(T+q) ->
 exists deficit,
 k+deficit+1=2^L /\ deficit<2^(7*j+2) /\
 q*4+3+2*deficit+4*T=2^(L+1)+3 /\ 2^L<=q*4+3.
Proof.

 intros Hroute Hn Hdim HT Hbudget.
 destruct (wall_deficit _ _ _ _ _ Hroute ltac:(cbn[length]; lia))
   as [j0 [d [Hdim0 [HL [Hbalance Hd]]]]].
 cbn[length] in Hdim0. assert (j0=j) by lia. subst j0.

 assert (HL':L=7*j+length rest+3) by lia.

 assert (Hcap:2^L=2^(7*j+2)*2^length rest*2).
 { rewrite HL'. replace (7*j+length rest+3) with ((7*j+2)+length rest+1) by lia.
   rewrite !Nat.pow_add_r. reflexivity. }

 assert (Hx:4<=2^(7*j+2)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow]. pose proof (Nat.pow_nonzero 2 (7*j) ltac:(lia)). nia. }

 assert (Hy:0<2^length rest) by (pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia)); lia).
 exists d. repeat split; try assumption.
 - rewrite Nat.pow_add_r. cbn[Nat.pow]. nia.
 - rewrite Hcap in *. nia.
Qed.

Print Assumptions wall_deficit.
Print Assumptions tight_coefficient_bound.
End MarkedDeficit.
End MarkedDeficit.

Module TerminalLoose.
(* Markers in the loose displaced-digit successors of terminal counters.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import OddFuel OddImage OddAdjacent TerminalSuccessor MarkedDeficit MagnitudeMarker.
Import CounterBits CDPasses WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.
Module TerminalLoose.
Module W := WallInvariant.WallInvariant.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module A := OddAdjacent.OddAdjacent.
Module MD := MarkedDeficit.MarkedDeficit.
Module MM := MagnitudeMarker.MagnitudeMarker.
Module CB := CounterBits.CounterBits.
Module CD := CDPasses.CDPasses.
Open Scope nat.

Lemma initial_gap_three u z : 0<z ->
 MD.initial_deficit u z+3<2^(u+2+z).
Proof.

 intro Hz. unfold MD.initial_deficit.
 rewrite (Nat.pow_add_r 2 (u+2) z).
 assert (Hz2:2<=2^z) by
   (destruct z; [lia|]; cbn[Nat.pow]; pose proof (Nat.pow_nonzero 2 z ltac:(lia)); nia).
 assert (Hu:4<=2^(u+2)) by
   (rewrite Nat.pow_add_r; cbn[Nat.pow]; pose proof (Nat.pow_nonzero 2 u ltac:(lia)); nia).
 nia.
Qed.

Lemma even_balance L v : 0<v ->
 I.first_mass (L+v*2+1) v+MD.initial_deficit (v*2) (v*5-1)=2^(L+v*7+1).
Proof.

 intro Hv.
 pose proof (MD.initial_balance (L+v*2+1) (v*2) (v*5-1) ltac:(lia)) as H.
 unfold F.grown in H. unfold I.first_mass.
 pose proof (Nat.pow_nonzero 2 (v*5-1) ltac:(lia)).
 replace (L+v*2+1+1+(v*5-1)) with (L+v*7+1) in H by lia. nia.
Qed.

Lemma odd_balance L v :
 A.odd_mass (L+v*2+2) v+MD.initial_deficit (v*2+1) (v*5+4)+3=2^(L+v*7+7).
Proof.

 pose proof (MD.initial_balance (L+v*2+2) (v*2+1) (v*5+4) ltac:(lia)) as H.
 unfold F.grown in H. unfold A.odd_mass.
 assert (Hz:16<=2^(v*5+4)) by (change (2^4<=2^(v*5+4)); apply Nat.pow_le_mono_r; lia).
 replace (L+v*2+2+1+(v*5+4)) with (L+v*7+7) in H by lia. nia.
Qed.

Lemma near_power_marker out top gap :
 3<=top -> length out+1=top -> gap<2^(top-3) ->
 2^top<=CD.value out+2^length out+gap -> W.marked 1 out.
Proof.

 intros Htop Hlen Hgap Hvalue.
 apply (MM.magnitude_marker out (length out)).
 - change (CD.value out < 2^length out). apply CD.value_bound.
 - change (2^(length out+1)<3*CD.value out).
   set (b:=top-3).
   assert (Ht:top=b+3) by (unfold b; lia).
   assert (Hl:length out=b+2) by lia.
   rewrite Ht,Hl in Hvalue. rewrite Hl.
   fold b in Hgap.
   replace (b+2+1) with (b+3) by lia.
   rewrite !Nat.pow_add_r in *. cbn[Nat.pow] in *.
   pose proof (Nat.pow_nonzero 2 b ltac:(lia)). nia.
Qed.

Lemma even_loose_marker L v q out :
 3<=L -> 0<v -> length out+3=L+v*7+3 ->
 CD.value out+2^length out=I.first_mass (L+v*2+1) v+(q*2+1) ->
 W.marked 1 out.
Proof.

 intros HL Hv Hlen Hmass.
 pose proof (even_balance L v Hv) as Hbalance.
 apply (near_power_marker out (L+v*7+1) (MD.initial_deficit (v*2) (v*5-1))); try lia.
 pose proof (MD.initial_bound (v*2) (v*5-1)) as Hbound.
 assert (2^(v*2+2+(v*5-1))<=2^(L+v*7+1-3)) by (apply Nat.pow_le_mono_r; lia).
 lia.
Qed.

Lemma odd_loose_marker L v q out :
 3<=L -> length out+3=L+v*7+9 ->
 CD.value out+2^length out=A.odd_mass (L+v*2+2) v+q ->
 W.marked 1 out.
Proof.

 intros HL Hlen Hmass.
 pose proof (odd_balance L v) as Hbalance.
 apply (near_power_marker out (L+v*7+7) (MD.initial_deficit (v*2+1) (v*5+4)+3)); try lia.
 pose proof (initial_gap_three (v*2+1) (v*5+4) ltac:(lia)) as Hbound.
 assert (2^((v*2+1)+2+(v*5+4))<=2^(L+v*7+7-3)) by (apply Nat.pow_le_mono_r; lia).
 lia.
Qed.

Print Assumptions even_loose_marker.
Print Assumptions odd_loose_marker.
End TerminalLoose.
End TerminalLoose.

Module OdStrongMarker.
(* Reachable terminal counters preserve a marked displaced digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import GuardedRoute OdEvenMarker OdOddMarker OdDirectMarker.
Import TerminalLoose TerminalSuccessor MarkedDeficit OddImage OddAdjacent.
Import CounterBits CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module OdStrongMarker.
Module W := WallInvariant.WallInvariant.
Module G := GuardedRoute.GuardedRoute.
Module EM := OdEvenMarker.OdEvenMarker.
Module OM := OdOddMarker.OdOddMarker.
Module DM := OdDirectMarker.OdDirectMarker.
Module TL := TerminalLoose.TerminalLoose.
Module MD := MarkedDeficit.MarkedDeficit.
Module I := OddImage.OddImage.
Module A := OddAdjacent.OddAdjacent.
Module CB := CounterBits.CounterBits.
Module CD := CDPasses.CDPasses.

Lemma good_positive j delta : G.good_deficit j delta -> 1<=j.
Proof. intros [[Hj H]|[u [c [Hj H]]]]; lia. Qed.

Lemma even_tight_marker out L q j delta m a T :
 L=m+7*j+3 -> G.good_deficit j delta ->
 m<=4*a -> 0<T -> T<=6*2^m ->
 2*(T+q)+delta=2^L ->
 length out+2=L+(5*a+2)*7+3 ->
 CD.value out+2^length out=I.first_mass (L+(5*a+2)*2+1) (5*a+2)+(q*2+1) ->
 W.marked 1 out.
Proof.

 intros HL HG Hm HT HTb Hcap Hlen Hmass.
 pose proof (TL.even_balance L (5*a+2) ltac:(lia)) as HB.
 assert (Hcancel:CD.value out+MD.initial_deficit ((5*a+2)*2) ((5*a+2)*5-1)=q*2+1).
 { clear -HB Hlen Hmass.
   replace (L+(5*a+2)*7+1) with (length out) in HB by lia. lia. }
 unfold MD.initial_deficit in Hcancel.
 replace ((5*a+2)*2+2) with (10*a+6) in Hcancel by lia.
 replace ((5*a+2)*5-1) with (25*a+9) in Hcancel by lia.
 change (CB.value out+(2^(10*a+6)-3)*2^(25*a+9)=q*2+1) in Hcancel.

 destruct HG as [[Hj HD]|[u [c [Hj [Hu [HC HD]]]]]].
 - apply (DM.direct_even_marker out a j m T); try assumption.
   subst delta. rewrite HL in Hcap. clear -Hcap Hcancel HT. lia.
 - apply (EM.reachable_even_marker out a j m u c T); try assumption.
   subst delta. rewrite HL in Hcap. clear -Hcap Hcancel HT. lia.
Qed.

Lemma odd_tight_marker out L q j delta m a T :
 L=m+7*j+3 -> G.good_deficit j delta ->
 1<=m<=4*a+2 -> 0<T -> T<=6*2^m ->
 2*(T+q)+delta=2^L ->
 length out+2=L+(5*a+4)*7+9 ->
 CD.value out+2^length out=A.odd_mass (L+(5*a+4)*2+2) (5*a+4)+q ->
 W.marked 1 out.
Proof.

 intros HL HG Hm HT HTb Hcap Hlen Hmass.
 pose proof (TL.odd_balance L (5*a+4)) as HB.
 assert (Hcancel:CD.value out+MD.initial_deficit ((5*a+4)*2+1) ((5*a+4)*5+4)+3=q).
 { clear -HB Hlen Hmass.
   replace (L+(5*a+4)*7+7) with (length out) in HB by lia. lia. }
 unfold MD.initial_deficit in Hcancel.
 replace ((5*a+4)*2+1+2) with (10*a+11) in Hcancel by lia.
 replace ((5*a+4)*5+4) with (25*a+24) in Hcancel by lia.
 change (CB.value out+(2^(10*a+11)-3)*2^(25*a+24)+3=q) in Hcancel.

 assert (Hj:1<=j) by (apply (good_positive j delta);exact HG).
 assert (HF:2^(5*j)=2*2^(5*j-1)).
 { replace (5*j) with (S (5*j-1)) at 1 by (clear -Hj;lia). reflexivity. }
 assert (HP:2^L=2*2^(m+7*j+2)).
 { rewrite HL. replace (m+7*j+3) with (S (m+7*j+2)) by lia. reflexivity. }
 destruct HG as [[Hj0 HD]|[u [c [Hj0 [Hu [HC HD]]]]]].
 - apply (DM.direct_odd_marker out a j m T); try assumption.
   subst delta. rewrite HF,HP in Hcap.
   clear -Hcap Hcancel. nia.

 - subst delta. rewrite HF,HP in Hcap.
   destruct (mod2 c) as [c0 He|c0 He]; subst c.
   + apply (OM.reachable_odd_marker out a j m u c0 T); try assumption.
     * replace (5*j-5) with (S (5*j-6)) in HC by (clear -Hj0;lia).
       cbn[Nat.pow] in HC. clear -HC. lia.
     * clear -Hcap Hcancel. nia.
   + exfalso. clear -Hcap. nia.
Qed.

Print Assumptions even_tight_marker.
Print Assumptions odd_tight_marker.
End OdStrongMarker.
End OdStrongMarker.

Module TightEd.
(* The first wall step when a displaced terminal digit has tight space.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import LocalPasses ExceptionalPasses PhaseE PhaseEd WallInvariant.
Import String List PeanoNat NArith Lia.
Import LocalPasses.Mirrored ExceptionalPasses.Exceptional PhaseE.PhaseE.
Open Scope sym.

Module TightEd.
Notation mtm := LocalPasses.Mirrored.local_tm.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dc := [0;0;0;0;1].
Notation dd := [0;0;0;1;0].
Notation dd1 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Module W := WallInvariant.WallInvariant.

Lemma terminal_tight b :
 sideRLs mtm (xp 2 b) (dd *> 0inf) ((if b then db else da) *> dd1 *> 0inf).
Proof. destruct b; unfold xp; esc. Qed.

Lemma digits_terminal previous bs :
 sideRLs mtm (xp (length bs+2) previous) (shifted bs *> dd *> 0inf)
   ((if previous then db else da) *> normal bs *> dd1 *> 0inf).
Proof.
 rewrite <-(Str_app_assoc (if previous then db else da) (normal bs)).
 rewrite <-normal_lag, Str_app_assoc.
 eapply segRLs_sideRLs_concat.
 - apply digits_shift; lia.
 - apply terminal_tight.
Qed.

Open Scope nat.

Lemma shifted_terminal u bs :
 sideRLs mtm (p^^(2^(u+length bs+3)))
   (da^^u *> dc *> shifted bs *> dd *> 0inf)
   (da^^(u+1) *> db *> normal bs *> dd1 *> 0inf).
Proof.

 replace (da^^(u+1)) with (da^^u ++ da) by
   (rewrite lpow_add; cbn [lpow]; rewrite app_nil_r; reflexivity).
 rewrite Str_app_assoc.
 eapply @segRLs_sideRLs_concat with (ls2:=p^^(2^(length bs+3))).
 - applys_eq (d0s_Incs (2^(length bs+3)) u).
   repeat rewrite Nat.pow_add_r. flia.

 - eapply @segRLs_sideRLs_concat with (ls2:=xp (length bs+2) true).
   + unfold xp.
     assert (Hpow:2<=2^(length bs+2)).
     { rewrite Nat.pow_add_r. cbn [Nat.pow].
       pose proof (Nat.pow_nonzero 2 (length bs) ltac:(lia)); nia. }
     replace (length bs+3) with (S (length bs+2)) by lia.
     cbn [Nat.pow].
     applys_eq (shifted_even (2^(length bs+2)-1)); flia.

   + apply digits_terminal.
Qed.

Open Scope sym.
Lemma even_tight_wall u bs :
 let k := u+length bs+3 in
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1;1]^^k *> da^^u *> dc *> shifted bs *> dd *> 0inf)
 -[mtm]->+
 (0inf <* <[1;1]) <* [0] {{A}}>
   ([1] *> [1;1]^^k *> da^^(u+1) *> db *> normal bs *> dd1 *> 0inf).
Proof.
 cbn zeta. apply BigStep.
 eapply segRLs_sideRLs_concat.
 - apply lds_Incs'.
 - rewrite Nat.mul_1_l. apply shifted_terminal.
Qed.

Definition after n bs := W.wall ([1;1]^^n ++ [1] ++ W.normal (false::bs) ++ dd1).

Lemma tight_Ed_step n bs :
 (length bs+2=n)%nat -> In true bs ->
 W.Ed n bs -[mtm]->+ after n bs.
Proof.

 intros Hn Hin.
 destruct (first_true bs Hin) as [u [t E]]. subst bs.
 rewrite length_app, repeat_length in Hn. cbn [length] in Hn.
 assert (Hk:(n=u+length t+3)%nat) by lia.
 pose proof (even_tight_wall u t) as Hrun.
 cbn zeta in Hrun. rewrite <-Hk in Hrun.

 unfold W.Ed, after, W.wall.
 change W.shifted with shifted.
 change W.normal with normal.
 rewrite shifted_app, shifted_zeros.
 cbn [shifted normal].
 repeat rewrite normal_app.
 repeat rewrite normal_zeros.
 cbn [normal].
 applys_eq Hrun; ut; st; simpl_rotate;
 repeat rewrite <-const_unfold; reflexivity.
Qed.

Print Assumptions tight_Ed_step.
End TightEd.
End TightEd.

Module TightMarked.
(* Exact wall endpoints for a marked displaced digit with tight space.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import TightEd OddImage OddMarkedEntry TerminalClosure TightPrimer CDPasses CounterRules WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module TightMarked.
Module W := WallInvariant.WallInvariant.
Module TE := TightEd.TightEd.
Module I := OddImage.OddImage.
Module M := OddMarkedEntry.OddMarkedEntry.
Module TC := TerminalClosure.TerminalClosure.
Module TT := TightPrimer.TightPrimer.
Module CD := CDPasses.CDPasses.
Module CR := CounterRules.CounterRules.
Notation mtm := W.mtm.
Open Scope sym.
Notation one := [1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation endword := [1;0;0;1;0].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma marked_false bs : W.marked 1 bs -> W.marked 0 (false::bs).
Proof.

 intros [pre [post [E Hp]]].
 exists (false::pre),post. split.
 - cbn. rewrite E. reflexivity.
 - cbn[length]. replace (S (length pre)) with (length pre+1) by lia.
   rewrite Nat.add_mod by lia. rewrite Hp. reflexivity.
Qed.

Lemma marked_true bs : W.marked 1 bs -> In true bs.
Proof.

 intros [pre [post [E Hp]]]. rewrite E. apply in_or_app. right. cbn. auto.
Qed.

Lemma realign bs :
 r4 *> W.normal bs *> endword *> 0inf = one *> CD.third bs *> tight *> 0inf.
Proof.

 change (one *> z3 *> W.normal bs *> endword *> 0inf =
   one *> CD.third bs *> tight *> 0inf).
 rewrite <-(Str_app_assoc z3 (W.normal bs)),I.phase_three_word,Str_app_assoc.
 reflexivity.
Qed.

Lemma tight_marked_entry n bs :
 length bs+2=n -> W.marked 1 bs ->
 exists L k rest j,
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+3)-1<=k /\
 W.Ed n bs -[mtm]->+
 CR.LC L k |> one *> CD.third rest *> tight *> 0inf.
Proof.

 intros Hn Hmark.
 destruct (M.marked_entry n (false::bs) (endword *> 0inf)
    ltac:(eexists; reflexivity) (marked_false bs Hmark) ltac:(cbn[length]; lia))
   as [L [k [rest [j [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]].
 exists L,k,rest,j. cbn[length] in Hlen.
 repeat split; try assumption; try lia.
 rewrite <-realign.
 eapply progress_trans; [|exact Hrun].
 pose proof (TE.tight_Ed_step n bs Hn (marked_true bs Hmark)) as Hstep.
 unfold TE.after,W.wall,M.odd_wall in *.
 repeat rewrite Str_app_assoc in Hstep.
 exact Hstep.
Qed.

Lemma tight_marked_cases n bs :
 length bs+2=n -> W.marked 1 bs ->
 exists L k rest j q,
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k+1<2^L /\ k+1=2*(TT.demand rest+q) /\ q*4+3<2^(L+1) /\
 ((exists w, length rest=w*2 /\
   W.Ed n bs -[mtm]->+ TC.even_wall L (w*5+2) q /\
   W.invariant (TC.even_wall L (w*5+2) q)) \/
  (exists w, length rest=w*2+1 /\
   W.Ed n bs -[mtm]->+ TC.odd_wall L (w*5+6) q)).
Proof.

 intros Hn Hmark.
 destruct (tight_marked_entry n bs Hn Hmark)
   as [L [k [rest [j [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]].

 assert (Hdemand:2*TT.demand rest<=k+1).
 { unfold TT.demand. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (CD.value_bound rest). lia. }
 destruct (TC.tight_counter_cases L k rest ltac:(lia) Ho Hdemand)
   as [q [Heq [Hcoeff Hcases]]].
 exists L,k,rest,j,q. repeat split; try assumption.
 destruct Hcases as [[w [Hw [Hfinish Hinv]]]|[w [Hw Hfinish]]].
 - left. exists w. repeat split; try assumption.
   eapply progress_trans; eassumption.
 - right. exists w. split; [exact Hw|].
   eapply progress_trans; eassumption.
Qed.

Print Assumptions tight_marked_entry.
Print Assumptions tight_marked_cases.
End TightMarked.
End TightMarked.

Module ZeroDefect.
(* Converting a zero digit word with a displaced terminal digit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.DivModCases.
Import LocalPasses PhaseEd CounterRules CounterFinish CounterBits CounterBatch WallInvariant.
Import String List PeanoNat NArith Lia.
Import ListNotations.
Module ZeroDefect.
Module LP := LocalPasses.Mirrored.
Module PE := PhaseEd.PhaseEd.
Module CR := CounterRules.CounterRules.
Module CF := CounterFinish.CounterFinish.
Module CB := CounterBits.CounterBits.
Module Batch := CounterBatch.CounterBatch.
Module W := WallInvariant.WallInvariant.

Notation mtm := W.mtm.
Open Scope sym.
Notation da := [0;0;0;0;0].
Notation db := [1;0;0;0;0].
Notation dd := [0;0;0;1;0].
Notation dd1 := [1;0;0;1;0].
Notation p := [((A,[]),(B,[]))].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma shifted_zeros u : W.shifted (repeat false u) = da^^u.
Proof. induction u; cbn [repeat W.shifted lpow]; [reflexivity|].
 rewrite IHu. simpl_rotate. reflexivity. Qed.

Lemma zero_terminal : sideRLs mtm p (dd *> 0inf) (dd1 *> 0inf).
Proof. esc. Qed.

Lemma zero_preconversion u :
 sideRLs mtm (p^^(2^(u+1)-1)) (da^^u *> dd *> 0inf)
   (db^^u *> dd1 *> 0inf).
Proof.
 eapply segRLs_sideRLs_concat.
 - applys_eq (LP.d01s_Incs 1 u); rewrite Nat.pow_add_r; flia.
 - apply zero_terminal.
Qed.

Open Scope nat.
Lemma zero_remaining_bound n u : u+3<=n ->
 0<2^n-2^(u+1) /\ 2^n-2^(u+1)<2^n.
Proof.
 intro Hn.
 assert (2^(u+1)<2^n) by (apply Nat.pow_lt_mono_r; lia).
 pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)); lia.
Qed.

Lemma zero_remaining_decomposition n u : u+3<=n ->
 exists q, 2^n-2^(u+1)=(q*2+1)*2^(u+2)+2^(u+1).
Proof.
 intro Hn. set (d:=n-u-3).
 assert (He:n=u+3+d) by (unfold d; lia).
 pose proof (Nat.pow_nonzero 2 d ltac:(lia)).
 pose proof (Nat.pow_nonzero 2 u ltac:(lia)).
 exists (2^d-1). rewrite He at 1.
 repeat rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

Lemma zero_even_marker n a : a*2+3<=n ->
 W.marked 1 (CF.digits (n+a*5+1) (((2^n-2^(a*2+1))*2+1)*2^(a*5))).
Proof.

 intro Hn. destruct (mod2 a) as [b Hb|b Hb]; subst a.
 - destruct (zero_remaining_decomposition n (b*2*2) Hn) as [q Hq].
   pose proof (CB.marked_remainder (n+b*2*5+1)
      (((2^n-2^(b*2*2+1))*2+1)*2^(b*2*5)) (b*2*7+3) q
      ((2^(b*2*2+2)+1)*2^(b*2*5))) as Hmark.
   assert (Hpar:(b*2*7+3) mod 2=1).
   { replace (b*2*7+3) with ((b*7+1)*2+1) by lia.
     rewrite Nat.add_comm, Nat.mod_add by lia. reflexivity. }
   rewrite Hpar in Hmark. apply Hmark.

   + lia.
   + replace (b*2*7+3) with (b*2*5+(b*2*2+3)) by lia.
     repeat rewrite Nat.pow_add_r. cbn [Nat.pow].
     pose proof (Nat.pow_nonzero 2 (b*2*2) ltac:(lia)).
     pose proof (Nat.pow_nonzero 2 (b*2*5) ltac:(lia)). nia.
   + rewrite Hq. replace (b*2*7+3) with (b*2*5+(b*2*2+3)) by lia.
     repeat rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
 - apply CB.marked_shift_odd; [lia|].
   replace ((1+b*2)*5) with ((b*5+2)*2+1) by lia.
   rewrite Nat.add_comm, Nat.mod_add by lia. reflexivity.
Qed.

Open Scope sym.
Lemma zero_counter_entry n u : (u+3<=n)%nat ->
 W.Ed n (repeat false u) -[mtm]->*
 CR.LC n (2^n-2^(u+1)) |> db^^u *> dd1 *> 0inf.
Proof.
 intro Hn. unfold W.Ed, W.wall. rewrite shifted_zeros.
 repeat rewrite Str_app_assoc.
 eapply evstep_trans.
 - apply PE.even_wall_counter.
 - destruct (zero_remaining_bound n u Hn) as [Hpos Hb].
   replace (2^n-1)%nat with ((2^n-2^(u+1))+(2^(u+1)-1))%nat by
     (assert (2^(u+1)<2^n)%nat by (apply Nat.pow_lt_mono_r; lia); lia).
   apply Batch.right_pass_batch.
   + pose proof (Nat.pow_nonzero 2 (u+1) ltac:(lia)). lia.
   + apply zero_preconversion.
Qed.

Lemma zero_defect_invariant n u : (u+3<=n)%nat ->
 exists c, W.Ed n (repeat false u) -[mtm]->+ c /\ W.invariant c.
Proof.

 intro Hn. destruct (zero_remaining_bound n u Hn) as [Hpos Hb].
 destruct (mod2 u) as [a Hu|a Hu]; subst u.
 - eexists. split.
   + eapply evstep_progress_trans.
     * apply zero_counter_entry; exact Hn.
     * apply PE.gap2_even_wall; exact Hb.

   + replace (n+1+(a*5+1))%nat with ((n+a*5+1)+1)%nat by lia.
     replace (((2^n-2^(a*2+1))*2+1)*2^(a*5+1)+1)%nat with
       ((((2^n-2^(a*2+1))*2+1)*2^(a*5))*2+1)%nat by
       (repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
     apply CB.numeric_odd.
     * pose proof (PE.shifted_value_bound n (2^n-2^(a*2+1)) (a*5) Hb).
       replace (n+1+a*5)%nat with (n+a*5+1)%nat in H by lia. exact H.
     * apply zero_even_marker; exact Hn.

 - replace (1+a*2)%nat with (a*2+1)%nat in * by lia.
   eexists. split.
   + eapply evstep_progress_trans.
     * apply zero_counter_entry; exact Hn.
     * apply PE.gap2_odd_wall; exact Hb.
   + replace (((2^n-2^(a*2+1+1))*2+1)*2^(a*5+4))%nat with
       ((((2^n-2^(a*2+1+1))*2+1)*2^(a*5+3))*2)%nat by
       (replace (a*5+4)%nat with (a*5+3+1)%nat by lia;
        repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
     apply CB.numeric_even.
     * pose proof (Nat.pow_nonzero 2 (a*5+3) ltac:(lia)). nia.
     * replace ((((2^n-2^(a*2+1+1))*2+1)*2^(a*5+3))*2)%nat with
       (((2^n-2^(a*2+1+1))*2+1)*2^(a*5+4))%nat by
       (replace (a*5+4)%nat with (a*5+3+1)%nat by lia;
        repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
       apply PE.shifted_value_bound; exact Hb.
Qed.

Print Assumptions zero_defect_invariant.
End ZeroDefect.
End ZeroDefect.

Module ZeroEdOrbit.
(* Returning the zero-word defect branches to even walls.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import ZeroDefect PhaseEd EdEvenOrbit EdOddOrbit OddImage OddFuel OddRecursion.
Import CounterBits CounterFinish CounterRules MarkerArithmetic WallInvariant CDPasses.
Import List PeanoNat Lia.
Import ListNotations.

Module ZeroEdOrbit.
Module Z := ZeroDefect.ZeroDefect.
Module PE := PhaseEd.PhaseEd.
Module EO := EdEvenOrbit.EdEvenOrbit.
Module OO := EdOddOrbit.EdOddOrbit.
Module OI := OddImage.OddImage.
Module F := OddFuel.OddFuel.
Module R := OddRecursion.OddRecursion.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module MA := MarkerArithmetic.MarkerArithmetic.
Module W := WallInvariant.WallInvariant.
Module CD := CDPasses.CDPasses.
Notation mtm := W.mtm.
Open Scope nat.

Definition rank n m := 2^n-2^(m+1).

Lemma digits_ones n : CF.digits n (2^n-1)=repeat true n.
Proof.

 induction n; [reflexivity|].
 cbn[Nat.pow repeat].
 replace (2*2^n-1) with ((2^n-1)*2+1) by
   (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia).
 rewrite CF.digits_odd,IHn. reflexivity.
Qed.

Lemma digits_power_shift n v u :
 CF.digits (n+u) (v*2^u)=repeat false u++CF.digits n v.
Proof.

 induction u.
 - cbn[Nat.pow repeat app]. rewrite Nat.add_0_r,Nat.mul_1_r. reflexivity.
 - replace (n+S u) with (S (n+u)) by lia.
   cbn[Nat.pow repeat].
   replace (v*(2*2^u)) with ((v*2^u)*2) by nia.
   rewrite CF.digits_even,IHu. reflexivity.
Qed.

Lemma rank_digits n m : m+1<=n ->
 CF.digits n (rank n m)=repeat false (m+1)++repeat true (n-m-1).
Proof.

 intro Hn.

 assert (He:n=(n-m-1)+(m+1)) by lia.

 assert (Hrank:rank n m=(2^(n-m-1)-1)*2^(m+1)).
 { unfold rank. rewrite He at 1. rewrite Nat.pow_add_r.
   pose proof (Nat.pow_nonzero 2 (n-m-1) ltac:(lia)). nia. }
 rewrite Hrank.
 rewrite He at 1. rewrite digits_power_shift,digits_ones. reflexivity.
Qed.

Open Scope sym.
Notation ld := [1;1].
Notation z3 := [0;0;0].
Notation r4 := [1;0;0;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma zero_odd_exit n a : (a*2+4<=n)%nat ->
 W.Ed n (repeat false (a*2+1)) -[mtm]->+
 W.O (n+a*5+5)
   (repeat false (a*5+4)++true::CF.digits n (rank n (a*2+1))).
Proof.

 intro Hn.
 destruct (Z.zero_remaining_bound n (a*2+1) ltac:(lia)) as [Hpositive Hb].
 fold (rank n (a*2+1)) in Hb.
 pose proof (Z.zero_counter_entry n (a*2+1) ltac:(lia)) as Hentry.
 fold (rank n (a*2+1)) in Hentry.
 pose proof (PE.gap2_odd_wall n (rank n (a*2+1)) a Hb) as Hwall.

 assert (Hstart:W.Ed n (repeat false (a*2+1)) -[mtm]->+
   (0inf<*<[1;1])<*[0] {{A}}>
   ([1]*>ld^^(n+a*5+5)*>CR.RC ((rank n (a*2+1)*2+1)*2^(a*5+4)))).
 { replace (n+a*5+5)%nat with (n+1+(a*5+4))%nat by lia.
   eapply evstep_progress_trans; eassumption. }
 unfold W.O,W.wall. repeat rewrite Str_app_assoc.
 rewrite EO.normal_shift_odd by exact Hb.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.

Lemma zero_even_valuation n b : (4*b+4<=n)%nat ->
 exists out,
 (length out+2<=n+35*b+17)%nat /\ W.marked 1 out /\
 W.Ed n (repeat false (4*b+1)) -[mtm]->+ W.Ed (n+35*b+17) out.
Proof.

 intro Hn.
 destruct (Z.zero_remaining_bound n (4*b+1) ltac:(lia)) as [Hp Hk].
 fold (rank n (4*b+1)) in Hp,Hk.
 destruct (Z.zero_remaining_decomposition n (4*b+1) ltac:(lia)) as [q He].
 fold (rank n (4*b+1)) in He.

 assert (Hsmall:(2^(4*b+1+1)<2^(4*b+1+2))%nat)
   by (apply Nat.pow_lt_mono_r; lia).

 destruct (EO.even_image_marker (n+10*b+5) (5*b+2) n
   (rank n (4*b+1)) (4*b+1+2) q (2^(4*b+1+1))
   ltac:(lia) ltac:(lia) ltac:(lia) Hk ltac:(lia)
   ltac:(lia) Hsmall He) as [out [Hlen [Hmark Hrun]]].
 replace (n+10*b+5+(5*b+2)*5+2)%nat with (n+35*b+17)%nat in * by lia.
 exists out. split; [exact Hlen|]. split; [exact Hmark|].
 eapply progress_trans; [|exact Hrun].

 pose proof (zero_odd_exit n (b*2) ltac:(lia)) as Hexit.
 replace (b*2*2+1)%nat with (4*b+1)%nat in Hexit by lia.
 replace (n+b*2*5+5)%nat with (n+10*b+5)%nat in Hexit by lia.
 replace (b*2*5+4)%nat with ((5*b+2)*2)%nat in Hexit by lia.
 exact Hexit.
Qed.

Lemma zero_odd_valuation_entry n b : (4*b+6<=n)%nat ->
 W.Ed n (repeat false (4*b+3)) -[mtm]->+
 CR.LC (OO.initial_width n b) (OO.initial_rank n b) |>
 z3 *> W.normal (CF.digits n (rank n (4*b+3))) *> 0inf.
Proof.

 intro Hn.
 eapply progress_trans.

 - pose proof (zero_odd_exit n (b*2+1) ltac:(lia)) as Hexit.
   replace ((b*2+1)*2+1)%nat with (4*b+3)%nat in Hexit by lia.
   replace (n+(b*2+1)*5+5)%nat with (n+10*b+10)%nat in Hexit by lia.
   replace ((b*2+1)*5+4)%nat with ((5*b+4)*2+1)%nat in Hexit by lia.
   exact Hexit.
 - pose proof (R.initial_odd_entry (n+10*b+10) (5*b+4)
     (CF.digits n (rank n (4*b+3))) ltac:(lia)) as Hentry.
   replace ((5*b+4)*2+1)%nat with (10*b+9)%nat in Hentry by lia.
   replace ((5*b+4)*5+3)%nat with (25*b+23)%nat in Hentry by lia.

   replace (n+10*b+10+1+(25*b+23))%nat with (OO.initial_width n b) in Hentry by
     (unfold OO.initial_width; lia).
   replace ((5*b+4)*2+1)%nat with (10*b+9)%nat by lia.
   exact Hentry.
Qed.

Print Assumptions zero_even_valuation.
Print Assumptions zero_odd_valuation_entry.
End ZeroEdOrbit.
End ZeroEdOrbit.

Module StrongDigits.
(* Digit guards for the shifted counters produced by conversions.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import CounterBits CounterFinish CounterRules ZeroEdOrbit StrongInvariant WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongDigits.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module Z := ZeroEdOrbit.ZeroEdOrbit.
Module S := StrongInvariant.StrongInvariant.
Module W := WallInvariant.WallInvariant.
Open Scope nat.

Lemma shifted_digits n q u :
 CF.digits (n+u+1) ((q*2+1)*2^u)=repeat false u++true::CF.digits n q.
Proof.
 replace (n+u+1) with (Datatypes.S n+u) by lia.
 rewrite Z.digits_power_shift,CF.digits_odd. reflexivity.
Qed.

Lemma odd_shift_guard n q u : u mod 2=1 ->
 S.digit_guard (CF.digits (n+u+1) ((q*2+1)*2^u)).
Proof.
 intro H. rewrite shifted_digits. left.
 destruct (mod2 u) as [v E|v E]; subst u; [lia|].
 exists v,(CF.digits n q). f_equal. f_equal. lia.
Qed.

Lemma adjacent_shift_guard n q u : 0<u ->
 S.digit_guard (CF.digits (n+u+2) ((q*4+3)*2^u)).
Proof.
 intro Hu.
 replace (q*4+3) with ((q*2+1)*2+1) by lia.
 replace (n+u+2) with ((n+1)+u+1) by lia.
 rewrite shifted_digits.
 replace (n+1) with (Datatypes.S n) by lia.
 rewrite CF.digits_odd. right. left.
 exists u,(CF.digits n q). split; [exact Hu|reflexivity].
Qed.

Lemma digits_true_at width v i q :
 i<width -> v/2^i=q*2+1 -> nth i (CF.digits width v) false=true.
Proof.
 intros Hi Hq.
 rewrite (CB.digits_split width i v) by lia.
 rewrite app_nth2 by (rewrite CF.digits_length; lia).
 rewrite CF.digits_length,Nat.sub_diag,Hq.
 replace (width-i) with (Datatypes.S (width-i-1)) by lia.
 rewrite CF.digits_odd. reflexivity.
Qed.

Lemma digits_bit_remainder width v i q r :
 i<width -> r<2^i -> v=(q*2+1)*2^i+r ->
 nth i (CF.digits width v) false=true.
Proof.
 intros Hi Hr Hv. apply (digits_true_at width v i q Hi).
 rewrite Hv,Nat.add_comm,Nat.div_add by (apply Nat.pow_nonzero; lia).
 rewrite Nat.div_small by exact Hr. lia.
Qed.

Lemma close_shift_guard n q a i : 0<a ->
 nth i (CF.digits (n+10*a+1) ((q*2+1)*2^(10*a))) false=true ->
 i mod 2=1 -> i<=14*a+3 ->
 S.digit_guard (CF.digits (n+10*a+1) ((q*2+1)*2^(10*a))).
Proof.
 intros Ha Hi Hp Hb. right. right.
 exists a,(CF.digits n q),i. repeat split; try assumption.
 apply shifted_digits.
Qed.

Open Scope sym.
Lemma odd_counter_wall n v : (v<2^n)%nat ->
 (0inf<*<[1;1])<*[0] {{A}}> ([1]*>[1;1]^^(n+1)*>CR.RC (v*2+1))=
 W.E (n+2) (CF.digits n v).
Proof.

 intro Hv. unfold CR.RC. rewrite BinInc_mul2add1.
 change ((0inf<*<[1;1])<*[0] {{A}}>
   ([1]*>[1;1]^^(n+1)*>[1;0;0;0;0]*>CR.RC v)=W.E (n+2) (CF.digits n v)).
 rewrite <-(CF.digits_normal n v Hv).
 replace ([1]*>[1;1]^^(n+1)*>[1;0;0;0;0]*>W.normal(CF.digits n v)*>0inf)
   with ([1;1]^^(n+2)*>[0;0;0;0]*>W.normal(CF.digits n v)*>0inf)
   by (replace (n+2)%nat with ((n+1)+1)%nat by lia; st; simpl_rotate; reflexivity).
 rewrite CB.shifted_normal. unfold W.E,W.wall. rewrite Str_app_assoc. reflexivity.
Qed.

Print Assumptions odd_shift_guard.
Print Assumptions adjacent_shift_guard.
Print Assumptions odd_counter_wall.
End StrongDigits.
End StrongDigits.

Module TightTrace.
(* Tight displaced walls with their exact conversion path retained.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import TightEd TightMarked MarkedTrace OddMarkedEntry TerminalClosure TightPrimer.
Import TerminalSuccessor StrongInvariant StrongDigits BlankPasses CounterFinish.
Import CDPasses CounterRules WallInvariant.
Import String List PeanoNat Lia.

Import ListNotations.

Module TightTrace.
Module W := WallInvariant.WallInvariant.
Module TE := TightEd.TightEd.
Module TM := TightMarked.TightMarked.
Module M := MarkedTrace.MarkedTrace.
Module ME := OddMarkedEntry.OddMarkedEntry.
Module TC := TerminalClosure.TerminalClosure.
Module TS := TerminalSuccessor.TerminalSuccessor.
Module TT := TightPrimer.TightPrimer.

Module S := StrongInvariant.StrongInvariant.
Module SD := StrongDigits.StrongDigits.
Module BP := BlankPasses.BlankPasses.
Module CF := CounterFinish.CounterFinish.
Module CD := CDPasses.CDPasses.
Module CR := CounterRules.CounterRules.
Notation mtm := W.mtm.
Open Scope sym.
Notation one := [1].
Notation r4 := [1;0;0;0].
Notation endword := [1;0;0;1;0].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma terminal_even_strong L s q :
 0<s -> q*4+3<2^(L+1) -> S.strong (TC.even_wall L s q).
Proof.

 intros Hs Hcoeff.
 destruct (TS.coefficient_parts L q Hcoeff) as [HL Hrest].

 assert (Hvalue:(q*4+3)*2^s<2^(L+s+1)).
 { replace (L+s+1) with ((L+1)+s) by lia. rewrite Nat.pow_add_r.
   pose proof (Nat.pow_nonzero 2 s ltac:(lia)). nia. }

 assert (Hwall:TC.even_wall L s q=
   W.E (L+s+3) (CF.digits (L+s+1) ((q*4+3)*2^s))).
 { unfold TC.even_wall,W.E,W.wall. rewrite Str_app_assoc.
   rewrite BP.digits_shifted by exact Hvalue. reflexivity. }
 rewrite Hwall. constructor.
 - rewrite CF.digits_length. lia.
 - replace (L+s+1) with ((L-1)+s+2) by lia.
   apply SD.adjacent_shift_guard. exact Hs.
Qed.

Lemma tight_entry n bs :
 length bs+2=n -> W.marked 1 bs ->
 exists L k rest j,
 M.wall_route n (false::bs) L k rest /\
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k mod 2=1 /\ k+1<2^L /\ 2^(length rest+4)-1<=k /\
 W.Ed n bs -[mtm]->+
 CR.LC L k |> one *> CD.third rest *> tight *> 0inf.
Proof.

 intros Hn Hmark.
 destruct (M.marked_entry_trace n (false::bs) (endword *> 0inf)
   ltac:(eexists; reflexivity) (TM.marked_false bs Hmark)
   ltac:(cbn[length]; lia))
   as [L [k [rest [j [Hroute [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]]].
 exists L,k,rest,j. cbn[length] in Hlen.
 repeat split; try assumption; try lia.
 rewrite <-TM.realign.
 eapply progress_trans; [|exact Hrun].
 pose proof (TE.tight_Ed_step n bs Hn (TM.marked_true bs Hmark)) as Hstep.
 unfold TE.after,W.wall,ME.odd_wall in *.
 repeat rewrite Str_app_assoc in Hstep. exact Hstep.
Qed.

Lemma tight_cases n bs :
 length bs+2=n -> W.marked 1 bs ->
 exists L k rest j q,
 M.wall_route n (false::bs) L k rest /\
 length bs=2*j+length rest /\ L=n+5*j+1 /\
 k+1<2^L /\ 2^(length rest+4)-1<=k /\
 k+1=2*(TT.demand rest+q) /\ 0<q /\ q*4+3<2^(L+1) /\
 ((exists w, length rest=w*2 /\
   W.Ed n bs -[mtm]->+ TC.even_wall L (w*5+2) q /\
   S.strong (TC.even_wall L (w*5+2) q)) \/
  (exists w, length rest=w*2+1 /\
   W.Ed n bs -[mtm]->+ TC.odd_wall L (w*5+6) q)).
Proof.

 intros Hn Hmark.
 destruct (tight_entry n bs Hn Hmark)
   as [L [k [rest [j [Hroute [Hlen [HL [Ho [Hb [Hmin Hrun]]]]]]]]]].

 assert (Hdemand:2*TT.demand rest<=k+1).
 { unfold TT.demand. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (CD.value_bound rest). lia. }
 destruct (TC.tight_counter_cases L k rest ltac:(lia) Ho Hdemand)
   as [q [Heq [Hcoeff Hcases]]].

 assert (Hq:0<q).
 { unfold TT.demand in Heq.
   rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia)). nia. }
 exists L,k,rest,j,q. repeat split; try assumption.
 destruct Hcases as [[w [Hw [Hfinish Hinv]]]|[w [Hw Hfinish]]].
 - left. exists w. repeat split; try assumption.
   + eapply progress_trans; eassumption.
   + apply terminal_even_strong; lia.
 - right. exists w. split; [exact Hw|].
   eapply progress_trans; eassumption.
Qed.

Print Assumptions terminal_even_strong.
Print Assumptions tight_cases.
End TightTrace.
End TightTrace.

Module StrongE.
(* The guarded shifted-digit wall returns to a guarded wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3 BusyCoq.DivModCases.
Import StrongInvariant GuardedRoute OdStrongMarker PhaseE MarkedTrace OddMarkedEntry.
Import TerminalClosure TerminalSuccessor TerminalLoose TightTrace OddDefectTail OddDefectFinish.
Import CounterRules CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongE.
Module S := StrongInvariant.StrongInvariant.
Module G := GuardedRoute.GuardedRoute.
Module SM := OdStrongMarker.OdStrongMarker.
Module PE := PhaseE.PhaseE.
Module M := MarkedTrace.MarkedTrace.

Module ME := OddMarkedEntry.OddMarkedEntry.
Module TC := TerminalClosure.TerminalClosure.
Module TS := TerminalSuccessor.TerminalSuccessor.
Module TL := TerminalLoose.TerminalLoose.
Module TT := TightTrace.TightTrace.
Module T := OddDefectTail.OddDefectTail.
Module F := OddDefectFinish.OddDefectFinish.

Module CR := CounterRules.CounterRules.
Module CD := CDPasses.CDPasses.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.
Open Scope sym.
Notation one := [1].
Notation z3 := [0;0;0].

Notation dc := [0;0;0;0;1].
Notation defect := [0;0;0;0;0;0;0;1].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma demand_bound bs : T.demand bs<=6*2^length bs.
Proof.

 unfold T.demand. destruct (Nat.eqb (CD.value bs) 0).
 - rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
 - lia.
Qed.

Lemma converted_bounds bs :
 length bs+1<=T.converted_digits bs<=length bs+2.
Proof. unfold T.converted_digits. destruct (Nat.eqb (CD.value bs) 0); lia. Qed.

Lemma ordinary_successor L rest j delta q w :
 L=length rest+7*j+3 -> G.good_deficit j delta ->
 2*(T.demand rest+q)+delta=2^L ->
 0<q -> q*4+3<2^(L+1) -> T.converted_digits rest=w*2+1 ->
 exists out, TC.odd_wall L (w*5+4) q -[mtm]->+ out /\ S.strong out.
Proof.

 intros HL HG Hcap Hq Hcoeff Hg.
 pose proof (SM.good_positive j delta HG) as Hj.
 pose proof (converted_bounds rest) as Hgb.
 pose proof (F.demand_positive rest) as HT.
 pose proof (demand_bound rest) as HTb.
 assert (HL3:3<=L) by (clear -HL;lia).

 destruct (mod2 w) as [a Ha|a Ha]; subst w.
 - replace (a*2*5+4) with ((5*a+2)*2) by lia.
   destruct (TS.ordinary_even_image L (5*a+2) q ltac:(lia) Hcoeff)
    as [out [Hlen [Hlower [Hupper [Hmass Hrun]]]]].
   exists (W.Ed (L+(5*a+2)*7+3) out). split; [exact Hrun|].
   apply S.StrongEd; [exact Hlen|].
   destruct Hlen as [Hlo|Hti].

   + apply (TL.even_loose_marker L (5*a+2) q out); try assumption; lia.
   + apply (SM.even_tight_marker out L q j delta (length rest) a (T.demand rest)); try assumption.
     clear -Hgb Hg. lia.
 - replace ((1+a*2)*5+4) with ((5*a+4)*2+1) by lia.
   destruct (TS.ordinary_odd_image L (5*a+4) q Hq Hcoeff)
    as [out [Hlen [Hlower [Hupper [Hmass Hrun]]]]].
   exists (W.Ed (L+(5*a+4)*7+9) out). split; [exact Hrun|].
   apply S.StrongEd; [exact Hlen|].
   destruct Hlen as [Hlo|Hti].

   + apply (TL.odd_loose_marker L (5*a+4) q out); assumption.
   + apply (SM.odd_tight_marker out L q j delta (length rest) a (T.demand rest)); try assumption.
     clear -Hgb Hg. lia.
Qed.

Lemma defect_entry n bs L k rest :
 M.wall_route n bs L k rest -> length bs+1<=n ->
 W.Od n bs -[mtm]->+ CR.LC L k |> one *> CD.third rest *> defect *> 0inf.
Proof.

 intros Hr Hn.
 pose proof (M.route_run n bs L k rest (dc *> 0inf) Hr Hn) as Hrun.
 assert (Hwall:ME.odd_wall n bs (dc *> 0inf)=W.Od n bs).
 { unfold ME.odd_wall,W.Od,W.wall. repeat rewrite Str_app_assoc. reflexivity. }
 rewrite Hwall in Hrun.
 change (W.Od n bs -[mtm]->+ CR.LC L k |> one *> z3 *> W.normal rest *> dc *> 0inf) in Hrun.
 rewrite F.third_normal_side in Hrun. exact Hrun.
Qed.

Lemma defect_strong n bs :
 length bs+1=n -> W.first_zero bs -> G.source_data n bs ->
 exists out, W.Od n bs -[mtm]->+ out /\ S.strong out.
Proof.

 intros Hfull Hzero [L [k [rest [j [delta [Hr [Hdim [HL [HD HG]]]]]]]]].
 assert (Hn:length bs+1<=n) by lia.
 assert (HLfull:L=length rest+7*j+3) by (clear -Hfull Hdim HL;lia).
 destruct (M.route_bounds n bs L k rest Hr Hzero Hn) as [Hk Ho].
 pose proof (M.route_margin4 n bs L k rest Hr Hzero Hn) as Hmin.
 pose proof (defect_entry n bs L k rest Hr Hn) as Hentry.

 pose proof (demand_bound rest) as HTb.
 assert (Hpow:0<2^length rest) by (pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia));lia).
 assert (Hb:2*T.demand rest<=k+1).
 { rewrite (Nat.pow_add_r 2 (length rest) 4) in Hmin. cbn[Nat.pow] in Hmin. lia. }
 destruct (TC.defect_counter_cases L k rest ltac:(lia) Ho Hb)
   as [q [Hbudget [Hcoeff Hcases]]].
 assert (Hq:0<q).
 { rewrite (Nat.pow_add_r 2 (length rest) 4) in Hmin. cbn[Nat.pow] in Hmin. lia. }

 destruct Hcases as [[w [Hg [Hfinish Hold]]]|[w [Hg Hfinish]]].
 - exists (TC.even_wall L (w*5) q). split.
   + eapply progress_trans; eassumption.
   + apply TT.terminal_even_strong; [|exact Hcoeff].
     pose proof (converted_bounds rest). lia.
 - destruct (ordinary_successor L rest j delta q w HLfull HG
      ltac:(clear -HD Hbudget;lia) Hq Hcoeff Hg) as [out [Hnext Hstrong]].
   exists out. split; [|exact Hstrong].
   eapply progress_trans; [exact Hentry|].
   eapply progress_trans; eassumption.
Qed.

Lemma strong_E n bs :
 length bs+2<=n -> S.digit_guard bs ->
 exists out, W.E n bs -[mtm]->+ out /\ S.strong out.
Proof.

 intros Hn HG.
 set (padded:=bs++repeat false (n-length bs-2)).
 assert (Hp:length padded+2=n).
 { unfold padded. rewrite length_app,repeat_length. lia. }
 assert (Hpguard:S.digit_guard padded) by (apply S.guard_append; exact HG).
 pose proof (G.guard_source n padded ltac:(lia) Hpguard) as Hdata.

 assert (Hbits:PE.output_bits n bs=false::padded) by reflexivity.
 assert (Htrue:In true bs).
 { destruct (S.guard_marked bs HG) as [pre [post [E Hparity]]].
   rewrite E. apply in_or_app. right. cbn. auto. }
 destruct (defect_strong n (false::padded) ltac:(cbn[length];lia)
   ltac:(exists padded;reflexivity) Hdata) as [out [Hnext Hstrong]].
 exists out. split; [|exact Hstrong].

 eapply progress_trans; [apply PE.phase_E; eassumption|].
 rewrite Hbits. exact Hnext.
Qed.

Print Assumptions ordinary_successor.
Print Assumptions defect_strong.
Print Assumptions strong_E.
End StrongE.
End StrongE.

Module StrongEdDirect.
(* The direct conversion of an odd-length displaced digit word.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import PhaseEd StrongDigits StrongInvariant CounterFinish CounterRules WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongEdDirect.
Module PE := PhaseEd.PhaseEd.
Module SD := StrongDigits.StrongDigits.
Module S := StrongInvariant.StrongInvariant.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.
Open Scope nat.

Lemma direct_guard n bs a :
 length bs+1=a*2 -> length bs+3<=n ->
 S.digit_guard (CF.digits (n+a*5+1)
   (((2^n-PE.fuel bs-3)*2+1)*2^(a*5))).
Proof.

 intros Hlen Hn.
 set (k:=2^n-PE.fuel bs-3).
 destruct (mod2 a) as [b Ha|b Ha].
 - subst a.
   replace (b*2*5) with (10*b) by lia.
   apply (SD.close_shift_guard n k b (14*b+1)); try lia.
   destruct (PE.remaining_decomposition n bs Hn) as [q Hk].
   fold k in Hk.
   replace (length bs+1) with (4*b) in Hk by lia.
   apply (SD.digits_bit_remainder (n+10*b+1)
     ((k*2+1)*2^(10*b)) (14*b+1) q ((PE.value bs*4+1)*2^(10*b)));
     try lia.

   + pose proof (PE.value_bound bs) as Hv.
     assert (Hp:2^(length bs+1)=2^(4*b)) by (f_equal; lia).
     rewrite Nat.pow_add_r in Hp. cbn[Nat.pow] in Hp.
     replace (14*b+1) with ((4*b+1)+10*b) by lia.
     rewrite Nat.pow_add_r,(Nat.pow_add_r 2 (4*b) 1). cbn[Nat.pow].
     pose proof (Nat.pow_nonzero 2 (10*b) ltac:(lia)). nia.
   + replace (14*b+1) with ((4*b+1)+10*b) by lia.
     rewrite Nat.pow_add_r,(Nat.pow_add_r 2 (4*b) 1). cbn[Nat.pow].
     nia.
 - apply SD.odd_shift_guard. lia.
Qed.

Open Scope sym.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma Ed_direct_strong n bs a :
 (length bs+1=a*2)%nat -> (length bs+3<=n)%nat -> W.marked 1 bs ->
 exists c, W.Ed n bs -[mtm]->+ c /\ S.strong c.
Proof.

 intros Hlen Hn Hmark.
 assert (Hin:In true bs).
 { destruct Hmark as [pre [post [E Hp]]]. rewrite E.
   apply in_or_app. right. cbn. auto. }
 set (k:=(2^n-PE.fuel bs-3)%nat).
 assert (Hk:(k<2^n)%nat) by (unfold k; apply PE.remaining_bound; exact Hn).
 pose proof (PE.nonzero_counter_entry n bs Hn Hin) as Hentry.
 fold k in Hentry. rewrite Hlen in Hentry.
 pose proof (PE.gap2_even_wall n k a Hk) as Hwall.
 set (v:=((k*2+1)*2^(a*5))%nat).
 assert (Hv:(v<2^(n+a*5+1))%nat).
 { unfold v. replace (n+a*5+1)%nat with (n+1+a*5)%nat by lia.
   apply PE.shifted_value_bound. exact Hk. }

 assert (Heq:((k*2+1)*2^(a*5+1)+1=v*2+1)%nat).
 { unfold v. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }
 rewrite Heq in Hwall.
 replace (n+1+(a*5+1))%nat with ((n+a*5+1)+1)%nat in Hwall by lia.
 rewrite (SD.odd_counter_wall (n+a*5+1) v Hv) in Hwall.
 exists (W.E (n+a*5+1+2) (CF.digits (n+a*5+1) v)). split.
 - eapply evstep_progress_trans; eassumption.
 - apply S.StrongE; [rewrite CF.digits_length; lia|].
   unfold v,k. apply direct_guard; assumption.
Qed.

Print Assumptions direct_guard.
Print Assumptions Ed_direct_strong.
End StrongEdDirect.
End StrongEdDirect.

Module StrongEdEven.
(* Exact amplifier slack in the even-valuation defect branch.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2.
Import PhaseEd OddImage EdEvenOrbit CounterBits CounterFinish CounterRules.
Import MarkerArithmetic WallInvariant CDPasses TerminalSuccessor StrongInvariant.
Import List PeanoNat Lia.
Import ListNotations.

Module StrongEdEven.
Module PE := PhaseEd.PhaseEd.
Module OI := OddImage.OddImage.
Module EO := EdEvenOrbit.EdEvenOrbit.
Module CD := CDPasses.CDPasses.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module MA := MarkerArithmetic.MarkerArithmetic.
Module W := WallInvariant.WallInvariant.
Module TS := TerminalSuccessor.TerminalSuccessor.
Module S := StrongInvariant.StrongInvariant.
Notation mtm := W.mtm.
Open Scope sym.
Notation ld := [1;1].

Lemma even_image_exact n v width k i q r :
 (0<v)%nat -> (v*2+2<=n)%nat -> (width<=n)%nat -> (k<2^width)%nat ->
 (i<v*5-1)%nat -> (i mod 2=1)%nat -> (r<2^i)%nat ->
 (k=(q*2+1)*2^i+r)%nat ->
 exists out,
 ((length out+3=n+v*5+2)%nat \/ (length out+2=n+v*5+2)%nat) /\ W.marked 1 out /\
 W.O n (repeat false (v*2)++true::CF.digits width k) -[mtm]->+
 W.Ed (n+v*5+2) out.
Proof.

 intros Hv Hn Hw Hk Hi Hodd Hr Hdecomp.
 destruct (EO.first_mass_bounds n v width k Hv Hn Hw Hk) as [Hmin Hmax].
 assert (Hlength:(width+(n+v*5+1-width)=n+v*5+1)%nat) by lia.
 assert (Hvalue:CD.value (CF.digits width k)=k).
 { change (CB.value (CF.digits width k)=k). apply CB.digits_value; exact Hk. }
 assert (Hmin':(2^length (CF.digits width k)<=OI.first_mass n v)%nat).
 { rewrite CF.digits_length. exact Hmin. }
 assert (Hmax':(OI.first_mass n v+CD.value (CF.digits width k)<
   2^(length (CF.digits width k)+(n+v*5+1-width)))%nat).
 { rewrite CF.digits_length,Hvalue,Hlength. exact Hmax. }

 destruct (OI.initial_even_image n v (CF.digits width k)
   (n+v*5+1-width) Hv ltac:(lia) Hmin' Hmax')
   as [out [Hlen [Hval Hrun]]].
 rewrite CF.digits_length,Hlength in Hlen.
 rewrite Hvalue in Hval.
 assert (Hnonzero:(k<>0)%nat).
 { pose proof (Nat.pow_nonzero 2 i ltac:(lia)). nia. }
 assert (Hany:CD.any (CF.digits width k)=true).
 { apply EO.any_true. apply CB.value_nonzero. rewrite CB.digits_value by exact Hk.
   exact Hnonzero. }
 rewrite Hany in Hrun. cbn [CD.terminal] in Hrun.

 assert (Hlower:(2^(n+v*5-1)<=OI.first_mass n v+k)%nat).
 { pose proof (TS.first_mass_lower n v Hv Hn). lia. }
 assert (Hupper:(OI.first_mass n v+k<2^((n+v*5-1)+2))%nat).
 { replace (n+v*5-1+2)%nat with (n+v*5+1)%nat by lia. exact Hmax. }
 pose proof (TS.mass_length out (n+v*5-1) (OI.first_mass n v+k)
   Hval Hlower Hupper) as Hsizes.
 exists out. split; [lia|]. split.
 - rewrite <-Hodd.
   apply (MA.low_marker_preserved out k i q r (v*5-1)
     (2*OI.first_fuel n (v*2)+1)); try lia.
   change (CB.value out+2^length out=OI.first_mass n v+k)%nat in Hval.
   exact Hval.
 - exact Hrun.
Qed.

Lemma Ed_even_valuation_exact n bs b :
 (length bs=4*b)%nat -> (length bs+3<=n)%nat -> In true bs ->
 exists out,
 ((length out+3=n+35*b+17)%nat \/ (length out+2=n+35*b+17)%nat) /\ W.marked 1 out /\
 W.Ed n bs -[mtm]->+ W.Ed (n+35*b+17) out.
Proof.

 intros Hlength Hn Hin.
 set (k:=(2^n-PE.fuel bs-3)%nat).
 assert (Hk:(k<2^n)%nat) by (unfold k; apply PE.remaining_bound; exact Hn).
 destruct (PE.remaining_decomposition n bs Hn) as [q Hdecomp].
 fold k in Hdecomp. rewrite Hlength in Hdecomp.
 pose proof (PE.value_bound bs) as Hsmall. rewrite Hlength in Hsmall.
 assert (Hr:(2*PE.value bs<2^(4*b+1))%nat).
 { rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }

 destruct (even_image_exact (n+10*b+5) (5*b+2) n k (4*b+1) q
   (2*PE.value bs) ltac:(lia) ltac:(lia) ltac:(lia) Hk ltac:(lia)
   ltac:(rewrite Nat.add_mod, Nat.mul_mod by lia; reflexivity) Hr Hdecomp)
   as [out [Hlen [Hmark Hrun]]].
 replace (n+10*b+5+(5*b+2)*5+2)%nat with (n+35*b+17)%nat in * by lia.
 exists out. split; [exact Hlen|]. split; [exact Hmark|].
 eapply progress_trans; [|exact Hrun].

 pose proof (PE.nonzero_counter_entry n bs Hn Hin) as Hentry.
 fold k in Hentry.
 replace (length bs+1)%nat with ((b*2)*2+1)%nat in Hentry by lia.
 pose proof (PE.gap2_odd_wall n k (b*2) Hk) as Hwall.

 assert (Hstart:W.Ed n bs -[mtm]->+
   (0inf <* <[1;1]) <* [0] {{A}}>
     ([1] *> ld^^(n+10*b+5) *> CR.RC ((k*2+1)*2^((5*b+2)*2)))).
 { replace (n+10*b+5)%nat with (n+1+((b*2)*5+4))%nat by lia.
   replace ((5*b+2)*2)%nat with ((b*2)*5+4)%nat by lia.
   eapply evstep_progress_trans; eassumption. }
 unfold W.O,W.wall.
 repeat rewrite Str_app_assoc.
 rewrite EO.normal_shift_odd by exact Hk.
 applys_eq Hstart; ut; st; simpl_rotate; reflexivity.
Qed.


Lemma Ed_even_strong n bs b :
 (length bs=4*b)%nat -> (length bs+3=n)%nat -> W.marked 1 bs ->
 exists c, W.Ed n bs -[mtm]->+ c /\ S.strong c.
Proof.
 intros Hlen Hn Hmark.
 assert (Hin:In true bs).
 { destruct Hmark as [pre [post [E Hp]]]. rewrite E.
   apply in_or_app. right. cbn. auto. }
 destruct (Ed_even_valuation_exact n bs b Hlen ltac:(lia) Hin)
   as [out [Hslack [Hmarker Hrun]]].
 exists (W.Ed (n+35*b+17) out). split; [exact Hrun|].
 apply S.StrongEd; assumption.
Qed.
Print Assumptions Ed_even_strong.
End StrongEdEven.
End StrongEdEven.

Module EdOddBounds.
(* Arithmetic bounds for the odd branch of a displaced-digit wall.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddOrbit PhaseEd OddImage OddFuel OddRoute RouteDeficit.
Import CounterBits CounterFinish WallInvariant CDPasses RouteMarkerBound.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddBounds.
Module EO := EdOddOrbit.EdOddOrbit.
Module PE := PhaseEd.PhaseEd.
Module OI := OddImage.OddImage.
Module F := OddFuel.OddFuel.
Module R := OddRoute.OddRoute.
Module RD := RouteDeficit.RouteDeficit.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CD := CDPasses.CDPasses.
Module W := WallInvariant.WallInvariant.
Open Scope nat.

Lemma digits_true_at width value i q :
 i<width -> value/2^i=q*2+1 -> nth i (CF.digits width value) false=true.
Proof.
 intros Hi Hq.
 rewrite (CB.digits_split width i value) by lia.
 rewrite app_nth2 by (rewrite CF.digits_length; lia).
 rewrite CF.digits_length,Nat.sub_diag,Hq.
 replace (width-i) with (S (width-i-1)) by lia.
 rewrite CF.digits_odd. reflexivity.
Qed.

Lemma source_even_bit n bs : length bs+5<=n ->
 nth (length bs+4) (CF.digits n (EO.source_rank n bs)) false=true.
Proof.

 intro Hn.
 set (m:=length bs). set (d:=n-m-5).
 assert (He:n=m+5+d) by (unfold d,m; lia).
 pose proof (PE.fuel_value bs) as Hfuel.
 pose proof (PE.value_bound bs) as Hv.
 pose proof (PE.fuel_fits n bs ltac:(lia)) as Hfits.
 fold m in Hfuel,Hv.
 assert (Hp:0<2^m) by (pose proof (Nat.pow_nonzero 2 m ltac:(lia)); lia).
 assert (Hd:0<2^d) by (pose proof (Nat.pow_nonzero 2 d ltac:(lia)); lia).

 assert (Hbig:2^n=2^m*32*2^d).
 { rewrite He. rewrite !Nat.pow_add_r. reflexivity. }
 assert (Hbit:2^(m+4)=2^m*16) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Hsmall:10*2^m+2*PE.value bs<2^(m+4)) by (rewrite Hbit; nia).
 assert (Hdecomp:EO.source_rank n bs=
   ((2^d-1)*2+1)*2^(m+4)+(10*2^m+2*PE.value bs)).
 { unfold EO.source_rank. rewrite Hbig,Hbit in *. nia. }

 apply (digits_true_at n (EO.source_rank n bs) (m+4) (2^d-1)); [lia|].
 rewrite Hdecomp,Nat.add_comm,Nat.div_add by (apply Nat.pow_nonzero; lia).
 rewrite Nat.div_small by exact Hsmall. lia.
Qed.

Lemma first_deficit n u z : u+1<=n ->
 F.grown (OI.first_fuel n u) z+(2^(u+2)-3)*2^z+1=2^(n+1+z).
Proof.

 intro Hn. destruct (OI.first_fuel_bounds n u Hn) as [He Hb].
 assert (Hp:0<2^u) by (pose proof (Nat.pow_nonzero 2 u ltac:(lia)); lia).
 assert (Hz:0<2^z) by (pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia).
 assert (Hu:2^(u+2)=2^u*4) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Htotal:2^(n+1+z)=2^n*2*2^z).
 { rewrite !Nat.pow_add_r. reflexivity. }
 unfold F.grown. rewrite Hu,Htotal. nia.
Qed.

Lemma initial_deficit n (bs:list bool) b : length bs=4*b+2 -> length bs+3<=n ->
 EO.initial_rank n b+(2^(10*b+11)-3)*2^(25*b+23)+1=
   2^(EO.initial_width n b).
Proof.
 intros Hm Hn. unfold EO.initial_rank,EO.initial_width.
 replace (10*b+11) with ((10*b+9)+2) by lia.
 replace (n+35*b+34) with ((n+10*b+10)+1+(25*b+23)) by lia.
 apply first_deficit. lia.
Qed.

Lemma marked_drop_pair bs : W.marked 1 (false::false::bs) -> W.marked 1 bs.
Proof.
 intros [pre [post [E Hp]]].
 destruct pre as [|a [|a' pre]]; try discriminate E.
 inversion E; subst.
 exists pre,post. split; [reflexivity|].
 cbn [length] in Hp.
 replace (S (S (length pre))) with (length pre+1*2) in Hp by lia.
 rewrite Nat.mod_add in Hp by lia. exact Hp.
Qed.

Lemma marked_drop_even_zeros s bs :
 W.marked 1 (repeat false (s*2)++bs) -> W.marked 1 bs.
Proof.
 induction s; intro H; [exact H|].
 replace (S s*2) with (S (S (s*2))) in H by lia.
 cbn [repeat app] in H.
 apply IHs. apply marked_drop_pair. exact H.
Qed.

Print Assumptions source_even_bit.
Print Assumptions initial_deficit.
Print Assumptions marked_drop_even_zeros.
End EdOddBounds.
End EdOddBounds.

Module EdOddTight.
(* The low marker survives an overflowing odd-gap conversion route.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddBounds EdOddOrbit PhaseEd OddRoute RouteDeficit RouteMarkerBound.
Import CounterBits CounterFinish WallInvariant CDPasses GapMarker.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddTight.
Module E := EdOddOrbit.EdOddOrbit.
Module B := EdOddBounds.EdOddBounds.
Module PE := PhaseEd.PhaseEd.
Module R := OddRoute.OddRoute.
Module RD := RouteDeficit.RouteDeficit.
Module RB := RouteMarkerBound.RouteMarkerBound.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CD := CDPasses.CDPasses.
Module W := WallInvariant.WallInvariant.
Module GM := GapMarker.GapMarker.
Open Scope nat.

Lemma value_zeros n : CD.value (repeat false n)=0.
Proof. induction n; cbn [repeat CD.value CD.bitval]; lia. Qed.

Lemma correction_small b j e v w :
 2*j<=4*b+6 -> e<2^(7*j+3) -> v<2^(4*b+2) -> w<2^(2*j+1) ->
 let c:=e*2^(2*j+1)+12*2^(4*b+2)+2*w-4*v in
 0<c /\ c<2^((25*b+7*j+26)-2) /\
 c+4*v=e*2^(2*j+1)+12*2^(4*b+2)+2*w.
Proof.

 intros Hj He Hv Hw. cbn zeta.
 set (c:=e*2^(2*j+1)+12*2^(4*b+2)+2*w-4*v).
 assert (Hp:0<2^(4*b+2)).
 { pose proof (Nat.pow_nonzero 2 (4*b+2) ltac:(lia)); lia. }
 assert (Hpos:0<c) by (unfold c; nia).
 assert (Hbalance:c+4*v=e*2^(2*j+1)+12*2^(4*b+2)+2*w)
   by (unfold c; nia).
 split; [exact Hpos|]. split; [|exact Hbalance].

 assert (Hfirst:e*2^(2*j+1)<2^(9*j+4)).
 { assert (Hprod:2^(9*j+4)=2^(7*j+3)*2^(2*j+1)).
   { replace (9*j+4) with ((7*j+3)+(2*j+1)) by lia. apply Nat.pow_add_r. }
   rewrite Hprod. pose proof (Nat.pow_nonzero 2 (2*j+1) ltac:(lia)). nia. }
 assert (Hsecond:12*2^(4*b+2)<2^(4*b+6)).
 { assert (Hprod:2^(4*b+6)=2^(4*b+2)*16).
   { replace (4*b+6) with ((4*b+2)+4) by lia.
     rewrite Nat.pow_add_r. reflexivity. }
   rewrite Hprod. nia. }
 assert (Hthird:2*w<2^(2*j+2)).
 { replace (2*j+2) with ((2*j+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }

 assert (Ha:2^(9*j+4)<=2^(25*b+7*j+22)) by (apply Nat.pow_le_mono_r; lia).
 assert (Hb:2^(4*b+6)<=2^(25*b+7*j+22)) by (apply Nat.pow_le_mono_r; lia).
 assert (Hc:2^(2*j+2)<=2^(25*b+7*j+22)) by (apply Nat.pow_le_mono_r; lia).
 assert (Htarget:2^(25*b+7*j+26-2)=2^(25*b+7*j+22)*4).
 { replace (25*b+7*j+26-2) with ((25*b+7*j+22)+2) by lia.
   rewrite Nat.pow_add_r. reflexivity. }
 rewrite Htarget. nia.
Qed.

Lemma odd_route_tight_marker n bs b L' k' rest out t :
 length bs=4*b+2 -> length bs+3<=n ->
 R.route (E.initial_width n b) (E.initial_rank n b)
   (CF.digits n (E.source_rank n bs)) L' k' rest ->
 t*2=k'+1 -> CD.value out+2^length out=t+CD.value rest ->
 length out+1=L' -> W.marked 1 out.
Proof.

 intros Hm Hn Hroute Ht Hmass Htight.
 set (d:=(2^(10*b+11)-3)*2^(25*b+23)).
 pose proof (B.initial_deficit n bs b Hm ltac:(lia)) as Hd.
 fold d in Hd.
 destruct (RD.route_deficit _ _ _ _ _ _ Hroute d Hd)
   as [j [e [Hlen [HL [Hdef He]]]]].

 assert (Hj:2*j<=4*b+6).
 { destruct (Nat.le_gt_cases (length bs+5) n) as [Hwide|Hnarrow].
   - pose proof (B.source_even_bit n bs Hwide) as Hbit.
     assert (Hpar:(length bs+4) mod 2=0).
     { rewrite Hm. replace (4*b+2+4) with ((2*b+3)*2) by lia.
       apply Nat.mod_mul. lia. }
     pose proof (RB.route_known_even_bound _ _ _ _ _ _ j (length bs+4)
       Hroute Hlen Hbit Hpar). lia.
   - rewrite CF.digits_length in Hlen. lia. }

 destruct (RD.route_suffix _ _ _ _ _ _ Hroute) as [pre Hprefix].
 assert (Hpre:length pre=2*j+1).
 { rewrite Hprefix,length_app in Hlen. lia. }
 assert (Hrank:E.source_rank n bs<2^n).
 { unfold E.source_rank. apply PE.remaining_bound. lia. }

 assert (Hvalue:CD.value (CF.digits n (E.source_rank n bs))=E.source_rank n bs).
 { change (CB.value (CF.digits n (E.source_rank n bs))=E.source_rank n bs).
   apply CB.digits_value; exact Hrank. }
 rewrite Hprefix,CD.value_append,Hpre in Hvalue.
 pose proof (CD.value_bound pre) as Hw. rewrite Hpre in Hw.
 pose proof (PE.value_bound bs) as Hv. rewrite Hm in Hv.
 destruct (correction_small b j e (PE.value bs) (CD.value pre) ltac:(lia) He Hv Hw)
   as [Hc [Hcsmall Hcbalance]].
 set (c:=e*2^(2*j+1)+12*2^(4*b+2)+2*CD.value pre-4*PE.value bs) in *.

 assert (Hsource:E.source_rank n bs+6*2^(4*b+2)=2^n+2*PE.value bs).
 { pose proof (PE.fuel_value bs) as Hf. rewrite Hm in Hf.
   pose proof (PE.fuel_fits n bs ltac:(lia)) as Hfits.
   unfold E.source_rank. lia. }
 assert (Hpowtight:2^L'=2^length out*2).
 { rewrite <-Htight,Nat.pow_add_r. reflexivity. }
 assert (Hcore:2*CD.value out+d*2^(5*j+2)+e=2*CD.value rest).
 { rewrite Hpowtight in Hdef. nia. }

 assert (Hbig:d*2^(5*j+2)*2^(2*j+1)=
   (2^(10*b+11)-3)*2^(25*b+7*j+26)).
 { unfold d.
   replace (25*b+7*j+26) with ((25*b+23)+(5*j+2)+(2*j+1)) by lia.
   rewrite !Nat.pow_add_r. nia. }

 assert (Hshift:2^(2*j+2)=2^(2*j+1)*2).
 { replace (2*j+2) with ((2*j+1)+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (Hright:2^(n+1)=2^n*2) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Hequation:CD.value out*2^(2*j+2)+c+
   (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(n+1)).
 { rewrite <-Hbig,Hshift,Hright.
   pose proof (f_equal (fun x=>x*2^(2*j+1)) Hcore) as Hscaled.
   cbn beta in Hscaled.
   clear -Hscaled Hvalue Hsource Hcbalance.
   nia. }

 assert (Hmarked:W.marked 1 (repeat false (2*j+2)++out)).
 { apply (GM.small_subtraction_marker (repeat false (2*j+2)++out)
     (n+1) (10*b+11) (25*b+7*j+26) c).
   - clear -b j. lia.
   - clear -b. lia.
   - exact Hc.
   - exact Hcsmall.
   -
   change (CD.value (repeat false (2*j+2)++out)+c+
     (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(n+1)).
   rewrite CD.value_append,value_zeros,repeat_length. cbn [Nat.add].
   rewrite (Nat.mul_comm (2^(2*j+2)) (CD.value out)). exact Hequation. }
 replace (2*j+2) with ((j+1)*2) in Hmarked by (clear -j; lia).
 apply B.marked_drop_even_zeros in Hmarked. exact Hmarked.
Qed.

Print Assumptions correction_small.
Print Assumptions odd_route_tight_marker.
End EdOddTight.
End EdOddTight.

Module SignedGapMarker.
(* A small signed correction preserves a marker next to a binary gap.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits MarkerArithmetic WallInvariant GapMarker.
Import String List PeanoNat Lia.
Import ListNotations CounterBits.CounterBits MarkerArithmetic.MarkerArithmetic.
Import WallInvariant.WallInvariant GapMarker.GapMarker.
Open Scope nat.

Module SignedGapMarker.

Lemma high_residue v A C M low : M<=A -> M<=C ->
 v+2^C=2^A+low -> v mod 2^M=low mod 2^M.
Proof.
 intros HA HC Heq.
 rewrite (power_multiple M C), (power_multiple M A) in Heq by assumption.
 replace (2^(A-M)*2^M+low) with (low+2^(A-M)*2^M) in Heq by lia.
 apply (f_equal (fun n=>n mod 2^M)) in Heq.
 rewrite !Nat.mod_add in Heq by (apply Nat.pow_nonzero; lia). exact Heq.
Qed.

Lemma positive_three_marker bs A B J delta :
 3<=B -> J+2<=A -> delta<2^J ->
 value bs+(2^B-3)*2^J=2^A+delta -> marked 1 bs.
Proof.

 intros HB HA Hd Heq.
 assert (HpowB:8<=2^B) by (change (2^3<=2^B); apply Nat.pow_le_mono_r; lia).
 assert (Hsum:value bs+2^(B+J)=2^A+(3*2^J+delta)).
 { rewrite Nat.pow_add_r. clear -Heq HpowB. nia. }

 destruct (mod2 J) as [a EJ|a EJ]; subst J.
 - pose proof (high_residue (value bs) A (B+a*2) (a*2+2)
     (3*2^(a*2)+delta) ltac:(lia) ltac:(lia) Hsum) as Hmod.
   pose proof (marked_residue_auto bs (a*2+1) (2^(a*2)+delta)) as Hmark.
   replace ((a*2+1) mod 2) with 1 in Hmark by
     (rewrite Nat.add_comm,Nat.mod_add by lia; reflexivity).
   apply Hmark.
   + rewrite Nat.pow_add_r. cbn [Nat.pow]. lia.
   + replace (a*2+1+1) with (a*2+2) by lia. rewrite Hmod.
     rewrite Nat.mod_small.
     * rewrite (Nat.pow_add_r 2 (a*2) 1). cbn [Nat.pow]. nia.
     * rewrite (Nat.pow_add_r 2 (a*2) 2). cbn [Nat.pow]. lia.

 - pose proof (high_residue (value bs) A (B+(1+a*2)) ((1+a*2)+1)
     (3*2^(1+a*2)+delta) ltac:(lia) ltac:(lia) Hsum) as Hmod.

   pose proof (marked_residue_auto bs (1+a*2) delta) as Hmark.
   replace ((1+a*2) mod 2) with 1 in Hmark by
     (rewrite Nat.mod_add by lia; reflexivity).
   apply Hmark; [exact Hd|]. rewrite Hmod.
   replace (3*2^(1+a*2)+delta) with
     ((2^(1+a*2)+delta)+1*2^((1+a*2)+1)) by
     (rewrite (Nat.pow_add_r 2 (1+a*2) 1); cbn [Nat.pow]; nia).
   rewrite Nat.mod_add by (apply Nat.pow_nonzero; lia).
   apply Nat.mod_small. rewrite (Nat.pow_add_r 2 (1+a*2) 1). cbn [Nat.pow]. lia.
Qed.

Lemma signed_small_marker bs A B J c small :
 3<=J -> 3<=B -> J+2<=A ->
 0<c -> c<2^(J-2) -> small<2^(J-2) ->
 value bs+c+(2^B-3)*2^J=2^A+small -> marked 1 bs.
Proof.

 intros HJ HB HA Hc Hcsmall Hsmall Heq.
 destruct (Nat.lt_ge_cases small c) as [Hnegative|Hpositive].
 - apply (small_subtraction_marker bs A B J (c-small)); try assumption; try lia.
 - apply (positive_three_marker bs A B J (small-c)); try assumption.
   + assert (2^(J-2)<=2^J) by (apply Nat.pow_le_mono_r; lia). lia.
   + lia.
Qed.

Print Assumptions signed_small_marker.
End SignedGapMarker.
End SignedGapMarker.

Module EdOddLoose.
(* A loose displaced-digit output also retains the odd-position marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddBounds EdOddOrbit EdOddTight PhaseEd OddRoute RouteDeficit.
Import CounterBits CounterFinish WallInvariant CDPasses SignedGapMarker.
Import String List PeanoNat Lia.
Import ListNotations.

Module EdOddLoose.
Module E := EdOddOrbit.EdOddOrbit.
Module B := EdOddBounds.EdOddBounds.
Module T := EdOddTight.EdOddTight.
Module PE := PhaseEd.PhaseEd.
Module R := OddRoute.OddRoute.
Module RD := RouteDeficit.RouteDeficit.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module CD := CDPasses.CDPasses.
Module W := WallInvariant.WallInvariant.
Module GM := SignedGapMarker.SignedGapMarker.
Open Scope nat.

Lemma odd_route_loose_marker n bs b L' k' rest out t :
 length bs=4*b+2 -> length bs+3=n ->
 R.route (E.initial_width n b) (E.initial_rank n b)
   (CF.digits n (E.source_rank n bs)) L' k' rest ->
 t*2=k'+1 -> CD.value out+2^length out=t+CD.value rest ->
 length out+2=L' -> W.marked 1 out.
Proof.

 intros Hm Hn Hroute Ht Hmass Hloose.
 set (d:=(2^(10*b+11)-3)*2^(25*b+23)).
 pose proof (B.initial_deficit n bs b Hm ltac:(lia)) as Hd.
 fold d in Hd.
 destruct (RD.route_deficit _ _ _ _ _ _ Hroute d Hd)
   as [j [e [Hlen [HL [Hdef He]]]]].
 assert (Hj:2*j<=4*b+6) by (rewrite CF.digits_length in Hlen; lia).

 destruct (RD.route_suffix _ _ _ _ _ _ Hroute) as [pre Hprefix].
 assert (Hpre:length pre=2*j+1).
 { rewrite Hprefix,length_app in Hlen. lia. }
 assert (Hrank:E.source_rank n bs<2^n).
 { unfold E.source_rank. apply PE.remaining_bound. lia. }

 assert (Hvalue:CD.value (CF.digits n (E.source_rank n bs))=E.source_rank n bs).
 { change (CB.value (CF.digits n (E.source_rank n bs))=E.source_rank n bs).
   apply CB.digits_value; exact Hrank. }
 rewrite Hprefix,CD.value_append,Hpre in Hvalue.
 pose proof (CD.value_bound pre) as Hw. rewrite Hpre in Hw.
 pose proof (PE.value_bound bs) as Hv. rewrite Hm in Hv.
 destruct (T.correction_small b j e (PE.value bs) (CD.value pre) Hj He Hv Hw)
   as [Hc [Hcsmall Hcbalance]].
 set (c:=e*2^(2*j+1)+12*2^(4*b+2)+2*CD.value pre-4*PE.value bs) in *.

 assert (Hsource:E.source_rank n bs+6*2^(4*b+2)=2^n+2*PE.value bs).
 { pose proof (PE.fuel_value bs) as Hf. rewrite Hm in Hf.
   pose proof (PE.fuel_fits n bs ltac:(lia)) as Hfits.
   unfold E.source_rank. lia. }
 assert (Hpowloose:2^L'=2^length out*4).
 { rewrite <-Hloose,Nat.pow_add_r. reflexivity. }
 assert (Hpowhalf:2^(L'-1)=2^length out*2).
 { replace (L'-1) with (length out+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (Hcore:2*CD.value out+d*2^(5*j+2)+e=2^(L'-1)+2*CD.value rest).
 { rewrite Hpowloose in Hdef. rewrite Hpowhalf. clear -Hdef Hmass Ht. nia. }

 assert (Hbig:d*2^(5*j+2)*2^(2*j+1)=
   (2^(10*b+11)-3)*2^(25*b+7*j+26)).
 { unfold d.
   replace (25*b+7*j+26) with ((25*b+23)+(5*j+2)+(2*j+1)) by lia.
   rewrite !Nat.pow_add_r. nia. }

 assert (Hshift:2^(2*j+2)=2^(2*j+1)*2).
 { replace (2*j+2) with ((2*j+1)+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (Hright:2^(n+1)=2^n*2) by (rewrite Nat.pow_add_r; reflexivity).
 assert (Hlarge:2^(L'+2*j)=2^(L'-1)*2^(2*j+1)).
 { replace (L'+2*j) with ((L'-1)+(2*j+1)) by (clear -Hloose; lia).
   apply Nat.pow_add_r. }
 assert (Hequation:CD.value out*2^(2*j+2)+c+
   (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(L'+2*j)+2^(n+1)).
 { rewrite <-Hbig,Hshift,Hright,Hlarge.
   pose proof (f_equal (fun x=>x*2^(2*j+1)) Hcore) as Hscaled.
   cbn beta in Hscaled.
   clear -Hscaled Hvalue Hsource Hcbalance. nia. }

 assert (Hmarked:W.marked 1 (repeat false (2*j+2)++out)).
 { apply (GM.signed_small_marker (repeat false (2*j+2)++out)
     (L'+2*j) (10*b+11) (25*b+7*j+26) c (2^(n+1))).
   - clear -b j. lia.
   - clear -b. lia.
   - clear -HL Hm Hn. unfold E.initial_width in HL. lia.
   - exact Hc.
   - exact Hcsmall.

   - clear -Hm Hn. apply Nat.pow_lt_mono_r; lia.
   - change (CD.value (repeat false (2*j+2)++out)+c+
       (2^(10*b+11)-3)*2^(25*b+7*j+26)=2^(L'+2*j)+2^(n+1)).
     rewrite CD.value_append,T.value_zeros,repeat_length. cbn [Nat.add].
     rewrite (Nat.mul_comm (2^(2*j+2)) (CD.value out)). exact Hequation. }

 replace (2*j+2) with ((j+1)*2) in Hmarked by (clear -j; lia).
 apply B.marked_drop_even_zeros in Hmarked. exact Hmarked.
Qed.

Print Assumptions odd_route_loose_marker.
End EdOddLoose.
End EdOddLoose.

Module StrongEdOddFacts.
(* Exact rank digits and lower bounds for the marked displaced-digit family.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import EdOddOrbit EdOddBounds PhaseEd OddRoute RouteDeficit.
Import CounterBits CounterFinish MarkerArithmetic WallInvariant CDPasses.
Import String List PeanoNat Lia.
Import ListNotations.

Module StrongEdOddFacts.
Module E := EdOddOrbit.EdOddOrbit.
Module B := EdOddBounds.EdOddBounds.
Module PE := PhaseEd.PhaseEd.
Module R := OddRoute.OddRoute.
Module RD := RouteDeficit.RouteDeficit.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module MA := MarkerArithmetic.MarkerArithmetic.
Module CD := CDPasses.CDPasses.
Module W := WallInvariant.WallInvariant.
Open Scope nat.

Lemma source_rank_exact n bs : length bs+3=n ->
 E.source_rank n bs=2^(length bs+1)+2*PE.value bs.
Proof.

 intro Hn.
 pose proof (PE.fuel_value bs) as Hf.
 pose proof (PE.fuel_fits n bs ltac:(lia)) as Hfits.
 unfold E.source_rank. rewrite <-Hn in *.
 rewrite !Nat.pow_add_r in *. cbn [Nat.pow] in *. nia.
Qed.

Lemma source_digits_exact n bs : length bs+3=n ->
 CF.digits n (E.source_rank n bs)=false::bs++[true;false].
Proof.
 intro Hn.
 pose proof (MA.digits_value_inverse (false::bs++[true;false])) as H.
 assert (Hlength:length (false::bs++[true;false])=n).
 { cbn [length]. rewrite length_app. cbn [length]. lia. }

 assert (Hvalue:CB.value (false::bs++[true;false])=E.source_rank n bs).
 { change (CD.value (false::bs++[true;false])=E.source_rank n bs).
   cbn [CD.value CD.bitval]. rewrite CD.value_append.
   cbn [CD.value CD.bitval]. rewrite source_rank_exact by exact Hn.
   change (CD.value bs) with (PE.value bs).
   rewrite Nat.pow_add_r. cbn [Nat.pow]. nia. }
 rewrite Hlength,Hvalue in H. exact H.
Qed.

Lemma marked_prefix bs : W.marked 1 bs -> W.marked 0 (false::bs).
Proof.
 intros [pre [post [Epre Hpar]]].
 exists (false::pre),post. split; [rewrite Epre; reflexivity|].
 cbn [length]. replace (S (length pre)) with (length pre+1) by lia.
 rewrite Nat.add_mod by lia. rewrite Hpar. reflexivity.
Qed.

Lemma route_append L k bs L' k' rest tail :
 R.route L k bs L' k' rest -> R.route L k (bs++tail) L' k' (rest++tail).
Proof.
 intro H. induction H.
 - rewrite <-app_assoc. cbn [app]. constructor.
 - rewrite <-app_assoc. cbn [app]. constructor. exact IHroute.
Qed.

Lemma route_mass_large n bs b L k rest t :
 length bs=4*b+2 -> length bs+3=n ->
 R.route (E.initial_width n b) (E.initial_rank n b)
   (CF.digits n (E.source_rank n bs)) L k rest ->
 t*2=k+1 -> 2^(L-2)<=t.
Proof.

 intros Hm Hn Hroute Ht.
 set (d:=(2^(10*b+11)-3)*2^(25*b+23)).
 pose proof (B.initial_deficit n bs b Hm ltac:(lia)) as Hd. fold d in Hd.
 destruct (RD.route_deficit _ _ _ _ _ _ Hroute d Hd)
   as [j [e [Hlen [HL [Hdef He]]]]].
 rewrite CF.digits_length in Hlen.
 unfold E.initial_width in HL.
 assert (HLpos:2<=L) by lia.

 assert (Hdom:d*2^(5*j+2)<2^(35*b+5*j+36)).
 { assert (Hp:0<2^(25*b+23)*2^(5*j+2)).
   { pose proof (Nat.pow_nonzero 2 (25*b+23) ltac:(lia)).
     pose proof (Nat.pow_nonzero 2 (5*j+2) ltac:(lia)). nia. }
   assert (HB:0<2^(10*b+11)) by (pose proof (Nat.pow_nonzero 2 (10*b+11) ltac:(lia)); lia).

   assert (Hpow:2^(35*b+5*j+36)=2^(10*b+11)*2^(25*b+23)*2^(5*j+2)).
   { replace (35*b+5*j+36) with ((10*b+11)+(25*b+23)+(5*j+2)) by lia.
     rewrite !Nat.pow_add_r. reflexivity. }
   unfold d. rewrite Hpow. clear -Hp HB. nia. }

 assert (Hsmall:2^(7*j+3)<=2^(35*b+5*j+36)) by (apply Nat.pow_le_mono_r; lia).
 assert (Hdeficit:d*2^(5*j+2)+e<2^(L-1)).
 { assert (Htwice:2^(35*b+5*j+37)=2^(35*b+5*j+36)*2).
   { replace (35*b+5*j+37) with ((35*b+5*j+36)+1) by lia.
     rewrite Nat.pow_add_r. reflexivity. }
   assert (Hcap:2^(35*b+5*j+37)<=2^(L-1)) by (apply Nat.pow_le_mono_r; lia).
   rewrite Htwice in Hcap. nia. }

 assert (HpowL:2^L=2^(L-2)*4).
 { replace L with ((L-2)+2) at 1 by lia. rewrite Nat.pow_add_r. reflexivity. }
 assert (HpowHalf:2^(L-1)=2^(L-2)*2).
 { replace (L-1) with ((L-2)+1) by lia. rewrite Nat.pow_add_r. reflexivity. }
 rewrite HpowL in Hdef. rewrite HpowHalf in Hdeficit.
 clear -Hdef Hdeficit Ht. nia.
Qed.

Print Assumptions source_digits_exact.
Print Assumptions route_mass_large.
End StrongEdOddFacts.
End StrongEdOddFacts.

Module StrongEdOdd.
(* Preservation of the marked displaced-digit family in the odd-valuation case.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import EdOddOrbit EdOddTight EdOddLoose StrongEdOddFacts EdEvenOrbit.
Import OddRoute OddImage CounterFinish CounterRules WallInvariant CDPasses.
Import StrongInvariant.
Import String List PeanoNat Lia.
Import ListNotations.

Module StrongEdOdd.
Module E := EdOddOrbit.EdOddOrbit.
Module T := EdOddTight.EdOddTight.
Module Loose := EdOddLoose.EdOddLoose.
Module F := StrongEdOddFacts.StrongEdOddFacts.
Module EO := EdEvenOrbit.EdEvenOrbit.
Module R := OddRoute.OddRoute.
Module I := OddImage.OddImage.
Module CF := CounterFinish.CounterFinish.
Module CR := CounterRules.CounterRules.
Module CD := CDPasses.CDPasses.
Module W := WallInvariant.WallInvariant.
Module S := StrongInvariant.StrongInvariant.
Notation mtm := W.mtm.
Open Scope sym.
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma strong_ed_odd n bs b :
 (length bs=4*b+2)%nat -> (length bs+3=n)%nat -> W.marked 1 bs ->
 exists c, W.Ed n bs -[mtm]->+ c /\ S.strong c.
Proof.

 intros Hm Hn Hmarked.
 assert (Hin:In true bs).
 { destruct Hmarked as [pre [post [He Hp]]]. rewrite He.
   apply in_or_app. right. cbn. auto. }
 pose proof (E.Ed_odd_valuation_entry n bs b Hm ltac:(lia) Hin) as Hentry.
 destruct (E.Ed_odd_entry_fuel n bs b Hm ltac:(lia)) as [Hfuel [Hbound Hodd]].
 pose proof (F.source_digits_exact n bs Hn) as Hdigits.
 pose proof (F.marked_prefix bs Hmarked) as Hmark.
 assert (Hprefixfuel:(2^length (false::bs)-1<=E.initial_rank n b)%nat).
 { rewrite CF.digits_length in Hfuel.
   assert (2^length (false::bs)<=2^n)%nat by
     (apply Nat.pow_le_mono_r; cbn [length]; lia). lia. }

 destruct (R.marked_route (E.initial_width n b) (E.initial_rank n b)
   (false::bs) Hmark Hprefixfuel) as [L [k [rest [Hr Hlower]]]].
 assert (Hroute:R.route (E.initial_width n b) (E.initial_rank n b)
   (CF.digits n (E.source_rank n bs)) L k (rest++[true;false])).
 { rewrite Hdigits. change (R.route (E.initial_width n b) (E.initial_rank n b)
     ((false::bs)++[true;false]) L k (rest++[true;false])).
   apply F.route_append. exact Hr. }

 destruct (R.route_bound _ _ _ _ _ _ Hroute Hbound) as [Hcap Hpar].
 destruct (R.route_dimensions _ _ _ _ _ _ Hroute) as [j [Hlen HL]].
 assert (Hwidth:(length (rest++[true;false])+2<=L)%nat).
 { rewrite CF.digits_length in Hlen. rewrite HL. unfold E.initial_width. lia. }
 pose proof (R.route_run _ _ _ _ _ _ 0inf Hroute Hbound) as Hrun.

 destruct (mod2 k) as [q Hq|q Hq].
 { rewrite Hq,Nat.mod_mul in Hpar by lia. discriminate. }
 assert (Ht:((q+1)*2=k+1)%nat) by lia.
 set (t:=(q+1)%nat). fold t in Ht.
 pose proof (F.route_mass_large n bs b L k (rest++[true;false]) t Hm Hn Hroute Ht) as Hlarge.

 assert (Hmin:(2^length (rest++[true;false])<=t)%nat).
 { assert (2^length (rest++[true;false])<=2^(L-2))%nat by
     (apply Nat.pow_le_mono_r; lia). lia. }
 pose proof (CD.value_bound (rest++[true;false])) as Hrest.
 assert (Hmax:(t+CD.value (rest++[true;false])<
   2^(length (rest++[true;false])+(L-length (rest++[true;false]))))%nat).
 { replace (length (rest++[true;false])+(L-length (rest++[true;false])))%nat
     with L by lia. lia. }

 destruct (I.fuel_C_image L k t (rest++[true;false])
   (L-length (rest++[true;false])) ltac:(lia) (eq_sym Ht) Hmin Hmax)
   as [out [Houtlen [Hvalue Hfinish]]].
 replace (length (rest++[true;false])+(L-length (rest++[true;false])))%nat
   with L in Houtlen by lia.
 assert (Hany:CD.any (rest++[true;false])=true).
 { apply EO.any_true. apply in_or_app. right. cbn. auto. }
 rewrite Hany in Hfinish.
 change (CR.LC L k |> [1;0;0;0] *> W.normal (rest++[true;false]) *> 0inf
   -[mtm]->+ W.Ed (L+1) out) in Hfinish.

 assert (Hlo:(L-2<=length out)%nat).
 { pose proof (CD.value_bound out) as Hv.
   destruct (Nat.le_gt_cases (L-2) (length out)); [assumption|].
   assert (Hp:(2^(length out+1)<=2^(L-2))%nat) by (apply Nat.pow_le_mono_r; lia).
   rewrite Nat.pow_add_r in Hp. cbn [Nat.pow] in Hp. lia. }

 assert (Hcases:(length out+2=L \/ length out+1=L)%nat) by lia.
 assert (Hmarker:W.marked 1 out).
 { destruct Hcases as [Hloose|Htight].
   - apply (Loose.odd_route_loose_marker n bs b L k (rest++[true;false]) out t
       Hm Hn Hroute Ht Hvalue Hloose).
   - apply (T.odd_route_tight_marker n bs b L k (rest++[true;false]) out t
       Hm ltac:(lia) Hroute Ht Hvalue Htight). }

 exists (W.Ed (L+1) out). split.
 - eapply progress_trans; [exact Hentry|].
   eapply progress_trans; eassumption.
 - apply S.StrongEd; [destruct Hcases; [left|right]; lia|exact Hmarker].
Qed.

Print Assumptions strong_ed_odd.
End StrongEdOdd.
End StrongEdOdd.

Module StrongEdLoose.
(* Closure of the displaced-digit walls with three spare amplifier pairs.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import StrongEdDirect StrongEdEven StrongEdOdd StrongInvariant WallInvariant.
Import List PeanoNat Lia.

Module StrongEdLoose.
Module D := StrongEdDirect.StrongEdDirect.
Module E := StrongEdEven.StrongEdEven.
Module O := StrongEdOdd.StrongEdOdd.
Module S := StrongInvariant.StrongInvariant.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.

Lemma strong_ed_loose n bs :
 (length bs+3=n)%nat -> W.marked 1 bs ->
 exists c, W.Ed n bs -[mtm]->+ c /\ S.strong c.
Proof.
 intros Hn Hmark.
 destruct (mod2 (length bs)) as [a Ha|a Ha].
 - destruct (mod2 a) as [b Hb|b Hb].
   + apply (E.Ed_even_strong n bs b); try lia; exact Hmark.
   + apply (O.strong_ed_odd n bs b); try lia; exact Hmark.
 - apply (D.Ed_direct_strong n bs (a+1)); try lia; exact Hmark.
Qed.

Print Assumptions strong_ed_loose.
End StrongEdLoose.
End StrongEdLoose.

Module TightEquations.
(* Eliminating the terminal budget from tight successor counter values.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import OddImage OddAdjacent MarkedDeficit TerminalLoose CDPasses.
Import List PeanoNat Lia.
Import ListNotations.
Module TightEquations.
Module I := OddImage.OddImage.
Module A := OddAdjacent.OddAdjacent.
Module MD := MarkedDeficit.MarkedDeficit.
Module TL := TerminalLoose.TerminalLoose.
Module CD := CDPasses.CDPasses.
Open Scope nat.

Lemma even_tight_equation L v q k d T out :
 0<v -> 0<T -> k+d+1=2^L -> k+1=2*(T+q) ->
 length out+2=L+v*7+3 ->
 CD.value out+2^length out=I.first_mass (L+v*2+1) v+(q*2+1) ->
 CD.value out+(2*T-1)+d+MD.initial_deficit (v*2) (v*5-1)=2^L.
Proof.

 intros Hv HT Hdef Hfuel Hlen Hmass.
 pose proof (TL.even_balance L v Hv) as Hbal.
 assert (Hlength:length out=L+v*7+1) by lia.
 rewrite Hlength in Hmass. lia.
Qed.

Lemma deficit_half L k d :
 0<L -> k mod 2=1 -> k+d+1=2^L -> exists half, d=half*2.
Proof.

 intros HL Ho Hdef. destruct (mod2 k) as [a E|a E]; subst k; [lia|].
 destruct (mod2 d) as [b E|b E]; [eauto|]. subst d.
 replace L with (S (L-1)) in Hdef by lia. cbn[Nat.pow] in Hdef. lia.
Qed.

Lemma odd_tight_equation L v q k half T out :
 0<L -> k+half*2+1=2^L -> k+1=2*(T+q) ->
 length out+2=L+v*7+9 ->
 CD.value out+2^length out=A.odd_mass (L+v*2+2) v+q ->
 CD.value out+(T+3)+half+MD.initial_deficit (v*2+1) (v*5+4)=2^(L-1).
Proof.

 intros HL Hdef Hfuel Hlen Hmass.
 pose proof (TL.odd_balance L v) as Hbal.
 assert (Hlength:length out=L+v*7+7) by lia.
 rewrite Hlength in Hmass.
 replace L with (S (L-1)) in Hdef by lia. cbn[Nat.pow] in Hdef. lia.
Qed.

Print Assumptions even_tight_equation.
Print Assumptions deficit_half.
Print Assumptions odd_tight_equation.
End TightEquations.
End TightEquations.

Module TightInitialMarker.
(* Markers after a tight terminal conversion whose first normal digit is even.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import CounterBits WallInvariant MarkedDeficit MultiGapMarker OdEvenMarker.
Import List PeanoNat Lia.
Import ListNotations.
Module TightInitialMarker.
Module CB := CounterBits.CounterBits.
Module W := WallInvariant.WallInvariant.
Module MD := MarkedDeficit.MarkedDeficit.
Module G := MultiGapMarker.MultiGapMarker.
Module O := OdEvenMarker.OdEvenMarker.
Open Scope nat.

Lemma even_initial_marker out a j T :
 0<j -> 0<T -> T<=2^(a*4+1) ->
 CB.value out+(2*T-1)+MD.initial_deficit (j*2) (j*5)+
   MD.initial_deficit (a*10+6) (a*25+14)=2^(j*7+a*4+4) ->
 W.marked 1 out.
Proof.

 intros Hj HT HTb HE.
 set (J:=j*5). set (K:=a*25+14). set (A:=j*7+a*4+4).
 set (D:=2^(j*2+2)-3). set (E:=2^(a*10+8)-3).
 set (F:=D*2^J). set (c:=2*T-1).
 assert (HD:0<D) by (unfold D; apply O.minus_three_positive).
 assert (HEpos:0<E).
 { unfold E. replace (a*10+8) with ((a*10+6)+2) by lia.
   apply O.minus_three_positive. }
 assert (Hc:0<c) by (unfold c; lia).
 assert (HK:4<=K) by (unfold K; lia).
 assert (Hcb:c<2^(a*4+2)).

 { unfold c. replace (a*4+2) with ((a*4+1)+1) by lia.

   rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }
 assert (HF:F<2^(j*7+2)).
 { unfold F,D,J. pose proof (O.scaled_minus_three (j*2) (j*5)) as H.
   replace (j*2+2+j*5) with (j*7+2) in H by lia. exact H. }
 assert (HEq:CB.value out+c+F+E*2^K=2^A).
 { unfold MD.initial_deficit in HE. fold c in HE.
   replace (a*10+6+2) with (a*10+8) in HE by lia. exact HE. }
 destruct (Nat.le_gt_cases j (a*3+1)) as [Hsmall|Hlarge].
 - assert (HFsmall:F<2^(K-3)).

   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   assert (Hcsmall:c<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }

   apply (G.positive_subtraction_marker out A K E (c+F)); try assumption; try lia.
   apply O.sum_small; assumption || lia.
 - assert (HJ:3<=J) by (unfold J; lia).
   assert (HcJ:c<2^(J-2)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold J; lia. }
   assert (HcK:c<2^(K-2)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   apply (G.two_gap_marker out A J K D E c); try assumption.

   + apply Nat.min_glb; lia.
   + destruct (Nat.le_ge_cases J K).
     * rewrite Nat.min_l by assumption. exact HcJ.
     * rewrite Nat.min_r by assumption. exact HcK.

Qed.

Lemma odd_initial_marker out a j T :
 0<j -> 0<T -> T<=2^(a*4+3) ->
 CB.value out+(T+3)+MD.initial_deficit (j*2) (j*5-1)+
   MD.initial_deficit (a*10+11) (a*25+29)=2^(j*7+a*4+5) ->
 W.marked 1 out.
Proof.

 intros Hj HT HTb HE.
 set (J:=j*5-1). set (K:=a*25+29). set (A:=j*7+a*4+5).
 set (D:=2^(j*2+2)-3). set (E:=2^(a*10+13)-3).
 set (F:=D*2^J). set (c:=T+3).
 assert (HD:0<D) by (unfold D; apply O.minus_three_positive).
 assert (HEpos:0<E).
 { unfold E. replace (a*10+13) with ((a*10+11)+2) by lia.
   apply O.minus_three_positive. }
 assert (Hc:0<c) by (unfold c; lia).
 assert (HK:4<=K) by (unfold K; lia).
 assert (Hcb:c<2^(a*4+4)).

 { unfold c. assert (8<=2^(a*4+3)) by (change (2^3<=2^(a*4+3)); apply Nat.pow_le_mono_r; lia).

   replace (a*4+4) with ((a*4+3)+1) by lia.
   rewrite Nat.pow_add_r. cbn[Nat.pow]. lia. }
 assert (HF:F<2^(j*7+1)).
 { unfold F,D,J. pose proof (O.scaled_minus_three (j*2) (j*5-1)) as H.
   replace (j*2+2+(j*5-1)) with (j*7+1) in H by lia. exact H. }
 assert (HEq:CB.value out+c+F+E*2^K=2^A).
 { unfold MD.initial_deficit in HE. fold c in HE.
   replace (a*10+11+2) with (a*10+13) in HE by lia. exact HE. }
 destruct (Nat.le_gt_cases j (a*3+2)) as [Hsmall|Hlarge].

 - assert (HFsmall:F<2^(K-3)).
   { eapply Nat.lt_le_trans; [exact HF|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   assert (Hcsmall:c<2^(K-3)).

   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   apply (G.positive_subtraction_marker out A K E (c+F)); try assumption; try lia.
   apply O.sum_small; assumption || lia.
 - assert (HJ:3<=J) by (unfold J; lia).
   assert (HcJ:c<2^(J-2)).
   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold J; lia. }
   assert (HcK:c<2^(K-2)).

   { eapply Nat.lt_le_trans; [exact Hcb|]. apply Nat.pow_le_mono_r; unfold K; lia. }
   apply (G.two_gap_marker out A J K D E c); try assumption.
   + apply Nat.min_glb; lia.
   + destruct (Nat.le_ge_cases J K).
     * rewrite Nat.min_l by assumption. exact HcJ.

     * rewrite Nat.min_r by assumption. exact HcK.
Qed.

Print Assumptions even_initial_marker.
Print Assumptions odd_initial_marker.
End TightInitialMarker.
End TightInitialMarker.

Module TightInitialClosure.
(* Closing the ordinary endpoint after the first even normal digit.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import TerminalClosure TerminalSuccessor TerminalLoose TightEquations TightInitialMarker.
Import TightPrimer StrongInvariant MarkedDeficit CounterBits CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module TightInitialClosure.
Module W := WallInvariant.WallInvariant.
Module S := StrongInvariant.StrongInvariant.

Module TC := TerminalClosure.TerminalClosure.
Module TS := TerminalSuccessor.TerminalSuccessor.
Module TL := TerminalLoose.TerminalLoose.
Module EQ := TightEquations.TightEquations.

Module IM := TightInitialMarker.TightInitialMarker.
Module TT := TightPrimer.TightPrimer.
Module MD := MarkedDeficit.MarkedDeficit.
Module CB := CounterBits.CounterBits.
Module CD := CDPasses.CDPasses.
Notation mtm := W.mtm.
Open Scope nat.

Lemma deficit_halved j : 0<j ->
 MD.initial_deficit (j*2) (j*5)=MD.initial_deficit (j*2) (j*5-1)*2.
Proof.

 intro Hj. unfold MD.initial_deficit.
 replace (j*5) with ((j*5-1)+1) at 1 by lia.
 rewrite (Nat.pow_add_r 2 (j*5-1) 1). cbn[Nat.pow]. nia.
Qed.

Lemma ordinary_initial_close L j rest k q w :
 0<j -> L=j*7+length rest+3 -> length rest=w*2+1 ->
 k+MD.initial_deficit (j*2) (j*5)+1=2^L ->
 k+1=2*(TT.demand rest+q) -> 0<q -> q*4+3<2^(L+1) ->
 exists out, TC.odd_wall L (w*5+6) q -[mtm]->+ out /\ S.strong out.
Proof.

 intros Hj HL Hm Hdef Hfuel Hq Hcoef.
 assert (HL3:3<=L) by lia.
 assert (HT:0<TT.demand rest<=2^length rest).
 { unfold TT.demand. pose proof (CD.value_bound rest). lia. }
 destruct (mod2 w) as [a Ha|a Ha]; subst w.
 - replace (a*2*5+6) with ((a*5+3)*2) by lia.
   destruct (TS.ordinary_even_image L (a*5+3) q ltac:(lia) Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].
   exists (W.Ed (L+(a*5+3)*7+3) out). split; [exact Hrun|].

   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].
   + apply (TL.even_loose_marker L (a*5+3) q out); assumption || lia.
   + pose proof (EQ.even_tight_equation L (a*5+3) q k

       (MD.initial_deficit (j*2) (j*5)) (TT.demand rest) out
       ltac:(lia) ltac:(lia) Hdef Hfuel Htight Hmass) as HE.

     replace ((a*5+3)*2) with (a*10+6) in HE by lia.
     replace ((a*5+3)*5-1) with (a*25+14) in HE by lia.
     replace L with (j*7+a*4+4) in HE by lia.
     apply (IM.even_initial_marker out a j (TT.demand rest)); try assumption; try lia.
     replace (a*4+1) with (length rest) by lia. lia.
 - replace ((1+a*2)*5+6) with ((a*5+5)*2+1) by lia.
   destruct (TS.ordinary_odd_image L (a*5+5) q Hq Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].

   exists (W.Ed (L+(a*5+5)*7+9) out). split; [exact Hrun|].
   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].
   + apply (TL.odd_loose_marker L (a*5+5) q out); assumption || lia.

   + rewrite deficit_halved in Hdef by exact Hj.

     pose proof (EQ.odd_tight_equation L (a*5+5) q k
       (MD.initial_deficit (j*2) (j*5-1)) (TT.demand rest) out
       ltac:(lia) Hdef Hfuel Htight Hmass) as HE.
     replace ((a*5+5)*2+1) with (a*10+11) in HE by lia.
     replace ((a*5+5)*5+4) with (a*25+29) in HE by lia.
     replace (L-1) with (j*7+a*4+5) in HE by lia.
     apply (IM.odd_initial_marker out a j (TT.demand rest)); try assumption; try lia.
     replace (a*4+3) with (length rest) by lia. lia.
Qed.

Print Assumptions ordinary_initial_close.
End TightInitialClosure.
End TightInitialClosure.

Module TightDirect.
(* Full tight-wall closure when the first ordinary one is at an even position.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.ES_v3.
Import TightEd TightMarked TightTrace TightInitialClosure MarkedTrace.
Import OddMarkedEntry OddFuel OddImage MarkedDeficit TerminalClosure TightPrimer.
Import StrongInvariant CounterRules CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module TightDirect.
Module W := WallInvariant.WallInvariant.

Module S := StrongInvariant.StrongInvariant.
Module TE := TightEd.TightEd.
Module TM := TightMarked.TightMarked.
Module TR := TightTrace.TightTrace.
Module IC := TightInitialClosure.TightInitialClosure.
Module M := MarkedTrace.MarkedTrace.
Module ME := OddMarkedEntry.OddMarkedEntry.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module MD := MarkedDeficit.MarkedDeficit.
Module TC := TerminalClosure.TerminalClosure.

Module TT := TightPrimer.TightPrimer.

Module CR := CounterRules.CounterRules.
Module CD := CDPasses.CDPasses.
Notation mtm := W.mtm.
Open Scope sym.
Notation one := [1].
Notation endword := [1;0;0;1;0].
Notation tight := [0;0;0;1;0;0;1;0].
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Open Scope nat.

Lemma tight_direct n bs v tail :
 length bs+2=n -> W.marked 1 bs ->
 false::bs=repeat false (v*2)++true::tail ->
 exists out, W.Ed n bs -[mtm]->+ out /\ S.strong out.
Proof.

 intros Hn Hmark Hword.
 assert (Hzero:W.first_zero (false::bs)) by (eexists; reflexivity).
 assert (Hv:0<v).
 { rewrite Hword in Hzero. apply M.first_zero_prefix in Hzero. lia. }
 assert (Hn':n=v*2+length tail+2).
 { pose proof (f_equal (@length bool) Hword) as Hlength.
   rewrite length_app,repeat_length in Hlength. cbn[length] in Hlength. lia. }
 set (L:=n+1+v*5).
 set (k:=F.grown (I.first_fuel n (v*2)) (v*5)).

 assert (Hroute:M.wall_route n (false::bs) L k tail).
 { rewrite Hword. constructor. }
 destruct (M.route_bounds _ _ _ _ _ Hroute Hzero ltac:(cbn[length]; lia)) as [Hb Ho].

 pose proof (M.route_margin4 _ _ _ _ _ Hroute Hzero ltac:(cbn[length]; lia)) as Hmin.
 assert (Hrun:W.Ed n bs -[mtm]->+
   CR.LC L k |> one *> CD.third tail *> tight *> 0inf).
 { rewrite <-TM.realign.
   eapply progress_trans.
   - pose proof (TE.tight_Ed_step n bs Hn (TM.marked_true bs Hmark)) as Hstep.
     unfold TE.after,W.wall,ME.odd_wall in *.
     repeat rewrite Str_app_assoc in Hstep. exact Hstep.
   - apply (M.route_run _ _ _ _ _ (endword *> 0inf) Hroute).

     cbn[length]. lia. }
 assert (Hdemand:2*TT.demand tail<=k+1).
 { unfold TT.demand. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.

   pose proof (CD.value_bound tail). lia. }
 destruct (TC.tight_counter_cases L k tail ltac:(lia) Ho Hdemand)
   as [q [Hfuel [Hcoef Hcases]]].
 assert (Hq:0<q).
 { unfold TT.demand in Hfuel. rewrite Nat.pow_add_r in Hmin. cbn[Nat.pow] in Hmin.
   pose proof (Nat.pow_nonzero 2 (length tail) ltac:(lia)). nia. }
 destruct Hcases as [[w [Hw [Hfinish Hinv]]]|[w [Hw Hfinish]]].
 - exists (TC.even_wall L (w*5+2) q). split.
   + eapply progress_trans; eassumption.

   + apply TR.terminal_even_strong; lia.
 - assert (Hdef:k+MD.initial_deficit (v*2) (v*5)+1=2^L).
   { unfold k,L. apply MD.initial_balance. lia. }
   destruct (IC.ordinary_initial_close L v tail k q w Hv

     ltac:(unfold L; lia) Hw Hdef Hfuel Hq Hcoef) as [out [Hlast Hstrong]].
   exists out. split; [|exact Hstrong].
   eapply progress_trans; [exact Hrun|]. eapply progress_trans; eassumption.
Qed.

Print Assumptions tight_direct.
End TightDirect.
End TightDirect.

Module DeficitResidues.
(* Small binary windows in the deficits produced before the final conversion.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import List PeanoNat Lia Bool.
Import ListNotations.
Open Scope nat.

Module DeficitResidues.

Inductive pre_deficit : nat -> Prop :=
| PreInitial v : pre_deficit ((2^(2*v+3)-3)*2^(5*v+3))
| PreOdd d v : pre_deficit d ->
    pre_deficit ((2*d+2^(2*v+3)-1)*2^(5*v+4)).

Definition residues := [0;40;112;1392;3696;7424;7680].

Lemma power_mod_zero coefficient z : 13<=z ->
 (coefficient*2^z) mod 8192=0.
Proof.

 intro Hz.
 assert (Hp:2^z=2^(z-13)*8192).
 { change (2^z=2^(z-13)*2^13).
   rewrite <-Nat.pow_add_r. f_equal. lia. }
 rewrite Hp.
 replace (coefficient*(2^(z-13)*8192)) with
   ((coefficient*2^(z-13))*8192) by nia.
 apply Nat.mod_mul. vm_compute. discriminate.
Qed.

Lemma step_mod d v :
 ((2*d+2^(2*v+3)-1)*2^(5*v+4)) mod 8192 =
 ((2*(d mod 8192)+2^(2*v+3)-1)*2^(5*v+4)) mod 8192.
Proof.

 pose proof (Nat.div_mod d 8192 ltac:(vm_compute; discriminate)) as Hd.
 pose proof (Nat.pow_nonzero 2 (2*v+3) ltac:(lia)) as Hp.
 replace ((2*d+2^(2*v+3)-1)*2^(5*v+4)) with
   ((2*(d mod 8192)+2^(2*v+3)-1)*2^(5*v+4)+
    (2*(d/8192)*2^(5*v+4))*8192) by nia.
 rewrite Nat.mod_add by (vm_compute; discriminate). reflexivity.
Qed.

Lemma initial_residue v :
 In (((2^(2*v+3)-3)*2^(5*v+3)) mod 8192) residues.
Proof.

 destruct v as [|[|v]].
 - vm_compute. tauto.
 - vm_compute. tauto.
 - rewrite power_mod_zero by lia. unfold residues. left. reflexivity.
Qed.

Lemma finite_step :
 forallb (fun r =>
   forallb (fun v =>
     existsb (Nat.eqb (((2*r+2^(2*v+3)-1)*2^(5*v+4)) mod 8192)) residues)
     [0;1]) residues = true.
Proof. vm_compute. reflexivity. Qed.

Lemma residue_step d v :
 In (d mod 8192) residues ->
 In (((2*d+2^(2*v+3)-1)*2^(5*v+4)) mod 8192) residues.
Proof.

 intro Hd. destruct (Nat.le_gt_cases 2 v) as [Hv|Hv].
 - rewrite power_mod_zero by lia. unfold residues. left. reflexivity.
 - rewrite step_mod.
   pose proof finite_step as Hcheck.
   apply forallb_forall with (x:=d mod 8192) in Hcheck; [|exact Hd].
   assert (Hin:In v [0;1]) by (cbn; lia).
   apply forallb_forall with (x:=v) in Hcheck; [|exact Hin].
   apply existsb_exists in Hcheck.
   destruct Hcheck as [r [Hr He]]. apply Nat.eqb_eq in He.
   rewrite He. exact Hr.
Qed.

Lemma deficit_residue d : pre_deficit d -> In (d mod 8192) residues.
Proof.

 intro Hd. induction Hd.
 - apply initial_residue.
 - apply residue_step. exact IHHd.
Qed.

Definition window_test r h p c i :=
 (h<=?i) && ((i<=?3*h+6) &&
 ((i mod 2=?p) && (((r+c)/2^i) mod 2=?0))).

Lemma finite_windows :
 forallb (fun r =>
   forallb (fun h =>
     forallb (fun p =>
       forallb (fun c => existsb (window_test r h p c) (seq 0 13))
         (seq 0 (2^h))) (seq 0 2)) (seq 0 4)) residues = true.
Proof. vm_compute. reflexivity. Qed.

Lemma residue_window r h p c :
 In r residues -> h<=3 -> p<2 -> c<2^h ->
 exists i, h<=i /\ i<13 /\ i<=3*h+6 /\ i mod 2=p /\
   ((r+c)/2^i) mod 2=0.
Proof.

 intros Hr Hh Hp Hc.
 pose proof finite_windows as Hcheck.
 apply forallb_forall with (x:=r) in Hcheck; [|exact Hr].
 apply forallb_forall with (x:=h) in Hcheck; [|apply in_seq; lia].
 apply forallb_forall with (x:=p) in Hcheck; [|apply in_seq; lia].
 apply forallb_forall with (x:=c) in Hcheck; [|apply in_seq; lia].
 apply existsb_exists in Hcheck.

 destruct Hcheck as [i [Hi Htest]]. apply in_seq in Hi.
 unfold window_test in Htest.
 repeat rewrite Bool.andb_true_iff in Htest.
 destruct Htest as [Hlo [Hhi [Hpar Hbit]]].
 apply Nat.leb_le in Hlo. apply Nat.leb_le in Hhi.
 apply Nat.eqb_eq in Hpar. apply Nat.eqb_eq in Hbit.
 exists i. repeat split; assumption || lia.
Qed.

Lemma bit_residue d c i : i<13 ->
 ((d+c)/2^i) mod 2=(((d mod 8192)+c)/2^i) mod 2.
Proof.

 intro Hi.
 assert (Hp:8192=(2^(12-i)*2)*2^i).
 { change (2^13=(2^(12-i)*2^1)*2^i).
   rewrite <-!Nat.pow_add_r. f_equal. lia. }
 pose proof (Nat.div_mod d 8192 ltac:(vm_compute; discriminate)) as Hd.
 assert (He:d+c=(d mod 8192)+c+((d/8192)*2^(12-i)*2)*2^i).
 { rewrite Hp in Hd at 1. nia. }
 rewrite He, Nat.div_add by (apply Nat.pow_nonzero; lia).
 rewrite Nat.mod_add by (vm_compute; discriminate). reflexivity.
Qed.

Lemma small_window d h p c :
 pre_deficit d -> h<=3 -> p<2 -> c<2^h ->
 exists i, h<=i /\ i<=3*h+6 /\ i mod 2=p /\
   ((d+c)/2^i) mod 2=0.
Proof.

 intros Hd Hh Hp Hc.
 destruct (residue_window (d mod 8192) h p c
   (deficit_residue d Hd) Hh Hp Hc)
   as [i [Hlo [Hi [Hhi [Hpar Hbit]]]]].
 exists i. repeat split; try assumption.
 rewrite bit_residue by exact Hi. exact Hbit.
Qed.

Print Assumptions deficit_residue.
Print Assumptions small_window.
End DeficitResidues.
End DeficitResidues.

Module BinaryZero.
(* Zero bits under the shifts used by recursive digit conversions.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import PeanoNat Lia.

Module BinaryZero.
Open Scope nat.

Lemma parity_index n p : p<2 ->
 exists i, n<=i /\ i<=n+1 /\ i mod 2=p.
Proof.

 intro Hp. destruct (Nat.eq_dec (n mod 2) p) as [E|E].
 - exists n. repeat split; lia.
 - exists (n+1). repeat split; try lia.
Qed.

Lemma parity_lift s i p : p<2 -> i mod 2=(p+s) mod 2 ->
 (s+i) mod 2=p.
Proof.

 intros Hp Hi. rewrite Nat.add_mod,Hi by lia.
 rewrite (Nat.add_mod p s) by lia.
 pose proof (Nat.mod_upper_bound s 2 ltac:(lia)).
 rewrite (Nat.mod_small p 2) by exact Hp. lia.
Qed.

Lemma zero_below_shift d z c h i :
 c<2^h -> h<=i -> i<z ->
 ((d*2^z+c)/2^i) mod 2=0.
Proof.

 intros Hc Hhi Hiz.

 assert (Hp:2^h<=2^i) by (apply Nat.pow_le_mono_r; lia).

 assert (Hpow:2^z=2^(z-i)*2^i).
 { rewrite <-Nat.pow_add_r. f_equal. lia. }
 replace (d*2^z+c) with (c+(d*2^(z-i))*2^i) by (rewrite Hpow; nia).
 rewrite Nat.div_add by (apply Nat.pow_nonzero; lia).
 rewrite Nat.div_small by lia. cbn[Nat.add].
 replace (z-i) with ((z-i-1)+1) by lia.
 rewrite Nat.pow_add_r. cbn[Nat.pow].
 change ((d*(2^(z-i-1)*2)) mod 2=0).
 replace (d*(2^(z-i-1)*2)) with ((d*2^(z-i-1))*2) by nia.
 apply Nat.mod_mul. lia.
Qed.

Lemma step_div d a z c :
 ((2*d+2^(a+1)-1)*2^z+c)/2^(z+1)=
 d+(2^a-1)+(2^z+c)/2^(z+1).
Proof.

 pose proof (Nat.pow_nonzero 2 a ltac:(lia)).

 assert (E:((2*d+2^(a+1)-1)*2^z+c)=
   (2^z+c)+(d+(2^a-1))*2^(z+1)).
 { rewrite !Nat.pow_add_r. cbn[Nat.pow]. nia. }
 rewrite E,Nat.div_add by (apply Nat.pow_nonzero; lia). lia.
Qed.

Lemma step_bit d a z c i :
 (((2*d+2^(a+1)-1)*2^z+c)/2^((z+1)+i)) mod 2=
 ((d+(2^a-1)+(2^z+c)/2^(z+1))/2^i) mod 2.
Proof.

 rewrite (Nat.pow_add_r 2 (z+1) i),<-Nat.div_div by (apply Nat.pow_nonzero; lia).
 rewrite step_div. reflexivity.
Qed.

Lemma low_carry z c h : c<2^h -> h<=z -> (2^z+c)/2^(z+1)=0.
Proof.

 intros Hc Hh. apply Nat.div_small.
 pose proof (Nat.pow_le_mono_r 2 h z ltac:(lia) Hh).
 rewrite Nat.pow_add_r. cbn[Nat.pow]. lia.
Qed.

Lemma high_carry z c h : c<2^h -> z+1<=h ->
 (2^z+c)/2^(z+1)<=2^(h-z-1).
Proof.

 intros Hc Hh.
 apply Nat.lt_succ_r.
 apply Nat.div_lt_upper_bound; [apply Nat.pow_nonzero; lia|].

 assert (E:2^h=2^(z+1)*2^(h-z-1)).
 { rewrite <-Nat.pow_add_r. f_equal. lia. }
 rewrite E in Hc.

 assert (2^z<2^(z+1)).
 { rewrite Nat.pow_add_r. cbn[Nat.pow].
   pose proof (Nat.pow_nonzero 2 z ltac:(lia)). lia. }
 nia.
Qed.

Print Assumptions step_bit.

Definition window d := forall h p c, p<2 -> c<2^h ->
 exists i, h<=i /\ i<=3*h+6 /\ i mod 2=p /\ ((d+c)/2^i) mod 2=0.

Lemma lift_low d a z h bound p c : window d ->
 p<2 -> c<2^h -> h<=z -> z+1+3*a+6<=bound ->
 exists i, h<=i /\ i<=bound /\ i mod 2=p /\
 (((2*d+2^(a+1)-1)*2^z+c)/2^i) mod 2=0.
Proof.

 intros Hd Hp Hc Hh Hb.

 assert (Ha:2^a-1<2^a) by (pose proof (Nat.pow_nonzero 2 a ltac:(lia)); lia).

 destruct (Hd a ((p+(z+1)) mod 2) (2^a-1)
   (Nat.mod_upper_bound (p+(z+1)) 2 ltac:(lia)) Ha) as [i [Hi [Hupper [Hpar Hzero]]]].
 exists (z+1+i). split; [lia|]. split; [lia|]. split.
 - apply parity_lift; assumption.
 - rewrite step_bit,(low_carry z c h Hc Hh),Nat.add_0_r. exact Hzero.
Qed.

Lemma lift_high d a z h bound p c : window d ->
 p<2 -> c<2^h -> z+1<=h ->
 z+1+3*(a+1)+6<=bound -> z+1+3*(h-z)+6<=bound ->
 exists i, h<=i /\ i<=bound /\ i mod 2=p /\
 (((2*d+2^(a+1)-1)*2^z+c)/2^i) mod 2=0.
Proof.

 intros Hd Hp Hc Hh Ha Hb.
 set (j:=Nat.max (a+1) (h-z)).
 set (r:=(2^z+c)/2^(z+1)).

 assert (Hcarry:r<=2^(h-z-1)) by (unfold r; apply high_carry; assumption).

 assert (Hja:a+1<=j) by (unfold j; apply Nat.le_max_l).

 assert (Hjb:h-z<=j) by (unfold j; apply Nat.le_max_r).

 assert (HpowA:2*2^a<=2^j).
 { replace (2*2^a) with (2^(a+1)) by (rewrite Nat.pow_add_r; cbn[Nat.pow]; nia).
   apply Nat.pow_le_mono_r; lia. }

 assert (HpowB:2*2^(h-z-1)<=2^j).
 { pose proof (Nat.pow_add_r 2 (h-z-1) 1) as Heq.
   replace (h-z-1+1) with (h-z) in Heq by lia. cbn[Nat.pow] in Heq.

   assert (2^(h-z)<=2^j) by (apply Nat.pow_le_mono_r; lia). nia. }

 assert (Hsmall:2^a-1+r<2^j).
 { pose proof (Nat.pow_nonzero 2 a ltac:(lia)). nia. }

 destruct (Hd j ((p+(z+1)) mod 2) (2^a-1+r)
   (Nat.mod_upper_bound (p+(z+1)) 2 ltac:(lia)) Hsmall)
   as [i [Hi [Hupper [Hpar Hzero]]]].
 exists (z+1+i). split; [lia|]. split.
 - unfold j in Hupper. destruct (Nat.le_ge_cases (a+1) (h-z)).
   + rewrite Nat.max_r in Hupper by lia. lia.
   + rewrite Nat.max_l in Hupper by lia. lia.
 - split; [apply parity_lift; assumption|].
   rewrite step_bit. unfold r in Hzero. replace
     (d+(2^a-1)+(2^z+c)/2^(z+1)) with
     (d+(2^a-1+(2^z+c)/2^(z+1))) by lia. exact Hzero.
Qed.

End BinaryZero.
End BinaryZero.

Module DeficitWindow.
(* A bounded zero-bit witness for every recursive conversion deficit.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import BinaryZero DeficitResidues PeanoNat Lia.

Module DeficitWindow.
Module BZ := BinaryZero.BinaryZero.
Module DR := DeficitResidues.DeficitResidues.
Open Scope nat.

Lemma internal_window d : DR.pre_deficit d -> BZ.window d.
Proof.

 intro Hd. induction Hd as [v|d v Hd IH]; intros h p c Hp Hc.
 - destruct (Nat.le_gt_cases h 3) as [Hsmall|Hlarge].
   { apply DR.small_window; try assumption. apply DR.PreInitial. }

   destruct (Nat.le_gt_cases (h+2) (5*v+3)) as [Hz|Hz].
   + destruct (BZ.parity_index h p Hp) as [i [Hi [Htop Hpar]]].
     exists i. repeat split; try lia.
     apply (BZ.zero_below_shift _ _ _ h); lia.
   + assert (Hd:((2^(2*v+3)-3)*2^(5*v+3))<2^(7*v+6)).
     { replace (7*v+6) with ((2*v+3)+(5*v+3)) by lia.
       rewrite (Nat.pow_add_r 2 (2*v+3) (5*v+3)).
       pose proof (Nat.pow_nonzero 2 (2*v+3) ltac:(lia)).
       pose proof (Nat.pow_nonzero 2 (5*v+3) ltac:(lia)). nia. }
     set (j:=Nat.max h (7*v+6)).

     assert (Hh:h<=j) by (unfold j; apply Nat.le_max_l).

     assert (Hv:7*v+6<=j) by (unfold j; apply Nat.le_max_r).

     assert (HpowH:2^h<=2^j) by (apply Nat.pow_le_mono_r; lia).

     assert (HpowV:2^(7*v+6)<=2^j) by (apply Nat.pow_le_mono_r; lia).

     assert (Hsum:(2^(2*v+3)-3)*2^(5*v+3)+c<2^(j+1)).
     { rewrite (Nat.pow_add_r 2 j 1). cbn[Nat.pow]. nia. }

     destruct (BZ.parity_index (j+1) p Hp) as [i [Hi [Htop Hpar]]].
     exists i. split; [lia|]. split.
     * unfold j in Htop. destruct (Nat.le_ge_cases h (7*v+6)).
       -- rewrite Nat.max_r in Htop by lia. lia.
       -- rewrite Nat.max_l in Htop by lia. lia.
     * split; [exact Hpar|].
       rewrite Nat.div_small; [reflexivity|].

       assert (2^(j+1)<=2^i) by (apply Nat.pow_le_mono_r; lia). lia.

 - destruct (Nat.le_gt_cases h 3) as [Hsmall|Hlarge].
   { apply DR.small_window; try assumption. apply DR.PreOdd. exact Hd. }

   destruct (Nat.le_gt_cases (h+2) (5*v+4)) as [Hz|Hz].
   + destruct (BZ.parity_index h p Hp) as [i [Hi [Htop Hpar]]].
     exists i. repeat split; try lia.
     apply (BZ.zero_below_shift _ _ _ h); lia.

   + replace (2*v+3) with ((2*v+2)+1) by lia.

     destruct (Nat.le_gt_cases h (5*v+4)) as [Hh|Hh].
     * apply (BZ.lift_low d (2*v+2) (5*v+4) h (3*h+6) p c);
         try assumption. destruct v; lia.
     * apply (BZ.lift_high d (2*v+2) (5*v+4) h (3*h+6) p c);
         try assumption; lia.
Qed.

Lemma final_window d v h p c :
 DR.pre_deficit d -> 2<=h -> p<2 -> c<2^h ->
 exists i, h<=i /\ i<=3*h+8 /\ i mod 2=p /\
 (((2*d+2^(2*v+2)-1)*2^(5*v+1)+c)/2^i) mod 2=0.
Proof.

 intros Hd Hh Hp Hc. pose proof (internal_window d Hd) as Hw.

 destruct (Nat.le_gt_cases (h+2) (5*v+1)) as [Hz|Hz].
 - destruct (BZ.parity_index h p Hp) as [i [Hi [Htop Hpar]]].
   exists i. repeat split; try lia.
   apply (BZ.zero_below_shift _ _ _ h); lia.
 - replace (2*v+2) with ((2*v+1)+1) by lia.

   destruct (Nat.le_gt_cases h (5*v+1)) as [Hlow|Hhigh].
   + apply (BZ.lift_low d (2*v+1) (5*v+1) h (3*h+8) p c);
       try assumption. destruct v; lia.
   + apply (BZ.lift_high d (2*v+1) (5*v+1) h (3*h+8) p c);
       try assumption; lia.
Qed.

Lemma half_window d v h p c :
 DR.pre_deficit d -> 2<=h -> p<2 -> c<2^h ->
 exists i, h<=i /\ i<=3*h+9 /\ i mod 2=p /\
 (((2*d+2^(2*v+2)-1)*2^(5*v)+c)/2^i) mod 2=0.
Proof.

 intros Hd Hh Hp Hc. pose proof (internal_window d Hd) as Hw.

 destruct (Nat.le_gt_cases (h+2) (5*v)) as [Hz|Hz].
 - destruct (BZ.parity_index h p Hp) as [i [Hi [Htop Hpar]]].
   exists i. repeat split; try lia.
   apply (BZ.zero_below_shift _ _ _ h); lia.
 - replace (2*v+2) with ((2*v+1)+1) by lia.

   destruct (Nat.le_gt_cases h (5*v)) as [Hlow|Hhigh].
   + apply (BZ.lift_low d (2*v+1) (5*v) h (3*h+9) p c);
       try assumption. destruct v; lia.
   + apply (BZ.lift_high d (2*v+1) (5*v) h (3*h+9) p c);
       try assumption; destruct v; lia.
Qed.

Print Assumptions internal_window.
Print Assumptions final_window.
Print Assumptions half_window.
End DeficitWindow.
End DeficitWindow.

Module TightDeficitClass.
(* The deficit grammar of an odd-wall conversion route.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import OddFuel OddImage OddRoute OdDeficit MarkedDeficit MarkedTrace DeficitResidues.
Import List PeanoNat Lia.
Import ListNotations.
Module TightDeficitClass.
Module F := OddFuel.OddFuel.
Module I := OddImage.OddImage.
Module R := OddRoute.OddRoute.
Module OD := OdDeficit.OdDeficit.
Module MD := MarkedDeficit.MarkedDeficit.
Module DR := DeficitResidues.DeficitResidues.

Module M := MarkedTrace.MarkedTrace.
Open Scope nat.

Definition final_deficit d v := (2*d+2^(v*2+2)-1)*2^(v*5+1).

Lemma exact_step L k d u z :
 k+(2^(u+1)-1)+d+1=2^L ->
 F.grown k z+(2*d+2^(u+2)-1)*2^z+1=2^(L+1+z).
Proof.

 intro H.
 pose proof (OD.step_deficit L k d u z ltac:(lia)) as HE.
 rewrite (Nat.pow_add_r 2 z 1) in HE. cbn[Nat.pow] in HE.
 pose proof (Nat.pow_nonzero 2 (u+2) ltac:(lia)). nia.
Qed.

Lemma route_final L k bs L' k' rest :
 R.route L k bs L' k' rest ->
 forall d, DR.pre_deficit d -> k+d+1=2^L ->
 exists previous v,
 DR.pre_deficit previous /\ k'+final_deficit previous v+1=2^L'.
Proof.

 intro Hr. induction Hr; intros d Hd Hbalance.
 - exists d,v. split; [exact Hd|].
   unfold final_deficit. apply exact_step. exact Hbalance.
 - apply (IHHr ((2*d+2^(v*2+3)-1)*2^(v*5+4))).
   + replace (v*2) with (2*v) by lia.
     replace (v*5) with (5*v) by lia.
     apply DR.PreOdd. exact Hd.
   + pose proof (exact_step L k d (v*2+1) (v*5+4)) as HE.
     replace (v*2+1+1) with (v*2+2) in HE by lia.
     replace (v*2+1+2) with (v*2+3) in HE by lia.
     apply HE. exact Hbalance.

Qed.

Lemma initial_odd_final n v tail L k rest :
 R.route (n+1+(v*5+3)) (F.grown (I.first_fuel n (v*2+1)) (v*5+3))
   tail L k rest -> v*2+2<=n ->
 exists previous last,
 DR.pre_deficit previous /\ k+final_deficit previous last+1=2^L.
Proof.

 intros Hr Hn.
 apply (route_final _ _ _ _ _ _ Hr ((2^(v*2+3)-3)*2^(v*5+3))).
 - replace (v*2) with (2*v) by lia.
   replace (v*5) with (5*v) by lia.
   apply DR.PreInitial.
 - pose proof (MD.initial_balance n (v*2+1) (v*5+3) ltac:(lia)) as H.
   unfold MD.initial_deficit in H.
   replace (v*2+1+2) with (v*2+3) in H by lia. exact H.
Qed.

Lemma first_index_unique u v tail rest :
 repeat false u++true::tail=repeat false v++true::rest -> u=v.
Proof.

 gen v. induction u; intros v HE; destruct v; cbn[repeat app] in HE;
   try discriminate; try reflexivity.
 inversion HE. f_equal. apply IHu. assumption.
Qed.

Lemma wall_odd_final n u tail L k rest :
 M.wall_route n (repeat false (u*2+1)++true::tail) L k rest ->
 u*2+2<=n ->
 exists previous last,
 DR.pre_deficit previous /\ k+final_deficit previous last+1=2^L.
Proof.

 intros Hr Hn.
 remember (repeat false (u*2+1)++true::tail) as word eqn:HE in Hr.
 destruct Hr.
 - pose proof (first_index_unique _ _ _ _ HE). lia.
 - pose proof (first_index_unique _ _ _ _ HE) as Hu.
   apply (initial_odd_final _ _ _ _ _ _ H). lia.
Qed.

Print Assumptions route_final.
Print Assumptions initial_odd_final.
Print Assumptions wall_odd_final.
End TightDeficitClass.
End TightDeficitClass.

Module ZeroComplement.
(* A zero in the subtrahend gives a one in its binary complement.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import CounterBits CounterFinish WallInvariant MarkerArithmetic GapMarker.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module ZeroComplement.
Module CB := CounterBits.CounterBits.
Module CF := CounterFinish.CounterFinish.
Module W := WallInvariant.WallInvariant.
Module MA := MarkerArithmetic.MarkerArithmetic.
Module GM := GapMarker.GapMarker.

Lemma zero_bit_residue S i :
 0<S -> ((S-1)/2^i) mod 2=0 ->
 exists r, r<2^i /\ S mod 2^(i+1)=r+1.
Proof.

 intros HS Hz.
 pose proof (Nat.pow_nonzero 2 i ltac:(lia)) as Hp.
 pose proof (Nat.div_mod (S-1) (2^i) Hp) as Hdiv.
 pose proof (Nat.div_mod ((S-1)/2^i) 2 ltac:(lia)) as Hquot.
 rewrite Hz in Hquot.
 pose proof (Nat.mod_upper_bound (S-1) (2^i) Hp) as Hr.
 set (r:=(S-1) mod 2^i).
 set (q:=((S-1)/2^i)/2).
 exists r. split; [exact Hr|].
 assert (HE:S=(r+1)+q*2^(i+1)).
 { unfold r,q. rewrite Nat.pow_add_r. cbn[Nat.pow]. nia. }
 rewrite HE,Nat.mod_add by (apply Nat.pow_nonzero;lia).
 apply Nat.mod_small. rewrite Nat.pow_add_r. cbn[Nat.pow]. unfold r. lia.
Qed.

Lemma zero_complement_mod bs S i :
 0<S -> i mod 2=1 -> ((S-1)/2^i) mod 2=0 ->
 (CB.value bs+S) mod 2^(i+1)=0 -> W.marked 1 bs.
Proof.

 intros HS Hi Hz Hsum.
 destruct (zero_bit_residue S i HS Hz) as [r [Hr Hres]].
 assert (Hp:0<2^i) by (pose proof (Nat.pow_nonzero 2 i ltac:(lia));lia).
 assert (Hc:0<r+1) by lia.
 assert (Hcd:r+1<2^(i+1)) by (rewrite Nat.pow_add_r;cbn[Nat.pow];lia).
 assert (Hsum':(CB.value bs+(r+1)) mod 2^(i+1)=0).
 { rewrite Nat.add_mod in Hsum by (apply Nat.pow_nonzero;lia).
   rewrite Hres in Hsum.
   rewrite Nat.add_mod by (apply Nat.pow_nonzero;lia).
   rewrite (Nat.mod_small (r+1) (2^(i+1)) Hcd). exact Hsum. }

 pose proof (GM.complement_residue (CB.value bs) (2^(i+1)) (r+1) Hc Hcd Hsum') as Hvalue.
 pose proof (GM.marked_residue_auto bs i (2^i-(r+1))) as Hmark.
 rewrite Hi in Hmark. apply Hmark.
 - clear -Hr Hp. lia.
 - rewrite Hvalue,Nat.pow_add_r. cbn[Nat.pow]. clear -Hr Hp. lia.
Qed.

Lemma zero_complement_multiple bs A J D S i :
 0<S -> i<A -> i<J -> i mod 2=1 ->
 ((S-1)/2^i) mod 2=0 ->
 CB.value bs+S+D*2^J=2^A -> W.marked 1 bs.
Proof.

 intros HS HiA HiJ Hi Hz HE.
 apply (zero_complement_mod bs S i); try assumption.
 rewrite (MA.power_multiple (i+1) A), (MA.power_multiple (i+1) J) in HE by lia.
 replace (D*(2^(J-(i+1))*2^(i+1))) with
   ((D*2^(J-(i+1)))*2^(i+1)) in HE by nia.
 apply (f_equal (fun x=>x mod 2^(i+1))) in HE.
 rewrite Nat.mod_add,Nat.mod_mul in HE by (apply Nat.pow_nonzero;lia).
 exact HE.
Qed.

Lemma zero_complement bs L S i :
 0<S -> i<L -> i mod 2=1 -> ((S-1)/2^i) mod 2=0 ->
 CB.value bs+S=2^L -> W.marked 1 bs.
Proof.

 intros HS HiL Hi Hz HE.
 apply (zero_complement_multiple bs L L 0 S i); try assumption. lia.
Qed.

Lemma zero_complement_digits L v S i :
 0<S -> v+S=2^L -> i<L -> i mod 2=1 ->
 ((S-1)/2^i) mod 2=0 -> W.marked 1 (CF.digits L v).
Proof.

 intros HS HE HiL Hi Hz.
 apply (zero_complement (CF.digits L v) L S i); try assumption.
 rewrite CB.digits_value by lia. exact HE.
Qed.

Print Assumptions zero_complement_multiple.
Print Assumptions zero_complement.
Print Assumptions zero_complement_digits.
End ZeroComplement.
End ZeroComplement.

Module TightRecursiveMarker.
(* A zero in an exact conversion deficit preserves the terminal marker.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import DeficitResidues DeficitWindow TightDeficitClass MarkedDeficit ZeroComplement.
Import CounterBits WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Open Scope nat.

Module TightRecursiveMarker.
Module DR := DeficitResidues.DeficitResidues.
Module DW := DeficitWindow.DeficitWindow.
Module TD := TightDeficitClass.TightDeficitClass.
Module MD := MarkedDeficit.MarkedDeficit.
Module ZC := ZeroComplement.ZeroComplement.
Module CB := CounterBits.CounterBits.
Module W := WallInvariant.WallInvariant.

Lemma positive_coefficient b : 2<=b -> 0<2^b-3.
Proof.
 intro Hb. assert (4<=2^b) by (change (2^2<=2^b);apply Nat.pow_le_mono_r;lia). lia.
Qed.

Lemma multiple_width v S E K A :
 0<E -> v+S+E*2^K=2^A -> K<=A.
Proof.
 intros HE Heq. destruct (Nat.le_gt_cases K A) as [Hle|Hgt]; [exact Hle|].
 assert (Hpow:2^A<2^K) by (apply Nat.pow_lt_mono_r;lia).
 clear -HE Heq Hpow. nia.
Qed.

Lemma even_recursive_marker out a L D v T :
 DR.pre_deficit D -> 0<T -> T<=2^(a*4+1) ->
 CB.value out+(2*T-1)+TD.final_deficit D v+
   MD.initial_deficit (a*10+6) (a*25+14)=2^L -> W.marked 1 out.
Proof.

 intros HD HT HTb HE.
 assert (Hc:2*T-2<2^(a*4+2)).
 { replace (a*4+2) with ((a*4+1)+1) by lia.
   rewrite Nat.pow_add_r. cbn[Nat.pow]. clear -HT HTb. lia. }
 destruct (DW.final_window D v (a*4+2) 1 (2*T-2) HD ltac:(lia) ltac:(lia) Hc)
   as [i [Hlo [Hhi [Hpar Hbit]]]].

 assert (Hi:i<a*25+14).
 { destruct (Nat.lt_ge_cases i (a*25+14)); [assumption|].
   assert (Ha:a=0) by (clear -Hhi H;lia). subst a.
   assert (Hi:i=14) by (clear -Hhi H;lia). subst i. discriminate Hpar. }
 set (S:=TD.final_deficit D v+(2*T-1)).
 assert (HS:0<S) by (unfold S;clear -HT;lia).
 assert (HE':CB.value out+S+(2^(a*10+8)-3)*2^(a*25+14)=2^L).
 { unfold S. unfold MD.initial_deficit in HE.
   replace (a*10+6+2) with (a*10+8) in HE by lia. clear -HE. lia. }

 assert (Hcoeff:0<2^(a*10+8)-3) by (apply positive_coefficient;clear -a;lia).
 pose proof (multiple_width (CB.value out) S _ _ _ Hcoeff HE') as Hwidth.
 apply (ZC.zero_complement_multiple out L (a*25+14) (2^(a*10+8)-3) S i);
   [exact HS|clear -Hi Hwidth;lia|exact Hi|exact Hpar| |exact HE'].
 assert (HSbit:S-1=(2*D+2^(2*v+2)-1)*2^(5*v+1)+(2*T-2)).
 { unfold S,TD.final_deficit.
   replace (v*2+2) with (2*v+2) by lia.
   replace (v*5+1) with (5*v+1) by (clear -v;lia). set (F:=(2*D+2^(2*v+2)-1)*2^(5*v+1)).
   clearbody F. clear -HT. lia. }
 rewrite HSbit. exact Hbit.
Qed.

Lemma odd_recursive_marker out a L D v T :
 DR.pre_deficit D -> 0<T -> T<=2^(a*4+3) ->
 CB.value out+(T+3)+(2*D+2^(v*2+2)-1)*2^(v*5)+
   MD.initial_deficit (a*10+11) (a*25+29)=2^L -> W.marked 1 out.
Proof.

 intros HD HT HTb HE.
 assert (Hc:T+2<2^(a*4+4)).
 { assert (8<=2^(a*4+3)) by (change (2^3<=2^(a*4+3));apply Nat.pow_le_mono_r;lia).
   replace (a*4+4) with ((a*4+3)+1) by lia.
   rewrite Nat.pow_add_r. cbn[Nat.pow]. clear -HTb H. lia. }
 destruct (DW.half_window D v (a*4+4) 1 (T+2) HD ltac:(lia) ltac:(lia) Hc)
   as [i [Hlo [Hhi [Hpar Hbit]]]].

 assert (Hi:i<a*25+29) by (clear -Hhi;lia).
 set (S:=(2*D+2^(v*2+2)-1)*2^(v*5)+(T+3)).
 assert (HS:0<S).
 { unfold S. apply Nat.lt_le_trans with (m:=T+3).
   - clear -T. lia.
   - apply Nat.le_add_l. }
 assert (HE':CB.value out+S+(2^(a*10+13)-3)*2^(a*25+29)=2^L).
 { unfold S. unfold MD.initial_deficit in HE.
   replace (a*10+11+2) with (a*10+13) in HE by lia. clear -HE. lia. }

 assert (Hcoeff:0<2^(a*10+13)-3) by (apply positive_coefficient;clear -a;lia).
 pose proof (multiple_width (CB.value out) S _ _ _ Hcoeff HE') as Hwidth.
 apply (ZC.zero_complement_multiple out L (a*25+29) (2^(a*10+13)-3) S i);
   [exact HS|clear -Hi Hwidth;lia|exact Hi|exact Hpar| |exact HE'].
 assert (HSbit:S-1=(2*D+2^(2*v+2)-1)*2^(5*v)+(T+2)).
 { unfold S. replace (v*2+2) with (2*v+2) by lia.
   replace (v*5) with (5*v) by (clear -v;lia).
   set (F:=(2*D+2^(2*v+2)-1)*2^(5*v)). clearbody F. clear -T. lia. }
 rewrite HSbit. exact Hbit.
Qed.

Print Assumptions even_recursive_marker.
Print Assumptions odd_recursive_marker.
End TightRecursiveMarker.
End TightRecursiveMarker.

Module TightRecursiveClosure.
(* Closing the ordinary endpoint after recursive odd conversions.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import TerminalClosure TerminalSuccessor TerminalLoose TightEquations TightRecursiveMarker.
Import TightPrimer StrongInvariant TightDeficitClass DeficitResidues MarkedDeficit.
Import CounterBits CDPasses WallInvariant.
Import List PeanoNat Lia.
Import ListNotations.
Module TightRecursiveClosure.
Module W := WallInvariant.WallInvariant.

Module S := StrongInvariant.StrongInvariant.
Module TC := TerminalClosure.TerminalClosure.
Module TS := TerminalSuccessor.TerminalSuccessor.
Module TL := TerminalLoose.TerminalLoose.
Module EQ := TightEquations.TightEquations.
Module RM := TightRecursiveMarker.TightRecursiveMarker.
Module TT := TightPrimer.TightPrimer.
Module DC := TightDeficitClass.TightDeficitClass.
Module DR := DeficitResidues.DeficitResidues.

Module MD := MarkedDeficit.MarkedDeficit.
Module CB := CounterBits.CounterBits.
Module CD := CDPasses.CDPasses.
Notation mtm := W.mtm.
Open Scope nat.

Lemma final_halved d v :
 DC.final_deficit d v=((2*d+2^(v*2+2)-1)*2^(v*5))*2.
Proof.

 unfold DC.final_deficit. rewrite (Nat.pow_add_r 2 (v*5) 1). cbn[Nat.pow]. nia.
Qed.

Lemma ordinary_recursive_close L d v rest k q w :
 3<=L -> DR.pre_deficit d -> length rest=w*2+1 ->
 k+DC.final_deficit d v+1=2^L ->
 k+1=2*(TT.demand rest+q) -> 0<q -> q*4+3<2^(L+1) ->
 exists out, TC.odd_wall L (w*5+6) q -[mtm]->+ out /\ S.strong out.
Proof.

 intros HL Hd Hm Hdef Hfuel Hq Hcoef.
 assert (HT:0<TT.demand rest<=2^length rest).
 { unfold TT.demand. pose proof (CD.value_bound rest). lia. }
 destruct (mod2 w) as [a Ha|a Ha]; subst w.
 - replace (a*2*5+6) with ((a*5+3)*2) by lia.
   destruct (TS.ordinary_even_image L (a*5+3) q ltac:(lia) Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].
   exists (W.Ed (L+(a*5+3)*7+3) out). split; [exact Hrun|].

   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].
   + apply (TL.even_loose_marker L (a*5+3) q out); assumption || lia.
   + pose proof (EQ.even_tight_equation L (a*5+3) q k
       (DC.final_deficit d v) (TT.demand rest) out
       ltac:(lia) ltac:(lia) Hdef Hfuel Htight Hmass) as HE.
     replace ((a*5+3)*2) with (a*10+6) in HE by lia.
     replace ((a*5+3)*5-1) with (a*25+14) in HE by lia.

     apply (RM.even_recursive_marker out a L d v (TT.demand rest)); try assumption; try lia.
     replace (a*4+1) with (length rest) by lia. lia.
 - replace ((1+a*2)*5+6) with ((a*5+5)*2+1) by lia.
   destruct (TS.ordinary_odd_image L (a*5+5) q Hq Hcoef)
     as [out [Hlen [Hlo [Hhi [Hmass Hrun]]]]].
   exists (W.Ed (L+(a*5+5)*7+9) out). split; [exact Hrun|].
   constructor; [exact Hlen|]. destruct Hlen as [Hloose|Htight].

   + apply (TL.odd_loose_marker L (a*5+5) q out); assumption || lia.
   + rewrite final_halved in Hdef.
     pose proof (EQ.odd_tight_equation L (a*5+5) q k
       ((2*d+2^(v*2+2)-1)*2^(v*5)) (TT.demand rest) out
       ltac:(lia) Hdef Hfuel Htight Hmass) as HE.
     replace ((a*5+5)*2+1) with (a*10+11) in HE by lia.
     replace ((a*5+5)*5+4) with (a*25+29) in HE by lia.
     apply (RM.odd_recursive_marker out a (L-1) d v (TT.demand rest)); try assumption; try lia.

     replace (a*4+3) with (length rest) by lia. lia.
Qed.

Print Assumptions ordinary_recursive_close.
End TightRecursiveClosure.
End TightRecursiveClosure.

Module TightStrong.
(* Closure of all marked displaced walls with tight space.

   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62 BusyCoq.DivModCases.
Import TightTrace TightDirect TightRecursiveClosure TightDeficitClass TightMarked.
Import MarkedTrace OddRoute StrongInvariant WallInvariant TerminalClosure.
Import List PeanoNat Lia.
Import ListNotations.
Module TightStrong.
Module W := WallInvariant.WallInvariant.
Module S := StrongInvariant.StrongInvariant.
Module TR := TightTrace.TightTrace.

Module TD := TightDirect.TightDirect.
Module RC := TightRecursiveClosure.TightRecursiveClosure.
Module DC := TightDeficitClass.TightDeficitClass.
Module TM := TightMarked.TightMarked.
Module M := MarkedTrace.MarkedTrace.
Module R := OddRoute.OddRoute.
Module TC := TerminalClosure.TerminalClosure.
Notation mtm := W.mtm.
Open Scope nat.

Lemma tight_strong n bs :
 length bs+2=n -> W.marked 1 bs ->
 exists out, W.Ed n bs -[mtm]->+ out /\ S.strong out.
Proof.

 intros Hn Hmark.
 destruct (TR.tight_cases n bs Hn Hmark)
   as [L [k [rest [j [q [Hroute [Hlen [HL [Hb [Hmin [Hfuel [Hq [Hcoef Hcases]]]]]]]]]]]]].
 destruct Hcases as [[w [Hw [Hrun Hstrong]]]|[w [Hw Hrun]]].
 - eexists. split; eassumption.
 - destruct (R.first_true (false::bs) (R.marked_true _ (TM.marked_false bs Hmark)))
     as [u [tail Hword]].
   destruct (mod2 u) as [v Hv|v Hv]; subst u.
   + apply (TD.tight_direct n bs v tail); assumption.

   + replace (1+v*2) with (v*2+1) in Hword by lia.
     assert (Hroute':M.wall_route n (repeat false (v*2+1)++true::tail) L k rest).
     { rewrite <-Hword. exact Hroute. }
     assert (Hcap:v*2+2<=n).
     { pose proof (f_equal (@length bool) Hword) as Hlength.
       rewrite length_app,repeat_length in Hlength. cbn[length] in Hlength. lia. }
     destruct (DC.wall_odd_final _ _ _ _ _ _ Hroute' Hcap)
       as [d [last [Hd Hbalance]]].

     destruct (RC.ordinary_recursive_close L d last rest k q w
       ltac:(lia) Hd Hw Hbalance Hfuel Hq Hcoef) as [out [Hlast Hstrong]].
     exists out. split; [|exact Hstrong]. eapply progress_trans; eassumption.
Qed.

Print Assumptions tight_strong.
End TightStrong.
End TightStrong.

Module InitialWall.
(* Entry into the candidate wall family.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62 BusyCoq.ES_v3.
Import WallInvariant.
Import String List PeanoNat Lia.
Import WallInvariant.WallInvariant.
Open Scope sym.

Lemma initial_wall :
  c0 -[mtm]->* E 6 [false;true;false;true].
Proof.
  unfold E, wall, shifted.
  esx.
Qed.

Lemma initial_wall_invariant : invariant (E 6 [false;true;false;true]).
Proof.
  apply InvE.
  - cbn. lia.
  - exists [false], [false;true]. split; reflexivity.
Qed.

Print Assumptions initial_wall.
Print Assumptions initial_wall_invariant.
End InitialWall.

Module StrongEntry.
(* The blank-tape entry and the final progress criterion.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)
Import BusyCoq.Individual62.
Import InitialWall StrongInvariant WallInvariant.
Import String List Lia.
Import ListNotations.
Module StrongEntry.
Module S := StrongInvariant.StrongInvariant.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.

Lemma initial_strong : S.strong (W.E 6 [false;true;false;true]).
Proof. constructor; [cbn; lia|apply S.initial_guard]. Qed.

Lemma closure_nonhalt :
 (forall c, S.strong c -> exists c', c -[mtm]->+ c' /\ S.strong c') ->
 ~halts mtm c0.
Proof.
 intro Hclosure.
 eapply multistep_nonhalt; [exact InitialWall.initial_wall|].
 apply (progress_nonhalt mtm S.strong).
 - intros c Hc. destruct (Hclosure c Hc) as [c' [Hrun Hnext]].
   exists c'. auto.
 - exact initial_strong.
Qed.

Lemma target_mirror :
 flip (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC")=mtm.
Proof.
 apply FunctionalExtensionality.functional_extensionality.
 intros [q s]. destruct q,s; reflexivity.
Qed.

Print Assumptions initial_strong.
Print Assumptions closure_nonhalt.
Print Assumptions target_mirror.
End StrongEntry.
End StrongEntry.

Module StrongClosure.
(* Every wall in the invariant reaches another wall by positive progress.
   AI assistance: this proof sketch, the scripts and the checks were produced
   with the help of GPT-6 Astra (OpenAI). *)

Import BusyCoq.Individual62.
Import StrongInvariant StrongE StrongEdLoose TightStrong StrongEntry WallInvariant.

Module StrongClosure.
Module S := StrongInvariant.StrongInvariant.
Module E := StrongE.StrongE.
Module Ed := StrongEdLoose.StrongEdLoose.
Module T := TightStrong.TightStrong.
Module Entry := StrongEntry.StrongEntry.
Module W := WallInvariant.WallInvariant.
Notation mtm := W.mtm.

Lemma strong_progress c : S.strong c ->
 exists c', c -[mtm]->+ c' /\ S.strong c'.
Proof.
 intro H. destruct H as [n bs Hn Hguard|n bs Hslack Hmarker].
 - apply E.strong_E; assumption.
 - destruct Hslack as [Hloose|Htight].
   + apply Ed.strong_ed_loose; assumption.
   + apply T.tight_strong; assumption.
Qed.

Lemma mirrored_nonhalt : ~halts mtm c0.
Proof. apply Entry.closure_nonhalt. exact strong_progress. Qed.

Print Assumptions mirrored_nonhalt.
End StrongClosure.
End StrongClosure.

From BusyCoq Require Import Individual62.
Require Import String.

Definition tm := Eval compute in
 (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC").

Lemma nonhalt: ~halts tm c0.
Proof.
 apply flip_halts_c0.
 change (~halts (flip (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC")) c0).
 rewrite StrongEntry.StrongEntry.target_mirror.
 exact StrongClosure.StrongClosure.mirrored_nonhalt.
Qed.

Print Assumptions nonhalt.
