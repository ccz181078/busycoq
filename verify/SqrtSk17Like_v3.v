From BusyCoq Require Import Individual62 Longitudinal ES_v3 LongitudinalHalt.
From Coq Require Import String List ZArith NArith ZifyNat Lia.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RF_1LC0RD_1RC0LE_1LA1RA_1RD---").
Notation hR := (BB62.D,[1]).
Notation hL := (BB62.A,[0]).
Notation h := [(hR,hL)].
Notation o := [1;0;1].
Notation d := [0;1;0;1;0;0].

Lemma cycle20:
  sideRLs tm (h^^20)
    ([0;1;0;1;0;1;0;0;0;0;0;1;0;1;1] *> 0inf)
    (d^^2 *> [0;1;0;1;0;1;0;0;0;0;0;1;0;1;1] *> 0inf).
Proof.
  rewrite <-Str_app_assoc.
  apply BoundedConfig.sideRLs_c_spec with (T:=10^5).
  vm_check_eq.
Qed.

Lemma cycle24:
  sideRLs tm (h^^24)
    ([0;1;0;1;1;0;1] *> 0inf)
    (d^^7 *> [0;1;0;1;1;0;1] *> 0inf).
Proof.
  rewrite <-Str_app_assoc.
  apply BoundedConfig.sideRLs_c_spec with (T:=10^5).
  vm_check_eq.
Qed.

Lemma cycle41:
  sideRLs tm (h^^41)
    ([0;1;0;1;0;1;0;0;1;0;0;0;1;0;1;1] *> 0inf)
    (d^^6 *> [0;1;0;1;0;1;0;0;1;0;0;0;1;0;1;1] *> 0inf).
Proof.
  rewrite <-Str_app_assoc.
  apply BoundedConfig.sideRLs_c_spec with (T:=10^5).
  vm_check_eq.
Qed.

Lemma pass_C: segRLs tm h h d d.
Proof. esx. Qed.

Lemma branch_OC: segRLs tm h (h++h) (o++d) (d++o).
Proof. esx. Qed.

Lemma pass_C_calls k: segRLs tm (h^^k) (h^^k) d d.
Proof. apply segRLs_wall'', pass_C. Qed.

Lemma pass_Cs n: segRLs tm h h (d^^(S n)) (d^^(S n)).
Proof.
  induction n; [exact pass_C|].
  rewrite !lpow_S. eapply segRLs_concat; eauto using pass_C.
Qed.

Lemma branch_one n:
  segRLs tm h (h^^2)
    (o++d^^(S n)) (d++o++d^^n).
Proof.
  destruct n.
  - exact branch_OC.
  - change (segRLs tm h (h++h)
      ((o++d)++d^^(S n)) ((d++o)++d^^(S n))).
    eapply segRLs_concat; [exact branch_OC|].
    exact (segRLs_wall'' (n:=2) (pass_Cs n)).
Qed.

Lemma branch_many m n:
  segRLs tm (h^^m) (h^^(m*2))
    (o++d^^(m+n)) (d^^m++o++d^^n).
Proof.
  induction m.
  - cbn. constructor.
  - change (segRLs tm (h++h^^m) ((h++h)++h^^(m*2))
      ((o++d)++d^^(m+n)) (d++(d^^m++o++d^^n))).
    eapply segRLs_trans; [apply branch_one|].
    eapply segRLs_concat; [apply pass_C_calls|].
    apply IHm.
Qed.

Definition nn := N.to_nat.
Definition ND n := d^^nn n.

Inductive RS :=
| Raw (w:list Sym)
| Cs (n:N) (r:RS)
| Os (r:RS)
| As (r:RS)
| Bs (r:RS).

Fixpoint bits (r:RS) : list Sym :=
  match r with
  | Raw w => w
  | Cs n r => (d^^nn n ++ bits r)%list
  | Os r => (o ++ bits r)%list
  | As r => ([0;0;0] ++ bits r)%list
  | Bs r => ([1;0;0] ++ bits r)%list
  end.

Definition addCs n r :=
  if N.eqb n 0 then r else
  match r with Cs m r => Cs (n+m)%N r | _ => Cs n r end.

Definition obind {A B:Type} (x:option A) (f:A->option B) :=
  match x with Some x => f x | None => None end.

Fixpoint parse (fuel:nat) (w:list Sym) : RS :=
  match fuel with
  | O => Raw w
  | S fuel =>
      match w with
      | 1::0::1::w => Os (parse fuel w)
      | 0::1::0::1::0::0::w => addCs 1%N (parse fuel w)
      | 0::0::0::w => As (parse fuel w)
      | 1::0::0::w => Bs (parse fuel w)
      | _ => Raw w
      end
  end.

Definition parse_bits w := parse (length w) w.

Fixpoint trim0 (w:list Sym) : list Sym :=
  match w with
  | [] => []
  | x::w =>
      match trim0 w with
      | [] => if Eqb.eqb x 0 then [] else [x]
      | w' => x::w'
      end
  end.

Definition edge_run (w:list Sym) : option (list Sym) :=
  match BoundedConfig.steps1_r0inf tm 2000
    (BoundedConfig.Build_T [1] w BB62.D R) with
  | Some (BoundedConfig.Build_T l [] q0 L) =>
      if Eqb.eqb BB62.A q0 then
        BoundedConfig.skip_prefix_list_r0inf [0] l
      else None
  | _ => None
  end.

Definition edge_step r :=
  obind (edge_run (bits r))
    (fun w => Some (parse_bits (trim0 w))).

Definition RS_eq_dec : forall x y:RS, {x=y}+{x<>y}.
Proof.
  decide equality.
  - apply list_eq_dec. decide equality.
  - apply N.eq_dec.
Defined.

Definition s20 := parse_bits [0;1;0;1;0;1;0;0;0;0;0;1;0;1;1].
Definition s24 := parse_bits [0;1;0;1;1;0;1].
Definition s41 := parse_bits [0;1;0;1;0;1;0;0;1;0;0;0;1;0;1;1].
Definition shalt := parse_bits [1;0;1;0;1;0;1;1;0;1;1;1].

Definition cycle_info r : option (N*N) :=
  if RS_eq_dec r s20 then Some (20,2)%N else
  if RS_eq_dec r s24 then Some (24,7)%N else
  if RS_eq_dec r s41 then Some (41,6)%N else None.

Inductive HResult := Returned (r:RS) | Halted.

Definition add_result n x :=
  match x with
  | Returned r => Returned (addCs n r)
  | Halted => Halted
  end.

Definition oneH r : option HResult :=
  if RS_eq_dec r shalt then Some Halted else
  match edge_step r with
  | Some r' => Some (Returned r')
  | None => None
  end.

Fixpoint runH (fuel:nat) (count:N) (r:RS) : option HResult :=
  match count with
  | 0%N => Some (Returned r)
  | _ =>
      match fuel with
      | O => None
      | S fuel =>
          match r with
          | Cs n t =>
              if N.eqb n 0 then runH fuel count t else
              match runH fuel count t with
              | Some x => Some (add_result n x)
              | None => None
              end
          | As t => runH fuel (N.pred count) (Bs t)
          | Bs t => runH fuel (N.pred count) (Os t)
          | Os (Cs n t) =>
              if N.eqb n 0 then
                match oneH r with
                | Some Halted => Some Halted
                | Some (Returned r') => runH fuel (N.pred count) r'
                | None => None
                end
              else
                let moved := N.min count n in
                match runH fuel (2*moved)%N t with
                | Some Halted => Some Halted
                | Some (Returned t') =>
                    runH fuel (count-moved)%N
                      (addCs moved (Os (addCs (n-moved)%N t')))
                | None => None
                end
          | _ =>
              match cycle_info r with
              | Some (period,emitted) =>
                  let copies := (count/period)%N in
                  if N.eqb copies 0 then
                    match oneH r with
                    | Some Halted => Some Halted
                    | Some (Returned r') => runH fuel (N.pred count) r'
                    | None => None
                    end
                  else
                    match runH fuel (count mod period)%N r with
                    | Some x => Some (add_result (copies*emitted)%N x)
                    | None => None
                    end
              | None =>
                  match oneH r with
                  | Some Halted => Some Halted
                  | Some (Returned r') => runH fuel (N.pred count) r'
                  | None => None
                  end
              end
          end
      end
  end.

Fixpoint OCs (xs:list N) (r:RS) : RS :=
  match xs with
  | [] => r
  | x::xs => Os (Cs (N.succ x) (OCs xs r))
  end.

Definition start_right :=
  OCs [0%N;1%N;3%N;7%N;15%N;31%N;63%N;10%N]
    (parse_bits
      [0;0;0;0;1;0;1;0;0;1;0;1;0;0;1;0;1;1;0;1]).

Definition Cache := list (RS*RS).

Fixpoint cache_find r (cache:Cache) : option RS :=
  match cache with
  | [] => None
  | (x,y)::cache => if RS_eq_dec r x then Some y else cache_find r cache
  end.

Definition oneHM r (cache:Cache) : option (HResult*Cache) :=
  if RS_eq_dec r shalt then Some (Halted,cache) else
  match cache_find r cache with
  | Some r' => Some (Returned r',cache)
  | None =>
      match edge_step r with
      | Some r' => Some (Returned r',(r,r')::cache)
      | None => None
      end
  end.

Definition add_mresult n (x:HResult*Cache) :=
  let '(out,cache) := x in (add_result n out,cache).

Fixpoint runHM (fuel:nat) (count:N) (r:RS) (cache:Cache)
    : option (HResult*Cache) :=
  match count with
  | 0%N => Some (Returned r,cache)
  | _ =>
      match fuel with
      | O => None
      | S fuel =>
          match r with
          | Cs n t =>
              if N.eqb n 0 then runHM fuel count t cache else
              match runHM fuel count t cache with
              | Some x => Some (add_mresult n x)
              | None => None
              end
          | As t => runHM fuel (N.pred count) (Bs t) cache
          | Bs t => runHM fuel (N.pred count) (Os t) cache
          | Os (Cs n t) =>
              if N.eqb n 0 then
                match oneHM r cache with
                | Some (Halted,cache') => Some (Halted,cache')
                | Some (Returned r',cache') =>
                    runHM fuel (N.pred count) r' cache'
                | None => None
                end
              else
                let moved := N.min count n in
                match runHM fuel (2*moved)%N t cache with
                | Some (Halted,cache') => Some (Halted,cache')
                | Some (Returned t',cache') =>
                    runHM fuel (count-moved)%N
                      (addCs moved (Os (addCs (n-moved)%N t'))) cache'
                | None => None
                end
          | _ =>
              match cycle_info r with
              | Some (period,emitted) =>
                  let copies := (count/period)%N in
                  if N.eqb copies 0 then
                    match oneHM r cache with
                    | Some (Halted,cache') => Some (Halted,cache')
                    | Some (Returned r',cache') =>
                        runHM fuel (N.pred count) r' cache'
                    | None => None
                    end
                  else
                    match runHM fuel (count mod period)%N r cache with
                    | Some x => Some (add_mresult (copies*emitted)%N x)
                    | None => None
                    end
              | None =>
                  match oneHM r cache with
                  | Some (Halted,cache') => Some (Halted,cache')
                  | Some (Returned r',cache') =>
                      runHM fuel (N.pred count) r' cache'
                  | None => None
                  end
              end
          end
      end
  end.

Fixpoint run_resetsM (inner_fuel fuel:nat) (r:RS) (cache:Cache) : bool :=
  match runHM inner_fuel 1 r cache with
  | Some (Halted,_) => true
  | Some (Returned r',cache') =>
      match fuel with
      | O => false
      | S fuel => run_resetsM inner_fuel fuel (Os r') cache'
      end
  | None => false
  end.

Lemma complete_compute: run_resetsM 1000 240 start_right [] = true.
Proof. native_check_eq. Qed.

Fixpoint denote (r:RS) : side :=
  match r with
  | Raw w => w *> 0inf
  | Cs n r => ND n *> denote r
  | Os r => o *> denote r
  | As r => [0;0;0] *> denote r
  | Bs r => [1;0;0] *> denote r
  end.

Lemma denote_bits r: denote r = bits r *> 0inf.
Proof.
  induction r; cbn [denote bits]; try rewrite IHr;
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma denote_addCs n r: denote (addCs n r) = ND n *> denote r.
Proof.
  unfold addCs.
  destruct (N.eqb_spec n 0); subst; cbn [denote ND nn].
  - reflexivity.
  - destruct r; cbn [denote]; try reflexivity.
    unfold ND, nn. rewrite N2Nat.inj_add, lpow_add, Str_app_assoc.
    reflexivity.
Qed.

Lemma parse_sound fuel w: denote (parse fuel w) = w *> 0inf.
Proof.
  gen w.
  induction fuel; intros; [reflexivity|].
  destruct w as [|x0 w]; [reflexivity|].
  destruct w as [|x1 w]; [destruct x0; reflexivity|].
  destruct w as [|x2 w]; [destruct x0,x1; reflexivity|].
  destruct x0,x1,x2; cbn [parse denote].
  all: try (rewrite IHfuel; reflexivity).
  all: try reflexivity.
  destruct w as [|x3 w]; [reflexivity|]. destruct x3; [reflexivity|].
  destruct w as [|x4 w]; [reflexivity|]. destruct x4; [|reflexivity].
  destruct w as [|x5 w]; [reflexivity|]. destruct x5; [|reflexivity].
  cbn [parse]. rewrite denote_addCs, IHfuel.
  cbn [ND nn]. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma parse_bits_sound w: denote (parse_bits w) = w *> 0inf.
Proof. apply parse_sound. Qed.

Lemma trim0_sound w: trim0 w *> 0inf = w *> 0inf.
Proof.
  induction w as [|x0 w IH]; [reflexivity|].
  cbn [trim0]. destruct (trim0 w) as [|y w'] eqn:E.
  - destruct (Eqb.eqb_spec x0 0); subst.
    + cbn. rewrite <-IH, <-const_unfold. reflexivity.
    + cbn. f_equal. rewrite <-IH. reflexivity.
  - cbn. f_equal. rewrite <-IH. reflexivity.
Qed.

Lemma eq_app_r0inf_refl w: BoundedConfig.eq_app_r0inf w w = true.
Proof.
  induction w; cbn [BoundedConfig.eq_app_r0inf BoundedConfig.all0];
    [reflexivity|].
  destruct (Eqb.eqb_spec a a); [rewrite IHw; reflexivity|congruence].
Qed.

Lemma edge_run_sound w w':
  edge_run w = Some w' -> sideRLs tm h (w *> 0inf) (w' *> 0inf).
Proof.
  intro E.
  apply BoundedConfig.sideRLs_c_spec with (T:=2000).
  unfold edge_run in E.
  cbn [BoundedConfig.sideRLs_c].
  destruct (BoundedConfig.steps1_r0inf tm 2000
    (BoundedConfig.Build_T [1] w BB62.D R)) as [[l r s dr]|] eqn:H;
    [|discriminate].
  destruct r; [|discriminate].
  destruct dr; [|discriminate].
  destruct (Eqb.eqb_spec BB62.A s); subst; [|discriminate].
  destruct (BoundedConfig.skip_prefix_list_r0inf [0] l) eqn:Hskip;
    [|discriminate].
  inversion E; subst.
  rewrite eq_app_r0inf_refl. vm_compute. reflexivity.
Qed.

Lemma edge_step_sound r r':
  edge_step r = Some r' -> sideRLs tm h (denote r) (denote r').
Proof.
  unfold edge_step, obind.
  destruct (edge_run (bits r)) eqn:E; [|discriminate].
  intro H; inversion H; subst.
  rewrite denote_bits, parse_bits_sound, trim0_sound.
  exact (edge_run_sound _ _ E).
Qed.

Lemma hash_A r: sideRLs tm h (denote (As r)) (denote (Bs r)).
Proof. cbn [denote]. es' & (denote r). Qed.

Lemma hash_B r: sideRLs tm h (denote (Bs r)) (denote (Os r)).
Proof. cbn [denote]. es' & (denote r). Qed.

Lemma pass_Cs_calls k n:
  segRLs tm (h^^k) (h^^k) (d^^(S n)) (d^^(S n)).
Proof. apply segRLs_wall'', pass_Cs. Qed.

Lemma pass_Cs_calls_pos k n:
  n <> O -> segRLs tm (h^^k) (h^^k) (d^^n) (d^^n).
Proof.
  intro Hn. replace n with (S (n-1)) by lia. apply pass_Cs_calls.
Qed.

Lemma pass_Cs_calls_N k n:
  n <> 0%N -> segRLs tm (h^^nn k) (h^^nn k) (ND n) (ND n).
Proof.
  intro Hn. unfold ND, nn.
  replace (N.to_nat n) with (S (N.to_nat (N.pred n))).
  - apply pass_Cs_calls.
  - pose proof (f_equal N.to_nat (N.succ_pred n Hn)) as E.
    rewrite N2Nat.inj_succ in E. exact E.
Qed.

Lemma branch_many_N m n:
  (m <= n)%N ->
  segRLs tm (h^^nn m) (h^^nn (2*m)%N)
    (o++ND n) (ND m++o++ND (n-m)%N).
Proof.
  intro Hmn. unfold ND, nn.
  rewrite N2Nat.inj_mul, N2Nat.inj_sub by exact Hmn.
  cbn [Pos.to_nat].
  change (N.to_nat 2) with 2.
  replace (2*N.to_nat m) with (N.to_nat m*2) by lia.
  replace (N.to_nat n) with
    (N.to_nat m+(N.to_nat n-N.to_nat m)) by lia.
  replace (N.to_nat m+(N.to_nat n-N.to_nat m)-N.to_nat m)
    with (N.to_nat n-N.to_nat m) by lia.
  apply branch_many.
Qed.

Lemma prefix_Cs_side k n r r':
  n <> 0%N -> sideRLs tm (h^^nn k) r r' ->
  sideRLs tm (h^^nn k) (ND n *> r) (ND n *> r').
Proof.
  intros Hn H.
  eapply segRLs_sideRLs_concat; [apply pass_Cs_calls_N; exact Hn|exact H].
Qed.

Lemma prefix_Cs_halt k n r:
  n <> 0%N -> sideRLs_halt tm (h^^nn k) r ->
  sideRLs_halt tm (h^^nn k) (ND n *> r).
Proof.
  intros Hn H.
  eapply segRLs_sideRLs_halt_concat;
    [apply pass_Cs_calls_N; exact Hn|exact H].
Qed.

Lemma cycle_iter (k p e:nat) r:
  e <> O ->
  sideRLs tm (h^^p) (denote r) (d^^e *> denote r) ->
  sideRLs tm (h^^(k*p)) (denote r) (d^^(k*e) *> denote r).
Proof.
  intros He Hcycle. induction k.
  - cbn. constructor.
  - replace (S k*p) with (p+k*p) by lia.
    rewrite lpow_add. eapply sideRLs_trans; [exact Hcycle|].
    epose proof
      (segRLs_sideRLs_concat (pass_Cs_calls_pos (k*p) e He) IHk) as H.
    replace (S k*e) with (e+k*e) by lia.
    rewrite lpow_add, Str_app_assoc. exact H.
Qed.

Lemma cycle20_state:
  sideRLs tm (h^^20) (denote s20) (d^^2 *> denote s20).
Proof. unfold s20. rewrite parse_bits_sound. exact cycle20. Qed.

Lemma cycle24_state:
  sideRLs tm (h^^24) (denote s24) (d^^7 *> denote s24).
Proof. unfold s24. rewrite parse_bits_sound. exact cycle24. Qed.

Lemma cycle41_state:
  sideRLs tm (h^^41) (denote s41) (d^^6 *> denote s41).
Proof. unfold s41. rewrite parse_bits_sound. exact cycle41. Qed.

Lemma cycle_info_iter r period emitted copies:
  cycle_info r = Some (period,emitted) ->
  sideRLs tm (h^^nn (copies*period)%N) (denote r)
    (denote (addCs (copies*emitted)%N r)).
Proof.
  unfold cycle_info. destruct (RS_eq_dec r s20) as [->|E20].
  - intro E; inversion E; subst. rewrite denote_addCs. unfold ND, nn.
    rewrite !N2Nat.inj_mul. cbn.
    exact (cycle_iter (N.to_nat copies) 20 2 s20 ltac:(lia)
      cycle20_state).
  - destruct (RS_eq_dec r s24) as [->|E24].
    + intro E; inversion E; subst. rewrite denote_addCs. unfold ND, nn.
      rewrite !N2Nat.inj_mul. cbn.
      exact (cycle_iter (N.to_nat copies) 24 7 s24 ltac:(lia)
        cycle24_state).
    + destruct (RS_eq_dec r s41) as [->|E41]; [|discriminate].
      intro E; inversion E; subst. rewrite denote_addCs. unfold ND, nn.
      rewrite !N2Nat.inj_mul. cbn.
      exact (cycle_iter (N.to_nat copies) 41 6 s41 ltac:(lia)
        cycle41_state).
Qed.

Definition result_spec count r out :=
  match out with
  | Returned r' => sideRLs tm (h^^nn count) (denote r) (denote r')
  | Halted => sideRLs_halt tm (h^^nn count) (denote r)
  end.

Lemma count_pred count:
  count <> 0%N -> nn count = S (nn (N.pred count)).
Proof.
  intro H. unfold nn.
  pose proof (f_equal N.to_nat (N.succ_pred count H)) as E.
  rewrite N2Nat.inj_succ in E. exact (eq_sym E).
Qed.

Lemma result_after_one count r r1 out:
  count <> 0%N ->
  sideRLs tm h (denote r) (denote r1) ->
  result_spec (N.pred count) r1 out ->
  result_spec count r out.
Proof.
  intros Hcount Hstep Hrest. unfold result_spec in *.
  rewrite count_pred by exact Hcount. cbn [lpow]. destruct out.
  - eapply sideRLs_trans; eassumption.
  - eapply sideRLs_halt_app_right; eassumption.
Qed.

Lemma result_trans_N total used rest r r1 out:
  total = (used+rest)%N ->
  sideRLs tm (h^^nn used) (denote r) (denote r1) ->
  result_spec rest r1 out -> result_spec total r out.
Proof.
  intros -> Hrun Hrest. unfold result_spec in *.
  unfold nn. rewrite N2Nat.inj_add, lpow_add. destruct out.
  - eapply sideRLs_trans; eassumption.
  - eapply sideRLs_halt_app_right; eassumption.
Qed.

Lemma halt_prefix_N total used r:
  (used <= total)%N ->
  sideRLs_halt tm (h^^nn used) (denote r) ->
  sideRLs_halt tm (h^^nn total) (denote r).
Proof.
  intros Hle Hhalt.
  replace total with (used+(total-used))%N by
    (rewrite N.add_comm, N.sub_add by exact Hle; reflexivity).
  unfold nn. rewrite N2Nat.inj_add, lpow_add.
  apply sideRLs_halt_app_left. exact Hhalt.
Qed.

Lemma prefix_result count n r out:
  n <> 0%N -> result_spec count r out ->
  result_spec count (addCs n r) (add_result n out).
Proof.
  intros Hn H. unfold result_spec in *. destruct out; cbn [add_result].
  - rewrite !denote_addCs. eapply prefix_Cs_side; eassumption.
  - rewrite denote_addCs. eapply prefix_Cs_halt; eassumption.
Qed.

Lemma prefix_Cs_result count n r out:
  n <> 0%N -> result_spec count r out ->
  result_spec count (Cs n r) (add_result n out).
Proof.
  intros Hn H. unfold result_spec in *. destruct out; cbn [add_result denote].
  - rewrite denote_addCs. eapply prefix_Cs_side; eassumption.
  - eapply prefix_Cs_halt; eassumption.
Qed.

Lemma branch_side_N moved n r r':
  (moved <= n)%N ->
  sideRLs tm (h^^nn (2*moved)%N) (denote r) (denote r') ->
  sideRLs tm (h^^nn moved) (denote (Os (Cs n r)))
    (denote (addCs moved (Os (addCs (n-moved)%N r')))).
Proof.
  intros Hle H.
  epose proof
    (segRLs_sideRLs_concat (branch_many_N moved n Hle) H) as E.
  cbn [denote]. rewrite denote_addCs. cbn [denote]. rewrite denote_addCs.
  repeat rewrite Str_app_assoc in E. exact E.
Qed.

Lemma branch_halt_N moved n r:
  (moved <= n)%N ->
  sideRLs_halt tm (h^^nn (2*moved)%N) (denote r) ->
  sideRLs_halt tm (h^^nn moved) (denote (Os (Cs n r))).
Proof.
  intros Hle H.
  epose proof
    (segRLs_sideRLs_halt_concat tm _ _ _ _ _
      (branch_many_N moved n Hle) H) as E.
  cbn [denote]. repeat rewrite Str_app_assoc in E. exact E.
Qed.

Lemma cycle_info_positive r period emitted:
  cycle_info r = Some (period,emitted) ->
  period <> 0%N /\ emitted <> 0%N.
Proof.
  unfold cycle_info. destruct (RS_eq_dec r s20); [intro E; inversion E|].
  - split; discriminate.
  - destruct (RS_eq_dec r s24); [intro E; inversion E|].
    + split; discriminate.
    + destruct (RS_eq_dec r s41); [intro E; inversion E|discriminate].
      split; discriminate.
Qed.

Lemma cycle_result count r period emitted copies out:
  cycle_info r = Some (period,emitted) ->
  copies = (count/period)%N -> copies <> 0%N ->
  result_spec (count mod period)%N r out ->
  result_spec count r (add_result (copies*emitted)%N out).
Proof.
  intros Hcycle -> Hcopies Hrest.
  destruct (cycle_info_positive _ _ _ Hcycle) as [Hperiod Hemitted].
  pose proof (cycle_info_iter r period emitted
    (count/period)%N Hcycle) as Hiter.
  pose proof (prefix_result (count mod period)%N
    ((count/period)*emitted)%N r out) as Hprefix.
  specialize (Hprefix ltac:(intro E; apply N.mul_eq_0 in E; tauto) Hrest).
  eapply result_trans_N with
    (used:=((count/period)*period)%N)
    (rest:=(count mod period)%N) (r1:=addCs ((count/period)*emitted)%N r).
  - rewrite N.mul_comm. exact (N.div_mod count period Hperiod).
  - exact Hiter.
  - exact Hprefix.
Qed.

Lemma halt_state:
  sideRLs_halt tm h (denote shalt).
Proof.
  unfold shalt. rewrite parse_bits_sound.
  eapply sideRLs_halt_here. intros l.
  unfold to_DH_config. es' & l.
Qed.

Lemma oneH_sound r out:
  oneH r = Some out -> result_spec 1%N r out.
Proof.
  unfold oneH. destruct (RS_eq_dec r shalt) as [->|E].
  - intro H; inversion H; subst. exact halt_state.
  - destruct (edge_step r) eqn:Hstep; [|discriminate].
    intro H; inversion H; subst. cbn [result_spec nn lpow].
    exact (edge_step_sound _ _ Hstep).
Qed.

Lemma oneH_halted count r:
  count <> 0%N -> oneH r = Some Halted -> result_spec count r Halted.
Proof.
  intros Hcount H. apply oneH_sound in H. unfold result_spec in *.
  eapply halt_prefix_N with (used:=1%N).
  - destruct count as [|p]; [contradiction|exact (Pos.le_1_l p)].
  - exact H.
Qed.

Ltac solve_runH_default IH E fuel count r :=
  destruct (cycle_info r) as [[period emitted]|] eqn:Hcycle;
  [ destruct (N.eqb_spec (count/period)%N 0%N);
    [ destruct (oneH r) as [[r'|]|] eqn:Hone;
      [ eapply result_after_one;
        [ discriminate
        | apply oneH_sound in Hone; exact Hone
        | eapply IH; exact E ]
      | inversion E; subst; eapply oneH_halted; [discriminate|exact Hone]
      | discriminate ]
    | destruct (runH fuel (count mod period)%N r) eqn:Hrun;
      [ inversion E; subst; eapply cycle_result; eauto
      | discriminate ] ]
  | destruct (oneH r) as [[r'|]|] eqn:Hone;
    [ eapply result_after_one;
      [ discriminate
      | apply oneH_sound in Hone; exact Hone
      | eapply IH; exact E ]
    | inversion E; subst; eapply oneH_halted; [discriminate|exact Hone]
    | discriminate ] ].

Ltac solve_runH_one IH E count r :=
  destruct (oneH r) as [[r'|]|] eqn:Hone;
  [ eapply result_after_one;
    [ discriminate
    | apply oneH_sound in Hone; exact Hone
    | eapply IH; exact E ]
  | inversion E; subst; eapply oneH_halted; [discriminate|exact Hone]
  | discriminate ].

Lemma runH_sound fuel count r out:
  runH fuel count r = Some out -> result_spec count r out.
Proof.
  gen count r out. induction fuel; intros count r out E;
    destruct count as [|count]; cbn [runH] in E |- *.
  - inversion E; constructor.
  - discriminate.
  - inversion E; constructor.
  - destruct r as [w|n t|t|t|t].
    + solve_runH_default IHfuel E fuel (N.pos count) (Raw w).
    + destruct (N.eqb_spec n 0%N); subst.
      * pose proof (IHfuel _ _ _ E) as H.
        unfold result_spec in *. destruct out;
          cbn [denote ND nn] in *; exact H.
      * destruct (runH fuel (N.pos count) t) as [[r'|]|] eqn:Hrun;
          try discriminate; inversion E; subst.
        -- change (result_spec (N.pos count) (Cs n t)
             (add_result n (Returned r'))).
           eapply prefix_Cs_result; [exact n0|eapply IHfuel; exact Hrun].
        -- change (result_spec (N.pos count) (Cs n t) (add_result n Halted)).
           eapply prefix_Cs_result; [exact n0|eapply IHfuel; exact Hrun].
    + destruct t as [w|n u|u|u|u].
      * solve_runH_default IHfuel E fuel (N.pos count) (Os (Raw w)).
      * destruct (N.eqb_spec n 0%N); subst.
        -- solve_runH_one IHfuel E (N.pos count) (Os (Cs 0 u)).
        -- remember (N.min (N.pos count) n) as moved.
           destruct (runH fuel (2*moved)%N u) as [[u'|]|] eqn:Hinner;
             [| |discriminate].
           ++ destruct (runH fuel (N.pos count-moved)%N
                (addCs moved (Os (addCs (n-moved)%N u')))) eqn:Hrest;
                [|discriminate].
              inversion E; subst out.
              eapply result_trans_N with (used:=moved)
                (rest:=(N.pos count-moved)%N)
                (r1:=addCs moved (Os (addCs (n-moved)%N u'))).
              ** rewrite N.add_comm, N.sub_add.
                 --- reflexivity.
                 --- subst moved. apply N.le_min_l.
              ** eapply branch_side_N.
                 --- subst moved. apply N.le_min_r.
                 --- pose proof (IHfuel _ _ _ Hinner) as H.
                     exact H.
              ** eapply IHfuel. exact Hrest.
           ++ inversion E; subst out.
              eapply halt_prefix_N with (used:=moved).
              ** subst moved. apply N.le_min_l.
              ** eapply branch_halt_N.
                 --- subst moved. apply N.le_min_r.
                 --- pose proof (IHfuel _ _ _ Hinner) as H.
                     exact H.
      * solve_runH_default IHfuel E fuel (N.pos count) (Os (Os u)).
      * solve_runH_default IHfuel E fuel (N.pos count) (Os (As u)).
      * solve_runH_default IHfuel E fuel (N.pos count) (Os (Bs u)).
    + eapply result_after_one; [discriminate|apply hash_A|].
      eapply IHfuel. exact E.
    + eapply result_after_one; [discriminate|apply hash_B|].
      eapply IHfuel. exact E.
Qed.

Notation hL_at := (BB62.A,[0;0]).
Notation hat := [(hR,hL_at)].
Notation z := [0;0;0].
Notation w := [1;0;1;0;0].
Notation x := [1;0;1;0;1;0;0].
Notation lh :=
  (0inf<*<[1;1;1;1;0;0;1;1;1;1;1;0;1;0;1;0;1;1;1;1;1;1;0;1;1]).

Lemma left_reset r:
  lh {{{ (hL_at,L) }}} r -[tm]->+
  lh {{{ (hR,R) }}} w *> r.
Proof. esx. Qed.

Lemma w_wall: segRLs tm hat hat w w.
Proof. esx. Qed.

Lemma w_walls n: segRLs tm hat hat (w^^n) (w^^n).
Proof.
  induction n; [apply segRLs_nil|].
  rewrite !lpow_S. eapply segRLs_concat; eauto using w_wall.
Qed.

Lemma odd_base r: sideRLs tm hat (w *> z *> r) (x *> r).
Proof. es' & r. Qed.

Lemma odd_side n r:
  sideRLs tm hat (w^^(S n) *> z *> r) (w^^n *> x *> r).
Proof.
  rewrite lpow_S, <-lpow_shift, Str_app_assoc.
  eapply segRLs_sideRLs_concat; [apply w_walls|apply odd_base].
Qed.

Lemma launch_base: segRLs tm hat h x (z++o).
Proof. esx. Qed.

Lemma launch n: segRLs tm hat h (w^^n++x) (w^^n++z++o).
Proof.
  applys_eq (segRLs_concat (w_walls n) launch_base);
    autorewrite with list; reflexivity.
Qed.

Lemma macro_step m r r':
  sideRLs tm h (denote r) (denote r') ->
  lh {{{ (hL_at,L) }}} w^^m *> z *> denote r -[tm]->+
  lh {{{ (hL_at,L) }}} w^^(S m) *> z *> denote (Os r').
Proof.
  intro Hright.
  eapply progress_trans; [apply left_reset|].
  epose proof (odd_side m (denote r)) as Hodd.
  eapply sideRLs_1 in Hodd.
  eapply progress_trans.
  1: applys_eq Hodd; cbn [lpow]; autorewrite with list; reflexivity.
  eapply progress_trans; [apply left_reset|].
  epose proof (segRLs_sideRLs_concat (launch (S m)) Hright) as Hside.
  eapply sideRLs_1 in Hside. cbn [denote lpow] in Hside |- *.
  applys_eq Hside; autorewrite with list;
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Lemma macro_halt m r:
  sideRLs_halt tm h (denote r) ->
  halts tm (lh {{{ (hL_at,L) }}} w^^m *> z *> denote r).
Proof.
  intro Hright.
  eapply halts_evstep.
  2: apply progress_evstep, left_reset.
  epose proof (odd_side m (denote r)) as Hodd.
  eapply sideRLs_1 in Hodd.
  eapply halts_evstep.
  2: { apply progress_evstep.
       applys_eq Hodd; cbn [lpow]; autorewrite with list; reflexivity. }
  eapply halts_evstep.
  2: apply progress_evstep, left_reset.
  epose proof
    (segRLs_sideRLs_halt_concat tm _ _ _ _ _ (launch (S m)) Hright) as Hside.
  epose proof (sideRLs_halt_single tm _ _ _ Hside lh) as Hhalt.
  cbn [denote lpow] in Hhalt |- *.
  applys_eq Hhalt; autorewrite with list;
    repeat rewrite Str_app_assoc; reflexivity.
Qed.

Definition cache_valid (cache:Cache) :=
  forall r r', In (r,r') cache -> edge_step r = Some r'.

Lemma cache_find_sound cache r r':
  cache_valid cache -> cache_find r cache = Some r' ->
  edge_step r = Some r'.
Proof.
  intros Hvalid. induction cache as [|[x y] cache IH]; cbn; [discriminate|].
  destruct (RS_eq_dec r x); subst.
  - intro E; inversion E; subst. eapply Hvalid. now left.
  - intro E. eapply IH.
    + intros r0 r1 Hin. eapply Hvalid. now right.
    + exact E.
Qed.

Lemma oneHM_refines r cache out cache':
  cache_valid cache -> oneHM r cache = Some (out,cache') ->
  oneH r = Some out /\ cache_valid cache'.
Proof.
  intros Hvalid. unfold oneHM.
  destruct (RS_eq_dec r shalt) as [E|E].
  - intro H; inversion H; subst. split; [|exact Hvalid].
    unfold oneH. destruct (RS_eq_dec shalt shalt); [reflexivity|congruence].
  - destruct (cache_find r cache) eqn:Hfind.
    + intro H; inversion H; subst. split; [|exact Hvalid].
    unfold oneH. destruct (RS_eq_dec r shalt); [congruence|].
    erewrite cache_find_sound; eauto.
    + destruct (edge_step r) eqn:Hstep; [|discriminate].
    intro H; inversion H; subst. split.
    * unfold oneH. destruct (RS_eq_dec r shalt); [congruence|].
      now rewrite Hstep.
    * intros x y [Hxy|Hxy]; [inversion Hxy; subst; exact Hstep|eauto].
Qed.

Ltac solve_runHM_one IH E fuel count r cache Hvalid :=
  destruct (oneHM r cache) as [[[r'|] c]|] eqn:Hone;
  [ destruct (oneHM_refines _ _ _ _ Hvalid Hone) as [Hone' Hc];
    destruct (IH _ _ _ _ _ Hc E) as [Hrun Hc'];
    split; [now rewrite Hone',Hrun|exact Hc']
  | inversion E; subst;
    destruct (oneHM_refines _ _ _ _ Hvalid Hone) as [Hone' Hc];
    split; [now rewrite Hone'|exact Hc]
  | discriminate ].

Ltac solve_runHM_default IH E fuel count r cache Hvalid :=
  destruct (cycle_info r) as [[period emitted]|] eqn:Hcycle;
  [ destruct (N.eqb (count/period)%N 0%N);
    [ solve_runHM_one IH E fuel count r cache Hvalid
    | destruct (runHM fuel (count mod period)%N r cache)
        as [[x c]|] eqn:Hrun; [|discriminate];
      inversion E; subst;
      destruct (IH _ _ _ _ _ Hvalid Hrun) as [Hrun' Hc];
      split; [now rewrite Hrun'|exact Hc] ]
  | solve_runHM_one IH E fuel count r cache Hvalid ].

Lemma runHM_refines fuel count r cache out cache':
  cache_valid cache ->
  runHM fuel count r cache = Some (out,cache') ->
  runH fuel count r = Some out /\ cache_valid cache'.
Proof.
  gen count r cache out cache'. induction fuel;
    intros count r cache out cache' Hvalid E;
    destruct count as [|count]; cbn [runHM runH] in E |- *.
  - inversion E; subst; eauto.
  - discriminate.
  - inversion E; subst; eauto.
  - destruct r as [w|n t|t|t|t].
    + solve_runHM_default IHfuel E fuel (N.pos count) (Raw w) cache Hvalid.
    + destruct (N.eqb n 0%N).
      * eapply IHfuel; eauto.
      * destruct (runHM fuel (N.pos count) t cache) as [[x c]|] eqn:Hrun;
          [|discriminate].
        inversion E; subst. destruct (IHfuel _ _ _ _ _ Hvalid Hrun) as [-> Hc].
        eauto.
    + destruct t as [w|n u|u|u|u].
      * solve_runHM_default IHfuel E fuel (N.pos count)
          (Os (Raw w)) cache Hvalid.
      * destruct (N.eqb n 0%N).
        -- solve_runHM_one IHfuel E fuel (N.pos count)
             (Os (Cs n u)) cache Hvalid.
        -- remember (N.min (N.pos count) n) as moved.
           destruct (runHM fuel (2*moved)%N u cache)
             as [[[u'|] c]|] eqn:Hinner; try discriminate.
           ++ destruct (IHfuel _ _ _ _ _ Hvalid Hinner) as [Hinner' Hc].
              destruct (runHM fuel (N.pos count-moved)%N
                (addCs moved (Os (addCs (n-moved)%N u'))) c)
                as [[x c']|] eqn:Hrest; [|discriminate].
              inversion E; subst.
              destruct (IHfuel _ _ _ _ _ Hc Hrest) as [Hrest' Hc'].
              split; [now rewrite Hinner',Hrest'|exact Hc'].
           ++ inversion E; subst.
              destruct (IHfuel _ _ _ _ _ Hvalid Hinner) as [Hinner' Hc].
              split; [now rewrite Hinner'|exact Hc].
      * solve_runHM_default IHfuel E fuel (N.pos count)
          (Os (Os u)) cache Hvalid.
      * solve_runHM_default IHfuel E fuel (N.pos count)
          (Os (As u)) cache Hvalid.
      * solve_runHM_default IHfuel E fuel (N.pos count)
          (Os (Bs u)) cache Hvalid.
    + eapply IHfuel; eauto.
    + eapply IHfuel; eauto.
Qed.

Lemma empty_cache_valid: cache_valid [].
Proof. intros r r' []. Qed.

Lemma run_resetsM_sound inner_fuel fuel m r cache:
  cache_valid cache ->
  run_resetsM inner_fuel fuel r cache = true ->
  halts tm (lh {{{ (hL_at,L) }}} w^^m *> z *> denote r).
Proof.
  gen m r cache. induction fuel as [|fuel IH]; intros m r cache Hvalid H;
    cbn [run_resetsM] in H.
  - destruct (runHM inner_fuel 1 r cache) as [[out cache']|] eqn:E;
      try discriminate.
    destruct out as [r'|]; [discriminate|].
    destruct (runHM_refines _ _ _ _ _ _ Hvalid E) as [Erun _].
    eapply macro_halt. exact (runH_sound _ _ _ _ Erun).
  - destruct (runHM inner_fuel 1 r cache) as [[out cache']|] eqn:E;
      try discriminate.
    destruct (runHM_refines _ _ _ _ _ _ Hvalid E) as [Erun Hvalid'].
    destruct out as [r'|].
    + eapply halts_evstep.
      * exact (IH (S m) (Os r') cache' Hvalid' H).
      * apply progress_evstep, macro_step.
        exact (runH_sound _ _ _ _ Erun).
    + eapply macro_halt. exact (runH_sound _ _ _ _ Erun).
Qed.

Fixpoint multistep_c' tm0 n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm0 n3 c
  | S n1 =>
      match multistep_c tm0 n2 c with
      | Some c => multistep_c' tm0 n1 n2 n3 c
      | None => None
      end
  end.

Lemma multistep_c'_spec tm0 n1 n2 n3 c c':
  multistep_c' tm0 n1 n2 n3 c = Some c' <->
  c -[ tm0 ]->> (n1*n2+n3) / c'.
Proof.
  gen c c'.
  induction n1; cbn [multistep_c']; intros.
  - apply multistep_c_spec.
  - destruct (multistep_c tm0 n2 c) eqn:E.
    + apply multistep_c_spec in E. rewrite IHn1.
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      split; intro H.
      * eapply multistep_trans; eauto.
      * eapply rewind_split in H. destruct H as [u [I1 I2]].
        multistep_deterministic. eauto.
    + split; [congruence|].
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      intro H. eapply rewind_split in H. destruct H as [u [I1 I2]].
      eapply multistep_c_spec in I1. congruence.
Qed.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Lemma init_accelerator:
  c0 -->* lh {{{ (hL_at,L) }}} w^^22 *> z *> denote start_right.
Proof.
  eapply without_counter.
  eapply multistep_c'_spec with (n1:=736) (n2:=736) (n3:=11).
  vm_check_eq.
Qed.

Theorem halt: halts tm c0.
Proof.
  eapply halts_evstep.
  - eapply run_resetsM_sound with
      (inner_fuel:=1000) (fuel:=240) (m:=22) (r:=start_right) (cache:=[]).
    + exact empty_cache_valid.
    + exact complete_compute.
  - exact init_accelerator.
Qed.

End TM1.
