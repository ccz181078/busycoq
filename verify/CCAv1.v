From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal ES_v3 LongitudinalHalt.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Fixpoint sideRL_halt_rec(tm:TM)(l:list Sym)(r:side)(q:Q)(T:nat) :=
match T with
| O => false
| S T =>
  match r with
  | m>>r =>
    match tm (q,m) with
    | Some (m,L,q) =>
      match l with
      | m'::l => sideRL_halt_rec tm l (m'>>m>>r) q T
      | [] => false
      end
    | Some (m,R,q) => sideRL_halt_rec tm (m::l) r q T
    | None => true
    end
  end
end.

Lemma sideRL_halt_rec_spec tm l r q T:
  sideRL_halt_rec tm l r q T = true ->
  (forall l0, halts tm (l0 <* l {{q}}> r)).
Proof.
  gen l r q.
  induction T; cbn[sideRL_halt_rec]; intros.
  1: congruence.
  destruct r as [m r].
  destruct (tm (q,m)) as [[[m0 []] q0]|] eqn:E.
  - destruct l as [|m' l].
    + inverts H.
    + eapply halts_step.
      2: econstructor; apply E.
      cbn.
      eapply IHT in H.
      apply H.
  - eapply halts_step.
    2: econstructor; apply E.
    cbn.
    eapply IHT in H.
    apply H.
  - eapply halted_halts,E.
Qed.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1LA_0RD0LB_0RA1RD_1LC0LF_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR0 := (A,<[0]).
Definition hR(b:bool) := if b then (B,<[0;0;1;0;1]) else (A,<[0;0;1;1;0]).
Definition hL := (C,@nil Sym).
Definition h b := [(hR b,hL)].
Definition h0 := [(hR0,hL)].
Definition w(b:bool) := if b then [1;0;1;0] else [1;0;0;0].

Lemma h0w a:
  segRLs tm h0 (h (negb a)) (w a) [].
Proof.
  destruct a; esc.
Qed.

Lemma hw a b:
  segRLs tm (h a) (h (Bool.eqb a b)) (w b) (w a).
Proof.
  destruct a,b; esc.
Qed.

Fixpoint upds a b :=
match b with
| [] => (a,[])
| b0::b1 =>
  let (a',b'):=upds (Bool.eqb a b0) b1 in
  (a',a::b')
end.

Lemma upds_spec a b a' b':
  upds a b = (a',b') ->
  segRLs tm (h a) (h a') (flat_map w b) (flat_map w b').
Proof.
  gen a a' b'.
  induction b; cbn[upds]; intros.
  - inverts H.
    eapply segRLs_nil.
  - destruct (upds (Bool.eqb a0 a) b) as [a'0 b'0] eqn:E.
    inverts H.
    eapply IHb in E.
    cbn[flat_map].
    eapply segRLs_concat.
    2: apply E.
    apply hw.
Qed.

Fixpoint rw_r(T:nat)(r:side):(list bool)*side :=
match T with
| O => ([],r)
| S T =>
  match r with
  | 1>>0>>0>>0>>r =>
    let (l,r):=rw_r T r in (false::l,r)
  | 1>>0>>1>>0>>r =>
    let (l,r):=rw_r T r in (true::l,r)
  | _ => ([],r)
  end
end.

Lemma rw_r_spec T r l r':
  rw_r T r = (l,r') ->
  r = flat_map w l *> r'.
Proof.
  gen r l r'.
  induction T; cbn; intros.
  - inverts H; trivial.
  - destruct r as [[] r]. 1: inverts H; trivial.
    destruct r as [[] r]. 2: inverts H; trivial.
    destruct r as [[] [[] r]]. 2,4: inverts H; trivial.
    + destruct (rw_r T r) as [l0 r0] eqn:E.
      inverts H.
      apply IHT in E.
      rewrite E; trivial.
    + destruct (rw_r T r) as [l0 r0] eqn:E.
      inverts H.
      apply IHT in E.
      rewrite E; trivial.
Qed.

Section maxT_sec.
Hypothesis maxT:nat.

Definition mstep '(l,r) :=
match l with
| l0::l1 =>
  let (a,l2):=upds (negb l0) l1 in
  match sideRLs_c tm (h a) r maxT with
  | Some r0 =>
    let (l3,r1):=rw_r maxT r0 in
    inl (l2++l3,r1)
  | _ => inr (sideRL_halt_rec tm (snd (hR a)) r (fst (hR a)) maxT)
  end
| _ => inr false
end.

Definition to_config '(l,r) := 0inf <* <[1] {{{ (hL,L) }}} flat_map w l *> r.

Lemma LRst r:
  0inf <* <[1] {{{ (hL,L) }}} r -->*
  0inf <* <[1] {{{ (hR0,R) }}} r.
Proof.
  es.
Qed.

Lemma mstep_spec x:
  match mstep x with
  | inl x' => to_config x -->* to_config x'
  | inr true => halts tm (to_config x)
  | inr false => True
  end.
Proof with trivial.
  unfold mstep,to_config.
  destruct x as [[|l0 l1] r]...
  destruct (upds (negb l0) l1) as [a l2] eqn:E.
  eapply upds_spec in E.
  destruct (sideRLs_c tm (h a) r maxT) as [r0|] eqn:E0.
  - eapply sideRLs_c_spec in E0...
    destruct (rw_r maxT r0) as [l3 r1] eqn:E1.
    eapply rw_r_spec in E1.
    rewrite E1 in E0.
    eassert (I1:_). {
      eapply segRLs_sideRLs_concat.
      1: apply (h0w l0).
      eapply segRLs_sideRLs_concat.
      1: apply E.
      apply E0.
    }
    follow LRst.
    eapply sideRLs_1 in I1.
    eapply progress_evstep.
    cbn[flat_map].
    rewrite flat_map_app.
    do 2 rewrite Str_app_assoc.
    apply I1.
  - destruct (sideRL_halt_rec tm (snd (hR a)) r (fst (hR a)) maxT) eqn:E1...
    eassert (I1:_). {
      eapply segRLs_sideRLs_halt_concat.
      1: apply (h0w l0).
      eapply segRLs_sideRLs_halt_concat.
      1: apply E.
      apply sideRLs_halt_here with (r:=r).
      intros.
      destruct a;
      eapply sideRL_halt_rec_spec in E1; apply E1.
    }
    cbn[flat_map].
    rewrite Str_app_assoc.
    eapply sideRLs_halt_single in I1.
    eapply halts_evstep.
    1: apply I1.
    apply LRst.
Qed.

Import Eqb.

Definition msteps T := N_iter_until mstep (inl ([true],[0;0;1;0;1]*>0inf)) T.

Lemma msteps_spec T:
  match msteps T with
  | inl x => c0 -->* to_config x
  | inr true => halts tm c0
  | inr false => True
  end.
Proof with trivial.
  eapply N_iter_until_spec.
  2: esx.
  intros.
  epose proof (mstep_spec x0) as I1.
  destruct (mstep x0) as [x1|[]]...
  - eapply evstep_trans; eauto 1.
  - eapply halts_evstep; eauto 1.
Qed.

Lemma msteps_spec' T:
  msteps T = inr true ->
  halts tm c0.
Proof.
  intros.
  pose proof (msteps_spec T) as I1.
  rewrite H in I1.
  apply I1.
Qed.

End maxT_sec.

Lemma halt: halts tm c0.
Proof.
  apply msteps_spec' with (maxT:=10^5) (T:=(10^6)%N).
  native_check_eq.
Time Qed.

End TM1.

