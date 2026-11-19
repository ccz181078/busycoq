From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.


Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Module TM1.
  
Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0RA_1LD---_0LD0LE_1RE0LF_1RB1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint LC ls :=
match ls with
| [] => 0inf
| h::t => LC t <* [0] <* [1]^^h
end.

Fixpoint RC ls :=
match ls with
| [] => 0inf
| h::t => [1]^^h *> [0] *> RC t
end.
   
Definition S1 l r :=
  LC l {{A}}> [0;0;0] *> RC r.

Definition S2 l r :=
  LC l {{A}}> [0] *> RC r.

Definition S3 l r :=
  LC l <{{E}} [0;0] *> RC r.

Open Scope nat.

Lemma Inc1 l a b c r:
  S1 (2+a::b::l) (c::r) -->*
  S1 (a::1+b::l) (1+c::r).
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 (n*2+a::b::l) (c::r) -->*
  S1 (a::n+b::l) (n+c::r).
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1 l c r:
  S1 l (c::r) -->*
  S3 l (1+c::r).
Proof.
  es.
Qed.

Lemma IncsOv1 l a b c r:
  S1 (a::b::l) (c::r) -->*
  S3 (a-a/2*2::a/2+b::l) (1+a/2+c::r).
Proof.
  follow (Incs1 (a/2) l (a mod 2) b c r).
  follow Ov1.
  finish.
Qed.

Lemma Rst2 l a c r:
  S2 (a::l) (1+c::r) -->*
  S2 (c::1+a::l) r.
Proof.
  es.
Qed.

Lemma Rst2_00 l r:
  S2 (l) (0::0::r) -->*
  S1 (l) r.
Proof.
  es.
Qed.

Lemma Rst3_1 l r:
  S3 (1::l) r -->*
  S3 l (1::r).
Proof.
  es.
Qed.

Lemma Rst3_2 l a b r:
  S3 (2+a::b::l) r -->*
  S1 (a::1+b::l) r.
Proof.
  es.
Qed.

Lemma Rst3_0_c1 l a b c r:
  S3 (0::a::b::l) (1+c::r) -->*
  S2 (2+a::1+b::l) (c::r).
Proof.
  es.
Qed.

Lemma Rst2_0 l c r:
  halts tm (S2 l (0::1+c::r)).
Proof.
  esx.
Qed.

From BusyCoq Require Import BigUint.

Inductive Tp := t1|t2|t3.

Definition to_config '(tp,l,r) :=
let l:=List.map to_nat l in
let r:=List.map to_nat r in
match tp with
| t1 => S1 l r
| t2 => S2 l r
| t3 => S3 l r
end.

Definition N2 := Eval compute in (succ N1).

Definition pop(ls:list N'):=
(List.hd N0 ls,List.tl ls).

Definition nxt x :=
let '(tp,l,r):=x in
(match tp with
| t1 =>
  let '(a,l):=pop l in
  let '(b,l):=pop l in
  let '(c,r):=pop r in
  let n:=a/N2 in
  Some (t3,a-n*N2::n+b::l,N1+n+c::r)
| t2 =>
  let '(c,r):=pop r in
  match pred c with
  | Some c =>
    let '(a,l):=pop l in
    Some (t2,c::N1+a::l,r)
  | None =>
    let '(c',r):=pop r in
    match pred c' with
    | None => Some (t1,l,r)
    | Some c' => None
    end
  end
| t3 =>
  let '(a,l):=pop l in
  match pred a with
  | Some a =>
    match pred a with
    | Some a =>
      let '(b,l):=pop l in
      Some (t1,a::N1+b::l,r)
    | None =>
      Some (t3,l,N1::r)
    end
  | None =>
    let '(c,r):=pop r in
    match pred c with
    | None => Some x
    | Some c =>
      let '(a,l):=pop l in
      let '(b,l):=pop l in
      Some (t2,N2+a::N1+b::l,c::r)
    end
  end
end)%N'.

Lemma LC_spec x:
  LC (to_nat (List.hd N0 x)::List.map to_nat (List.tl x)) = LC (List.map to_nat x).
Proof.
  destruct x; st; reflexivity.
Qed.

Lemma RC_spec x:
  RC (to_nat (List.hd N0 x)::List.map to_nat (List.tl x)) = RC (List.map to_nat x).
Proof.
  destruct x; st; reflexivity.
Qed.

Ltac des_pred :=
  match goal with
  | |- match match pred ?a with _ => _ end with _ => _ end =>
    let I:=fresh "I" in
    pose proof (inj_pred a) as I;
    destruct (pred a)
  end.

Lemma nxt_spec x:
match nxt x with
| Some x' => to_config x -->* to_config x'
| None => halts tm (to_config x)
end.
Proof.
  unfold nxt,to_config,pop.
  destruct x as [[[] l] r]; repeat des_pred; cbn[List.map]; rw_N'.
  - eapply evstep_trans.
    2: apply IncsOv1.
    unfold S1.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(LC_spec (List.tl l)); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    finish.
  - eapply evstep_trans.
    2: apply Rst2.
    unfold S2.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    finish.
  - unfold S2.
    rewrite <-(RC_spec r); cbn[RC].
    rewrite <-(RC_spec (List.tl r)); cbn[RC].
    rewrite I,I0.
    apply Rst2_0.
  - eapply evstep_trans.
    2: apply Rst2_00.
    unfold S2.
    rewrite <-(RC_spec r); cbn[RC].
    rewrite <-(RC_spec (List.tl r)); cbn[RC].
    finish.
  - eapply evstep_trans.
    2: apply Rst3_2.
    unfold S3.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(LC_spec (List.tl l)); cbn[LC].
    finish.
  - eapply evstep_trans.
    2: apply Rst3_1.
    unfold S3.
    rewrite <-(LC_spec l); cbn[LC].
    finish.
  - eapply evstep_trans.
    2: apply Rst3_0_c1.
    unfold S3.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(LC_spec (List.tl l)); cbn[LC].
    rewrite <-(LC_spec (List.tl (List.tl l))); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    finish.
  - finish.
Qed.

Definition nxt' x :=
match nxt x with
| Some x' => inl x'
| None => inr tt
end.

Import Eqb.

Definition nxts T x :=
  N_iter_until nxt' (inl x) T.

Lemma nxts_spec T x:
match nxts T x with
| inl x' => to_config x -->* to_config x'
| inr _ => halts tm (to_config x)
end.
Proof.
  unfold nxts.
  apply N_iter_until_spec.
  2: finish.
  intros.
  unfold nxt'.
  epose proof (nxt_spec x0).
  destruct (nxt x0).
  - eapply evstep_trans; eauto.
  - eapply halts_evstep; eauto.
Qed.

Lemma nxts_h T:
  nxts T (t1,List.map ofZ [12;40;2]%Z,[]) = inr tt ->
  halts tm c0.
Proof.
  intros.
  epose proof (nxts_spec _ _) as I.
  rewrite H in I.
  eapply halts_evstep.
  1: apply I.
  cbn.
  unfold S1.
  esx.
Qed.

Lemma halt:
  halts tm c0.
Proof.
  eapply (nxts_h (10^9)%N).
  native_check_eq.
Time Qed.

End TM1.


Module TM2.
  
Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC---_1LD0RA_0LE0LF_1RE0LD_0LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint LC ls :=
match ls with
| [] => 0inf
| h::t => LC t <* [0;0] <* [1]^^h
end.

Fixpoint RC ls :=
match ls with
| [] => 0inf
| h::t => [1]^^h *> [0;0] *> RC t
end.

Definition S1 l r :=
  LC l {{A}}> [0;0;0] *> RC r.

Definition S2 l r :=
  LC l {{A}}> [0;0] *> RC r.

Definition S3 l r :=
  LC l <{{D}} [0;0] *> RC r.

Open Scope nat.

Lemma Inc1 l a b c r:
  S1 (2+a::b::l) (c::r) -->*
  S1 (a::1+b::l) (1+c::r).
Proof.
  es.
Qed.

Lemma Incs1 n l a b c r:
  S1 (n*2+a::b::l) (c::r) -->*
  S1 (a::n+b::l) (n+c::r).
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Ov1 l c r:
  S1 l (c::r) -->*
  S3 l (1+c::r).
Proof.
  es.
Qed.

Lemma IncsOv1 l a b c r:
  S1 (a::b::l) (c::r) -->*
  S3 (a-a/2*2::a/2+b::l) (1+a/2+c::r).
Proof.
  follow (Incs1 (a/2) l (a mod 2) b c r).
  follow Ov1.
  finish.
Qed.

Lemma Rst2 l a c r:
  S2 (a::l) (1+c::r) -->*
  S2 (c::1+a::l) r.
Proof.
  es.
Qed.

Lemma Rst2_00 l:
  S2 l [] -->*
  S1 l [].
Proof.
  es.
Qed.

Lemma Rst3_1 l r:
  S3 (1::l) r -->*
  S3 l (1::r).
Proof.
  es.
Qed.

Lemma Rst3_2 l a b r:
  S3 (2+a::b::l) r -->*
  S1 (a::1+b::l) r.
Proof.
  es.
Qed.

Lemma Rst3_0_c1 l a b c r:
  S3 (0::a::b::l) (1+c::r) -->*
  S2 (2+a::1+b::l) (c::r).
Proof.
  es.
Qed.

Lemma Rst2_0 l c r:
  halts tm (S2 (2::l) (0::1+c::r)).
Proof.
  destruct l; esx.
Qed.

From BusyCoq Require Import BigUint.

Inductive Tp := t1|t2|t3.

Definition to_config '(tp,l,r) :=
let l:=List.map to_nat l in
let r:=List.map to_nat r in
match tp with
| t1 => S1 l r
| t2 => S2 l r
| t3 => S3 l r
end.

Definition N2 := Eval compute in (succ N1).

Definition pop(ls:list N'):=
(List.hd N0 ls,List.tl ls).

Definition nxt x :=
let '(tp,l,r):=x in
(match tp with
| t1 =>
  let '(a,l):=pop l in
  let '(b,l):=pop l in
  let '(c,r):=pop r in
  let n:=a/N2 in
  Some (t3,a-n*N2::n+b::l,N1+n+c::r)
| t2 =>
  let '(c,r):=pop r in
  match pred c with
  | Some c =>
    let '(a,l):=pop l in
    Some (t2,c::N1+a::l,r)
  | None =>
    let '(c',r):=pop r in
    match pred c' with
    | None =>
      match r with
      | [] => Some (t1,l,[])
      | _ => Some x
      end
    | Some c' =>
      let '(a,l):=pop l in
      if a=?N2 then None else Some x
    end
  end
| t3 =>
  let '(a,l):=pop l in
  match pred a with
  | Some a =>
    match pred a with
    | Some a =>
      let '(b,l):=pop l in
      Some (t1,a::N1+b::l,r)
    | None =>
      Some (t3,l,N1::r)
    end
  | None =>
    let '(c,r):=pop r in
    match pred c with
    | None => Some x
    | Some c =>
      let '(a,l):=pop l in
      let '(b,l):=pop l in
      Some (t2,N2+a::N1+b::l,c::r)
    end
  end
end)%N'.

Lemma LC_spec x:
  LC (to_nat (List.hd N0 x)::List.map to_nat (List.tl x)) = LC (List.map to_nat x).
Proof.
  destruct x; st; reflexivity.
Qed.

Lemma RC_spec x:
  RC (to_nat (List.hd N0 x)::List.map to_nat (List.tl x)) = RC (List.map to_nat x).
Proof.
  destruct x; st; reflexivity.
Qed.

Ltac des_pred :=
  match goal with
  | |- match match pred ?a with _ => _ end with _ => _ end =>
    let I:=fresh "I" in
    pose proof (inj_pred a) as I;
    destruct (pred a)
  end.

Lemma nxt_spec x:
match nxt x with
| Some x' => to_config x -->* to_config x'
| None => halts tm (to_config x)
end.
Proof.
  unfold nxt,to_config,pop.
  destruct x as [[[] l] r]; repeat des_pred; cbn[List.map]; rw_N'.
  - eapply evstep_trans.
    2: apply IncsOv1.
    unfold S1.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(LC_spec (List.tl l)); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    finish.
  - eapply evstep_trans.
    2: apply Rst2.
    unfold S2.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    finish.
  - destruct (eqb_spec (List.hd N0 l) N2) as [E|E].
    2: finish.
    unfold S2.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    rewrite <-(RC_spec (List.tl r)); cbn[RC].
    rewrite I,I0,E.
    apply Rst2_0.
  - destruct (List.tl (List.tl r)) eqn:E.
    2: finish.
    eapply evstep_trans.
    2: apply Rst2_00.
    unfold S2.
    rewrite <-(RC_spec r); cbn[RC].
    rewrite <-(RC_spec (List.tl r)); cbn[RC].
    rewrite E,I,I0.
    st.
    finish.
  - eapply evstep_trans.
    2: apply Rst3_2.
    unfold S3.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(LC_spec (List.tl l)); cbn[LC].
    finish.
  - eapply evstep_trans.
    2: apply Rst3_1.
    unfold S3.
    rewrite <-(LC_spec l); cbn[LC].
    finish.
  - eapply evstep_trans.
    2: apply Rst3_0_c1.
    unfold S3.
    rewrite <-(LC_spec l); cbn[LC].
    rewrite <-(LC_spec (List.tl l)); cbn[LC].
    rewrite <-(LC_spec (List.tl (List.tl l))); cbn[LC].
    rewrite <-(RC_spec r); cbn[RC].
    finish.
  - finish.
Qed.

Definition nxt' x :=
match nxt x with
| Some x' => inl x'
| None => inr tt
end.

Import Eqb.

Definition nxts T x :=
  N_iter_until nxt' (inl x) T.

Lemma nxts_spec T x:
match nxts T x with
| inl x' => to_config x -->* to_config x'
| inr _ => halts tm (to_config x)
end.
Proof.
  unfold nxts.
  apply N_iter_until_spec.
  2: finish.
  intros.
  unfold nxt'.
  epose proof (nxt_spec x0).
  destruct (nxt x0).
  - eapply evstep_trans; eauto.
  - eapply halts_evstep; eauto.
Qed.

Lemma nxts_h T:
  nxts T (t1,List.map ofZ [12;40;2]%Z,[]) = inr tt ->
  halts tm c0.
Proof.
  intros.
  epose proof (nxts_spec _ _) as I.
  rewrite H in I.
  eapply halts_evstep.
  1: apply I.
  cbn.
  unfold S1.
  esx.
Qed.

Lemma halt:
  halts tm c0.
Proof.
  eapply (nxts_h (10^9)%N).
  native_check_eq.
Time Qed.

End TM2.


