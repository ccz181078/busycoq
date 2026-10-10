From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* A common word machine; neither machine's halting behavior is decided. *)
Module TM77.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---").
Definition tm' := Eval compute in (TM_from_str "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W10 | W101.
Fixpoint toLC l := match l with
| [] => 0inf
| W1::l => toLC l << 1
| W10::l => toLC l << 1 << 0
| W101::l => toLC l << 1 << 0 << 1
end.
Inductive Config :=
| hB (l:list Word) (r:side)
| hC (l:list Word) (r:side)
| hD (l:list Word) (r:side)
| hF (l:list Word) (r:side)
| ret (l:list Word) (r:side)
| root (r:side).

Definition to_config (b:bool) c := match c with
| hB l r => if b then toLC l << 1 {{A}}> r
                 else toLC l << 1 << 1 {{B}}> r
| hC l r => if b then toLC l << 1 << 1 {{B}}> r
                 else toLC l << 1 << 1 << 0 {{C}}> r
| hD l r => if b then toLC l << 1 << 0 {{C}}> r
                 else toLC l << 1 << 0 << 1 {{D}}> r
| hF l r => if b then toLC l {{E}}> r
                 else toLC l << 1 {{F}}> r
| ret l r => if b then toLC l <{{F}} r
                  else toLC l <{{E}} 1>>r
| root r => if b then 0inf << 1 {{B}}> r
                else 0inf << 1 << 0 {{C}}> r
end.

Definition f c := match c with
| hB l (0>>r) => Some (hC l r)
| hB l (1>>r) => Some (hB (W1::l) r)
| hC l (0>>r) => Some (ret l ([0;0;1] *> r))
| hC l (1>>r) => Some (hD (W1::l) r)
| hD l (0>>r) => Some (hF (W101::l) r)
| hD l (1>>r) => Some (hB (W10::l) r)
| hF l (0>>r) => Some (hB l r)
| hF _ (1>>_) => None
| ret (W1::l) r => Some (ret l (1>>r))
| ret (W10::l) r => Some (hC l r)
| ret (W101::l) r => Some (hD (W1::l) r)
| ret [] r => Some (root r)
| root (0>>r) => Some (hF [] ([0;1] *> r))
| root (1>>r) => Some (hD [] r)
end.
Definition cfg0 := hB [W1] 0inf.

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c; unfold f;
  repeat match goal with
  | |- context[match ?r with _ >> _ => _ end] => destruct r
  | |- context[match ?s with 0 => _ | 1 => _ end] => destruct s
  | |- context[match ?l with [] => _ | _::_ => _ end] => destruct l
  | |- context[match ?w with W1 => _ | _ => _ end] => destruct w
  end; cbn [to_config toLC]; esx.
Qed.

Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM77.

(* A short word-model proof of the already published 363/470 pair. *)
Module TM78.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1RC0LD_0RE1RA_0LF1LA_1LD0RA_---0LB").
Definition tm' := Eval compute in (TM_from_str "1LB1RC_1RC0LD_0RE1RA_---1LA_1LF0RA_0LF0LB").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W110 | W1100 | W0010 | W00100 | W001.
Fixpoint toLC l := match l with
| [] => 0inf << 1
| W1::l => toLC l << 1
| W110::l => toLC l <* <[1;1;0]
| W1100::l => toLC l <* <[1;1;0;0]
| W0010::l => toLC l <* <[0;0;1;0]
| W00100::l => toLC l <* <[0;0;1;0;0]
| W001::l => toLC l <* <[0;0;1]
end.
Inductive Head := A11 | C111 | E1110 | A1100 | C11001 | E110010
  | A00100 | C001001 | E0010010.
Inductive Config := run (h:Head) (l:list Word) (r:side) | ret (l:list Word) (r:side).
Definition to_config c := match c with
| run A11 l r => toLC l <* <[1;1] {{A}}> r
| run C111 l r => toLC l <* <[1;1;1] {{C}}> r
| run E1110 l r => toLC l <* <[1;1;1;0] {{E}}> r
| run A1100 l r => toLC l <* <[1;1;0;0] {{A}}> r
| run C11001 l r => toLC l <* <[1;1;0;0;1] {{C}}> r
| run E110010 l r => toLC l <* <[1;1;0;0;1;0] {{E}}> r
| run A00100 l r => toLC l <* <[0;0;1;0;0] {{A}}> r
| run C001001 l r => toLC l <* <[0;0;1;0;0;1] {{C}}> r
| run E0010010 l r => toLC l <* <[0;0;1;0;0;1;0] {{E}}> r
| ret l r => toLC l <{{A}} [1;0] *> r
end.
Definition f c := match c with
| run A11 l (0>>r) => Some (ret l (1>>r))
| run A11 l (1>>r) => Some (run C111 l r)
| run C111 l (0>>r) => Some (run E1110 l r)
| run C111 l (1>>r) => Some (run A11 (W1::W1::l) r)
| run E1110 l (0>>r) => Some (ret l ([0;0;1] *> r))
| run E1110 l (1>>r) => Some (run A1100 (W1::l) r)
| run A1100 l (0>>r) => Some (run A11 (W110::l) r)
| run A1100 l (1>>r) => Some (run C11001 l r)
| run C11001 l (0>>r) => Some (run E110010 l r)
| run C11001 l (1>>r) => Some (run A11 (W1100::l) r)
| run E110010 l (0>>r) => Some (ret l ([0;0;1;1;1] *> r))
| run E110010 l (1>>r) => Some (run A00100 (W1::W1::l) r)
| run A00100 l (0>>r) => Some (run A11 (W0010::l) r)
| run A00100 l (1>>r) => Some (run C001001 l r)
| run C001001 l (0>>r) => Some (run E0010010 l r)
| run C001001 l (1>>r) => Some (run A11 (W00100::l) r)
| run E0010010 _ (0>>_) => None
| run E0010010 l (1>>r) => Some (run A00100 (W001::l) r)
| ret (W1::l) r => Some (ret l (1>>r))
| ret (W110::l) r => Some (ret l ([1;1;0] *> r))
| ret (W1100::l) r => Some (run E1110 (W1::W1::l) r)
| ret (W0010::_) _ => None
| ret (W00100::l) r => Some (run E1110 (W001::l) r)
| ret (W001::l) r => Some (run A1100 (W1::l) r)
| ret [] r => Some (run A1100 [] r)
end.
Definition cfg0 := run C111 [W1;W1] ([0;1;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config c -[machine b]->+ to_config c'
| None => halts (machine b) (to_config c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r]; unfold f;
  try destruct s; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f to_config (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM78.

(* 815-table rows 514/701. WX has different tape encodings. *)
Module TM79.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LE_1RD0LF_1RE0RA_1LF0LC_1RC1LC").
Definition tm' := Eval compute in (TM_from_str "1RB1LC_1RC0LE_1RD1RF_1LE0LB_1RF1LB_0RA---").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | WX.
Fixpoint toLC (b:bool) l := match l with
| [] => if b then 0inf << 1 else 0inf
| W1::l => toLC b l << 1
| WX::l => if b then toLC b l << 0 << 1 else toLC b l << 1 << 0
end.
Inductive Head := H0 | H1 | H2 | H3 | H4.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | ret (l:list Word) (r:side) | ret1 (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => if b then toLC b l {{F}}> r else toLC b l << 1 << 0 {{A}}> r
| run H1 l r => if b then toLC b l << 0 {{A}}> r else toLC b l << 1 << 0 << 1 {{B}}> r
| run H2 l r => if b then toLC b l {{B}}> r else toLC b l << 1 << 1 {{C}}> r
| run H3 l r => if b then toLC b l << 1 {{C}}> r else toLC b l <* <[1;1;1] {{D}}> r
| run H4 l r => if b then toLC b l << 1 << 1 {{D}}> r else toLC b l <* <[1;1;1;1] {{E}}> r
| ret l r => if b then toLC b l <{{E}} r else toLC b l <{{F}} [0;1] *> r
| ret1 l r => if b then toLC b l <{{B}} [1;0] *> r else toLC b l <{{C}} [1;0;1;0] *> r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (run H1 l r)
| run H0 _ (1>>_) => None
| run H1 l (0>>r) => Some (run H2 (WX::l) r)
| run H1 l (1>>r) => Some (ret l ([0;0] *> r))
| run H2 l (0>>r) => Some (run H3 l r)
| run H2 l (1>>r) => Some (ret l (0>>r))
| run H3 l (0>>r) => Some (run H4 l r)
| run H3 l (1>>r) => Some (run H0 (W1::W1::l) r)
| run H4 l (0>>r) => Some (ret l ([0;1;1] *> r))
| run H4 l (1>>r) => Some (ret1 l (0>>r))
| ret (WX::l) r => Some (run H0 (W1::W1::l) r)
| ret (W1::W1::l) r => Some (ret l ([0;1] *> r))
| ret (W1::WX::l) r => Some (run H0 (W1::l) ([0;1] *> r))
| ret [W1] r => Some (run H0 [] ([0;1] *> r))
| ret [] r => Some (run H0 [W1] r)
| ret1 (W1::l) r => Some (ret l ([0;1;0] *> r))
| ret1 (WX::l) r => Some (ret1 l ([0;0] *> r))
| ret1 [] r => Some (run H3 [WX;W1] r)
end.
Definition cfg0 := run H0 [W1] ([0;1;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|l r|l r]; unfold f; try destruct s;
  repeat match goal with
  | |- context[match ?l with [] => _ | _::_ => _ end] => destruct l as [|[] l]
  end; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM79.

(* 815-table rows 223/766; return across W1 examines at most one more word. *)
Module TM80.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC1LF_1RD1LD_1RA0RB_1LC0RD_0LC---").
Definition tm' := Eval compute in (TM_from_str "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W10.
Fixpoint toLC l := match l with
| [] => 0inf << 1 << 1
| W1::l => toLC l << 1
| W10::l => toLC l << 1 << 0
end.
Inductive Head := H0 | H1 | H2 | H3 | H4 | H5.
Inductive Config := run (h:Head) (l:list Word) (r:side) | ret (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => if b then toLC l << 1 << 0 {{B}}> r else toLC l << 1 << 0 {{D}}> r
| run H1 l r => if b then toLC l <* <[1;0;1] {{C}}> r else toLC l <* <[1;0;1] {{A}}> r
| run H2 l r => if b then toLC l <* <[1;0;0] {{D}}> r else toLC l <* <[1;0;0] {{B}}> r
| run H3 l r => toLC l <* <[1;0;1;1] {{E}}> r
| run H4 l r => if b then toLC l << 0 << 0 {{F}}> r else toLC l << 1 << 1 {{A}}> r
| run H5 l r => toLC l <* <[1;1;1] {{E}}> r
| ret l r => if b then toLC l <{{B}} [1;0] *> r else toLC l <{{D}} [1;0] *> r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (run H1 l r)
| run H0 l (1>>r) => Some (run H2 l r)
| run H1 l (0>>r) => Some (ret l ([1;1] *> r))
| run H1 l (1>>r) => Some (run H3 l r)
| run H2 l (0>>r) => Some (run H4 (W10::l) r)
| run H2 l (1>>r) => Some (run H5 (W1::l) r)
| run H3 l (0>>r) => Some (run H0 (W1::W1::W1::l) r)
| run H3 l (1>>r) => Some (run H0 (W1::W10::l) r)
| run H4 _ (0>>_) => None
| run H4 l (1>>r) => Some (run H5 l r)
| run H5 l (0>>r) => Some (ret l ([1;1] *> r))
| run H5 l (1>>r) => Some (run H0 (W1::W1::l) r)
| ret (W10::l) r => Some (ret l ([1;1] *> r))
| ret (W1::W1::l) r => Some (ret l ([1;0] *> r))
| ret (W1::W10::l) r => Some (run H2 l ([1;0] *> r))
| ret [W1] r => Some (run H0 [] ([1;1;1;0] *> r))
| ret [] r => Some (run H4 [W10] r)
end.
Definition cfg0 := run H0 [] ([1;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|l r]; unfold f; try destruct s;
  repeat match goal with
  | |- context[match ?l with [] => _ | _::_ => _ end] => destruct l as [|[] l]
  end; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM80.

(* 815-table rows 170/194. The common root is .1; words are 1 and 01. *)
Module TM81.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RE_1LD0LA_1RB1LA_0RF---_1RA1LB").
Definition tm' := Eval compute in (TM_from_str "1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W01.
Fixpoint toLC l := match l with
| [] => 0inf << 1
| W1::l => toLC l << 1
| W01::l => toLC l << 0 << 1
end.
Inductive Head := H0 | H1 | H2 | H3 | H4.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | ret (l:list Word) (r:side) | ret1 (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => if b then toLC l << 0 {{E}}> r else toLC l {{E}}> r
| run H1 l r => if b then toLC l << 0 << 1 {{F}}> r else toLC l << 0 {{F}}> r
| run H2 l r => if b then toLC l << 1 {{B}}> r else toLC l {{A}}> r
| run H3 l r => if b then toLC l << 1 {{C}}> r else toLC l {{B}}> r
| run H4 l r => if b then toLC l << 1 << 1 {{D}}> r else toLC l << 1 {{C}}> r
| ret l r => if b then toLC l <{{B}} 1>>r else toLC l <{{D}} r
| ret1 l r => if b then toLC l <{{A}} [0;1] *> r else toLC l <{{A}} 1>>r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (run H1 l r)
| run H0 _ (1>>_) => None
| run H1 l (0>>r) => Some (run H2 (W01::l) r)
| run H1 l (1>>r) => Some (ret l ([0;0] *> r))
| run H2 l (0>>r) => Some (run H3 (W1::l) r)
| run H2 l (1>>r) => Some (ret l (0>>r))
| run H3 l (0>>r) => Some (run H4 l r)
| run H3 l (1>>r) => Some (run H0 (W1::l) r)
| run H4 l (0>>r) => Some (ret1 l (1>>r))
| run H4 l (1>>r) => Some (ret l ([0;0] *> r))
| ret (W1::l) r => Some (ret1 l r)
| ret (W01::l) r => Some (run H0 (W1::W1::l) r)
| ret [] r => Some (run H0 [W1] r)
| ret1 (W1::l) r => Some (ret l ([0;1] *> r))
| ret1 (W01::l) r => Some (ret1 l ([0;0] *> r))
| ret1 [] r => Some (run H2 [W01;W1] r)
end.
Definition cfg0 := run H0 [W1;W1;W1] 0inf.

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r];
  try destruct s; cbn [f to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM81.

(* 815-table rows 270/545, the latter mirrored. *)
Module TM82.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC---_1RD1LE_1RE0LA_1RF1RB_1LA0LD").
Definition tm' := Eval compute in (TM_from_str "1LB0LC_1RC1LC_1RD0LB_1RA0RE_1RF---_1RC1LA").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W01.
Fixpoint toLC l := match l with
| [] => 0inf
| W1::l => toLC l << 1
| W01::l => toLC l << 0 << 1
end.
Inductive Head := H0 | H1 | H2 | H3 | H4.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | ret (l:list Word) (r:side) | ret1 (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => if b then toLC l << 0 {{E}}> r else toLC l {{B}}> r
| run H1 l r => if b then toLC l << 0 << 1 {{F}}> r else toLC l << 0 {{C}}> r
| run H2 l r => if b then toLC l << 1 {{C}}> r else toLC l {{D}}> r
| run H3 l r => if b then toLC l << 1 << 1 {{D}}> r else toLC l << 1 {{E}}> r
| run H4 l r => if b then toLC l <* <[1;1;1] {{A}}> r else toLC l << 1 << 1 {{F}}> r
| ret l r => if b then toLC l <{{C}} 1>>r else toLC l <{{A}} r
| ret1 l r => if b then toLC l <{{B}} [0;1] *> r else toLC l <{{D}} 1>>r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (run H1 l r)
| run H0 _ (1>>_) => None
| run H1 l (0>>r) => Some (run H2 (W01::l) r)
| run H1 l (1>>r) => Some (ret l ([0;0] *> r))
| run H2 l (0>>r) => Some (run H3 l r)
| run H2 l (1>>r) => Some (ret l (0>>r))
| run H3 l (0>>r) => Some (run H4 l r)
| run H3 l (1>>r) => Some (run H0 (W1::W1::l) r)
| run H4 l (0>>r) => Some (ret l ([0;1;1] *> r))
| run H4 l (1>>r) => Some (ret1 l ([0;0] *> r))
| ret (W1::l) r => Some (ret1 l r)
| ret (W01::l) r => Some (run H0 (W1::W1::l) r)
| ret [] r => Some (run H0 [W1] r)
| ret1 (W1::l) r => Some (ret l ([0;1] *> r))
| ret1 (W01::l) r => Some (ret1 l ([0;0] *> r))
| ret1 [] r => Some (run H0 [W1;W1] r)
end.
Definition cfg0 := run H0 [W1;W1;W1] ([0;1;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r];
  try destruct s; cbn [f to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM82.

(* 815-table rows 570/619, the latter mirrored. Only H1 changes a tape bit. *)
Module TM83.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC---_1RD0RD_1LE1RC_1RA1LE_1RE0LF").
Definition tm' := Eval compute in (TM_from_str "1LB---_1RC0RC_1LD1RB_1RE1LD_0RA1RF_1RD0LF").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Head := H0 | H1 | H2 | H3 | H4 | H5.
Inductive Config := run (h:Head) (l r:side) | ret (l r:side) | ret1 (l r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => if b then l {{E}}> r else l {{A}}> r
| run H1 l r => if b then l << 0 {{A}}> r else l << 1 {{B}}> r
| run H2 l r => if b then l {{B}}> r else l {{C}}> r
| run H3 l r => if b then l {{C}}> r else l {{D}}> r
| run H4 l r => if b then l {{D}}> r else l {{E}}> r
| run H5 l r => l {{F}}> r
| ret l r => l <{{F}} r
| ret1 l r => if b then l <{{D}} r else l <{{E}} r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (run H1 l r)
| run H0 l (1>>r) => Some (run H5 (l<<1) r)
| run H1 l (0>>r) => Some (run H2 (l<<1<<1) r)
| run H1 _ (1>>_) => None
| run H2 l (0>>r) => Some (run H3 (l<<1) r)
| run H2 l (1>>r) => Some (run H3 (l<<0) r)
| run H3 l (0>>r) => Some (ret1 l (1>>r))
| run H3 l (1>>r) => Some (run H2 (l<<1) r)
| run H4 l (0>>r) => Some (run H0 (l<<1) r)
| run H4 l (1>>r) => Some (ret1 l (1>>r))
| run H5 l (0>>r) => Some (run H4 (l<<1) r)
| run H5 l (1>>r) => Some (ret l (0>>r))
| ret (0>>l) r => Some (run H4 (l<<1) r)
| ret (1>>l) r => Some (ret l (0>>r))
| ret1 (0>>l) r => Some (run H0 (l<<1) r)
| ret1 (1>>l) r => Some (ret1 l (1>>r))
end.
Definition cfg0 := run H0 (0inf<<0<<1) ([1;1;1;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[s l] r|[s l] r];
  destruct s; cbn [f to_config]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM83.

(* 815-table rows 238/468. WX is 111 on one tape and 101 on the other. *)
Module TM84.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1RF_1LA1RD_1RB---_1LF1LF_0RB0LA").
Definition tm' := Eval compute in (TM_from_str "1LB0LE_1RC1RF_1LA0RD_1RB---_1LF1LA_0RB0LA").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W10 | WX.
Fixpoint toLC (b:bool) l := match l with
| [] => 0inf
| W10::l => toLC b l << 1 << 0
| WX::l => toLC b l << 1 << (if b then 0 else 1) << 1
end.
Inductive Head := H0 | H1 | H2 | H3.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | ret (l:list Word) (r:side) | ret1 (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => toLC b l << 1 {{C}}> r
| run H1 l r => toLC b l << 1 << (if b then 0 else 1) {{D}}> r
| run H2 l r => toLC b l {{B}}> r
| run H3 l r => toLC b l << 1 {{F}}> r
| ret l r => toLC b l <{{E}} r
| ret1 l r => toLC b l <{{A}} [0;1] *> r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (ret l ([0;1] *> r))
| run H0 l (1>>r) => Some (run H1 l r)
| run H1 l (0>>r) => Some (run H2 (WX::l) r)
| run H1 _ (1>>_) => None
| run H2 l (0>>r) => Some (run H0 l r)
| run H2 l (1>>r) => Some (run H3 l r)
| run H3 l (0>>r) => Some (run H2 (W10::l) r)
| run H3 l (1>>r) => Some (ret l ([0;0] *> r))
| ret (W10::l) r => Some (ret1 l r)
| ret (WX::l) r => Some (ret l ([0;0;1] *> r))
| ret [] r => Some (run H3 [] r)
| ret1 (W10::l) r => Some (ret l ([0;0;0;1] *> r))
| ret1 (WX::l) r => Some (ret1 l ([0;0;1] *> r))
| ret1 [] r => Some (run H3 [WX] r)
end.
Definition cfg0 := run H0 [] (1>>0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r]; unfold f;
  try destruct s; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM84.

(* 815-table rows 594/799. The long main_44 family factors as WX (10)^n. *)
Module TM85.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RF_1LA0LD_1LE1RD_0RA0LC_0LA---").
Definition tm' := Eval compute in (TM_from_str "1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W10 | WX.
Fixpoint toLC (b:bool) l := match l with
| [] => 0inf
| W10::l => toLC b l << 1 << 0
| WX::l => toLC b l << 1 << (if b then 0 else 1) << (if b then 1 else 0)
end.
Inductive Head := H0 | H1 | H2 | H3.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | ret (l:list Word) (r:side) | ret1 (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => toLC b l << 1 {{B}}> r
| run H1 l r => toLC b l << 1 << (if b then 0 else 1) {{F}}> r
| run H2 l r => toLC b l {{A}}> r
| run H3 l r => toLC b l << 1 {{E}}> r
| ret l r => toLC b l <{{D}} r
| ret1 l r => toLC b l <{{C}} [0;1] *> r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (ret l ([0;1] *> r))
| run H0 l (1>>r) => Some (run H1 l r)
| run H1 l (0>>r) => Some (run H2 (WX::l) r)
| run H1 _ (1>>_) => None
| run H2 l (0>>r) => Some (run H0 l r)
| run H2 l (1>>r) => Some (run H3 l r)
| run H3 l (0>>r) => Some (run H2 (W10::l) r)
| run H3 l (1>>r) => Some (ret l ([0;0] *> r))
| ret (W10::l) r => Some (ret1 l r)
| ret (WX::l) r => Some (ret l ([0;0;1] *> r))
| ret [] r => Some (run H3 [] r)
| ret1 (W10::l) r => Some (ret l ([0;0;0;1] *> r))
| ret1 (WX::l) r => Some (ret1 l ([0;0;1] *> r))
| ret1 [] r => Some (run H3 [WX] r)
end.
Definition cfg0 := run H0 [] 0inf.

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r]; unfold f;
  try destruct s; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM85.

(* 815-table rows 238/612; 468/612 then follows using TM84. *)
Module TM86.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1RF_1LA1RD_1RB---_1LF1LF_0RB0LA").
Definition tm' := Eval compute in (TM_from_str "1LB0LE_1RC1RF_1LA1RD_0RB---_1LF1RE_0RB0LA").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W10 | WX.
Fixpoint toLC (b:bool) l := match l with
| [] => 0inf
| W10::l => toLC b l << 1 << 0
| WX::l => toLC b l << 1 << 1 << (if b then 0 else 1)
end.
Inductive Head := H0 | H1 | H2 | H3.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | ret (l:list Word) (r:side) | ret1 (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => toLC b l << 1 {{C}}> r
| run H1 l r => toLC b l << 1 << 1 {{D}}> r
| run H2 l r => toLC b l {{B}}> r
| run H3 l r => toLC b l << 1 {{F}}> r
| ret l r => toLC b l <{{E}} r
| ret1 l r => toLC b l <{{A}} [0;1] *> r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (ret l ([0;1] *> r))
| run H0 l (1>>r) => Some (run H1 l r)
| run H1 l (0>>r) => Some (run H2 (WX::l) r)
| run H1 _ (1>>_) => None
| run H2 l (0>>r) => Some (run H0 l r)
| run H2 l (1>>r) => Some (run H3 l r)
| run H3 l (0>>r) => Some (run H2 (W10::l) r)
| run H3 l (1>>r) => Some (ret l ([0;0] *> r))
| ret (W10::l) r => Some (ret1 l r)
| ret (WX::l) r => Some (ret l ([0;0;1] *> r))
| ret [] r => Some (run H3 [] r)
| ret1 (W10::l) r => Some (ret l ([0;0;0;1] *> r))
| ret1 (WX::l) r => Some (ret1 l ([0;0;1] *> r))
| ret1 [] r => Some (run H3 [WX] r)
end.
Definition cfg0 := run H0 [] (1>>0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r]; unfold f;
  try destruct s; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM86.

(* 815-table rows 107/743. Move the fixed left 1 into the directed head. *)
Module TM87.
Definition tm := Eval compute in (TM_from_str "1LB1LB_0RC0LE_1RD1RB_1LE1RF_1LC0LA_1RC---").
Definition tm' := Eval compute in (TM_from_str "1LB1RA_0RC0LE_1RD1RB_1LE1RF_1LC0LA_0LC---").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W10 | WX.
Fixpoint toLC (b:bool) l := match l with
| [] => 0inf
| W10::l => toLC b l << 1 << 0
| WX::l => toLC b l << 1 << 1 << (if b then 0 else 1)
end.
Inductive Head := HF | HC | HD | HB.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | retA (l:list Word) (r:side) | retE (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run HF l r => toLC b l << 1 << 1 {{F}}> r
| run HC l r => toLC b l {{C}}> r
| run HD l r => toLC b l << 1 {{D}}> r
| run HB l r => toLC b l << 1 {{B}}> r
| retA l r => toLC b l <{{A}} 0 >> r
| retE l r => toLC b l <{{E}} 0 >> r
end.
Definition f c := match c with
| run HF l (0>>r) => Some (run HC (WX::l) r)
| run HF _ (1>>_) => None
| run HC l (0>>r) => Some (run HD l r)
| run HC l (1>>r) => Some (run HB l r)
| run HD l (0>>r) => Some (retA l (1>>r))
| run HD l (1>>r) => Some (run HF l r)
| run HB l (0>>r) => Some (run HC (W10::l) r)
| run HB l (1>>r) => Some (retA l (0>>r))
| retA (W10::l) r => Some (retE l ([1;0] *> r))
| retA (WX::l) r => Some (retA l ([0;1;0] *> r))
| retA [] r => Some (run HC [W10] r)
| retE (W10::l) r => Some (retA l ([0;0] *> r))
| retE (WX::l) r => Some (retE l ([1;0;0] *> r))
| retE [] r => Some (run HC [WX] r)
end.
Definition cfg0 := run HF [] ([0;1;0;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r]; unfold f;
  try destruct s; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM87.

(* 815-table rows 205/743. The long discovery heads reduce to two words. *)
Module TM88.
Definition tm := Eval compute in (TM_from_str "1LB1LE_0RC0LE_1RD1RB_1LE0RF_1LC0LA_1RC---").
Definition tm' := Eval compute in (TM_from_str "1LB1RA_0RC0LE_1RD1RB_1LE1RF_1LC0LA_0LC---").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W10 | WX.
Fixpoint toLC (b:bool) l := match l with
| [] => 0inf
| W10::l => toLC b l << 1 << 0
| WX::l => toLC b l << 1 << (if b then 1 else 0) << (if b then 0 else 1)
end.
Inductive Head := HC | HD | HB | HF.
Inductive Config := run (h:Head) (l:list Word) (r:side)
  | retA (l:list Word) (r:side) | retE (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run HC l r => toLC b l {{C}}> r
| run HD l r => toLC b l << 1 {{D}}> r
| run HB l r => toLC b l << 1 {{B}}> r
| run HF l r => toLC b l << 1 << (if b then 1 else 0) {{F}}> r
| retA l r => toLC b l <{{A}} r
| retE l r => toLC b l <{{E}} [0;1] *> r
end.
Definition f c := match c with
| run HC l (0>>r) => Some (run HD l r)
| run HC l (1>>r) => Some (run HB l r)
| run HD l (0>>r) => Some (retA l ([0;1] *> r))
| run HD l (1>>r) => Some (run HF l r)
| run HB l (0>>r) => Some (run HC (W10::l) r)
| run HB l (1>>r) => Some (retA l ([0;0] *> r))
| run HF l (0>>r) => Some (run HC (WX::l) r)
| run HF _ (1>>_) => None
| retA (W10::l) r => Some (retE l r)
| retA (WX::l) r => Some (retA l ([0;0;1] *> r))
| retA [] r => Some (run HB [] r)
| retE (W10::l) r => Some (retA l ([0;0;0;1] *> r))
| retE (WX::l) r => Some (retE l ([0;0;1] *> r))
| retE [] r => Some (run HB [WX] r)
end.
Definition cfg0 := run HC [] (1>>0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|[|[] l] r|[|[] l] r]; unfold f;
  try destruct s; cbn [to_config toLC]; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM88.

(* 815-table 10/716, old SOC(2,3) TM23/TM26. *)
Module TM89.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LB---").
Definition tm' := Eval compute in (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---").
Definition machine (b:bool) := if b then tm' else tm.
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{D}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Section Rules.
Variable b:bool.
Notation "c -->* c'" := (c -[machine b]->* c') (at level 40).
Notation "c -->+ c'" := (c -[machine b]->+ c') (at level 40).
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. destruct b; es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. destruct b; es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. destruct b; es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof. destruct b; es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. destruct b; es. Qed.
Lemma ROv2_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [1] *> r.
Proof. destruct b; es. Qed.
Lemma ROv2_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.
Proof. destruct b; es. Qed.
Lemma Bad l r n:
  halts (machine b) (l |> rd1^^n *> [1;0;1;1] *> r).
Proof. destruct b; solve_halt. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0] len n ([0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC',RC;
  rw_Bin; try solve[solve_pow2_lt]; follow_rule H.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc len n m l: 1+n<2^(len+1) -> l |> RC2 len (1+n) m -->+ l <| RC2 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC2 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC2 (a*2) 0 0 -->+ LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RC 1.
Proof. epose proof (ROv2_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC2_Ov_1 len k a m: k<2^len ->
  LC len k |> RC2 (a*2+1) 0 m -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)-1) |> RC m.
Proof. solve_rule ROv2_1. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.
Lemma corner_halt len:
  halts (machine b) (LC (len+1) 0 <| RC (2^(len+1))).
Proof.
  eapply halts_evstep; [|apply progress_evstep,corner_case].
  unfold RC'; rewrite BinDec2_O; apply Bad.
Qed.
End Rules.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR2 len k h n m => 1<=len /\ n+m<k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

(* The invariant permits a common halt; no orbit-avoidance assumption. *)
Lemma closed x: P x ->
  (exists y, (forall b, to_config x -[machine b]->+ to_config y) /\ P y) \/
  (forall b, halts (machine b) (to_config x)).
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; right; intro b; apply corner_halt.
      * lowbit_cases m; [lia|].
        left; eexists (cfgR1 _ _ _ _ _); split; [intro b; apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + left; eexists (cfgR _ _ _); split;
        [intro b; apply LC_Inc; lia|cbn [P]; lia].
  - left; eexists (cfgL _ _ _); split; [intro b; apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      left; eexists (cfgR1 _ _ _ _ _); split.
      - intro b; eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + left; eexists (cfgR _ _ _); split; [intro b; apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)); lia.
    + left; eexists (cfgR2 _ _ _ _ _); split; [intro b; apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + left; eexists (cfgR _ _ _); split; [intro b; apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)); lia.
    + left; eexists (cfgR1 _ _ _ _ _); split; [intro b; apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      left; eexists (cfgR2 _ _ _ _ _); split.
      - intro b; eapply progress_evstep_trans; [apply RC2_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + lowbit_cases m.
      * left; eexists (cfgR _ _ _); split; [intro b; apply RC2_Ov_0_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)); lia.
      * left; eexists (cfgR1 _ _ _ _ _); split; [intro b; apply RC2_Ov_0; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*3+1) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
    + left; eexists (cfgR _ _ _); split; [intro b; apply RC2_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*3+3) ltac:(lia)); lia.
Qed.

Lemma transfer b n x: P x -> halts_in (machine b) (to_config x) n ->
  halts (machine (negb b)) (to_config x).
Proof.
  gen x; induction n using Wf_nat.lt_wf_ind; intros x HP HH.
  destruct (closed x HP) as [[y [HS Hy]]|HH']; [|apply HH'].
  destruct (progress_multistep _ _ _ (HS b)) as [k HK].
  pose proof (within_halt _ _ _ _ _ HH HK) as Hle.
  eapply halts_evstep; [|apply progress_evstep,HS].
  eapply H with (m:=n-S k); [lia|exact Hy|].
  eapply preceeds_halt; eauto.
Qed.

Lemma init b: c0 -[machine b]->* to_config (cfgR 1 1 1).
Proof. destruct b; cbn [to_config LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (machine false) c0 <-> halts (machine true) c0).
  rewrite (halts_evstep_iff _ _ _ (init false)), (halts_evstep_iff _ _ _ (init true)).
  split; intros [n H]; [eapply (transfer false)|eapply (transfer true)];
    [cbn [P]; lia|exact H|cbn [P]; lia|exact H].
Qed.
Open Scope sym.
End TM89.

(* Shared SOC(2,5) model: ordinary calls, critical returns and common halts. *)
Module SOC25Model.
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma lpow_unrotate_10 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.
Ltac rw_unrotate_0 ::= rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 || rewrite lpow_unrotate_4 || rewrite lpow_unrotate_5 ||
  rewrite lpow_unrotate_6 || rewrite lpow_unrotate_10.


Record Machine := {
  machine : TM;
  qL : Q;
  qR : Q;
  raw_LInc : forall l r n,
    l <* ld0 <* ld1^^n <{{qL}} [1;1] *> r -[machine]->+ l <* ld1 <* ld0^^n <* [0;1] {{qR}}> r;
  raw_RInc : forall l r n,
    l <* [0;1] {{qR}}> rd1^^n *> [0] *> r -[machine]->+ l <{{qL}} [1;1] *> rd0^^n *> [1] *> r;
  raw_LOv : forall r n,
    ldh <* ld1^^n <{{qL}} [1;1] *> r -[machine]->+ ldh <* ld0^^n <* [0;1] {{qR}}> [1] *> r;
  raw_ROv1_0 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -[machine]->+
  l <* ld1 <* ld0^^(n*5) <* [0;1] {{qR}}> [1;0;0;0] *> r;
  raw_ROv1_1 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -[machine]->+
  l <* ld1 <* ld0^^(n*5+3) <* [0;1] {{qR}}> [0;0;0] *> r;
  raw_ROv3 : forall l r n,
    halts machine (l <* [0;1] {{qR}}> rd1^^n *> [1;0;0;1;0;0;0;0] *> r);
  raw_ROv4_0 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -[machine]->+
  l <* ld1 <* ld0^^(n*5+1) <* [0;1] {{qR}}> rd1 *> r;
  raw_ROv4_1 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -[machine]->+
  l <* ld1 <* ld0^^(n*5+4) <* [0;1] {{qR}}> [0;0;0;0] *> r;
  raw_ROv'_0 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2) *> [1;0;0;0;1;1] *> r -[machine]->+
  l <* ld1 <* ld0^^(n*5+2) <* [0;1] {{qR}}> r;
  raw_ROv'_1 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r -[machine]->+
  l <* ld1 <* ld0^^(n*5+4) <* [0;1] {{qR}}> [1] *> r
}.

Section Rules.
Variable b:Machine.
Notation "c -->* c'" := (c -[machine b]->* c') (at level 40).
Notation "c -->+ c'" := (c -[machine b]->+ c') (at level 40).
Notation "l <| r" := (l <{{qL b}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{qR b}}> r) (at level 30).

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0;0] len n (rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0] *> rd1 *> RC m).
Definition RC4 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC3,RC4,RC',RC;
  rw_Bin; try solve[solve_pow2_lt]; follow_rule H.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule (raw_LInc b). Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule (raw_RInc b). Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule (raw_RInc b). Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule (raw_RInc b). Qed.
Lemma RC4_Inc len n m l: 1+n<2^(len+1) -> l |> RC4 len (1+n) m -->+ l <| RC4 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule (raw_RInc b). Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule (raw_RInc b). Qed.
Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule (raw_LOv b). Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof. solve_rule (raw_ROv1_0 b). Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC 1.
Proof. epose proof ((raw_ROv1_0 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof. solve_rule (raw_ROv1_1 b). Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC 0.
Proof. epose proof ((raw_ROv1_1 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RC3_halt l h m: halts (machine b) (l |> RC3 h 0 m).
Proof. unfold RC3; rewrite BinDec2_O; apply (raw_ROv3 b). Qed.
Lemma RC4_Ov_0 len k a m: k<2^len ->
  LC len k |> RC4 (a*2) 0 m -->+
  LC (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) |> RC (m*2+1).
Proof. solve_rule (raw_ROv4_0 b). Qed.
Lemma RC4_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof. solve_rule (raw_ROv4_1 b). Qed.
Lemma RC4_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 0 -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC 0.
Proof. epose proof ((raw_ROv4_1 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+
  LC (len+1+(a*5+2)) ((k*2+1)*2^(a*5+2)-1) |> RC 0.
Proof. epose proof ((raw_ROv'_0 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC 1.
Proof. epose proof ((raw_ROv'_1 b) _ 0inf a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 (raw_LOv b); cbn; simpl_rotate.
  epose proof ((raw_ROv1_0 b) _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.
End Rules.

Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR3 (len k h n m:nat) | cfgR4 (len k h n m:nat).
Definition to_config b x := match x with
| cfgL len k n => LC len k <{{qL b}} [1;1] *> RC n
| cfgR len k n => LC len k <* [0;1] {{qR b}}> RC n
| cfgR1 len k h n m => LC len k <* [0;1] {{qR b}}> RC1 h n m
| cfgR3 len k h n m => LC len k <* [0;1] {{qR b}}> RC3 h n m
| cfgR4 len k h n m => LC len k <* [0;1] {{qR b}}> RC4 h n m
end.
Close Scope sym.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 2<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 2<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR3 len k h n m | cfgR4 len k h n m =>
  1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x ->
  (exists y, (forall b, to_config b x -[machine b]->+ to_config b y) /\ P y) \/
  (forall b, halts (machine b) (to_config b x)).
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- left; eexists (cfgR _ _ _); split.
           ++ intro b; eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- left; eexists (cfgR _ _ _); split.
           ++ intro b; eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        left; eexists (cfgR1 _ _ _ _ _); split; [intro b; apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + left; eexists (cfgR _ _ _); split;
        [intro b; apply LC_Inc; lia|cbn [P]; lia].
  - left; eexists (cfgL _ _ _); split; [intro b; apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      left; eexists (cfgR1 _ _ _ _ _); split.
      - intro b; eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + left; eexists (cfgR _ _ _); split; [intro b; apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)); lia.
    + left; eexists (cfgR4 _ _ _ _ _); split; [intro b; apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + left; eexists (cfgR _ _ _); split; [intro b; apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); arith.
    + left; eexists (cfgR3 _ _ _ _ _); split; [intro b; apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n]; [right; intro b; apply RC3_halt|].
    destruct k as [|k]; [lia|].
    left; eexists (cfgR3 _ _ _ _ _); split.
    + intro b; eapply progress_evstep_trans; [apply RC3_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    + cbn [P]; lia.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      left; eexists (cfgR4 _ _ _ _ _); split.
      - intro b; eapply progress_evstep_trans; [apply RC4_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + left; eexists (cfgR _ _ _); split; [intro b; apply RC4_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+1) ltac:(lia)); lia.
    + lowbit_cases m.
      * left; eexists (cfgR _ _ _); split; [intro b; apply RC4_Ov_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)); arith.
      * left; eexists (cfgR4 _ _ _ _ _); split; [intro b; apply RC4_Ov_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
Qed.

Lemma transfer b c n x: P x -> halts_in (machine b) (to_config b x) n ->
  halts (machine c) (to_config c x).
Proof.
  gen x; induction n using Wf_nat.lt_wf_ind; intros x HP HH.
  destruct (closed x HP) as [[y [HS Hy]]|HH']; [|apply HH'].
  destruct (progress_multistep _ _ _ (HS b)) as [k HK].
  pose proof (within_halt _ _ _ _ _ HH HK) as Hle.
  eapply halts_evstep; [|apply progress_evstep,HS].
  eapply H with (m:=n-S k); [lia|exact Hy|].
  eapply preceeds_halt; eauto.
Qed.

Lemma equivalent b c x: P x ->
  c0 -[machine b]->* to_config b x ->
  c0 -[machine c]->* to_config c x ->
  (halts (machine b) c0 <-> halts (machine c) c0).
Proof.
  intros HP Hb Hc.
  rewrite (halts_evstep_iff _ _ _ Hb), (halts_evstep_iff _ _ _ Hc).
  split; intros [n H]; eapply transfer; eauto.
Qed.
Open Scope sym.
End SOC25Model.

Module TM90.
Import SOC25Model.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LA_1RA---").
Definition tm' := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RC---").
Definition machine (b:bool) := if b then tm' else tm.
Definition qL (b:bool) := if b then C else A.
Definition qR (b:bool) := if b then A else B.
Definition model (b:bool) : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := machine b; SOC25Model.qL := qL b; SOC25Model.qR := qR b |}.
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; solve_halt).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
Defined.
Lemma init b: c0 -[machine b]->* to_config (model b) (cfgL 1 1 1).
Proof. destruct b; cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine (model false)) c0 <->
          halts (SOC25Model.machine (model true)) c0).
  apply (equivalent (model false) (model true) (cfgL 1 1 1)); [cbn [P]; lia|apply init|apply init].
Qed.
End TM90.

Module TM91.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1LE0RA_1RF1RE_1RC---").
Definition tm' := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RC---").
Import SOC25Model.
Definition model : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := tm; SOC25Model.qL := C; SOC25Model.qR := A |}.
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; solve_halt).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
Defined.
Lemma init: c0 -[tm]->* to_config model (cfgL 1 1 1).
Proof. cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine model) c0 <->
          halts (SOC25Model.machine (TM90.model true)) c0).
  apply (equivalent model (TM90.model true) (cfgL 1 1 1)); [cbn [P]; lia|apply init|apply TM90.init].
Qed.
End TM91.

Module TM92.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_0RF1RC_1LD---").
Definition tm' := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RC---").
Import SOC25Model.
Definition model : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := tm; SOC25Model.qL := C; SOC25Model.qR := A |}.
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; solve_halt).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
Defined.
Lemma init: c0 -[tm]->* to_config model (cfgL 1 1 1).
Proof. cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine model) c0 <->
          halts (SOC25Model.machine (TM90.model true)) c0).
  apply (equivalent model (TM90.model true) (cfgL 1 1 1)); [cbn [P]; lia|apply init|apply TM90.init].
Qed.
End TM92.

(* 815-table 249/707. *)
Module TM93.
Import SOC25Model.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LC_1RA---").
Definition tm' := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---").
Definition machine (b:bool) := if b then tm' else tm.
Definition qL (b:bool) := if b then A else A.
Definition qR (b:bool) := if b then B else B.
Definition model (b:bool) : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := machine b; SOC25Model.qL := qL b; SOC25Model.qR := qR b |}.
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; solve_halt).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
Defined.
Lemma init b: c0 -[machine b]->* to_config (model b) (cfgL 2 3 1).
Proof. destruct b; cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine (model false)) c0 <->
          halts (SOC25Model.machine (model true)) c0).
  apply (equivalent (model false) (model true) (cfgL 2 3 1));
    [cbn [P]; lia|apply init|apply init].
Qed.
End TM93.

(* 815-table 243/249. *)
Module TM94.
Import SOC25Model.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC---_1RD1LC_1LE1RF_1LC0LE_1RA0RD").
Definition tm' := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LC_1RA---").
Definition model : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := tm; SOC25Model.qL := C; SOC25Model.qR := D |}.
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; solve_halt).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
Defined.
Lemma init: c0 -[tm]->* to_config model (cfgL 2 3 1).
Proof. cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine model) c0 <->
          halts (SOC25Model.machine (TM93.model false)) c0).
  apply (equivalent model (TM93.model false) (cfgL 2 3 1));
    [cbn [P]; lia|apply init|apply TM93.init].
Qed.
End TM94.

(* 815-table 440/249. *)
Module TM95.
Import SOC25Model.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC---_1RD1LC_1LE1RF_1LC0LE_1LA0RD").
Definition tm' := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LC_1RA---").
Definition model : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := tm; SOC25Model.qL := C; SOC25Model.qR := D |}.
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; solve_halt).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
Defined.
Lemma init: c0 -[tm]->* to_config model (cfgL 2 3 1).
Proof. cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine model) c0 <->
          halts (SOC25Model.machine (TM93.model false)) c0).
  apply (equivalent model (TM93.model false) (cfgL 2 3 1));
    [cbn [P]; lia|apply init|apply TM93.init].
Qed.
End TM95.

(* 815-table 630/249; the first literal is the mirror. *)
Module TM96.
Import SOC25Model.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RE_0RA1RD_1RE1LD_1LF1RB_1LD0LF").
Definition tm' := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1LC_1RA---").
Definition model : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := tm; SOC25Model.qL := D; SOC25Model.qR := E |}.
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; solve_halt).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
  - abstract (intros; es).
Defined.
Lemma init: c0 -[tm]->* to_config model (cfgL 2 3 1).
Proof. cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine model) c0 <->
          halts (SOC25Model.machine (TM93.model false)) c0).
  apply (equivalent model (TM93.model false) (cfgL 2 3 1));
    [cbn [P]; lia|apply init|apply TM93.init].
Qed.
End TM96.

(* 815-table 298/753. *)
Module TM97.
Import SOC25Model.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0RB_1RA---").
Definition tm' := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---").
Definition machine (b:bool) := if b then tm' else tm.
Definition qL (b:bool) := if b then A else A.
Definition qR (b:bool) := if b then B else B.
Definition model (b:bool) : SOC25Model.Machine.
Proof.
  refine {| SOC25Model.machine := machine b; SOC25Model.qL := qL b; SOC25Model.qR := qR b |}.
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; solve_halt).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
  - abstract (intros; destruct b; es).
Defined.
Lemma init b: c0 -[machine b]->* to_config (model b) (cfgL 1 1 2).
Proof. destruct b; cbn [to_config model LC RC]; esx. Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (SOC25Model.machine (model false)) c0 <->
          halts (SOC25Model.machine (model true)) c0).
  apply (equivalent (model false) (model true) (cfgL 1 1 2));
    [cbn [P]; lia|apply init|apply init].
Qed.
End TM97.

(* 815-table 169/772.  A one-sided eight-state observer preserves the
   shared halting branches; H6/0 restores an unnecessarily omitted rule. *)
Module TM98.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_1LA0LD_0RE1LC_1LC1RF_1RB0RD").
Definition tm' := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---").
Definition machine (b:bool) := if b then tm' else tm.

Inductive Control := H0 | H1 | H2 | H3 | H4 | H5 | H6 | H7.
Inductive Obs := O0 | O1 | O2 | O3 | O4 | O5 | O6 | O7.
Definition delta o s := match o,s with
| O0,0 => O0 | O0,1 => O1 | O1,0 => O2 | O1,1 => O3
| O2,0 => O4 | O2,1 => O5 | O3,0 => O0 | O3,1 => O3
| O4,0 => O2 | O4,1 => O1 | O5,0 => O6 | O5,1 => O7
| O6,0 => O6 | O6,1 => O5 | O7,0 => O4 | O7,1 => O7
end.
Fixpoint observe l := match l with [] => O0 | s::l => delta (observe l) s end.
Definition good q s o := match q,s,o with
| H0,_,O1 | H0,_,O3 | H5,_,O1 | H5,_,O3 | H7,_,O1 | H7,_,O3 => true
| H1,0,O0 | H1,0,O2 | H1,0,O3 | H1,0,O7 => true
| H2,0,O0 | H2,0,O2 | H2,0,O3 | H2,0,O7 => true
| H1,1,O0 | H1,1,O1 | H1,1,O3 | H1,1,O4 => true
| H2,1,O0 | H2,1,O1 | H2,1,O3 | H2,1,O4 => true
| H3,0,O0 | H3,0,O1 | H3,0,O3 | H3,0,O4 => true
| H3,1,O1 | H3,1,O3 | H3,1,O5 | H3,1,O7 => true
| H4,_,O0 | H4,_,O3 | H4,_,O4 | H6,_,O0 | H6,_,O2 => true
| _,_,_ => false end.
Definition Config := (Control * list Sym * Sym * side)%type.
Definition P (c:Config) := let '(q,l,s,r) := c in good q s (observe l) = true.
Definition to_config (b:bool) (c:Config) := let '(q,l,s,r) := c in
  let l := 0inf <* l in
  match q with
  | H0 => l << 1 {{E}}> s>>r
  | H1 => l << s <{{D}} 0>>r
  | H2 => l << s <{{C}} 1>>r
  | H3 => l << s <{{A}} 1>>r
  | H4 => l << 1 {{if b then A else F}}> s>>r
  | H5 => l << 0 {{D}}> s>>r
  | H6 => l << 0 {{E}}> s>>r
  | H7 => l << 1 {{B}}> s>>r
  end.
Definition trans q s := match q,s with
| H0,0 => Some (1,L,H1) | H0,1 => Some (1,R,H4)
| H1,0 => Some (1,L,H3) | H1,1 => Some (0,L,H2)
| H2,0 => Some (1,L,H3) | H2,1 => Some (1,L,H1)
| H3,0 => Some (1,R,H0) | H3,1 => None
| H4,0 => Some (1,R,H7) | H4,1 => Some (1,R,H5)
| H5,0 => Some (0,R,H6) | H5,1 => None
| H6,0 => Some (1,L,H3) | H6,1 => Some (0,R,H4)
| H7,0 => Some (1,L,H1) | H7,1 => Some (1,R,H0)
end.
Definition f (c:Config) := let '(q,l,s,r) := c in match trans q s with
| Some (w,L,q') => Some (q',List.tl l,List.hd 0 l,w>>r)
| Some (w,R,q') => Some (q',w::l,Streams.hd r,Streams.tl r)
| None => None end.
Definition cfg0 : Config := (H0,[1]^^16,0,0inf).

Lemma f_closed c c': P c -> f c = Some c' -> P c'.
Proof.
  destruct c as [[[q l] s] [x r]], q, s; destruct l as [|y l];
  try destruct y; cbn [f trans List.hd List.tl]; intros H E; inverts E;
  cbn [P observe] in *; try destruct (observe l); destruct x;
  cbn [delta good] in *; congruence.
Qed.

Lemma f_spec b c: P c -> match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct c as [[[q l] s] [x r]], q, s;
  destruct l as [|y l]; try destruct y;
  cbn [P f trans observe List.hd List.tl]; intro H;
  cbn [good] in H; try discriminate;
  try (destruct (observe l); cbn [delta good] in H; discriminate);
  destruct b, x; cbn [to_config]; esx.
Qed.
Lemma init b: c0 -[machine b]->* to_config b cfg0.
Proof. destruct b; cbn [to_config cfg0]; esx. Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) P); [| |reflexivity].
  - apply halts_evstep_iff, init.
  - intros c H; specialize (f_spec b c H); destruct (f c) eqn:E;
      eauto using f_closed.
Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  change (halts (machine false) c0 <-> halts (machine true) c0).
  rewrite !eqv_model; tauto.
Qed.
End TM98.
