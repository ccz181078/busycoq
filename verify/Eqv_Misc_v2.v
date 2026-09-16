(* Ten new equivalences; numbering continues BusyCoq.Eqv_Misc (TM1--TM66).
   This file requires only existing BusyCoq modules, not HoldoutEquivalences.
   Both endpoints match old class members up to mirroring, without renaming. *)
From BusyCoq Require Import Individual62 Eqv_Misc DivModCases.
Require Import String.

(* TM10 and TM22 already describe the same abstract transition function.
   Their inductive Config types are nominally distinct. Rechecking TM22's
   machine with TM10's model avoids an otherwise redundant isomorphism. *)

(* Holdout representatives 38/379. *)
Module TM67.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RC---".

Lemma eqv1: halts tm c0 <-> iter_halts TM10.f TM10.cfg0.
Proof.
  TM10.solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2: halts tm' c0 <-> iter_halts TM10.f TM10.cfg0.
Proof. exact TM10.eqv1. Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM67.

(* Representatives 59 and 722; old classes 144 and 10. *)
(* Holdout representatives 59/722. *)
Module TM68.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0RE---".
Definition tm' := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RE---".

Lemma eqv1: halts tm c0 <-> iter_halts TM16.f TM16.cfg0.
Proof.
  TM16.solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2: halts tm' c0 <-> iter_halts TM16.f TM16.cfg0.
Proof. exact TM16.eqv1. Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM68.

(* Representatives 136 and 795; old classes 65 and 32. *)
(* Holdout representatives 136/795. *)
Module TM69.
Definition tm := TM_from_str "1LB0RB_0RC0LB_0LE0RD_1RA1RE_1LF---_1RC0LB".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_0LE0RD_1RA1RE_1LF---_1RC0LB".

Lemma eqv1: halts tm c0 <-> iter_halts TM25.f TM25.cfg0.
Proof.
  TM25.solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2: halts tm' c0 <-> iter_halts TM25.f TM25.cfg0.
Proof. exact TM25.eqv1. Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM69.

(* Representatives 188 and 868. The marker 10 prevents an E return from
   reaching the blank left boundary; C returns may pop the last marker. *)
(* Holdout representatives 188/868. *)
Module TM70.
Definition tm := TM_from_str "1LB1RF_1RC0RD_1RD1LC_1LE1RB_0LA0LE_0RA---".
Definition tm' := TM_from_str "1LB1RF_1RC0RD_1RD1LC_1LE1RB_0RA0LE_0RA---".
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W10.
Inductive Config :=
| hB (l:list Word) (r:side)
| hC (l:list Word) (r:side)
| hD10 (l:list Word) (r:side)
| hD1 (l:list Word) (r:side)
| hF (l:list Word) (r:side)
| hA (l:list Word) (r:side)
| retC (l:list Word) (r:side)
| retE (l:list Word) (r:side).

Fixpoint toLC l := match l with
| [] => 0inf
| W1::l => toLC l << 1
| W10::l => toLC l << 1 << 0
end.
Definition to_config c := match c with
| hB l r => toLC l << 1 {{B}}> r
| hC l r => toLC l << 1 << 1 {{C}}> r
| hD10 l r => toLC l << 1 << 0 {{D}}> r
| hD1 l r => toLC l << 1 {{D}}> r
| hF l r => toLC l << 1 {{F}}> r
| hA l r => toLC l << 1 << 0 {{A}}> r
| retC l r => toLC l <{{C}} [1;1;1] *> r
| retE l r => toLC l <{{E}} 0>>r
end.
Definition Inv c := match c with
| retC _ _ => True
| hB l _ | hC l _ | hD10 l _ | hD1 l _ | hF l _ | hA l _ | retE l _ => List.In W10 l
end.
Definition f c := match c with
| hB l (0>>r) => Some (hC l r)
| hB l (1>>r) => Some (hD10 l r)
| hC l (0>>r) => Some (hD1 (W1::W1::l) r)
| hC l (1>>r) => Some (retC l r)
| hD10 l (0>>r) => Some (hF (W10::l) r)
| hD10 l (1>>r) => Some (hB (W10::l) r)
| hD1 l (0>>r) => Some (retE l (1>>r))
| hD1 l (1>>r) => Some (hB (W1::l) r)
| hF l (0>>r) => Some (hA l r)
| hF l (1>>r) => None
| hA l (0>>r) => Some (retC l r)
| hA l (1>>r) => Some (hF (W10::l) r)
| retC (W1::l) r => Some (retC l (1>>r))
| retC (W10::l) r => Some (hB (W10::W1::W1::l) r)
| retC [] r => Some (hB [W10;W1] r)
| retE (W1::l) r => Some (retE l (0>>r))
| retE (W10::l) r => Some (retC l r)
| retE [] _ => None
end.
Definition cfg0 := hF [W10;W1] 0inf.

Ltac des_cfg := repeat match goal with
| |- context[match ?r with _ >> _ => _ end] => destruct r
| |- context[match ?s with 0 => _ | 1 => _ end] => destruct s
| |- context[match ?l with [] => _ | _::_ => _ end] => destruct l
| |- context[match ?w with W1 => _ | W10 => _ end] => destruct w
end.

Lemma f_spec b c: Inv c -> match f c with
| Some c' => to_config c -[machine b]->+ to_config c' /\ Inv c'
| None => halts (machine b) (to_config c)
end.
Proof.
  destruct b; destruct c; intro H; unfold f; des_cfg;
  cbn [Inv to_config toLC] in *;
  try solve [simpl in H; contradiction];
  try solve [split; [esx | simpl in *; intuition discriminate]];
  esx.
Qed.

Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f to_config Inv (f_spec b)); [|simpl; auto].
  apply halts_evstep_iff; destruct b; esx.
Qed.

Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM70.

(* Holdout representatives 191/901. *)
Module TM71.
Definition tm := TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RB---_0LD0LF".
Definition tm' := TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RB---_1LC0LF".
Definition machine (b:bool) := if b then tm' else tm.

Inductive Word := W1 | W10.
Inductive Config :=
| hA (l:list Word) (n:nat) (r:side)
| hD (l:list Word) (n:nat) (r:side)
| hE (l:list Word) (n:nat) (r:side)
| hB (l:list Word) (n:nat) (r:side)
| hC (l:list Word) (n:nat) (r:side)
| retC (l:list Word) (r:side).
Fixpoint toLC l := match l with
| [] => 0inf
| W1::l => toLC l << 1
| W10::l => toLC l << 1 << 0
end.
Lemma toLC_ones n l:
  toLC ([W1]^^n ++ l) = toLC l <* [1]^^n.
Proof. induction n; cbn; congruence. Qed.
Lemma toLC_tens n l:
  toLC ([W10]^^n ++ l) = toLC l <* <[1;0]^^n.
Proof. induction n; cbn; congruence. Qed.

Definition to_config c := match c with
| hA l n r => toLC l << 1 << 0 <* [1]^^n {{A}}> r
| hD l n r => toLC l << 1 << 0 <* [1]^^(1+n) {{D}}> r
| hE l n r => toLC l << 1 << 0 <* [1]^^(2+n) {{E}}> r
| hB l n r => toLC l << 1 << 0 <* [1]^^(3+n) {{B}}> r
| hC l n r => toLC l << 1 << 0 <* [1]^^(4+n) {{C}}> r
| retC l r => toLC l <{{C}} [1;1] *> r
end.
Definition f c := match c with
| hA l n (0>>r) => Some (retC l ([0]^^n *> 1>>r))
| hA l n (1>>r) => Some (hD l n r)
| hD l n (0>>r) => Some (hE l n r)
| hD l n (1>>r) => Some (hA ([W1]^^n ++ W10::l) 0 r)
| hE l n (0>>r) => Some (hB l n r)
| hE l n (1>>r) => None
| hB l n (0>>r) => Some (hC l n r)
| hB l n (1>>r) => Some (retC l ([0]^^(4+n) *> r))
| hC l n (0>>r) => Some (hA l (5+n) r)
| hC l n (1>>r) =>
  match mod2 n with
  | mod2eq0 k => Some (hD ([W10]^^(1+k) ++ W1::W1::l) 0 r)
  | mod2eq1 k => Some (hA ([W10]^^(2+k) ++ W1::W1::l) 0 r)
  end
| retC (W1::l) r => Some (retC l (1>>r))
| retC (W10::l) r => Some (hA (W1::W1::l) 0 r)
| retC [] r => Some (hA [W1] 0 r)
end.
Definition cfg0 := hA [W1] 0 0inf.

Lemma a0 b l r n:
  l << 1 << 0 <* [1]^^n {{A}}> 0>>r -[machine b]->+
  l <{{C}} [1;1] *> [0]^^n *> 1>>r.
Proof. destruct b; destruct n; esx. Qed.

Ltac des_cfg := repeat match goal with
| |- context[match ?r with _ >> _ => _ end] => destruct r
| |- context[match ?s with 0 => _ | 1 => _ end] => destruct s
| |- context[match ?l with [] => _ | _::_ => _ end] => destruct l
| |- context[match ?w with W1 => _ | W10 => _ end] => destruct w
| |- context[match mod2 ?n with _ => _ end] => destruct (mod2 n); subst
end.
Lemma f_spec b c: match f c with
| Some c' => to_config c -[machine b]->+ to_config c'
| None => halts (machine b) (to_config c)
end.
Proof.
  destruct b; destruct c; unfold f; des_cfg;
  cbn [to_config toLC];
  repeat (rewrite toLC_ones || rewrite toLC_tens);
  try apply a0; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f to_config (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM71.

(* Holdout representatives 205/389. *)
Module TM72.
Definition tm := TM_from_str "1LB0LF_0RC---_1RD1RC_1LE0RA_1LA1LD_0LD0LB".
Definition tm' := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---".
Definition machine (b:bool) := if b then tm' else tm.
(* A root run of ones, followed by words.  The head of l is nearest the head.
   U p n denotes (p11)0 1^n, where p is a tape symbol, not a state. *)
Inductive Word := W01 | W3 (p:Sym) | U (p:Sym) (n:nat).
Fixpoint toLC k l := match l with
| [] => 0inf <* [1]^^k
| W01::l => toLC k l << 0 << 1
| W3 p::l => toLC k l << p << 1 << 1
| U p n::l => toLC k l << p << 1 << 1 << 0 <* [1]^^n
end.
Inductive Config :=
| hD0 (k:nat) (l:list Word) (r:side)
| hA0 (k:nat) (l:list Word) (r:side)
| hC (k:nat) (l:list Word) (p:Sym) (n:nat) (r:side)
| hD (k:nat) (l:list Word) (p:Sym) (n:nat) (r:side)
| hA (k:nat) (l:list Word) (p:Sym) (n:nat) (r:side)
| retE (k:nat) (l:list Word) (r:side)
| rootC (n:nat) (r:side)
| rootD (n:nat) (r:side)
| rootA (n:nat) (r:side).
Definition to_config (qa qc qd qe:Q) c := match c with
| hD0 k l r => toLC k l << 0 << 1 << 1 {{qd}}> r
| hA0 k l r => toLC k l << 0 << 1 << 1 << 0 {{qa}}> r
| hC k l p n r => toLC k l << p << 1 << 1 << 0 <* [1]^^(1+n) {{qc}}> r
| hD k l p n r => toLC k l << p << 1 << 1 << 0 <* [1]^^(3+n) {{qd}}> r
| hA k l p n r => toLC k l << p << 1 << 1 << 0 <* [1]^^(3+n) << 0 {{qa}}> r
| retE k l r => toLC k l <{{qe}} 1>>r
| rootC n r => 0inf <* [1]^^(3+n) {{qc}}> r
| rootD n r => 0inf <* [1]^^(3+n) {{qd}}> r
| rootA n r => 0inf <* [1]^^(3+n) << 0 {{qa}}> r
end.
Definition f c := match c with
| hD0 k l (0>>r) => Some (retE k l ([0;0;1] *> r))
| hD0 k l (1>>r) => Some (hA0 k l r)
| hA0 k l (0>>r) => Some (hC k l 0 0 r)
| hA0 k l (1>>r) => Some (hD0 k (W01::l) r)
| hC k l p 0 (0>>r) => Some (hD0 k (W3 p::l) r)
| hC k l p (S n) (0>>r) => Some (hD k l p n r)
| hC k l p n (1>>r) => Some (hC k l p (1+n) r)
| hD k l p n (0>>r) => Some (hA0 k (U p n::l) r)
| hD k l p n (1>>r) => Some (hA k l p n r)
| hA k l p n (0>>r) => Some (hC k (U p n::l) 1 0 r)
| hA k l p n (1>>r) => Some (hD0 k (U p (2+n)::l) r)
| retE k (W01::l) r => Some (retE k l ([1;1] *> r))
| retE k (W3 0::l) r => Some (retE k l ([0;0;1] *> r))
| retE k (W3 1::l) r => Some (hA0 k l r)
| retE k (U 0 0::l) r => Some (retE k l ([1;1;1;1] *> r))
| retE _ (U 1 0::_) _ => None
| retE k (U 0 1::l) r => Some (retE k l ([0;0;1;1;1] *> r))
| retE k (U 1 1::l) r => Some (hA0 k l ([1;1] *> r))
| retE k (U 0 2::l) r => Some (retE k l ([0;0;1;0;0;1] *> r))
| retE k (U 1 2::l) r => Some (hA0 k l ([0;0;1] *> r))
| retE k (U p (S (S (S n)))::l) r => Some (hA0 k (U p n::l) r)
| retE 0 [] r => Some (rootC 0 r)
| retE 1 [] r => Some (rootC 2 r)
| retE 2 [] r => Some (rootC 0 ([0;0;1] *> r))
| retE (S (S (S n))) [] r => Some (hA0 n [] r)
| rootC n (0>>r) => Some (rootD (1+n) r)
| rootC n (1>>r) => Some (rootC (1+n) r)
| rootD n (0>>r) => Some (hA0 n [] r)
| rootD n (1>>r) => Some (rootA n r)
| rootA n (0>>r) => Some (hC n [] 1 0 r)
| rootA n (1>>r) => Some (hD0 (2+n) [] r)
end.
Ltac des_cfg := repeat match goal with
| |- context[match ?r with _ >> _ => _ end] => destruct r
| |- context[match ?s with 0 => _ | 1 => _ end] => destruct s
| |- context[match ?l with [] => _ | _::_ => _ end] => destruct l
| |- context[match ?w with W01 => _ | W3 _ => _ | U _ _ => _ end] => destruct w
| |- context[match ?n with O => _ | S _ => _ end] => destruct n
end.
Ltac solve_v1 qa qc qd qe :=
  erewrite <-(halts_iff _ _ _ f (to_config qa qc qd qe) (fun _=>True)); trivial;
  [apply halts_evstep_iff; esx | ];
  intros [] _; unfold f; des_cfg; cbn [to_config toLC];
  try (split; [|trivial]); esx.

Definition cfg0 := hD0 0 [] 0inf.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof. destruct b; [solve_v1 A B C D | solve_v1 A C D E]. Qed.
Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM72.

(* Holdout representatives 613/702. *)
Module TM73.
Import TM72.
Definition tm := TM_from_str "1LB1LE_1LC0LF_0RD---_1RE1RD_1LA0RB_0LE0LC".
Definition tm' := TM_from_str "1LB1LD_1RC0LE_1RD1RC_1LA0RB_0LD0LF_0RC---".
Definition machine (b:bool) := if b then tm' else tm.
Definition cfg0 := hD0 0 [] (1>>0inf).
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof. destruct b; [solve_v1 B C D A | solve_v1 B D E A]. Qed.
Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM73.

(* Holdout representatives 814/853. *)
Module TM74.
Import TM72.
Definition tm := TM_from_str "1LB0RC_1LC1LA_1LD0LF_0RE---_1RA1RE_0LA0LD".
Definition tm' := TM_from_str "1LB0RC_1LC1LA_1RD0LE_1RA1RD_0LA0LF_0RD---".
Definition machine (b:bool) := if b then tm' else tm.
Definition cfg0 := hD0 1 [] (1>>0inf).
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof. destruct b; [solve_v1 C D A B | solve_v1 C E A B]. Qed.
Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM74.

(* Holdout representatives 336/960. *)
Module TM75.
Import TM72.
Definition tm := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---".
Definition tm' := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE".
Definition machine (b:bool) := if b then tm' else tm.
Definition cfg0 := hD0 3 [] (1>>0inf).
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof. destruct b; solve_v1 D A B C. Qed.
Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM75.

(* Holdout representatives 43/881. *)
Module TM76.
Definition tm := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA0LE_0LC---".
Definition tm' := TM_from_str "1LB0RB_0RC0LE_1RA1RD_0RB1RF_1LA1LD_0LC---".
Definition machine (b:bool) := if b then tm' else tm.

(* 011(001)^n = 01(100)^n 1: the second spelling exposes the last 1. *)
Inductive Word := W (n:nat) | V (n:nat).
Definition putW l n := l << 0 << 1 <* <[1;0;0]^^n << 1.
Fixpoint toLC l := match l with
| [] => 0inf
| W n::l => putW (toLC l) n
| V n::l => putW (toLC l) n << 0
end.
Inductive Config :=
| hF (l:list Word) (r:side)
| hB (l:list Word) (n:nat) (r:side)
| hC (l:list Word) (n:nat) (r:side)
| hA (l:list Word) (n:nat) (r:side)
| hD (l:list Word) (n:nat) (r:side)
| retA (l:list Word) (r:side)
| retB (l:list Word) (r:side).
Definition to_config c := match c with
| hF l r => putW (toLC l) 0 {{F}}> r
| hB l n r => putW (toLC l) n << 0 {{B}}> r
| hC l n r => putW (toLC l) n << 0 << 0 {{C}}> r
| hA l n r => putW (toLC l) (1+n) {{A}}> r
| hD l n r => putW (toLC l) (1+n) {{D}}> r
| retA l r => toLC l <{{A}} [1;0;0] *> r
| retB l r => toLC l <{{B}} [1;1;0;0] *> r
end.
Definition f c := match c with
| hF l (0>>r) => Some (hB l 0 r)
| hF _ (1>>_) => None
| hB l n (0>>r) => Some (hC l n r)
| hB l 0 (1>>r) => Some (retB l (0>>r))
| hB l (S n) (1>>r) => Some (hC (W n::l) 0 r)
| hC l n (0>>r) => Some (hA l n r)
| hC l n (1>>r) => Some (hD l n r)
| hA l n (0>>r) => Some (retA l (1 >> [1;0;1]^^(1+n) *> r))
| hA l n (1>>r) => Some (hB l (1+n) r)
| hD l n (0>>r) => Some (hB l (1+n) r)
| hD l n (1>>r) => Some (hF (V n::l) r)
| retA (W 0::l) r => Some (retB l ([0;0] *> r))
| retA (W (S n)::l) r => Some (hA (W n::l) 0 r)
| retA (V n::l) r => Some (retA l (1 >> [1;0;1]^^n *> [1;0;0] *> r))
| retB (W n::l) r => Some (retA l (1 >> [1;0;1]^^n *> [1;0;0] *> r))
| retB (V n::l) r => Some (hC (W n::l) 0 r)
| retA [] r | retB [] r => Some (hF [] ([0;0] *> r))
end.
Definition cfg0 := hF [] ([0;1;1;0;1] *> 0inf).

Ltac des_cfg := repeat match goal with
| |- context[match ?r with _ >> _ => _ end] => destruct r
| |- context[match ?s with 0 => _ | 1 => _ end] => destruct s
| |- context[match ?l with [] => _ | _::_ => _ end] => destruct l
| |- context[match ?w with W _ => _ | V _ => _ end] => destruct w
| |- context[match ?n with O => _ | S _ => _ end] => destruct n
end.
Lemma f_spec b c: match f c with
| Some c' => to_config c -[machine b]->+ to_config c'
| None => halts (machine b) (to_config c)
end.
Proof.
  destruct b; destruct c; unfold f; des_cfg;
  cbn [to_config toLC]; unfold putW; esx.
Qed.
Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f to_config (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; unfold putW; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.
Lemma eqv1: halts tm c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model false). Qed.
Lemma eqv2: halts tm' c0 <-> iter_halts f cfg0.
Proof. exact (eqv_model true). Qed.
Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof. rewrite eqv1,eqv2; tauto. Qed.
End TM76.
