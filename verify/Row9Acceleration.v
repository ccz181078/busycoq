From Coq Require Import List Arith Lia.
From BusyCoq Require Import Row9Eval Row9Algebra Row9Operators Row9Numerals Row9Binary.
Import ListNotations.
Local Opaque f.

(** A small verified evaluator for the finite certificate.  Binary prefix
    identities compress pure counter work; the outer fuel only limits the
    checker, and is never used as a nonhalting argument. *)

Fixpoint fast_power (fuel p:nat) (w:word) : option word :=
  match fuel with
  | 0 => None
  | S fuel =>
    match p with
    | 0 => Some w
    | S _ =>
      match w with
      | [] => Some (numeral p)
      | 0::_ => None
      | 1::u => if Nat.odd p
          then option_map (first_plus 4) (fast_power fuel (S (Nat.div2 p)) u)
          else option_map (cons 1) (fast_power fuel (Nat.div2 p) u)
      | 2::u => option_map (cons 2) (fast_power fuel p u)
      | 3::u => option_map (cons 3) (fast_power fuel (2*p) u)
      | S(S(S(S g)))::u => if Nat.odd p
          then option_map (cons 1) (fast_power fuel (Nat.div2 p) (g::u))
          else option_map (first_plus 4) (fast_power fuel (Nat.div2 p) (g::u))
      end
    end
  end.

Fixpoint checked_f (accel fuel:nat) (w:word) : option result :=
  match fuel with
  | 0 => None
  | S fuel =>
    match fast_power accel 1 w with
    | Some v => Some (Some v)
    | None =>
      match w with
      | [] => Some (Some [1])
      | 1::u => option_map (lift_plus 4) (checked_f accel fuel u)
      | 2::u => option_map (lift_prefix [2]) (checked_f accel fuel u)
      | 3::u =>
        match checked_f accel fuel u with
        | None => None
        | Some None => Some None
        | Some (Some v) => option_map (lift_prefix [3]) (checked_f accel fuel v)
        end
      | S(S(S(S g)))::u => Some (Some (1::g::u))
      | [0] => Some (Some [2;2])
      | 0::0::u => Some None
      | 0::1::u => option_map (fun r => lift_prefix [2] (lift_plus 2 r)) (checked_f accel fuel u)
      | 0::2::u => option_map (lift_prefix [2;0]) (checked_f accel fuel u)
      | 0::S(S(S g))::u => option_map (fun r => lift_prefix [2] (lift_plus 1 r)) (checked_f accel fuel (g::u))
      end
    end
  end.

Theorem fast_power_sound fuel : forall p w v,
 fast_power fuel p w = Some v -> power F p (Some w) = Some v.
Proof.
  induction fuel as [|fuel IH]; intros p w v E; [discriminate|].
  destruct p as [|p].
  - cbn [fast_power] in E. inversion E. reflexivity.
  - destruct w as [|g u].
    + cbn [fast_power] in E. inversion E; subst. apply power_F_nil.
    + destruct g as [|[|[|[|g]]]].
      * discriminate.
      * cbn [fast_power] in E.
        change (power F (S p) (L1 (Some u)) = Some v).
        rewrite acc_L_binary.
        destruct (Nat.odd (S p)) eqn:O.
        -- destruct (fast_power fuel (S(Nat.div2(S p))) u) as [a|] eqn:A; try discriminate.
           inversion E; subst. exact (f_equal D (IH _ _ _ A)).
        -- destruct (fast_power fuel (Nat.div2(S p)) u) as [a|] eqn:A; try discriminate.
           inversion E; subst. exact (f_equal L1 (IH _ _ _ A)).
      * cbn [fast_power] in E.
        change (power F (S p) (prefix 2 (Some u)) = Some v).
        rewrite acc_power_two.
        destruct (fast_power fuel (S p) u) as [a|] eqn:A; try discriminate.
        inversion E; subst. exact (f_equal (prefix 2) (IH _ _ _ A)).
      * cbn [fast_power] in E.
        change (power F (S p) (prefix 3 (Some u)) = Some v).
        rewrite acc_power_three.
        destruct (fast_power fuel (2*S p) u) as [a|] eqn:A; try discriminate.
        inversion E; subst. exact (f_equal (prefix 3) (IH _ _ _ A)).
      * cbn [fast_power] in E.
        replace (S(S(S(S g)))) with (g+4) by lia.
        change (power F (S p) (D (Some (g::u))) = Some v).
        rewrite acc_D_binary by discriminate.
        destruct (Nat.odd (S p)) eqn:O;
          destruct (fast_power fuel (Nat.div2(S p)) (g::u)) as [a|] eqn:A; try discriminate;
          inversion E; subst; [exact (f_equal L1 (IH _ _ _ A)) | exact (f_equal D (IH _ _ _ A))].
Qed.

Theorem checked_f_sound accel fuel : forall w r,
 checked_f accel fuel w = Some r -> f w = r.
Proof.
  induction fuel as [|fuel IH]; intros w r E; [discriminate|].
  cbn [checked_f] in E.
  destruct (fast_power accel 1 w) as [v|] eqn:P.
  - inversion E; subst. exact (fast_power_sound _ _ _ _ P).
  - destruct w as [|g u].
    + inversion E; subst; apply f_nil.
    + destruct g as [|[|[|[|g]]]].
      * destruct u as [|h u].
        -- inversion E; subst; apply f_zero.
        -- destruct h as [|[|[|h]]].
           ++ inversion E; subst; apply f_zero_zero.
           ++ destruct (checked_f accel fuel u) as [a|] eqn:A; try discriminate.
              inversion E; subst. rewrite f_zero_one, (IH _ _ A). reflexivity.
           ++ destruct (checked_f accel fuel u) as [a|] eqn:A; try discriminate.
              inversion E; subst. rewrite f_zero_two, (IH _ _ A). reflexivity.
           ++ destruct (checked_f accel fuel (h::u)) as [a|] eqn:A; try discriminate.
              inversion E; subst. replace (S(S(S h))) with (h+3) by lia.
              rewrite f_zero_large, (IH _ _ A). reflexivity.
      * destruct (checked_f accel fuel u) as [a|] eqn:A; try discriminate.
        inversion E; subst. rewrite f_one, (IH _ _ A). reflexivity.
      * destruct (checked_f accel fuel u) as [a|] eqn:A; try discriminate.
        inversion E; subst. rewrite f_two, (IH _ _ A). reflexivity.
      * destruct (checked_f accel fuel u) as [[a|]|] eqn:A; try discriminate.
        -- destruct (checked_f accel fuel a) as [b|] eqn:B; try discriminate.
           inversion E; subst. rewrite f_three, (IH _ _ A).
           cbn [bind]. rewrite (IH _ _ B). reflexivity.
        -- inversion E; subst. rewrite f_three, (IH _ _ A). reflexivity.
      * inversion E; subst. replace (S(S(S(S g)))) with (g+4) by lia.
        apply f_large.
Qed.
