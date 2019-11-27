Require Import Reals.
Require Import Field Psatz.
From mathcomp Require Import all_ssreflect.

Section Edwards.

(* First create a field *)
Variable K : Set.

Variables kO kI : K.
Notation "0" := kO.
Notation "1" := kI.

Hypothesis one_not_zero: 1 <> 0.

Variable kplus kmul ksub kdiv : K -> K -> K.
Notation "x + y" := (kplus x y). 
Notation "x * y " := (kmul x y). 
Notation "x - y " := (ksub x y).
Notation "x / y" := (kdiv x y).

Variables kopp kinv :  K -> K.
Notation "- x" := (kopp x).
Notation "/ x" := (kinv x). 

(* Test to zero *)
Variable is_zero: K -> bool.

Hypothesis is_zero_correct : forall k, is_zero k = true <-> k = 0.
 
(* It is a field *)  
Variable Kfth :  field_theory kO kI kplus kmul ksub kopp kdiv kinv (@eq K).

(* Trick to get the power function *)
Fixpoint pow (k: K) (n: nat) :=
 match n with O => 1 | 1%nat => k | S n1 => k * pow k n1 end.

Notation "x ^ y" := (pow x y).

Lemma pow_S k n : k ^ (S n) = k * k ^ n.
Proof.
case: n => //=.
by rewrite Kfth.(F_R).(Rmul_comm) Kfth.(F_R).(Rmul_1_l).
Qed.

Let Mkmul := rmul_ext3_Proper (Eq_ext kplus kmul kopp).

Lemma Kpower_theory : 
  Ring_theory.power_theory 1 kmul (eq (A:=K)) BinNat.nat_of_N pow.
Proof.
constructor => r [|] //=.
elim/BinPos.Pind => // n H.
rewrite Pnat.nat_of_P_succ_morphism pow_S.
rewrite (Ring_theory.pow_pos_succ (Eqsth K) Mkmul) ?H //.
exact Kfth.(F_R).(Rmul_assoc).
Qed.

Ltac iskpow_coef t :=
  match t with
  | (S ?x) => iskpow_coef x
  | O => true
  | _ => false
  end.

Ltac kpow_tac t :=
 match iskpow_coef t with
 | true => constr:(BinNat.N_of_nat t)
 | _ => constr:(NotConstant)
 end.

Add Field Kfth : Kfth (power_tac Kpower_theory [kpow_tac]).

Lemma Kmult_integral x y : x * y = 0 -> x = 0 \/ y = 0.
Proof.
move=> H.
case: (is_zero x) (is_zero_correct x) => [[H1 _]|[_ H1]].
  by left; apply: H1.
right.
apply: trans_equal (_ : (/x) * (x * y) = _); try field.
  by move=> /H1.
rewrite H; ring.
Qed.

Lemma Kdiv_0_l x : 0 / x = 0.
Proof. rewrite (Fdiv_def Kfth); ring. Qed.

Lemma Kdiv_eq_0_compat_r x y : x = 0 -> x / y = 0.
Proof. rewrite (Fdiv_def Kfth)=>->; ring. Qed.

(* We can now start the elliptic part *)

Variables cs d : K.

Definition c := cs * cs.

(* not a non-zero square *)
Definition ns v := forall x, v = x * x -> v = 0.

Lemma nsD v y : ns v -> 1 - v * y * y <> 0.
Proof.
move=> H.
have := is_zero_correct v.
case: is_zero => // [[-> // _]|[_ H1] H2].
  contradict one_not_zero.
  by rewrite -one_not_zero; ring.
have H0 : v * y * y = 1.
  rewrite (_ : 1 = 1 - 0); last by ring.
  by rewrite -H2; ring.
have H3 : y <> 0.
  move=> H3; rewrite H3 in H0.
  case: one_not_zero.
  by rewrite -H0; ring.
suff : false = true by [].
apply/H1/(H (1 / y)).
by field[H0].
Qed.

Hypothesis ns_d : ns d.

(* A point *)
Notation point := (K * K)%type.

Implicit Types p q : point.

Definition dx p q := 1 - d * p.1 * p.2 * q.1 * q.2.

Lemma dxC p q : dx p q = dx q p.
Proof. rewrite /dx; ring. Qed.

Definition dy p q := 1 + d * p.1 * p.2 * q.1 * q.2.

Lemma dyC p q : dy p q = dy q p.
Proof. rewrite /dy; ring. Qed.

Definition dd p q :=
  1 - d * d * p.1 * p.1 * p.2 * p.2 * 
              q.1 * q.1 * q.2 * q.2.

Lemma ddE p q : dd p q = dx p q * dy p q.
Proof. rewrite /dd /dx /dy; ring. Qed.

Lemma ddC p q : dd p q = dd q p.
Proof. rewrite !ddE dxC dyC; ring. Qed.

Definition add p q : point :=
 (/(dx p q) * (p.1 * q.1 - c * p.2 * q.2),
  /(dy p q) * (p.1 * q.2 + q.1 * p.2)).

Infix "++" := add.

(* Adding is commutative *)
Lemma addC p q : p ++ q = q ++ p.
Proof. rewrite /add dxC dyC; congr (_, _); ring. Qed.

Definition d0 : point := (1, 0).

Lemma add0C p : d0 ++ p = p.
Proof.
case: p => x y.
by rewrite /add /dx /dy /=; congr (_, _); field.
Qed.

Definition on p :=
  d * p.1 * p.1 * p.2 * p.2 = p.1 * p.1 + c * p.2 * p.2 - 1.

(* 0 is on the curve *)
Lemma on0 : on d0.
Proof. rewrite /on /d0 /=; ring. Qed.

(* Opposite *)
Definition opp p : point := (p.1,-p.2).

Notation "-- x" := (opp x) (at level 10).

(* The opposite is on the curve *)
Lemma on_opp p : on p -> on (-- p).
Proof.
case: p => x y; rewrite /on /= => H; ring[H].
Qed.

(* If we are on the curve, we can divide by dd *)
Lemma on_dd p q : on p -> on q -> dd p q <> 0.
Proof.
case: p => x1 y1; case: q => x2 y2.
have F x : 1 - x = 0 -> x = 1.
  move=> H.
  replace 1 with (1 - x + x) by ring.
  by rewrite H; ring.
pose r := (1 - c * d * y1 * y1 * y2 * y2) *
          (1 - d * y1 * y1 * x2 * x2).
rewrite /on /dd /= => H1 H2 /F H3.
have /Kmult_integral[H|H] : r = 0.
- rewrite /r.
(* here we mimic a grobner computation *)
  ring_simplify [H1 H2] in H3.
  set u := _ * c ^ 2 in H3.
  have: u = u - 1 + 1 by ring.
  rewrite -[in u - _]H3 => H4; ring_simplify in H4; rewrite /u in H4.
  ring_simplify[H1 H2].
  ring_simplify[H4].
  ring_simplify[H1 H2].
  ring[H4].
- case (nsD _ (cs * y1 * y2) ns_d).
  by rewrite -H /c; ring.
case (nsD _ (y1 * x2) ns_d).
by rewrite -H /c; ring.
Time Qed.

(* If we are on the curve, we can divide by dx *)
Lemma on_dx p q : on p -> on q -> dx p q <> 0.
Proof.
intros H1 H2 H.
case (on_dd _ _ H1 H2).
rewrite ddE; ring[H].
Qed.

(* If we are on the curve, we can divide by dy *)
Lemma on_dy p q : on p -> on q -> dy p q <> 0.
Proof.
intros H1 H2 H.
case (on_dd _ _ H1 H2).
rewrite ddE; ring[H].
Qed.

(* Adding the opposite give 0 *)
Lemma addnK p : on p -> p ++ -- p = d0.
Proof.
intro H1.
have H2 := on_opp _ H1.
move: {H2}H1 (on_dx _ _ H1 H2) (on_dy _ _ H1 H2).
case: p => x y.
rewrite  /on /add /dx /dy /= => H1 H2 H3.
by congr (_, _); field[H1].
Qed.

(* Adding two elements of the curve gives an element of the curve *)
Lemma on_add p q : on p -> on q -> on (p ++ q).
Proof.
move=> H1 H2.
move: H1 H2 (on_dx _ _ H1 H2) (on_dy _ _ H1 H2).
case: p => x1 y1; case: q => x2 y2.
rewrite /on /= /dx /dy /= => H1 H2 H3 H4.
field_simplify => //.
congr (_ / _).
ring [H1 H2].
Time Qed.

(* Adding is associative *)
Lemma add_assoc p q r :
   on p -> on q -> on r -> (p ++ q) ++ r = p ++ (q ++ r).
Proof.
move=> H1 H2 H3.
move: H1 H2 H3 (on_dx _ _ H1 H2) (on_dy _ _ H1 H2) 
               (on_dx _ _ H2 H3) (on_dy _ _ H2 H3)
               (on_dx _ _  H1 (on_add _ _ H2 H3))
               (on_dy _ _  H1 (on_add _ _ H2 H3))
               (on_dx _ _  (on_add _ _ H1 H2) H3)
               (on_dy _ _  (on_add _ _ H1 H2) H3).
case: p => x1 y1; case: q => x2 y2; case: r => x3 y3.
rewrite /add /on /= /dx /dy /= => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
congr (_,_).
  field[H1 H2 H3]; repeat split => //.
    contradict H8; field_simplify; last by split.
    apply: Kdiv_eq_0_compat_r.
    by rewrite -H8; ring.
  contradict H10; field_simplify; last by split.
  apply: Kdiv_eq_0_compat_r.
  by rewrite -H10; ring.
Time field[H1 H2 H3]=> //.
repeat split => //.
  contradict H9; field_simplify; last by split.
  apply: Kdiv_eq_0_compat_r.
  by rewrite -H9; ring.
contradict H11; field_simplify; last by split; auto.
apply: Kdiv_eq_0_compat_r.
rewrite -H11; ring.
Time Qed.

End Edwards.

