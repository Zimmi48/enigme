From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Definition decimal := seq nat.

Parameter allowed : decimal -> Prop.

Axiom only_digits : forall d : decimal,
  allowed d -> all (fun x => x < 10) d.

Axiom no_leading_zeros : forall d : decimal,
  allowed d -> head 0 d = 0 -> d = [:: 0].

Axiom zero_if_sum_is_prime : forall d : decimal,
  allowed d -> (0 \in d = prime (foldr addn 0 d)).

Axiom one_if_product_is_odd : forall d : decimal,
  allowed d -> (1 \in d = odd (foldr muln 1 d)).

Axiom two_if_strictly_increasing : forall d : decimal,
  allowed d -> (2 \in d = pairwise (fun x y => x < y) d).

Axiom three_if_all_different : forall d : decimal,
  allowed d -> (3 \in d = pairwise (fun x y => x != y) d).

Axiom four_if_no_digit_above_4 : forall d : decimal,
  allowed d -> (4 \in d = all (fun x => x <= 4) d).

Axiom five_if_max_5_digits : forall d : decimal,
  allowed d -> (5 \in d = (size d <= 5)).

Axiom six_if_6_not_divisor_of_product : forall d : decimal,
  allowed d -> (6 \in d = ~~(6 %| foldr muln 1 d)).

Axiom seven_if_last_digit_is_even : forall d : decimal,
  allowed d -> (7 \in d = ((last 0 d) %% 2 == 0)).

Axiom eight_if_no_consecutive_digits : forall d : decimal,
  allowed d -> (8 \in d = pairwise (fun x y => (x != y.+1) && (y != x.+1)) d).

Axiom nine_if_digit_is_sum_of_two_others : forall d : decimal,
  allowed d -> (9 \in d <-> exists x y z, subseq [:: x; y; z] d && (
    (x + y == z) || (y + z == x) || (z + x == y))).

Lemma six_implies_no_6 : forall d : decimal,
  allowed d -> (6 \in d -> 6 \notin d).
Proof.
  move=> d /six_if_6_not_divisor_of_product Hprop6 H6. symmetry in Hprop6. move: Hprop6.
  rewrite H6.
  apply: contra => _. move: H6.
  elim: d => //= x xs Hrec.
  rewrite in_cons.
  move/orP; case.
  - move=> /eqP<- //=.
    by apply: dvdn_mulr.
  - move=> /Hrec Hrec2.
    by apply: dvdn_mull.
Qed.

Theorem no_6 : forall d : decimal,
  allowed d -> 6 \notin d.
Proof.
  move=> d /six_implies_no_6 Hcontra.
  apply: wlog_neg.
  apply: contraL => ?.
  apply/negPn.
  by apply: Hcontra.
Qed.

Lemma one_implies_only_odd_digit : forall d : decimal,
  allowed d -> 1 \in d -> all odd d.
Proof.
  move=> d /one_if_product_is_odd->.
  elim: d => //= x xs.
  rewrite oddM.
  move=> Hrec /andP[? ?].
  apply/andP; split.
  - by [].
  - apply: Hrec.
    by [].
Qed.

Lemma one_implies_no_8 : forall d : decimal,
  allowed d -> (1 \in d -> 8 \notin d).
Proof.
  (* specialize previous lemma *)
  move=> d /one_implies_only_odd_digit only_odd {}/only_odd.
  apply: contraL.
  move=> H8.
  apply/allPn.
  by exists 8.
Qed.

Search all mem.

Lemma no_8_implies_even_digit : forall d : decimal,
  allowed d -> (8 \notin d -> ~~ all odd d).
Proof.
  move=> d /eight_if_no_consecutive_digits->.
  apply: contra.
  elim: d => //= x xs Hrec.
  move=> /andP[H_odd_x H_all_odd].
  apply/andP; split; last by apply: Hrec.
  clear Hrec.
  move: H_all_odd.
  elim: xs => //= y ys Hrec /andP[H_odd_y ?].
  apply/andP; split; last by apply: Hrec.
  clear Hrec.
  apply/andP; split.
  - move: H_odd_x.
    apply: contraL.
    move=> /eqP-> //=.
    by rewrite H_odd_y.
  - move: H_odd_y.
    apply: contraL.
    move=> /eqP-> //=.
    by rewrite H_odd_x.
Qed.

Lemma no_1 : forall d : decimal,
  allowed d -> 1 \notin d.
Proof.
  move=> d Hallowed.
  apply/negP.
  move=> H1.
  exfalso.
  have/no_8_implies_even_digit: (8 \notin d) by apply: one_implies_no_8.
  move=> not_all_odd.
  have:= (not_all_odd Hallowed).
  have->:= (one_implies_only_odd_digit _ Hallowed H1).
  by [].
Qed.