From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Definition decimal := seq nat.

Parameter allowed : decimal -> Prop.

Axiom only_digits : forall d : decimal,
  allowed d -> all (leq^~ 9) d.

Axiom no_leading_zeros : forall d : decimal,
  allowed d -> head 0 d = 0 -> d = [:: 0].

Axiom zero_if_sum_is_prime : forall d : decimal,
  allowed d -> (0 \in d = prime (sumn d)).

Axiom one_if_product_is_odd : forall d : decimal,
  allowed d -> (1 \in d = odd (\prod_(i <- d) i)).

Axiom two_if_strictly_increasing : forall d : decimal,
  allowed d -> (2 \in d = sorted ltn d).

Axiom three_if_all_different : forall d : decimal,
  allowed d -> (3 \in d = uniq d).

Axiom four_if_no_digit_above_4 : forall d : decimal,
  allowed d -> (4 \in d = all (leq^~ 4) d).

Axiom five_if_max_5_digits : forall d : decimal,
  allowed d -> (5 \in d = (size d <= 5)).

Axiom six_if_6_not_divisor_of_product : forall d : decimal,
  allowed d -> (6 \in d = ~~(6 %| (\prod_(i <- d) i))).

Axiom seven_if_last_digit_is_even : forall d : decimal,
  allowed d -> (7 \in d = (~~ odd (last 0 d))).

Axiom eight_if_no_consecutive_digits : forall d : decimal,
  allowed d -> (8 \in d = pairwise (fun x y => (x != y.+1) && (y != x.+1)) d).

Axiom nine_if_digit_is_sum_of_two_others : forall d : decimal,
  allowed d -> (9 \in d <-> exists x y z, subseq [:: x; y; z] d && (
    (x + y == z) || (y + z == x) || (z + x == y))).

Lemma six_implies_no_6 : forall d : decimal,
  allowed d -> (6 \in d -> 6 \notin d).
Proof.
  move=> d /six_if_6_not_divisor_of_product /esym + H6.
  rewrite H6.
  apply: contra => _.
  have := (perm_rot (index 6 d) d).
  rewrite rot_index; last first. by [].
  move=> /permPl Hperm.
  rewrite -(perm_big _ Hperm) /= big_cons.
  by apply: dvdn_mulr.
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
  move=> Hrec.
  rewrite big_cons oddM.
  move=> /andP[? ?].
  apply/andP; split.
  - by [].
  - by apply: Hrec.
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
  move=> /allP Hall_odd.
  apply/allP=> y Hy.
  have H_odd_y := (Hall_odd _ Hy).
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

Theorem no_1 : forall d : decimal,
  allowed d -> 1 \notin d.
Proof.
  move=> d Hallowed.
  apply/negP=> H1.
  have/no_8_implies_even_digit: (8 \notin d) by apply: one_implies_no_8.
  move=> not_all_odd.
  have:= (not_all_odd Hallowed).
  have->:= (one_implies_only_odd_digit _ Hallowed H1).
  by [].
Qed.

Lemma two_implies_no_0 : forall d : decimal,
  allowed d -> (2 \in d -> 0 \notin d).
Proof.
  move=> d Hallowed H2.
  have:= (two_if_strictly_increasing _ Hallowed).
  rewrite H2.
  move=> /esym.
  apply: contraL.
  move: Hallowed H2.
  move=> /no_leading_zeros.
  case: d => //= x xs.
  case: x => //=.
  - move=> H0 H2 _.
    rewrite in_cons /= in H2.
    injection H0; last first. by [].
    move=> Hempty.
    by rewrite Hempty in H2.
  - move=> n _ _ H0.
    (* 0 is not the first element, but then the seq is not sorted *)
Admitted.    

Lemma two_implies_3 : forall d : decimal,
  allowed d -> (2 \in d -> 3 \in d).
Proof.
  move=> d Hallowed.
  have->:= (two_if_strictly_increasing _ Hallowed).
  have->:= (three_if_all_different _ Hallowed).
  rewrite ltn_sorted_uniq_leq.
  by move=> /andP[].
Qed.

Lemma three_implies_no_4 : forall d : decimal,
  allowed d -> (3 \in d -> 4 \notin d).
Proof.
  move=> d Hallowed.
  have->:= (three_if_all_different _ Hallowed).
  have->:= (four_if_no_digit_above_4 _ Hallowed).
  move=> H3.
  apply/negP=> H4.
  have/uniq_leq_size //=: ({subset d <= iota 0 5}). {
    move: H4. clear.
    move=> /allP H4 x /H4.
    by rewrite mem_iota.
  }
  move=> Hsub.
  apply Hsub in H3.
  move: H3.
  rewrite -five_if_max_5_digits; last first. by [].
  move: H4. clear.
  move=> /allP Hall H5.
  by have:= (Hall _ H5).
Qed.

Lemma two_implies_no_8 : forall d : decimal,
  allowed d -> (2 \in d -> 8 \notin d).
Proof.
  (* 2 => 3 *)
  (* 2 and 3 => no 8 by definition of 8 *)
  move=> d Hallowed H2.
  have H3 := (two_implies_3 _ Hallowed H2).
  have->:= (eight_if_no_consecutive_digits _ Hallowed).
  Search pairwise.
Admitted.

Lemma two_implies_no_7 : forall d : decimal,
  allowed d -> (2 \in d -> 7 \notin d).
Proof.
  (* The final digit is odd (because the digits are increasing and we have excluded all even digits after 3) *)
Admitted.

Lemma two_implies_5 : forall d : decimal,
  allowed d -> (2 \in d -> 5 \in d).
Proof.
  (* At this point, we can only have 2, 3, 5 and 9 and they can only appear once, so we have fewer than 5 digits *)
Admitted.

Lemma two_implies_9 : forall d : decimal,
  allowed d -> (2 \in d -> 9 \in d).
Proof.
  (* Since we have 2, 3 and 5, we have 2 + 3 = 5, and thus we have 9 *)
Admitted.

Lemma two_implies_2359 : forall d : decimal,
  allowed d -> d = [:: 2; 3; 5; 9].
Proof.
Admitted.

Lemma two_implies_0 : forall d : decimal,
  allowed d -> (2 \in d -> 0 \in d).
Proof.
  (* 2 + 3 + 5 + 9 = 19, so we have 0 *)
Admitted.

Lemma no_2 : forall d : decimal,
  allowed d -> 2 \notin d.
Proof.
  (* We have a contradiction from two_implies_0 and two_implies_no_0 *)
  move=> d Hallowed.
  apply/negP=> H2.
  have /negP H0 := (two_implies_no_0 _ Hallowed H2).
  have H2' := (two_implies_0 _ Hallowed H2).
  by apply: H0.
Qed.