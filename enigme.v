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
  allowed d -> (8 \in d = all2rel (fun x y => (x != y.+1)) d).

Axiom nine_if_digit_is_sum_of_two_others : forall d : decimal,
  allowed d -> (9 \in d <-> exists x y z, subseq [:: x; y; z] d && (
    (x + y == z) || (y + z == x) || (z + x == y))).

Section Allowed.

  Variable d : decimal.
  Hypothesis Hallowed : allowed d.

  Lemma six_implies_no_6 : 6 \in d -> 6 \notin d.
  Proof.
    have /esym := (six_if_6_not_divisor_of_product _ Hallowed).
    move=> + H6.
    rewrite H6.
    apply: contra => _.
    have := (perm_rot (index 6 d) d).
    rewrite rot_index; last by [].
    move=> /permPl Hperm.
    rewrite -(perm_big _ Hperm) /= big_cons.
    by apply: dvdn_mulr.
  Qed.

  Theorem no_6 : 6 \notin d.
  Proof.
    have := six_implies_no_6.
    rewrite -{1}[_ \in _]negbK.
    apply: wlog_neg.
  Qed.

  Lemma one_implies_only_odd_digit : 1 \in d -> all odd d.
  Proof.
    rewrite one_if_product_is_odd; last by [].
    elim: d => //= x xs Hrec.
    rewrite big_cons oddM.
    move=> /andP[->] //=.
  Qed.

  Lemma one_implies_no_8 : 1 \in d -> 8 \notin d.
  Proof.
    (* specialize previous lemma *)
    move=> {}/one_implies_only_odd_digit.
    apply: contraL.
    move=> H8.
    apply/allPn.
    by exists 8.
  Qed.

  Lemma no_8_implies_even_digit : 8 \notin d -> ~~ all odd d.
  Proof.
    rewrite eight_if_no_consecutive_digits; last by [].
    apply: contra.
    move=> /allP Hodd.
    apply/allP.
    move=> x /Hodd Hx.
    apply/allP.
    move=> y /Hodd Hy.
    move: Hx.
    apply: contraL.
    move=> /eqP-> //=.
    by rewrite Hy.
  Qed.

  Theorem no_1 : 1 \notin d.
  Proof.
    apply/negP=> H1.
    have/no_8_implies_even_digit: (8 \notin d) by apply: one_implies_no_8.
    by rewrite one_implies_only_odd_digit.
  Qed.

  Lemma two_implies_no_0 : 2 \in d -> 0 \notin d.
  Proof.
    move=> H2.
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
      injection H0; last by [].
      move=> Hempty.
      by rewrite Hempty in H2.
    - move=> n _ _.
      rewrite in_cons //=.
      (* 0 is not the first element, but then the seq is not sorted *)
      apply: contraL.
      move=> /order_path_min.
      move=> Hmin.
      have {}Hmin := (Hmin ltn_trans).
      move: Hmin.
      apply: contraL.
      move=> H0.
      apply/negP.
      move=> /allP Hall.
      by have {}Hall := (Hall _ H0).
  Qed.

  Lemma two_implies_3 : 2 \in d -> 3 \in d.
  Proof.
    rewrite two_if_strictly_increasing; last by [].
    rewrite three_if_all_different; last by [].
    rewrite ltn_sorted_uniq_leq.
    by move=> /andP[].
  Qed.

  Lemma three_implies_no_4 : 3 \in d -> 4 \notin d.
  Proof.
    rewrite three_if_all_different; last by [].
    rewrite four_if_no_digit_above_4; last by [].
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
    rewrite -five_if_max_5_digits; last by [].
    move: H4. clear.
    move=> /allP Hall H5.
    by have:= (Hall _ H5).
  Qed.

  Lemma two_implies_no_8 : 2 \in d -> 8 \notin d.
  Proof.
    move=> H2.
    (* 2 => 3 *)
    have H3 := (two_implies_3 H2).
    (* 2 and 3 => no 8 by definition of 8 *)
    rewrite eight_if_no_consecutive_digits; last by [].
    move: H2.
    apply: contraL.
    move=> /allP H8.
    apply/negP.
    have /allP {}H8 := (H8 _ H3).
    move=> H2.
    by have:= (H8 _ H2).
  Qed.

  Lemma two_remaining_digits : 2 \in d -> {subset d <= [:: 2; 3; 5; 7; 9] }.
  Proof.
    have : ({subset d <= iota 0 10}). {
      have:= (only_digits _ Hallowed).
      move=> /allP Hdigits x /Hdigits.
      by rewrite mem_iota.
    }
  Admitted.

  Lemma two_implies_no_7 : 2 \in d -> 7 \notin d.
  Proof.
    (* The final digit is odd (because the digits are increasing and we have excluded all even digits after 3) *)
  Admitted.

  Lemma two_implies_5 : 2 \in d -> 5 \in d.
  Proof.
    (* At this point, we can only have 2, 3, 5 and 9 and they can only appear once, so we have fewer than 5 digits *)
  Admitted.

  Lemma two_implies_9 : 2 \in d -> 9 \in d.
  Proof.
    (* Since we have 2, 3 and 5, we have 2 + 3 = 5, and thus we have 9 *)
  Admitted.

  Lemma two_implies_2359 : d = [:: 2; 3; 5; 9].
  Proof.
  Admitted.

  Lemma two_implies_0 : 2 \in d -> 0 \in d.
  Proof.
    (* 2 + 3 + 5 + 9 = 19, so we have 0 *)
  Admitted.

  Theorem no_2 : 2 \notin d.
  Proof.
    (* We have a contradiction from two_implies_0 and two_implies_no_0 *)
    apply/negP=> H2.
    have /negP H0 := (two_implies_no_0 H2).
    have H2' := (two_implies_0 H2).
    by apply: H0.
  Qed.

End Allowed.