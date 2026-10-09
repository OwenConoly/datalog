Abbreviation Reflects x := (BoolSpec x (~x)).

Lemma Reflects_iff P Q b :
  Reflects P b ->
  P <-> Q ->
  Reflects Q b.
Proof. intros HP Hiff. destruct HP; constructor; tauto. Qed.

Lemma Reflects_true_iff P b {H : Reflects P b} :
  b = true <-> P.
Proof. destruct H; intuition congruence. Qed.

Lemma Reflects_false_iff P b `{H : Reflects P b} :
  b = false <-> ~P.
Proof. destruct H; intuition congruence. Qed.
