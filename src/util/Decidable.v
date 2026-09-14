Abbreviation Reflects x := (BoolSpec x (~x)).

Lemma Reflects_iff P Q b :
  Reflects P b ->
  P <-> Q ->
  Reflects Q b.
Proof. intros HP Hiff. destruct HP; constructor; tauto. Qed.
