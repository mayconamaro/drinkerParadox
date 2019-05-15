Hypothesis U : Set.
Hypothesis u : U.
Hypothesis P : U -> Prop.

Axiom LEM : forall P : Prop, P \/ ~P.

Lemma drinkerParadox : exists x, (P x -> forall y, P y).
Proof.
  specialize (LEM (exists x, ~ P x)).
  intro H1.
  destruct H1 as [H2 | H3].
  +
    destruct H2 as [z H3].
    exists z.
    intro H4.
    contradiction.
  +
    exists u.
    intro H5.
    intro w.
    specialize (LEM (P w)).
    intro H6.
    destruct H6 as [H7 | H8].
    *
      assumption.
    *
      absurd (exists x, ~ P x).
      -
        assumption.
      -
        exists w.
        assumption.
Qed.