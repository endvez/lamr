import LAMR.Util.FirstOrder.Atp
open Std

/-
This example illustrates the use of Vampire. The problem it solves
is as follows:

"A very special island is inhabited only by knights and knaves.
Knights always tell the truth, and knaves always lie. You meet two
inhabitants: Zoey and Mel. Zoey tells you that Mel is a knave. Mel
says, 'Neither Zoey nor I are knaves.' Who is a knight and who is
a knave?"

Notice that we model "X says Y" as "Knight(X) ↔ Y." Think about why this
make sense! Notice also that we model "Knave(X)" as "¬ Knight(X)".
-/

def knights_knaves_hypotheses : List FOForm := [
  fo!{Knight(Zoey) ↔ ¬ Knight(Mel)},
  fo!{Knight(Mel) ↔ Knight(Zoey) ∧ Knight(Mel) }
]

def knights_knaves_conclusion: FOForm :=
  fo!{Knight(Zoey) ∧ ¬ Knight(Mel) }

-- Make sure hypotheses are consistent.
#eval (do
  discard <| callVampireTptp knights_knaves_hypotheses fo!{⊥} (verbose := true)
  : IO Unit)

-- Show that the conclusion follows from the hypotheses.
#eval (do
  discard <| callVampireTptp knights_knaves_hypotheses knights_knaves_conclusion (verbose := true)
  : IO Unit)

/-
Use Vampire to verify the following inference, by filling in the hypotheses and conclusion.

Every honest and industrious person is healthy.
No grocer is healthy.
Every industrious grocer is honest.
Every cyclist is industrious.
Every unhealthy cyclist is dishonest.

Conclusion: No grocer is a cyclist.

(Represent "unhealthy" as the negation of "healthy", and "dishonest" and the negation of
"honest." Let the variables range over people.)
-/

def grocer_is_not_a_cyclist_hypotheses : List FOForm := [
  fo!{∀ x. Honest(%x) ∧ Industrious(%x) → Healthy(%x)},
  fo!{∀ x. Grocer(%x) → ¬Healthy(%x)},
  fo!{∀ x. Grocer(%x) ∧ Industrious(%x) → Honest(%x)},
  fo!{∀ x. Cyclist(%x) → Industrious(%x)},
  fo!{∀ x. Cyclist(%x) ∧ ¬Healthy(%x) → ¬Honest(%x)}
]

def grocer_is_not_a_cyclist_conclusion: FOForm :=
  fo!{∀ x. Grocer(%x) → ¬Cyclist(%x)}

-- Should say Termination Reason: Satisfiable
#eval (do
  discard <| callVampireTptp grocer_is_not_a_cyclist_hypotheses fo!{⊥} (verbose := true)
  : IO Unit)

-- Should say Termination Reason: Refutation
#eval (do
  discard <| callVampireTptp grocer_is_not_a_cyclist_hypotheses grocer_is_not_a_cyclist_conclusion (verbose := true)
  : IO Unit)

/-
Do the same for this problem.

Wolves, foxes, birds, caterpillars, and snails are animals, and there are
some of each of them.
Also there are some grains, and grains are plants.
Every animal either likes to eat all plants or all animals smaller than itself that
like to eat some plants.
Caterpillars and snails are smaller than birds,
which are smaller than foxes, which in turn are smaller than wolves.
Wolves do not like to eat foxes or grains, while birds like to eat caterpillars
but not snails.
Caterpillars and snails like to eat some plants.
Therefore there is an animal that likes to eat an animal that eats some grains.

(Some of these hypotheses are best represented with multiple formulas.)
-/

def animals_hypotheses : List FOForm := [
  fo!{∃ w. Wolf(%w)},
  fo!{∀ w. Wolf(%w) → Animal(%w)},
  fo!{∃ f. Fox(%f)},
  fo!{∀ f. Fox(%f) → Animal(%f)},
  fo!{∃ b. Bird(%b)},
  fo!{∀ b. Bird(%b) → Animal(%b)},
  fo!{∃ c. Caterpillar(%c)},
  fo!{∀ c. Caterpillar(%c) → Animal(%c)},
  fo!{∃ s. Snail(%s)},
  fo!{∀ s. Snail(%s) → Animal(%s)},
  fo!{∃ g. Grain(%g)},
  fo!{∀ g. Grain(%g) → Plant(%g)},
  fo!{∀ x. Animal(%x) → (∀ y. Plant(%y) → LikesEating(%x, %y)) ∨ (∀ y. Animal(%y) ∧ Smaller(%y, %x) ∧ (∃ z. Plant(%z) ∧ LikesEating(%y, %z)) → LikesEating(%x, %y))},
  fo!{∀ c. ∀ b. (Caterpillar(%c) ∧ Bird(%b)) → Smaller(%c, %b)},
  fo!{∀ s. ∀ b. (Snail(%s) ∧ Bird(%b)) → Smaller(%s, %b)},
  fo!{∀ f. ∀ b. (Fox(%f) ∧ Bird(%b)) → Smaller(%b, %f)},
  fo!{∀ f. ∀ w. (Fox(%f) ∧ Wolf(%w)) → Smaller(%f, %w)},
  fo!{∀ w. ∀ f. (Wolf(%w) ∧ Fox(%f)) → (¬LikesEating(%w, %f))},
  fo!{∀ w. ∀ g. (Wolf(%w) ∧ Grain(%g)) → (¬LikesEating(%w, %g))},
  fo!{∀ b. ∀ c. (Bird(%b) ∧ Caterpillar(%c)) → LikesEating(%b, %c)},
  fo!{∀ b. ∀ s. (Bird(%b) ∧ Snail(%s)) → (¬LikesEating(%b, %s))},
  fo!{∀ c. Caterpillar(%c) → ∃ p. Plant(%p) ∧ LikesEating(%c, %p)},
  fo!{∀ s. Snail(%s) → ∃ p. Plant(%p) ∧ LikesEating(%s, %p)}
]

def animals_conclusion: FOForm :=
  fo!{∃ x. ∃ y. Animal(%x) ∧ Animal(%y) ∧ LikesEating(%x, %y) ∧ ∃ g. Grain(%g) ∧ LikesEating(%y, %g)}

#eval (do
  discard <| callVampireTptp animals_hypotheses fo!{⊥} (verbose := true)
  : IO Unit)

#eval (do
  discard <| callVampireTptp animals_hypotheses animals_conclusion (verbose := true)
  : IO Unit)
