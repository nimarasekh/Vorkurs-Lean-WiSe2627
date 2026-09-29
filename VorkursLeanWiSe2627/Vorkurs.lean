import Mathlib.Tactic

section introduction

-- Das ist eine `Lean` Datei.

-- Auf der linken Seite schreiben und sehen wir den `Code`,
-- Auf der rechten Seite sehen wir die `Ergebnisse`.

-- Das Symbol `--` am Anfang einer Zeile bedeutet,
-- dass der Rest der Zeile ein Kommentar ist.

-- Wie jede andere Programmiersprache hat Lean Zahlen
#check 1
-- Hier sehen wir in der oberen rechten Ecke,
-- `1 : ℕ`, was bedeutet, dass `1` eine natürliche Zahl ist.

-- `#check` überprüft den "Typ" hier

-- Wir können genau so weitermachen und andere Zahlen angucken:
#check 1 + 1
#check -2
#check 1.4


-- Natürlich brauchen wir auch neue Variablen, das geht mit `def`:
def x := 1
-- Im Gegensatz zu anderen Programmiersprachen,
-- geht `x := 1` ohne `def` nicht.

#check x

end introduction

section propositions

-- Im Unterschied zu anderen Programmiersprachen,
-- gibt es neben Zahlen auch `Aussagen`.

-- Die Wahrheitsaussage `True`
#check True
 -- Die Falschaussage `False`
#check False

-- Alle Wahrheitswerte leben in der Menge `Prop` (für Propositionen)
#check Prop

-- Natürlich können neue Variablen auch Aussagen sein:
def p := True
#check p

-- Es gibt nicht nur Wahrheitswerte, sondern auch logische Verknüpfungen:
-- Falsch impliziert wahr:
#check False → True

/-
Jetzt können wir anfangen, Mathematik zu machen.

Wir wollen die folgende Aussage in Lean schreiben:
Wenn `P` und `P → Q` wahr sind, dann ist auch `Q` wahr.

Hier besagt `theorem` am Anfang dass wir eine Aussage beweisen wollen.
- `mp` ist einfach ein Name des Satzes, den wir beweisen wollen
- `(P Q : Prop)` heißt, dass `P` und `Q` Aussagen sind.
- `(hP : P)` heißt, dass wir annehmen, dass `P` wahr ist.
- `(hPQ : P → Q)` heißt, dass wir annehmen, dass `P → Q` wahr ist.
- `(hQ : Q)` heißt, dass wir annehmen, dass `Q` wahr ist.
- `sorry` ist ein Platzhalter, der besagt,
  dass wir den Beweis noch nicht gemacht haben.
-/

theorem mp (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  sorry

end propositions

section natural_numbers
-- In diesem Teil sehen wir uns ein paar erste Beispiele
-- über die natürlichen Zahlen an.

-- Wir wissen, dass für jede natürliche Zahl `n` gilt:
-- `n + 0 = n`.

-- In Lean hat dieser Satz einen Namen: `Nat.add_zero`.
#check Nat.add_zero

-- Wenn `Nat.add_zero` sagt `Für alle n : ℕ, n + 0 = n`, was ist dann
-- `2 + 0 = 2`? Hier stecken wir einfach `2` in den Satz `Nat.add_zero` ein:
#check Nat.add_zero 2

/-
`Idee:` Aus der Programmierperspektive ist `Nat.add_zero` eine Funktion (Abbildung),
der Input ist eine natürliche Zahl `n` und der Output ist ein Beweis, dass `n + 0 = n`.
-/

-- Wir wollen jetzt den allgemeinen Fall nutzen um Spezialfälle zu beweisen.
-- Hier hat `example` den Vorteil, dass wir die Aussage nicht benennen müssen.

example : 3 + 0 = 3 := sorry
-- (Tipp: Die Antwort ist `Nat.add_zero 3`)

-- Normalerweise wissen wir aber auch, dass `0 + n = n`.
-- Können wir das auch in Lean beweisen? Leider nicht mit `Nat.add_zero`:
-- example (n : ℕ) : 0 + n = n := Nat.add_zero n

-- Aber es gibt eine funktionierende Alternative:
#check Nat.zero_add

-- Wir können ein paar Annahmen über natürliche Zahlen nutzen, und anfangen
-- neue Sätze zu beweisen. Zum Beispiel:

example : (3 * 4) + (2 + 1) = 15 := by
  -- Wir benutzen `rfl`, wenn es eine offensichtliche Gleichheit ist.
  rfl

example (n m : ℕ) (h1 : m = n) : m + 3 = n + 3 := by
  --  Wir benutzen `rw`, um eine Aussage mit einer Gleichheit umzuschreiben.
  rw [h1]

end natural_numbers

section induction

/-
Vorher haben wir `Nat.zero_add` einfach benutzt.
Jetzt wollen wir diesen Satz selbst mit Induktion beweisen.

Hierfür nutzen wir die `induction` Taktik (die ist vorgegeben).

Wir brauchen auch eine Tatsache über die natürlichen Zahlen, `Nat.add_succ`
die besagt, dass für natürliche Zahlen `n` und `m` gilt:
`n + (m + 1) = (n + m) + 1`.
-/
#check Nat.add_succ

theorem ex1 (n : Nat) : 0 + n = n := by
  induction n with
  -- Wir fangen an mit dem Basisfall, `n = 0`.
  | zero => {
    rfl
  }
  -- Dann machen wir den Induktionsschritt, `n = m + 1`.
  | succ n ih => {
    rw [Nat.add_succ]
    rw [ih]
  }

-- Die nächsten beiden Aufgaben sind ähnlich.
-- Aber hier brauchen wir `Nat.mul_succ`
-- Es besagt, dass für natürliche Zahlen `n` und `m` gilt:
-- `n * (m + 1) = (n * m) + n`.
#check Nat.mul_succ

-- Übung 2
theorem ex2 (n : Nat) : 0 * n = 0 := by
  induction n with
  | zero => {
    -- Hier `sorry` löschen und den Beweis schreiben.
    -- Wir sehen das Ziel ist `0 * 0 = 0`, was offensichtlich ist.
    -- Frage: Welche Taktik können wir hier benutzen?
    sorry
  }
  | succ n ih => {
    -- Hier `sorry` löschen und den Beweis schreiben.
    -- Wir sehen das Ziel ist `0 * (n + 1) = 0`,
    -- was wir zweimal umschreiben können.
    -- Frage: Welche Taktik können wir hier benutzen?
    sorry
  }

-- Übung 3
theorem ex3 (n : Nat) : 1 * n = n := by
  induction n with
  | zero => {
    sorry
  }
  | succ n ih => {
    sorry
  }

-- Lösung 2
-- theorem ex2sol (n : Nat) : 0 * n = 0 := by
--   induction n with
--   | zero => {
--     rfl
--   }
--   | succ n ih => {
--     rw [Nat.mul_succ]
--     rw [ih]
--   }

-- Lösung 3
-- theorem ex3sol (n : Nat) : 1 * n = n := by
--   induction n with
--   | zero => {
--     rfl
--   }
--   | succ n ih => {
--     rw [Nat.mul_succ]
--     rw [ih]
--   }

end induction

section propositional_logic
-- Wir können mit Lean auch Aussagenlogik machen.
-- Hierfür brauchen wir drei weitere Taktiken: `intro`, `apply` und `exact`.

-- P, Q und R sind drei Aussagen.
variable (P Q R : Prop)

-- Eine Annahme kann direkt als Beweis verwendet werden.
example (h : P) : P := by
  -- Wir benutzen `exact`, wenn wir die gewünschte Aussage parat haben.
  exact h

-- Eine Implikation anwenden.
example (hPQ : P → Q) (hP : P) : Q := by
  -- Wir benutzen `apply`, wenn wir eine gegebene Implikation anwenden wollen.
  apply hPQ
  exact hP

-- Eine Implikation beweisen.
example : P → P := by
  -- Wir benutzen `intro`, wenn wir eine Implikation beweisen wollen.
  intro hP
  exact hP

-- Wir können jetzt auch `mp` von oben beweisen.
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  -- Wir benutzen `apply`, um eine gegebene Implikation anzuwenden.
  apply hPQ
  -- Wir benutzen `exact`, wenn wir die gewünschte Aussage parat haben.
  exact hP


-- Für die nächsten Aufgaben brauchen
-- wir nur `intro`, `apply` und `exact`.

-- Übung 1
example (hP : P) : Q → P := by
  sorry


-- Übung 2
example (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  sorry

-- Übung 3
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  sorry

-- Lösung 1
example (hP : P) : Q → P := by
  intro hQ
  exact hP

-- Lösung 2
example (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  apply hQR
  apply hPQ
  exact hP

-- Lösung 3
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP

end propositional_logic


section next_steps
/-
Was sind sinnvolle nächste Schritte?
* Natural Number Game: https://adam.math.hhu.de/#/g/leanprover-community/nng4
* Lean installieren und ausprobieren!

Lean MathLib (eine bekannte Lean Bibliothek)
enthält bereits große Teile der typischen Bachelor-Mathematik:
-/
#check Group -- Gruppentheorie
#check Ring -- Ringtheorie
#check TopologicalSpace -- Topologie
#check MetricSpace -- Metrische Räume

end next_steps
