import Mathlib

/-!
# The restart-with-doubled-output-length pattern

`uniform_polynomial`, `eta_polynomial` and `challenge_polynomial` each run
one pass over a finite XOF prefix of length `L`, and when the pass does not
complete they call themselves again with `2 * L`. `restartLoop pass calls L`
is that recursion with the number of calls bounded by `calls`.

`restartLoop_returns_iff`: if (1) every completed pass yields a
specification output, (2) the specification has at most one output, and
(3) whenever the specification has an output, every pass over a long
enough prefix completes with it, then the recursion returns exactly the
specification output, and returns whenever the specification does.
-/

namespace OcamlPq.MLDSAAlg

/-- Generic restart recursion (see the module docstring). -/
def restartLoop {α : Type} (pass : ℕ → Option α) : ℕ → ℕ → Option α
  | 0, _ => none
  | calls + 1, L =>
    match pass L with
    | some a => some a
    | none => restartLoop pass calls (2 * L)

theorem restartLoop_some {α : Type} {pass : ℕ → Option α} :
    ∀ {calls L : ℕ} {a : α}, restartLoop pass calls L = some a → ∃ L', L ≤ L' ∧ pass L' = some a := by
  intro calls
  induction calls with
  | zero => intro L a h; simp [restartLoop] at h
  | succ c ih =>
    intro L a h
    rw [restartLoop] at h
    cases hp : pass L with
    | some b => rw [hp] at h; cases h; exact ⟨L, le_rfl, hp⟩
    | none =>
      rw [hp] at h
      obtain ⟨L', hL', h'⟩ := ih h
      exact ⟨L', by omega, h'⟩

theorem restartLoop_complete {α : Type} {pass : ℕ → Option α} {P : ℕ}
    (hP : ∀ L, P ≤ L → (pass L).isSome) :
    ∀ (calls L : ℕ), P ≤ L * 2 ^ calls → (restartLoop pass (calls + 1) L).isSome := by
  intro calls
  induction calls with
  | zero =>
    intro L hL
    have := hP L (by simpa using hL)
    rw [restartLoop]
    cases hp : pass L with
    | some b => simp
    | none => rw [hp] at this; simp at this
  | succ c ih =>
    intro L hL
    rw [restartLoop]
    cases hp : pass L with
    | some b => simp
    | none => exact ih (2 * L) (by rw [pow_succ] at hL; linarith)

/-- Generic refinement theorem for restart loops. Passes are only ever run
    with lengths `≥ L0`, so soundness is only needed there. -/
theorem restartLoop_returns_iff' {α : Type} {pass : ℕ → Option α} {Spec : α → Prop} {L0 : ℕ}
    (hsound : ∀ L a, L0 ≤ L → pass L = some a → Spec a)
    (huniq : ∀ a b, Spec a → Spec b → a = b)
    (hcomplete : ∀ a, Spec a → ∃ P, ∀ L, P ≤ L → pass L = some a)
    (hL0 : 0 < L0) (a : α) :
    (∃ calls, restartLoop pass calls L0 = some a) ↔ Spec a := by
  constructor
  · rintro ⟨calls, h⟩
    obtain ⟨L', hle, hL'⟩ := restartLoop_some h
    exact hsound _ _ hle hL'
  · intro ha
    obtain ⟨P, hP⟩ := hcomplete a ha
    have hbig : P ≤ L0 * 2 ^ P := by
      have : P < 2 ^ P := Nat.lt_two_pow_self
      nlinarith
    have := restartLoop_complete (pass := pass) (P := P)
      (fun L hL => by rw [hP L hL]; rfl) P L0 hbig
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp this
    obtain ⟨L', hle, hL'⟩ := restartLoop_some hb
    rw [huniq _ _ (hsound _ _ hle hL') ha] at hb
    exact ⟨_, hb⟩

/-- Generic refinement theorem for restart loops. -/
theorem restartLoop_returns_iff {α : Type} {pass : ℕ → Option α} {Spec : α → Prop}
    (hsound : ∀ L a, pass L = some a → Spec a)
    (huniq : ∀ a b, Spec a → Spec b → a = b)
    (hcomplete : ∀ a, Spec a → ∃ P, ∀ L, P ≤ L → pass L = some a)
    {L0 : ℕ} (hL0 : 0 < L0) (a : α) :
    (∃ calls, restartLoop pass calls L0 = some a) ↔ Spec a :=
  restartLoop_returns_iff' (fun L a _ h => hsound L a h) huniq hcomplete hL0 a

/-- The recursion is deterministic. -/
theorem restartLoop_unique {α : Type} {pass : ℕ → Option α} {Spec : α → Prop}
    (hsound : ∀ L a, pass L = some a → Spec a)
    (huniq : ∀ a b, Spec a → Spec b → a = b) {c c' L : ℕ} {a b : α}
    (ha : restartLoop pass c L = some a) (hb : restartLoop pass c' L = some b) : a = b := by
  obtain ⟨_, _, h1⟩ := restartLoop_some ha
  obtain ⟨_, _, h2⟩ := restartLoop_some hb
  exact huniq _ _ (hsound _ _ h1) (hsound _ _ h2)

end OcamlPq.MLDSAAlg
