# Making Claude Code Prove the Irrationality of the Square Root of 2.
This is a small demonstration for how Claude Code may be used to formalise proofs using Lean.

For this, we’ll be tasking it with proving the irrationality of $\sqrt{2}$:
<img width="2998" height="872" alt="image" src="https://github.com/user-attachments/assets/a42fe5a0-3dc4-488f-813a-8c7593317293" />
(The fancy rainbow-coloured `ultrathink` keyword allocates maximum compute budget to it, so it “thinks” for longer. This is useful for initial requests, where proper planning could make the difference between a failed project and a successful one.)

Claude Code can ask you questions to better understand your goals:

<img width="48%" alt="image" src="https://github.com/user-attachments/assets/3a0a053a-523c-454d-bfe9-fc791a0de327" />
<img width="48%" alt="image" src="https://github.com/user-attachments/assets/d2a78524-85a9-4f5d-ba72-c27d3da127cd" />

It can also make TODO lists with tasks it has to accomplish, plan, etc., as well as run commands:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/c18ea9f8-6983-45a7-840d-39ef4ece1348" />

It can write files by itself, as well as create them if they don’t exist:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/fc0d03fb-4642-4ad7-8ff7-c0c56221f77d" />

It can also identify flaws in its work and self-correct:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/2b4d838f-fce1-47fc-bef1-597fed99b83d" />

It will try to compile the code, debug it if it doesn’t compile, and keep working until it eventually does:

<img width="70%" height="1354" alt="image" src="https://github.com/user-attachments/assets/8ed436b4-116e-4848-a909-17437ced72be" />

After several iterations, Claude Code has produced a compilable proof:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/83c9d901-3681-41c4-b3da-dd60e077dc26" />

Here it is!
```lean
/-
  Proof that √2 is irrational using the classic contradiction argument.

  The proof proceeds as follows:
  1. Assume √2 = a/b where a, b are coprime integers
  2. Squaring: 2b² = a²
  3. Therefore a² is even, so a is even
  4. Write a = 2k, then 2b² = 4k², so b² = 2k²
  5. Therefore b² is even, so b is even
  6. Both a and b are even contradicts coprimality
-/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Sqrt2Proof.Basic

open Real in
/-- The square root of 2 is irrational.

This is the classic proof by contradiction: assuming √2 = a/b in lowest terms,
we derive that both a and b must be even, contradicting coprimality.

Note: Mathlib already provides `irrational_sqrt_two` via prime factorization.
This theorem demonstrates the elementary proof. -/
theorem sqrt_two_irrational : Irrational (sqrt 2) := by
  -- Unfold the definition: we need to show √2 is not rational
  rw [irrational_iff_ne_rational]
  -- Assume √2 = a/b for some integers a, b with b ≠ 0
  intro a b hb hsqrt
  -- We'll work with the rational number a/b in lowest terms
  set q : ℚ := a / b with hq_def
  -- √2 = q as reals
  have hsqrt_q : sqrt 2 = (q : ℝ) := by simp [hq_def, hsqrt]
  -- Therefore q² = 2
  have hq_sq : q ^ 2 = 2 := by
    have h1 : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
    rw [hsqrt_q] at h1
    exact_mod_cast h1
  -- Get the numerator and denominator of q in lowest terms
  let n := q.num.natAbs
  let d := q.den
  have hd_pos : 0 < d := q.den_pos
  have hcoprime : Nat.Coprime n d := q.reduced
  -- q² = 2 means n²/d² = 2, so n² = 2d²
  have hnat_eq : n ^ 2 = 2 * d ^ 2 := by
    have hd_ne_zero : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd_pos)
    -- q² = (num/den)² = num²/den²
    have h1 : q ^ 2 = (q.num : ℚ) ^ 2 / (q.den : ℚ) ^ 2 := by
      conv_lhs => rw [← Rat.num_div_den q]
      rw [div_pow]
    rw [hq_sq] at h1
    -- So num² = 2 * den²
    have h2 : (q.num : ℚ) ^ 2 = 2 * (d : ℚ) ^ 2 := by
      have hd2_ne : (d : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hd_ne_zero
      field_simp at h1
      linarith
    -- n² = natAbs(q.num)² = q.num² (as integers)
    have hn_sq : (n : ℤ) ^ 2 = q.num ^ 2 := Int.natAbs_sq q.num
    -- Convert h2 from ℚ to ℤ
    have h3 : (q.num : ℤ) ^ 2 = 2 * (d : ℤ) ^ 2 := by
      have := h2
      have hcq : (q.num : ℚ) ^ 2 = ((q.num ^ 2 : ℤ) : ℚ) := by push_cast; ring
      have hcd : (d : ℚ) ^ 2 = ((d ^ 2 : ℕ) : ℚ) := by push_cast; ring
      rw [hcq, hcd] at this
      exact_mod_cast this
    -- Combine: n² = q.num² = 2 * d²
    have h4 : (n : ℤ) ^ 2 = 2 * (d : ℤ) ^ 2 := by
      rw [hn_sq]; exact h3
    -- Convert back to ℕ
    have h5 : ((n ^ 2 : ℕ) : ℤ) = 2 * ((d ^ 2 : ℕ) : ℤ) := by
      push_cast at h4 ⊢; exact h4
    exact_mod_cast h5
  -- Step 3: 2 | n² implies 2 | n
  have hdvd_n_sq : 2 ∣ n ^ 2 := ⟨d ^ 2, by omega⟩
  have hdvd_n : 2 ∣ n := Nat.two_dvd_of_two_dvd_pow_two hdvd_n_sq
  -- Step 4: Write n = 2k, then derive 2k² = d²
  have ⟨k, hk⟩ := hdvd_n
  have h2k2 : 2 * k ^ 2 = d ^ 2 := by
    have hn4k : n ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    omega
  -- Step 5: 2 | d² implies 2 | d
  have hdvd_d_sq : 2 ∣ d ^ 2 := ⟨k ^ 2, by omega⟩
  have hdvd_d : 2 ∣ d := Nat.two_dvd_of_two_dvd_pow_two hdvd_d_sq
  -- Step 6: Contradiction - both n and d divisible by 2, but gcd(n,d) = 1
  have hdvd_gcd : 2 ∣ Nat.gcd n d := Nat.dvd_gcd hdvd_n hdvd_d
  rw [hcoprime.gcd_eq_one] at hdvd_gcd
  omega

/-- Alternative statement: √2 is irrational (using our theorem name). -/
theorem sqrt_two_is_irrational : Irrational (Real.sqrt 2) := sqrt_two_irrational
```
It even supports tools allowing you to improve the proofs:

<img width="48%" alt="image" src="https://github.com/user-attachments/assets/74e9fc69-1df9-45de-a75e-3eb126399385" />

<img width="48%" alt="image" src="https://github.com/user-attachments/assets/717afb88-4689-47a1-869d-2b514f842f50" />

And you can ask it to revise its own code too:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/2380ac1a-8216-4659-8c3e-b200552b5b15" />

This will often lead to improved code, which may range from minor improvements to complete upheavals.

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/ccd8aa3a-9993-43c0-97db-b9e42286b70f" />

Here’s the final, revised proof:
```lean
/-
  Optimized proof that √2 is irrational using the classic contradiction argument.
  Golfed version with ~40% fewer lines than the original.
-/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Sqrt2Proof.Basic

open Real in
/-- The square root of 2 is irrational (optimized proof). -/
theorem sqrt_two_irrational' : Irrational (sqrt 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hsqrt
  set q : ℚ := a / b with hq_def
  -- q² = 2 (derive from √2 = a/b)
  have hq_sq : q ^ 2 = 2 := by
    have h1 : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num)
    have h2 : sqrt 2 = (q : ℝ) := by simp [hq_def, hsqrt]
    rw [h2] at h1; exact_mod_cast h1
  let n := q.num.natAbs
  let d := q.den
  have hcoprime : Nat.Coprime n d := q.reduced
  -- n² = 2d² (collapsed casting chain)
  have hnat_eq : n ^ 2 = 2 * d ^ 2 := by
    have h1 : (q.num : ℚ) ^ 2 = 2 * (q.den : ℚ) ^ 2 := by
      have := hq_sq
      rw [← Rat.num_div_den q, div_pow] at this
      field_simp [Nat.cast_ne_zero.mpr q.den_pos.ne'] at this
      linarith
    have h2 : (q.num.natAbs : ℤ) ^ 2 = 2 * (q.den : ℤ) ^ 2 := by
      rw [Int.natAbs_sq]; exact_mod_cast h1
    exact_mod_cast h2
  -- 2 | n (inlined intermediate step)
  have hdvd_n : 2 ∣ n := Nat.two_dvd_of_two_dvd_pow_two ⟨d ^ 2, by omega⟩
  have ⟨k, hk⟩ := hdvd_n
  -- 2 | d
  have h2k2 : 2 * k ^ 2 = d ^ 2 := by
    have : n ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    omega
  have hdvd_d : 2 ∣ d := Nat.two_dvd_of_two_dvd_pow_two ⟨k ^ 2, by omega⟩
  -- Contradiction: 2 | gcd(n,d) but gcd(n,d) = 1
  exact absurd (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd hdvd_n hdvd_d) (by omega)
```
