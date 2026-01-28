def hello := "world"

variable (a b c : Nat)

theorem test1 : a = a := by
  rfl -- "Reflexivity"の略。両辺が等しいことを自動で判定します

theorem test2 : a + 0 + b = a + b := by
  rw [Nat.add_zero] -- "a + 0" を "a" に書き換える (Rewrite)

-- 【問題3】 少し複雑なパズル (交換律の応用)
theorem test3 : a + b + c = a + c + b := by
  -- ゴール: a + b + c = a + c + b
  rw [Nat.add_assoc] -- 結合律 (a+b)+c を a+(b+c) に変形
  -- ゴール: a + (b + c) = a + c + b
  rw [Nat.add_comm b c] -- カッコの中の b+c を c+b に変形
  -- ゴール: a + (c + b) = a + c + b
  rw [Nat.add_assoc] -- もう一度結合律を使って戻す
  -- ゴール: a + c + b = a + c + b (両辺が同じになった！)

theorem even_plus_even(m n : Nat) : ∃ k, 2 * m + 2 * n = 2 * k := by
  exists m + n
  rw [Nat.mul_add]

theorem odd_plus_odd (m n : Nat) : ∃ k , (2 * m + 1) + (2 * n + 1) = 2 * k := by
  exists m + n + 1
  rw [Nat.add_assoc]
  rw [Nat.add_comm (2*n) 1]
  rw [Nat.add_comm]
  rw [Nat.add_assoc]

