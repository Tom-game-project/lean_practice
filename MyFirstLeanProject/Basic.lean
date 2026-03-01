-- 証明の練習
-- 自然数の基本的な性質を示す

inductive MyNat where
  | zero: MyNat
  | succ: MyNat -> MyNat

def add (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero   => m
  | MyNat.succ n => MyNat.succ (add m n)

-- たぶんこれで、中置記法を使えるようにする
instance : Add MyNat where
  add := add


-- 加算に関わる定理

-- ここは自分には魔法のように思える
-- 後で何故かを確かめる
theorem add_succ (a b: MyNat): a + MyNat.succ b = MyNat.succ (a + b) := by
  rfl

-- これは定義より自明
theorem add_zero (a: MyNat): a + MyNat.zero = a := by
  rfl

theorem zero_add (a: MyNat): MyNat.zero + a = a := by
  induction a with
  | zero => 
    rfl
  | succ d hd =>
    rw [add_succ]
    rw [hd]

theorem zero_add_zero : MyNat.zero + MyNat.zero = MyNat.zero := by
  rfl

theorem succ_add (a b : MyNat): MyNat.succ a + b = MyNat.succ (a + b) := by
  induction b with
  | zero =>
    rw [add_zero]
    rw [add_zero]
  | succ d hd =>
    rw [add_succ]
    rw [hd]
    rw [add_succ]

theorem add_comm (a b: MyNat): a + b = b + a := by
  induction a with
  | zero =>
    rw [zero_add]
    rw [add_zero]
  | succ d hd =>
    rw [succ_add]
    rw [add_succ]
    rw [hd]

theorem add_assoc (a b c: MyNat): a + b + c = a + (c + b) := by
  induction a with
  | zero =>
    rw [zero_add]
    rw [zero_add]
    rw [add_comm]
  | succ k hd =>
    rw [succ_add]
    rw [succ_add]
    rw [succ_add]
    rw [hd]

-- 掛け算の定義

def mul (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero => MyNat.zero
  | MyNat.succ n => add (mul m n) m


-- たぶんこれで、中置記法を使えるようにする
instance : Mul MyNat where
  mul := mul

theorem mul_succ (a b: MyNat): a * MyNat.succ b = a * b + a := by
  rfl

theorem mul_zero (n: MyNat): n * MyNat.zero = MyNat.zero := by
  rfl

theorem zero_mul (n: MyNat): MyNat.zero * n = MyNat.zero := by
  induction n with
  | zero =>
    rw [mul_zero]
  | succ d hd =>
    rw [mul_succ]
    rw [hd]
    rw [zero_add]

theorem mul_one (n: MyNat): n * (MyNat.succ MyNat.zero) = n := by
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]

theorem one_mul (n: MyNat): (MyNat.succ MyNat.zero) * n = n := by
  induction n with
  | zero =>
    rw [mul_zero]
  | succ d hd =>
    rw [mul_succ]
    rw [hd]
    rw [mul_succ]
    -- succ_eq_add_one: TODO

-- theorem two_mul (n: MyNat): n * (MyNat.succ (MyNat.succ MyNat.zero)) = n + n := by
--   induction n with
--   | zero =>
--     rw [zero_mul]
--   | succ d hd =>
--     rw [succ_mul]

theorem succ_mul (a b: MyNat): MyNat.succ a * b = b + a * b := by
  induction a with
  | zero =>
    rw []
  | succ d hd =>


