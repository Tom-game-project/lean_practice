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

theorem succ_eq_add_one (n: MyNat): MyNat.succ n = n + MyNat.succ MyNat.zero := by
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

theorem add_right_comm (a b c: MyNat): a + b + c = a + c + b := by
  induction a with
  | zero =>
    rw [zero_add]
    rw [zero_add]
    rw [add_comm]
  | succ d hd =>
    rw [succ_add]
    rw [succ_add]
    rw [succ_add]
    rw [succ_add]
    rw [hd]

theorem add_assoc (a b c: MyNat): a + b + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_add]
    rw [zero_add]
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
    rw [add_succ]
    rw [add_zero]

-- theorem two_mul (n: MyNat): n * (MyNat.succ (MyNat.succ MyNat.zero)) = n + n := by
--   induction n with
--   | zero =>
--     rw [zero_mul]
--   | succ d hd =>
--     rw [succ_mul]

theorem succ_mul (a b: MyNat): MyNat.succ a * b = a * b + b := by
  -- (a + 1) *b
  -- a * b + b
  induction b with
  | zero =>
    rw [mul_zero]
    rw [mul_zero]
    rw [add_zero]
  | succ d hd =>
    rw [mul_succ]
    rw [mul_succ]
    rw [hd]
    rw [add_succ]
    rw [add_succ]
    rw [add_right_comm]

theorem mul_comm (a b : MyNat): a * b = b * a := by
  induction a with
  | zero =>
    rw [zero_mul]
    rw [mul_zero]
  | succ d hd =>
    rw [succ_mul]
    rw [mul_succ]
    rw [hd]

theorem mul_add (a b c: MyNat): a * (b + c) = a * b + a * c := by
  induction a with
  | zero =>
    rw [zero_mul]
    rw [zero_mul]
    rw [zero_mul]
    rw [add_zero]
  | succ d hd =>
    rw [succ_mul]
    rw [succ_mul]
    rw [succ_mul]
    rw [hd]
    rw [← add_assoc]
    rw [add_comm]
    rw [add_right_comm]
    rw [add_comm]
    rw [← add_assoc]
    
theorem add_mul (a b c: MyNat): (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
    rw [mul_zero]
    rw [mul_zero]
    rw [mul_zero]
    rw [add_zero]
  | succ d hd =>
    rw [mul_succ]
    rw [mul_succ]
    rw [mul_succ]
    rw [hd]
    rw [← add_assoc]
    rw [← add_assoc]
    rw [add_comm]
    rw [add_right_comm]
    rw [add_comm]

theorem mul_assoc (a b c: MyNat): a * b * c = a * (b * c) := by
  induction a with
  | zero =>
    rw [zero_mul]
    rw [zero_mul]
    rw [zero_mul]
  | succ d hd =>
    rw [succ_mul]
    rw [succ_mul]
    rw [add_mul]
    rw [hd]

def hello := "world"
