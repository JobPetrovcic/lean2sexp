module

public import ModTest.A

public theorem double_double (n : Nat) : double (double n) = 4 * n := by
  rw [double_eq, double_eq]
  omega

public def quad (n : Nat) : Nat := double (double n)
