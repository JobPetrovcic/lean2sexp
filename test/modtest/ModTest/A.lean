module

public def double (n : Nat) : Nat := n + n

-- `private`: name-mangled to `_private.ModTest.A.0.double_eq_aux`
private theorem double_eq_aux (n : Nat) : n + n = 2 * n := by omega

-- not `public`: lives only in the .olean.private part
theorem double_eq_internal (n : Nat) : double n = 2 * n := double_eq_aux n

public theorem double_eq (n : Nat) : double n = 2 * n := double_eq_internal n
