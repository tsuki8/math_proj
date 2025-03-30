namespace a
  scoped notation:71 lhs:50 " 💀 " rhs:72 => lhs - rhs
end a

namespace b
  set_option quotPrecheck false
  scoped infixl:71 " 💀 " => fun lhs rhs => lhs - rhs
end b

namespace c
  scoped syntax:71 term:50 " 💀 " term:72 : term
  scoped macro_rules | `($l:term 💀 $r:term) => `($l - $r)
end c

open a
#eval 5 * 8 💀 4 -- 20
#eval 8 💀 6 💀 1 -- 1
