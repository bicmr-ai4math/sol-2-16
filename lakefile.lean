import Lake
open Lake DSL

package «sol-2-16» {
  -- add package configuration options here
}

lean_lib «Sol-2-16-bonus» {
  -- add library configuration options here
}

@[default_target]
lean_exe «sol-2-16» {
  root := `Main
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
