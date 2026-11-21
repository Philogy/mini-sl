import Lake
open Lake DSL

package "mini-sl" where
  version := v!"0.1.0"

@[default_target]
lean_lib «MiniSl» where
  -- add library configuration options here
