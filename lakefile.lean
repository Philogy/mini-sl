import Lake
open Lake DSL

package "mini-sl" where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «MiniSl» where
  -- add library configuration options here
