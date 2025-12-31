import Lake
open Lake DSL

package convergent where
  version := v!"0.1.0"

require crucible from git "https://github.com/nathanial/crucible" @ "v0.0.1"
require plausible from git
  "https://github.com/leanprover-community/plausible.git" @ "v4.26.0"

@[default_target]
lean_lib Convergent where
  roots := #[`Convergent]

lean_lib ConvergentTests where
  globs := #[.submodules `ConvergentTests]

@[test_driver]
lean_exe convergent_tests where
  root := `ConvergentTests.Main
